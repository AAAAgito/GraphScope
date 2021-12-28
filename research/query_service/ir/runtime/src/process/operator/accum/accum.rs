//
//! Copyright 2021 Alibaba Group Holding Limited.
//!
//! Licensed under the Apache License, Version 2.0 (the "License");
//! you may not use this file except in compliance with the License.
//! You may obtain a copy of the License at
//!
//! http://www.apache.org/licenses/LICENSE-2.0
//!
//! Unless required by applicable law or agreed to in writing, software
//! distributed under the License is distributed on an "AS IS" BASIS,
//! WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//! See the License for the specific language governing permissions and
//! limitations under the License.

use std::convert::{TryFrom, TryInto};
use std::sync::Arc;

use ir_common::error::ParsePbError;
use ir_common::generated::algebra as algebra_pb;
use ir_common::generated::algebra::group_by::agg_func::Aggregate;
use ir_common::NameOrId;
use pegasus::codec::{Decode, Encode, ReadExt, WriteExt};

use crate::error::{FnExecError, FnExecResult, FnGenError, FnGenResult};
use crate::process::operator::accum::accumulator::{Accumulator, Count, ToList};
use crate::process::operator::accum::AccumFactoryGen;
use crate::process::operator::TagKey;
use crate::process::record::{Entry, ObjectElement, Record};

#[derive(Debug, Clone)]
pub enum EntryAccumulator {
    // TODO(bingqing): more accum kind
    ToCount(Count<Arc<Entry>>),
    ToList(ToList<Arc<Entry>>),
}

#[derive(Debug, Clone)]
pub struct RecordAccumulator {
    accum_ops: Vec<(EntryAccumulator, TagKey, NameOrId)>,
}

impl Accumulator<Record, Record> for RecordAccumulator {
    fn accum(&mut self, mut next: Record) -> FnExecResult<()> {
        for (accumulator, tag_key, _) in self.accum_ops.iter_mut() {
            let entry = tag_key.get_entry(&mut next)?;
            accumulator.accum(entry)?;
        }
        Ok(())
    }

    fn finalize(&mut self) -> FnExecResult<Record> {
        let mut record = Record::default();
        for (accumulator, _, alias) in self.accum_ops.iter_mut() {
            let entry = accumulator.finalize()?;
            record.append_arc_entry(entry, Some(alias.clone()));
        }
        Ok(record)
    }
}

impl Accumulator<Arc<Entry>, Arc<Entry>> for EntryAccumulator {
    fn accum(&mut self, next: Arc<Entry>) -> FnExecResult<()> {
        match self {
            EntryAccumulator::ToCount(count) => count.accum(next),
            EntryAccumulator::ToList(list) => list.accum(next),
        }
    }

    fn finalize(&mut self) -> FnExecResult<Arc<Entry>> {
        match self {
            EntryAccumulator::ToCount(count) => {
                let cnt = count.finalize()?;
                Ok(Arc::new(ObjectElement::Count(cnt).into()))
            }
            EntryAccumulator::ToList(list) => {
                let list_entry = list
                    .finalize()?
                    .into_iter()
                    .map(|entry| match entry.as_ref() {
                        Entry::Element(e) => Ok(e.clone()),
                        Entry::Collection(_) => {
                            Err(FnExecError::unsupported_error("fold collections is not supported yet"))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Arc::new(Entry::Collection(list_entry)))
            }
        }
    }
}

impl AccumFactoryGen for algebra_pb::GroupBy {
    fn gen_accum(self) -> FnGenResult<RecordAccumulator> {
        let mut accum_ops = Vec::with_capacity(self.functions.len());
        for agg_func in self.functions {
            let agg_kind: algebra_pb::group_by::agg_func::Aggregate =
                unsafe { ::std::mem::transmute(agg_func.aggregate) };
            if agg_func.vars.len() > 1 {
                // e.g., count_distinct((a,b));
                // TODO: to support this, we may need to define MultiTagKey (could define TagKey Trait, and impl for SingleTagKey and MultiTagKey)
                Err(FnGenError::unsupported_error("Do not support to aggregate multiple fields yet"))?
            }
            let tag_key = agg_func
                .vars
                .get(0)
                .map(|v| TagKey::try_from(v.clone()))
                .transpose()?
                .unwrap_or(TagKey::default());
            let alias: Option<NameOrId> = agg_func
                .alias
                .ok_or(ParsePbError::from("accum value alias is missing"))?
                .try_into()?;
            // TODO: accum value alias in fold can be None;
            let alias = alias.ok_or(ParsePbError::from("accum value alias cannot be None"))?;
            let entry_accumulator = match agg_kind {
                Aggregate::Count => EntryAccumulator::ToCount(Count { value: 0, _ph: Default::default() }),
                Aggregate::ToList => EntryAccumulator::ToList(ToList { inner: vec![] }),
                _ => Err(FnGenError::unsupported_error(&format!(
                    "Unsupported aggregate kind {:?}",
                    agg_kind
                )))?,
            };
            accum_ops.push((entry_accumulator, tag_key, alias));
        }
        debug!("Runtime accumulator operator: {:?}", accum_ops);
        Ok(RecordAccumulator { accum_ops })
    }
}

impl Encode for RecordAccumulator {
    fn write_to<W: WriteExt>(&self, _writer: &mut W) -> std::io::Result<()> {
        todo!()
    }
}

impl Decode for RecordAccumulator {
    fn read_from<R: ReadExt>(_reader: &mut R) -> std::io::Result<Self> {
        todo!()
    }
}

#[cfg(test)]
mod tests {

    use ir_common::generated::algebra as pb;
    use ir_common::generated::common as common_pb;
    use ir_common::NameOrId;
    use pegasus::api::{Fold, Sink};
    use pegasus::result::ResultStream;
    use pegasus::JobConf;

    use crate::process::operator::accum::accumulator::Accumulator;
    use crate::process::operator::accum::AccumFactoryGen;
    use crate::process::operator::tests::{init_source, init_vertex1, init_vertex2};
    use crate::process::record::{Entry, ObjectElement, Record, RecordElement};

    fn fold_test(source: Vec<Record>, fold_opr_pb: pb::GroupBy) -> ResultStream<Record> {
        let conf = JobConf::new("fold_test");
        let result = pegasus::run(conf, || {
            let fold_opr_pb = fold_opr_pb.clone();
            let source = source.clone();
            move |input, output| {
                let stream = input.input_from(source.into_iter())?;
                let accum = fold_opr_pb.clone().gen_accum().unwrap();
                let res_stream = stream
                    .fold(accum, || {
                        move |mut accumulator, next| {
                            accumulator.accum(next)?;
                            Ok(accumulator)
                        }
                    })?
                    .map(|mut accum| Ok(accum.finalize()?))?
                    .into_stream()?;
                res_stream.sink_into(output)
            }
        })
        .expect("build job failure");

        result
    }

    // g.V().fold().as("a")
    #[test]
    fn fold_to_list_test() {
        let function = pb::group_by::AggFunc {
            vars: vec![common_pb::Variable::from("@".to_string())],
            aggregate: 5, // to_list
            alias: Some(pb::Alias {
                alias: Some(NameOrId::Str("a".to_string()).into()),
                is_query_given: false,
            }),
        };
        let fold_opr_pb = pb::GroupBy { mappings: vec![], functions: vec![function] };
        let mut result = fold_test(init_source(), fold_opr_pb);
        let mut fold_result = Entry::Collection(vec![]);
        let expected_result = Entry::Collection(vec![
            RecordElement::OnGraph(init_vertex1().into()),
            RecordElement::OnGraph(init_vertex2().into()),
        ]);
        if let Some(Ok(record)) = result.next() {
            if let Some(entry) = record.get(Some(&"a".into())) {
                fold_result = entry.as_ref().clone();
            }
        }
        assert_eq!(fold_result, expected_result);
    }

    // g.V().count().as("a") // unoptimized version, use accumulator directly
    #[test]
    fn count_unopt_test() {
        let function = pb::group_by::AggFunc {
            vars: vec![common_pb::Variable::from("@".to_string())],
            aggregate: 3, // count
            alias: Some(pb::Alias {
                alias: Some(NameOrId::Str("a".to_string()).into()),
                is_query_given: false,
            }),
        };
        let fold_opr_pb = pb::GroupBy { mappings: vec![], functions: vec![function] };
        let mut result = fold_test(init_source(), fold_opr_pb);
        let mut cnt = 0;
        if let Some(Ok(record)) = result.next() {
            if let Some(entry) = record.get(Some(&"a".into())) {
                cnt = match entry.as_ref() {
                    Entry::Element(RecordElement::OffGraph(ObjectElement::Count(cnt))) => *cnt,
                    _ => {
                        unreachable!()
                    }
                };
            }
        }
        assert_eq!(cnt, 2);
    }

    // g.V().fold(to_list().as("a"), count().as("b"))
    #[test]
    fn fold_multi_accum_test() {
        let function_1 = pb::group_by::AggFunc {
            vars: vec![common_pb::Variable::from("@".to_string())],
            aggregate: 5, // to_list
            alias: Some(pb::Alias {
                alias: Some(NameOrId::Str("a".to_string()).into()),
                is_query_given: false,
            }),
        };
        let function_2 = pb::group_by::AggFunc {
            vars: vec![common_pb::Variable::from("@".to_string())],
            aggregate: 3, // Count
            alias: Some(pb::Alias {
                alias: Some(NameOrId::Str("b".to_string()).into()),
                is_query_given: false,
            }),
        };
        let fold_opr_pb = pb::GroupBy { mappings: vec![], functions: vec![function_1, function_2] };
        let mut result = fold_test(init_source(), fold_opr_pb);
        let mut fold_result: (Entry, Entry) = (Entry::Collection(vec![]), ObjectElement::Count(0).into());
        let expected_result: (Entry, Entry) = (
            Entry::Collection(vec![
                RecordElement::OnGraph(init_vertex1().into()),
                RecordElement::OnGraph(init_vertex2().into()),
            ]),
            ObjectElement::Count(2).into(),
        );
        if let Some(Ok(record)) = result.next() {
            let collection_entry = record
                .get(Some(&"a".into()))
                .unwrap()
                .as_ref()
                .clone();
            let count_entry = record
                .get(Some(&"b".into()))
                .unwrap()
                .as_ref()
                .clone();
            fold_result = (collection_entry, count_entry);
        }
        assert_eq!(fold_result, expected_result);
    }
}
