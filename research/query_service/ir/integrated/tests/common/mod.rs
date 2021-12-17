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
//!
//!

#[cfg(test)]
#[allow(dead_code)]
#[allow(unused_imports)]
pub mod test {
    use graph_proxy::{InitializeJobCompiler, QueryExpGraph};
    use ir_common::generated::algebra as pb;
    use ir_common::generated::common as common_pb;
    use ir_common::generated::results as result_pb;
    use lazy_static::lazy_static;
    use pegasus::result::{ResultSink, ResultStream};
    use pegasus::{run_opt, Configuration, JobConf, StartupError};
    use pegasus_server::service::JobParser;
    use pegasus_server::JobRequest;
    use runtime::expr::to_suffix_expr_pb;
    use runtime::expr::token::tokenize;
    use runtime::graph::element::{Edge, Vertex, VertexOrEdge};
    use runtime::graph::property::{DefaultDetails, DynDetails};
    use runtime::graph::ID;
    use runtime::process::record::{Entry, Record, RecordElement};
    use runtime::IRJobCompiler;
    use std::convert::{TryFrom, TryInto};
    use std::sync::Once;

    static INIT: Once = Once::new();

    lazy_static! {
        static ref FACTORY: IRJobCompiler = initialize_job_compiler();
    }

    pub fn initialize() {
        INIT.call_once(|| {
            start_pegasus();
        });
    }

    fn start_pegasus() {
        match pegasus::startup(Configuration::singleton()) {
            Ok(_) => {
                lazy_static::initialize(&FACTORY);
            }
            Err(err) => match err {
                StartupError::AlreadyStarted(_) => {}
                _ => panic!("start pegasus failed"),
            },
        }
    }

    fn initialize_job_compiler() -> IRJobCompiler {
        let query_exp_graph = QueryExpGraph::new(1);
        query_exp_graph.initialize_job_compiler()
    }

    pub fn submit_query(job_req: JobRequest, num_workers: u32) -> ResultStream<result_pb::Results> {
        let mut conf = JobConf::default();
        conf.workers = num_workers;
        let (tx, rx) = crossbeam_channel::unbounded();
        let sink = ResultSink::new(tx);
        let cancel_hook = sink.get_cancel_hook().clone();
        let results = ResultStream::new(conf.job_id, cancel_hook, rx);
        run_opt(conf, sink, |worker| {
            worker.dataflow(|input, output| FACTORY.parse(&job_req, input, output))
        })
        .expect("submit job failure;");

        results
    }

    pub fn parse_result(result: result_pb::Results) -> Option<Record> {
        if let Some(result_pb::results::Inner::Record(record_pb)) = result.inner {
            let mut record = Record::default();
            for column in record_pb.columns {
                let tag =
                    if let Some(tag) = column.name_or_id { Some(tag.try_into().unwrap()) } else { None };
                let entry = column.entry.unwrap();
                record.append(Entry::try_from(entry).unwrap(), tag);
            }
            Some(record)
        } else {
            None
        }
    }

    pub fn into_and_condition(id: ID) -> pb::index_predicate::AndCondition {
        pb::index_predicate::AndCondition {
            conds: vec![pb::index_predicate::EquivCond {
                key: Some(common_pb::Property {
                    item: Some(common_pb::property::Item::Id(common_pb::IdKey {})),
                }),
                value: Some(common_pb::Const {
                    value: Some(common_pb::Value { item: Some(common_pb::value::Item::I64(id as i64)) }),
                }),
            }],
        }
    }

    pub fn into_index_predicate(ids: Vec<ID>) -> pb::IndexPredicate {
        let or_conds: Vec<pb::index_predicate::AndCondition> = ids
            .into_iter()
            .map(|id| into_and_condition(id))
            .collect();

        pb::IndexPredicate { or_conds }
    }
}
