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

use std::sync::Arc;

use ir_common::generated::algebra as algebra_pb;
use ir_common::generated::algebra::join::JoinKind;
use ir_common::generated::common as common_pb;
use ir_common::generated::results as result_pb;
use pegasus::api::function::*;
use pegasus::api::{
    Collect, CorrelatedSubTask, Dedup, Filter, IterCondition, Iteration, Join, KeyBy, Limit, Map, Merge,
    PartitionByKey, Sink, SortBy, SortLimitBy, Source,
};
use pegasus::result::ResultSink;
use pegasus::stream::Stream;
use pegasus::BuildJobError;
use pegasus_server::pb as server_pb;
use pegasus_server::service::JobParser;
use pegasus_server::JobRequest;
use prost::Message;

use crate::error::{FnExecError, FnGenResult};
use crate::graph::partitioner::Partitioner;
use crate::process::functions::{CompareFunction, JoinKeyGen, KeyFunction};
use crate::process::operator::filter::FilterFuncGen;
use crate::process::operator::flatmap::FlatMapFuncGen;
use crate::process::operator::join::JoinFunctionGen;
use crate::process::operator::keyed::KeyFunctionGen;
use crate::process::operator::map::{FilterMapFuncGen, MapFuncGen};
use crate::process::operator::shuffle::RecordRouter;
use crate::process::operator::sink::RecordSinkEncoder;
use crate::process::operator::sort::CompareFunctionGen;
use crate::process::operator::source::SourceOperator;
use crate::process::record::{Record, RecordKey};

type RecordMap = Box<dyn MapFunction<Record, Record>>;
type RecordFilterMap = Box<dyn FilterMapFunction<Record, Record>>;
type RecordFlatMap = Box<dyn FlatMapFunction<Record, Record, Target = DynIter<Record>>>;
type RecordFilter = Box<dyn FilterFunction<Record>>;
type RecordLeftJoin = Box<dyn BinaryFunction<Record, Vec<Record>, Option<Record>>>;
type RecordEncode = Box<dyn MapFunction<Record, result_pb::Results>>;
type RecordShuffle = Box<dyn RouteFunction<Record>>;
type RecordCompare = Box<dyn CompareFunction<Record>>;
type RecordJoin = Box<dyn JoinKeyGen<Record, RecordKey, Record>>;
type RecordKeySelector = Box<dyn KeyFunction<Record, RecordKey, Record>>;
type BinaryResource = Vec<u8>;

pub struct IRJobCompiler {
    udf_gen: FnGenerator,
}

struct FnGenerator {
    partitioner: Arc<dyn Partitioner>,
}

impl FnGenerator {
    fn new(partitioner: Arc<dyn Partitioner>) -> Self {
        FnGenerator { partitioner }
    }

    fn gen_source(&self, res: &BinaryResource) -> FnGenResult<DynIter<Record>> {
        let mut step = decode::<algebra_pb::logical_plan::Operator>(res)?;
        let worker_id = pegasus::get_current_worker();
        let step = SourceOperator::new(
            &mut step,
            worker_id.local_peers as usize,
            worker_id.index,
            self.partitioner.clone(),
        )?;
        Ok(step.gen_source(worker_id.index as usize)?)
    }

    fn gen_shuffle(&self, res: &BinaryResource) -> FnGenResult<RecordShuffle> {
        let p = self.partitioner.clone();
        let num_workers = pegasus::get_current_worker().local_peers as usize;
        let shuffle_key = decode::<common_pb::NameOrIdKey>(res)?;
        let record_router = RecordRouter::new(p, num_workers, shuffle_key)?;
        Ok(Box::new(record_router))
    }

    fn gen_map(&self, res: &BinaryResource) -> FnGenResult<RecordMap> {
        let step = decode::<algebra_pb::logical_plan::Operator>(res)?;
        Ok(step.gen_map()?)
    }

    fn gen_filter_map(&self, res: &BinaryResource) -> FnGenResult<RecordFilterMap> {
        let step = decode::<algebra_pb::logical_plan::Operator>(res)?;
        Ok(step.gen_filter_map()?)
    }

    fn gen_flat_map(&self, res: &BinaryResource) -> FnGenResult<RecordFlatMap> {
        let step = decode::<algebra_pb::logical_plan::Operator>(res)?;
        Ok(step.gen_flat_map()?)
    }

    fn gen_filter(&self, res: &BinaryResource) -> FnGenResult<RecordFilter> {
        let step = decode::<algebra_pb::logical_plan::Operator>(res)?;
        Ok(step.gen_filter()?)
    }

    fn gen_cmp(&self, res: &BinaryResource) -> FnGenResult<RecordCompare> {
        let step = decode::<algebra_pb::logical_plan::Operator>(res)?;
        Ok(step.gen_cmp()?)
    }

    fn gen_subtask(&self, _res: &BinaryResource) -> FnGenResult<RecordLeftJoin> {
        todo!()
    }

    fn gen_join(&self, res: &BinaryResource) -> FnGenResult<RecordJoin> {
        let step = decode::<algebra_pb::logical_plan::Operator>(res)?;
        Ok(step.gen_join()?)
    }

    fn gen_key(&self, res: &BinaryResource) -> FnGenResult<RecordKeySelector> {
        let step = decode::<algebra_pb::logical_plan::Operator>(res)?;
        Ok(step.gen_key()?)
    }

    fn gen_sink(&self, _res: &BinaryResource) -> FnGenResult<RecordEncode> {
        Ok(Box::new(RecordSinkEncoder::default()))
    }
}

impl IRJobCompiler {
    pub fn new<D: Partitioner>(partitioner: D) -> Self {
        IRJobCompiler { udf_gen: FnGenerator::new(Arc::new(partitioner)) }
    }

    fn install(
        &self, mut stream: Stream<Record>, plan: &[server_pb::OperatorDef],
    ) -> Result<Stream<Record>, BuildJobError> {
        for op in &plan[..] {
            if let Some(ref op_kind) = op.op_kind {
                match op_kind {
                    server_pb::operator_def::OpKind::Comm(comm) => match &comm.ch_kind {
                        Some(server_pb::communicate::ChKind::ToAnother(exchange)) => {
                            let router = self.udf_gen.gen_shuffle(&exchange.resource)?;
                            stream = stream.repartition(move |t| router.route(t));
                        }
                        Some(server_pb::communicate::ChKind::ToOne(_)) => {
                            stream = stream.aggregate();
                        }
                        Some(server_pb::communicate::ChKind::ToOthers(_)) => stream = stream.broadcast(),
                        None => {}
                    },
                    server_pb::operator_def::OpKind::Map(map) => {
                        let func = self.udf_gen.gen_map(&map.resource)?;
                        stream = stream.map(move |input| func.exec(input))?;
                    }
                    server_pb::operator_def::OpKind::FilterMap(filter_map) => {
                        let func = self
                            .udf_gen
                            .gen_filter_map(&filter_map.resource)?;
                        stream = stream.filter_map(move |input| func.exec(input))?;
                    }
                    server_pb::operator_def::OpKind::FlatMap(flat_map) => {
                        let func = self.udf_gen.gen_flat_map(&flat_map.resource)?;
                        stream = stream.flat_map(move |input| func.exec(input))?;
                    }
                    server_pb::operator_def::OpKind::Filter(filter) => {
                        let func = self.udf_gen.gen_filter(&filter.resource)?;
                        stream = stream.filter(move |input| func.test(input))?;
                    }
                    server_pb::operator_def::OpKind::Limit(n) => {
                        stream = stream.limit(n.limit)?;
                    }
                    server_pb::operator_def::OpKind::Sort(sort) => {
                        let cmp = self.udf_gen.gen_cmp(&sort.compare)?;
                        if sort.limit > 0 {
                            stream =
                                stream.sort_limit_by(sort.limit as u32, move |a, b| cmp.compare(a, b))?;
                        } else {
                            stream = stream.sort_by(move |a, b| cmp.compare(a, b))?;
                        }
                    }
                    server_pb::operator_def::OpKind::Fold(_fold) => {
                        Err(BuildJobError::Unsupported("Fold is not supported yet".to_string()))?
                    }
                    server_pb::operator_def::OpKind::Group(_group) => {
                        Err(BuildJobError::Unsupported("Group is not supported yet".to_string()))?
                    }
                    server_pb::operator_def::OpKind::Dedup(dedup) => {
                        let selector = self.udf_gen.gen_key(&dedup.resource)?;
                        stream = stream
                            .key_by(move |record| selector.get_kv(record))?
                            .dedup()?
                            .map(|pair| Ok(pair.value))?;
                    }
                    server_pb::operator_def::OpKind::Merge(merge) => {
                        let (mut ori_stream, sub_stream) = stream.copied()?;
                        stream = self.install(sub_stream, &merge.tasks[0].plan[..])?;
                        for subtask in &merge.tasks[1..] {
                            let copied = ori_stream.copied()?;
                            ori_stream = copied.0;
                            stream = self
                                .install(copied.1, &subtask.plan[..])?
                                .merge(stream)?;
                        }
                    }
                    server_pb::operator_def::OpKind::Iterate(iter) => {
                        let until = if let Some(condition) = iter
                            .until
                            .as_ref()
                            .and_then(|f| Some(f.resource.as_ref()))
                        {
                            let cond = self.udf_gen.gen_filter(condition)?;
                            let mut until = IterCondition::new();
                            until.until(move |input| cond.test(input));
                            until.max_iters = iter.max_iters;
                            until
                        } else {
                            IterCondition::max_iters(iter.max_iters)
                        };
                        if let Some(ref iter_body) = iter.body {
                            stream = stream
                                .iterate_until(until, |start| self.install(start, &iter_body.plan[..]))?;
                        } else {
                            Err("iteration body can't be empty;")?
                        }
                    }
                    server_pb::operator_def::OpKind::Apply(sub) => {
                        let join_func = self.udf_gen.gen_subtask(
                            sub.join
                                .as_ref()
                                .ok_or("should have subtask_kind")?
                                .resource
                                .as_ref(),
                        )?;

                        if let Some(ref body) = sub.task {
                            stream = stream
                                .apply(|sub_start| {
                                    let sub_end = self
                                        .install(sub_start, &body.plan[..])?
                                        .collect::<Vec<Record>>()?;
                                    Ok(sub_end)
                                })?
                                .filter_map(move |(parent, sub)| join_func.exec(parent, sub))?;
                        }
                    }
                    server_pb::operator_def::OpKind::SegApply(_) => {
                        Err(BuildJobError::Unsupported("SegApply is not supported yet".to_string()))?
                    }
                    server_pb::operator_def::OpKind::Join(join) => {
                        let joiner = self.udf_gen.gen_join(&join.resource)?;
                        let left_key_selector = joiner.gen_left_kv_fn()?;
                        let right_key_selector = joiner.gen_right_kv_fn()?;
                        let join_kind = joiner.get_join_kind();
                        let left_task = join
                            .left_task
                            .as_ref()
                            .ok_or("left_task is missing in merge")?;
                        let right_task = join
                            .right_task
                            .as_ref()
                            .ok_or("right_task is missing in merge")?;
                        let (left_stream, right_stream) = stream.copied()?;
                        let left_stream = self
                            .install(left_stream, &left_task.plan[..])?
                            .key_by(move |record| left_key_selector.get_kv(record))?
                            // TODO(bingqing): remove this when new keyed-join in gaia-x is ready;
                            .partition_by_key();
                        let right_stream = self
                            .install(right_stream, &right_task.plan[..])?
                            .key_by(move |record| right_key_selector.get_kv(record))?
                            // TODO(bingqing): remove this when new keyed-join in gaia-x is ready;
                            .partition_by_key();
                        stream =
                            match join_kind {
                                JoinKind::Inner => left_stream
                                    .inner_join(right_stream)?
                                    .map(|(left, right)| Ok(left.value.join(right.value, None)))?,
                                JoinKind::LeftOuter => {
                                    left_stream
                                        .left_outer_join(right_stream)?
                                        .map(|(left, right)| {
                                            let left = left.ok_or(FnExecError::unexpected_data_error(
                                                "left cannot be None in left outer join",
                                            ))?;
                                            if let Some(right) = right {
                                                // TODO(bingqing): Specify HeadJoinOpt if necessary
                                                Ok(left.value.join(right.value, None))
                                            } else {
                                                Ok(left.value)
                                            }
                                        })?
                                }
                                JoinKind::RightOuter => left_stream
                                    .right_outer_join(right_stream)?
                                    .map(|(left, right)| {
                                        let right = right.ok_or(FnExecError::unexpected_data_error(
                                            "right cannot be None in right outer join",
                                        ))?;
                                        if let Some(left) = left {
                                            Ok(left.value.join(right.value, None))
                                        } else {
                                            Ok(right.value)
                                        }
                                    })?,
                                JoinKind::FullOuter => left_stream.full_outer_join(right_stream)?.map(
                                    |(left, right)| match (left, right) {
                                        (Some(left), Some(right)) => Ok(left.value.join(right.value, None)),
                                        (Some(left), None) => Ok(left.value),
                                        (None, Some(right)) => Ok(right.value),
                                        (None, None) => {
                                            unreachable!()
                                        }
                                    },
                                )?,
                                JoinKind::Semi => left_stream
                                    .semi_join(right_stream)?
                                    .map(|left| Ok(left.value))?,
                                JoinKind::Anti => left_stream
                                    .anti_join(right_stream)?
                                    .map(|left| Ok(left.value))?,
                                JoinKind::Times => Err(BuildJobError::Unsupported(
                                    "JoinKind of Times is not supported yet".to_string(),
                                ))?,
                            }
                    }
                    server_pb::operator_def::OpKind::KeyBy(_) => {
                        Err(BuildJobError::Unsupported("KeyBy is not supported yet".to_string()))?
                    }
                }
            } else {
                Err("Unknown operator with empty kind;")?;
            }
        }
        Ok(stream)
    }
}

impl JobParser<Record, result_pb::Results> for IRJobCompiler {
    fn parse(
        &self, plan: &JobRequest, input: &mut Source<Record>, output: ResultSink<result_pb::Results>,
    ) -> Result<(), BuildJobError> {
        if let Some(source) = plan.source.as_ref() {
            let source = input.input_from(
                self.udf_gen
                    .gen_source(source.resource.as_ref())?,
            )?;
            let stream = if let Some(task) = plan.plan.as_ref() {
                self.install(source, &task.plan)?
            } else {
                source
            };
            if let Some(_sinker) = plan.sink.as_ref() {
                // TODO: specify the columns to sink in _sinker
                let ec = self.udf_gen.gen_sink(&vec![])?;
                stream
                    .map(move |record| ec.exec(record))?
                    .sink_into(output)
            } else {
                Err("sink of job not found")?
            }
        } else {
            Err("source of job not found")?
        }
    }
}

#[inline]
fn decode<T: Message + Default>(binary: &[u8]) -> FnGenResult<T> {
    Ok(T::decode(binary)?)
}