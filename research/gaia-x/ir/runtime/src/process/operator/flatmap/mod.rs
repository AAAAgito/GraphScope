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
mod edge_expand;

use crate::process::record::Record;
use ir_common::error::{str_to_dyn_error, DynIter, DynResult};
use ir_common::generated::algebra as algebra_pb;
use pegasus::api::function::FlatMapFunction;

pub trait FlatMapFuncGen {
    fn gen_flat_map(
        self,
    ) -> DynResult<Box<dyn FlatMapFunction<Record, Record, Target = DynIter<Record>>>>;
}
impl FlatMapFuncGen for algebra_pb::logical_plan::Operator {
    fn gen_flat_map(
        self,
    ) -> DynResult<Box<dyn FlatMapFunction<Record, Record, Target = DynIter<Record>>>> {
        if let Some(opr) = self.opr {
            match opr {
                algebra_pb::logical_plan::operator::Opr::Edge(edge_expand) => {
                    edge_expand.gen_flat_map()
                }
                algebra_pb::logical_plan::operator::Opr::Unfold(_unfold) => {
                    todo!()
                }
                _ => Err(str_to_dyn_error("algebra_pb op is not a flatmap")),
            }
        } else {
            Err(str_to_dyn_error("algebra op is empty"))
        }
    }
}
