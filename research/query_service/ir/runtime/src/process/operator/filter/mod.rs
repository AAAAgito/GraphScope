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
mod select;

use ir_common::error::ParsePbError;
use ir_common::generated::algebra as algebra_pb;
use pegasus::api::function::FilterFunction;

use crate::error::FnGenResult;
use crate::process::record::Record;

pub trait FilterFuncGen {
    fn gen_filter(self) -> FnGenResult<Box<dyn FilterFunction<Record>>>;
}

impl FilterFuncGen for algebra_pb::logical_plan::Operator {
    fn gen_filter(self) -> FnGenResult<Box<dyn FilterFunction<Record>>> {
        if let Some(opr) = self.opr {
            match opr {
                algebra_pb::logical_plan::operator::Opr::Select(select) => select.gen_filter(),
                _ => Err(ParsePbError::from("algebra_pb op is not a filter"))?,
            }
        } else {
            Err(ParsePbError::EmptyFieldError("algebra op is empty".to_string()))?
        }
    }
}
