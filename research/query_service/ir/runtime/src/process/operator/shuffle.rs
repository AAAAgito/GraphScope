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

use crate::graph::element::GraphElement;
use crate::graph::partitioner::Partitioner;
use crate::process::record::{Entry, Record, RecordElement};
use ir_common::error::ParsePbError;
use ir_common::generated::common as common_pb;
use ir_common::NameOrId;
use pegasus::api::function::{FnResult, RouteFunction};
use std::convert::TryInto;
use std::sync::Arc;

pub struct RecordRouter {
    p: Arc<dyn Partitioner>,
    num_workers: usize,
    shuffle_key: Option<NameOrId>,
}

impl RecordRouter {
    pub fn new(
        p: Arc<dyn Partitioner>, num_workers: usize, shuffle_key: common_pb::NameOrIdKey,
    ) -> Result<Self, ParsePbError> {
        let shuffle_key = shuffle_key
            .key
            .map(|e| e.try_into())
            .transpose()?;
        debug!("Runtime shuffle number of worker {:?} and shuffle key {:?}", num_workers, shuffle_key);
        Ok(RecordRouter { p, num_workers, shuffle_key })
    }
}

impl RouteFunction<Record> for RecordRouter {
    fn route(&self, t: &Record) -> FnResult<u64> {
        if let Some(entry) = t.get(self.shuffle_key.as_ref()) {
            match entry.as_ref() {
                Entry::Element(element) => match element {
                    RecordElement::OnGraph(e) => self.p.get_partition(&e.id(), self.num_workers),
                    //TODO(bingqing): deal with the OffGraph element shuffle
                    RecordElement::OffGraph(_) => Ok(0),
                },
                Entry::Collection(_) => Ok(0),
            }
        } else {
            Ok(0)
        }
    }
}