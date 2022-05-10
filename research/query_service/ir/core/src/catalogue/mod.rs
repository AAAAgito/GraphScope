//
//! Copyright 2020 Alibaba Group Holding Limited.
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

type PatternId = usize;
type PatternLabelId = ir_common::KeyId;
type PatternRankId = i32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PatternDirection {
    Out = 0,
    In,
}

impl Into<u8> for PatternDirection {
    fn into(self) -> u8 {
        match self {
            PatternDirection::Out => 0,
            PatternDirection::In => 1,
        }
    }
}

pub mod codec;
pub mod extend_step;
pub mod pattern;
pub mod pattern_meta;

#[cfg(test)]
pub(crate) mod test_cases;