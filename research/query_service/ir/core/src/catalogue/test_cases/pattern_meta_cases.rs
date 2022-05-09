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

use std::fs::File;

use crate::catalogue::pattern::*;
use crate::catalogue::pattern_meta::*;
use crate::{plan::meta::Schema, JsonIO};

pub fn read_modern_graph_schema() -> Schema {
    let modern_schema_file = match File::open("resource/modern_schema.json") {
        Ok(file) => file,
        Err(_) => File::open("catalogue/resource/modern_schema.json").unwrap(),
    };
    Schema::from_json(modern_schema_file).unwrap()
}

pub fn get_modern_pattern_meta() -> PatternMeta {
    let modern_schema = read_modern_graph_schema();
    PatternMeta::from(modern_schema)
}

pub fn read_ldbc_graph_schema() -> Schema {
    let ldbc_schema_file = match File::open("resource/ldbc_schema.json") {
        Ok(file) => file,
        Err(_) => File::open("catalogue/resource/ldbc_schema.json").unwrap(),
    };
    Schema::from_json(ldbc_schema_file).unwrap()
}

pub fn get_ldbc_pattern_meta() -> PatternMeta {
    let ldbc_schema = read_ldbc_graph_schema();
    PatternMeta::from(ldbc_schema)
}

/// Pattern from ldbc schema file
/// Person -> knows -> Person
pub fn build_ldbc_pattern_case1() -> Pattern {
    let pattern_edge = PatternEdge::new(0, 12, 0, 1, 1, 1);
    let mut pattern = Pattern::from(vec![pattern_edge]);
    pattern
        .get_vertex_mut_from_id(1)
        .unwrap()
        .set_index(1);
    pattern
}
