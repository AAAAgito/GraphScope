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

use std::convert::TryInto;

use ir_common::generated::algebra as algebra_pb;
use ir_common::NameOrId;
use pegasus::api::function::{FilterMapFunction, FnResult};

use crate::error::{FnExecError, FnGenResult};
use crate::graph::element::{GraphElement, VertexOrEdge};
use crate::graph::QueryParams;
use crate::process::operator::map::FilterMapFuncGen;
use crate::process::record::{Entry, Record};

/// An Auxilia operator to get extra information for the current entity.
/// Specifically, we will replace the old entity with the new one with details,
/// and set rename the entity, if `alias` has been set.
#[derive(Debug)]
struct AuxiliaOperator {
    query_params: QueryParams,
    alias: Option<NameOrId>,
}

impl FilterMapFunction<Record, Record> for AuxiliaOperator {
    fn exec(&self, mut input: Record) -> FnResult<Option<Record>> {
        let entry = input
            .get(None)
            .ok_or(FnExecError::get_tag_error("get current entry failed in AuxiliaOperator"))?
            .clone();
        // Make sure there is anything to query with
        // Note that we need to guarantee the requested column if it has any alias,
        // e.g., for g.V().out().as("a").has("name", "marko"), we should compile as:
        // g.V().out().auxilia(as("a"))... where we give alias in auxilia,
        //     then we set tag=None and alias="a" in auxilia
        // TODO: it seems that we do not really care about getting head from curr or "a", we only need to save the updated entry with expected alias "a"
        if self.query_params.is_queryable() {
            // If queryable, then turn into graph element and do the query
            let vertex_or_edge = entry
                .as_graph_element()
                .ok_or(FnExecError::unexpected_data_error("should be vertex_or_edge in AuxiliaOperator"))?;
            let graph = crate::get_graph().ok_or(FnExecError::NullGraphError)?;
            let new_entry: Option<Entry> = match vertex_or_edge {
                VertexOrEdge::V(v) => {
                    let mut result_iter = graph.get_vertex(&[v.id()], &self.query_params)?;
                    result_iter.next().map(|vertex| vertex.into())
                }
                VertexOrEdge::E(e) => {
                    let mut result_iter = graph.get_edge(&[e.id()], &self.query_params)?;
                    result_iter.next().map(|edge| edge.into())
                }
            };
            if new_entry.is_some() {
                input.append(new_entry.unwrap(), self.alias.clone());
            } else {
                return Ok(None);
            }
        } else {
            if self.alias.is_some() {
                input.append_arc_entry(entry.clone(), self.alias.clone());
            }
        }

        Ok(Some(input))
    }
}

impl FilterMapFuncGen for algebra_pb::Auxilia {
    fn gen_filter_map(self) -> FnGenResult<Box<dyn FilterMapFunction<Record, Record>>> {
        let query_params = self.params.try_into()?;
        let alias = self
            .alias
            .map(|alias| alias.alias.unwrap().try_into())
            .transpose()?;
        let auxilia_operator = AuxiliaOperator { query_params, alias };
        debug!("Runtime auxilia operator: {:?}", auxilia_operator);
        Ok(Box::new(auxilia_operator))
    }
}
