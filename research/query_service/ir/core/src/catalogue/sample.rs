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
//!

// use crate::catalogue::extend_step::ExtendStep;
// use crate::catalogue::pattern::Pattern;
// use crate::catalogue::PatternId;

// use graph_store::prelude::DefaultId;

// type PatternRecord = std::collections::HashMap<PatternId, DefaultId>;

use std::collections::{HashSet, HashMap};

use graph_store::common::LabelId;
use graph_store::graph_db::{GlobalStoreTrait, GlobalStoreUpdate, Direction};
use graph_store::config::JsonConf;
use graph_store::prelude::{DefaultId, InternalId, LargeGraphDB, MutableGraphDB, GraphDBConfig, LDBCGraphSchema};
use rand::{thread_rng, Rng};

use ir_common::KeyId;
pub const TAG_A: KeyId = 0;
pub const TAG_B: KeyId = 1;
pub const TAG_C: KeyId = 2;
pub const TAG_D: KeyId = 3;
pub const TAG_E: KeyId = 4;
pub const TAG_F: KeyId = 5;
pub const TAG_G: KeyId = 6;
pub const TAG_H: KeyId = 7;
use crate::catalogue::query_params;
use pegasus::JobConf;
use ir_common::generated::algebra as pb;
use ir_common::generated::common as common_pb;
use pegasus::api::{Map, Sink};
use pegasus::result::ResultStream;
use graph_proxy::apis::{Details, Element, GraphElement};
use graph_proxy::{create_exp_store, SimplePartition};
use graph_store::ldbc::LDBCVertexParser;
use runtime::process::operator::flatmap::FlatMapFuncGen;
use runtime::process::operator::map::{FilterMapFuncGen, MapFuncGen};
use runtime::process::operator::source::SourceOperator;
use runtime::process::record::{Entry, Record};
use std::borrow::Borrow;
use std::sync::Arc;


pub fn sample(
    rate: u64, area: u64, sample_graph: &'static LargeGraphDB
) -> LargeGraphDB {
    let mut mut_graph: MutableGraphDB<DefaultId, InternalId> = GraphDBConfig::default().new();
    let mut added_vertex: HashSet<usize> = HashSet::new();
    // get graph with origion size
    if rate == 100u64 {
        // record all vertex into mut_graph
        let all_vertex = sample_graph.get_all_vertices(None);
        for vertex in all_vertex {
            let vertex_label = vertex.get_label();
            let vertex_id = vertex.get_id();
            added_vertex.insert(vertex_id);
            mut_graph.add_vertex(vertex_id, vertex_label);
        }
        // record all edges into mut_graph
        for vertex in added_vertex.clone() {
            let mut adj_edges = sample_graph.get_adj_edges(vertex as usize, None, Direction::Outgoing);
            for edge in adj_edges {
                let edge_label = edge.get_label();
                let dst_id = edge.get_dst_id();
                // in case that vertex of edge is not exist
                if added_vertex.contains(&dst_id) {
                    mut_graph.add_edge(vertex, dst_id, edge_label);
                }
            }
        }
    }
    // sample graph with given rate
    else if rate > 0 {
        // TODO
        // setting: lower bound
        let labels: Vec<u8> = (0..13).collect();
        let label_distribution = _graph_label_distribution(sample_graph, labels.clone());
        // For some label with extremely small size, set a lower bound of its number after sampling
        let mut lower_bound: Vec<u64> = Vec::new();
        let mut label_to_idx: HashMap<u8,usize> = HashMap::new();
        let sample_size = sample_graph.count_all_vertices(None) as u64 * rate /100;
        // lower bound try to keep label distribution similarly to the origion graph
        for label in labels.clone() {
            label_to_idx.insert(label, label_to_idx.len());
            let label_number = label_distribution[&(label_to_idx[&label] as u8)] as u64;
            let default_lower_bound = sample_size / 100;
            let vertex_to_sample = label_number * rate / 100;
            if default_lower_bound > vertex_to_sample {
                if default_lower_bound > label_number {
                    lower_bound.push(label_number)
                }
                else {
                    lower_bound.push(default_lower_bound);
                }
            }
            else {
                lower_bound.push(vertex_to_sample);
            }
        }

        let mut bfs_buffer: Vec<usize> = Vec::new();
        // select start vertex (area)
        for label in labels.clone() {
            let start_num = 1 + area / labels.len() as u64;
            let mut selected_num = 0;
            let start_list: Vec<usize> = 
                sample_graph.get_all_vertices(Some(&vec![label]))
                .map(|vertex| {
                    let vid = vertex.get_id();
                    vid
                }).filter(|vertex_id| 
                    sample_graph.get_both_edges(*vertex_id, None).count() != 0).collect();
            while selected_num <= start_num {
                let mut rng = thread_rng();
                let v_id = start_list[rng.gen_range(0..start_list.len())];
                if !added_vertex.contains(&v_id) {
                    let start_label = sample_graph.get_vertex(v_id).unwrap().get_label();
                    let super_label_idx = label_to_idx[&start_label[0]];
                    if start_label[1] != 255 {
                        let sub_label_idx = label_to_idx[&start_label[1]];
                        if lower_bound[sub_label_idx] ==0 {
                            break;
                        }
                        else {
                            lower_bound[sub_label_idx] -= 1;
                        }
                    }
                    if lower_bound[super_label_idx] == 0 {
                        break;
                    }
                    lower_bound[super_label_idx] -= 1;
                    // the vertex satisfies bound reqirement, record it into graph and BFS queue.
                    added_vertex.insert(v_id);
                    bfs_buffer.push(v_id);
                    mut_graph.add_vertex(v_id, start_label);
                    selected_num += 1;
                    if selected_num > start_num {
                        break;
                    }
                }
            }
        }

        // how much vertex should be sampling into graph in total
        let mut remain_sampling = 0;
        for i in lower_bound.clone() {
            remain_sampling += i;
        }
        // sampling vertex until it reach expected cost
        while remain_sampling > 0 {
            if bfs_buffer.len() == 0 {
                // break case 1: all connected vertices that do not break lower bound are sampled
                break;
            }
            // get all adjacent vertex to record in the graph
            let start_list = bfs_buffer.clone();
            bfs_buffer.clear();

            let adjlist: Vec<Vec<usize>> = start_list.into_iter().flat_map(|src_id| {
                sample_graph.get_both_vertices(src_id, None)
                .map(|v|{
                    let dst_id = v.get_id();
                    let dst_label = v.get_label();
                    let mut path = Vec::new();
                    path.push(dst_id);
                    path.push(dst_label[0] as usize);
                    path.push(dst_label[1] as usize);
                    path
                } )
            }).collect();
            
            for vtx in adjlist {
                let vtx_id = vtx[0];
                let super_label_idx = vtx[1];
                let sub_label_idx = vtx[2];
                let vtx_label: [u8;2] = [super_label_idx as u8, sub_label_idx as u8];
                // if vertex has added, continue
                if added_vertex.contains(&vtx_id) {
                    continue;
                }
                added_vertex.insert(vtx_id);
                // if this label has no budget in bound, continue
                if lower_bound[super_label_idx] <= 0 {
                    continue;
                }
                // if it has sub label abd has no budget, continue
                if sub_label_idx != 255 {
                    if lower_bound[sub_label_idx] <=0 {
                        continue;
                    }
                }
                lower_bound[super_label_idx] -= 1;
                if sub_label_idx != 255 {
                    lower_bound[sub_label_idx] -= 1;
                }
                remain_sampling -= 1;
                if remain_sampling >= 0 {
                    mut_graph.add_vertex(vtx_id, vtx_label);

                }
                bfs_buffer.push(vtx_id);
            }
        }
        // add edges of sampling vertices
        // consider all outgoing edge from vertex set
        let edges = added_vertex.clone().into_iter().flat_map(|vtx| {
        sample_graph.get_adj_edges(vtx, None, Direction::Outgoing)
        });
        for edge in edges {
            let src_id = edge.get_src_id();
            let dst_id = edge.get_dst_id();
            let edge_label = edge.get_label();
            if added_vertex.contains(&dst_id) {
                mut_graph.add_edge(src_id, dst_id, edge_label);
            }
        }
        
    }
    let schema_file = "data/schema.json";
    let schema =
            LDBCGraphSchema::from_json_file(schema_file).expect("Read graph schema error!");
    let graphdb = mut_graph.into_graph(schema);
    graphdb

}

fn _bound_generator() {
    
}

fn _start_select() {

}

// TODO: get label iter from schema
fn _graph_label_distribution(sample_graph: &'static LargeGraphDB, labels: Vec<LabelId>) -> HashMap<LabelId, usize> {
    let mut label_distribution: HashMap<LabelId, usize> = HashMap::new();
    for vertex_label in labels {
        let label_num = sample_graph.count_all_vertices(Some(&(vec![vertex_label])));
        label_distribution.insert(vertex_label, label_num);
    }
    label_distribution
}
fn source_gen_with_scan_opr(scan_opr_pb: pb::Scan) -> Box<dyn Iterator<Item = Record> + Send> {
    create_exp_store();
    let mut source_opr_pb =
        pb::logical_plan::Operator { opr: Some(pb::logical_plan::operator::Opr::Scan(scan_opr_pb)) };
    let source =
        SourceOperator::new(&mut source_opr_pb, 1, 1, Arc::new(SimplePartition { num_servers: 1 }))
            .unwrap();
    source.gen_source(0).unwrap()
}

    // marko (A) -> lop (B); marko (A) -> josh (C); lop (B) <- josh (C)
    // test the expand phase of A -> C
    #[test]
    fn expand_and_intersection_expand_test() {
        // marko (A) -> lop (B);
        let expand_opr1 = pb::EdgeExpand {
            v_tag: Some(TAG_A.into()),
            direction: 0, // out
            params: Some(query_params(vec![12.into()], vec![], None)),
            is_edge: false,
            alias: Some(TAG_B.into()),
        };

        // marko (A) -> josh (C): expand C;
        let expand_opr2 = pb::EdgeExpand {
            v_tag: Some(TAG_A.into()),
            direction: 0, // out
            params: Some(query_params(vec![12.into()], vec![], None)),
            is_edge: false,
            alias: Some(TAG_C.into()),
        };

        let conf = JobConf::new("expand_and_intersection_expand_test");
        let mut result = pegasus::run(conf, || {
            let expand1 = expand_opr1.clone();
            let expand2 = expand_opr2.clone();
            |input, output| {
                // source vertex: marko
                let source_iter = source_gen_with_scan_opr(pb::Scan {
                    scan_opt: 0,
                    alias: Some(TAG_A.into()),
                    params: None,
                    idx_predicate: None,
                });
                let mut stream = input.input_from(source_iter)?;
                let flatmap_func1 = expand1.gen_flat_map().unwrap();
                stream = stream.flat_map(move |input| flatmap_func1.exec(input))?;
                let map_func2 = expand2.gen_filter_map().unwrap();
                stream = stream.filter_map(move |input| map_func2.exec(input))?;
                stream.sink_into(output)
            }
        })
        .expect("build job failure");
        let v2: DefaultId = LDBCVertexParser::to_global_id(2, 0);
        let v3: DefaultId = LDBCVertexParser::to_global_id(3, 1);
        let v4: DefaultId = LDBCVertexParser::to_global_id(4, 0);
        let mut expected_collection = vec![v2, v3, v4];
        expected_collection.sort();
        let expected_collections =
            vec![expected_collection.clone(), expected_collection.clone(), expected_collection];
        let mut result_collections: Vec<Vec<usize>> = vec![];
        while let Some(Ok(record)) = result.next() {
            if let Entry::Collection(collection) = record.get(Some(TAG_C)).unwrap().borrow() {
                let mut result_collection: Vec<usize> = collection
                    .clone()
                    .into_iter()
                    .map(|r| r.as_graph_element().unwrap().id() as usize)
                    .collect();
                result_collection.sort();
                result_collections.push(result_collection);
            }
        }
        assert_eq!(result_collections.len(), expected_collections.len())
    }