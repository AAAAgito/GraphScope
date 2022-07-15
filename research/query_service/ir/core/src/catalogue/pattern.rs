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

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::convert::{TryFrom, TryInto};
use std::iter::FromIterator;

use bimap::BiBTreeMap;
use ir_common::generated::algebra as pb;
use ir_common::generated::common as common_pb;
use vec_map::VecMap;

use super::codec::{Cipher, Encoder};
use crate::catalogue::extend_step::{
    get_subsets, limit_repeated_element_num, DefiniteExtendEdge, DefiniteExtendStep, ExtendEdge, ExtendStep,
};
use crate::catalogue::pattern_meta::PatternMeta;
use crate::catalogue::{DynIter, PatternDirection, PatternId, PatternLabelId, PatternRankId};
use crate::error::{IrError, IrResult};
use crate::plan::meta::TagId;

/// PatternVertex represents a vertex within a pattern
#[derive(Debug, Clone, Copy)]
pub struct PatternVertex {
    id: PatternId,
    label: PatternLabelId,
    /// Used to Identify vertices with same label
    rank: PatternRankId,
}

impl PatternVertex {
    /// Create a new PatternVertex with user-defined ID and vertex label
    ///
    /// The rank is initially set as 0
    pub fn new(id: PatternId, label: PatternLabelId) -> PatternVertex {
        PatternVertex { id, label, rank: 0 }
    }
}

/// Methods to access the fields of PatternVertex
impl PatternVertex {
    pub fn get_id(&self) -> PatternId {
        self.id
    }

    pub fn get_label(&self) -> PatternLabelId {
        self.label
    }

    /// Get the rank of the PatternVertex
    pub fn get_rank(&self) -> PatternRankId {
        self.rank
    }

    /// Set the rank of the PatternVertex
    pub fn set_rank(&mut self, rank: PatternRankId) {
        self.rank = rank;
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PatternEdge {
    id: PatternId,
    label: PatternLabelId,
    start_v_id: PatternId,
    end_v_id: PatternId,
    start_v_label: PatternLabelId,
    end_v_label: PatternLabelId,
}

/// Initializers of PatternEdge
impl PatternEdge {
    /// Initializer
    pub fn new(
        id: PatternId, label: PatternLabelId, start_v_id: PatternId, end_v_id: PatternId,
        start_v_label: PatternLabelId, end_v_label: PatternLabelId,
    ) -> PatternEdge {
        PatternEdge { id, label, start_v_id, end_v_id, start_v_label, end_v_label }
    }
}

/// Methods to access the fields of a PatternEdge
impl PatternEdge {
    pub fn get_id(&self) -> PatternId {
        self.id
    }

    pub fn get_label(&self) -> PatternLabelId {
        self.label
    }

    pub fn get_start_vertex_id(&self) -> PatternId {
        self.start_v_id
    }

    pub fn get_end_vertex_id(&self) -> PatternId {
        self.end_v_id
    }

    pub fn get_start_vertex_label(&self) -> PatternLabelId {
        self.start_v_label
    }

    pub fn get_end_vertex_label(&self) -> PatternLabelId {
        self.end_v_label
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Adjacency {
    /// the source vertex connect to the adjacent vertex through this edge
    edge_id: PatternId,
    /// the adjacent vertex
    adj_vertex_id: PatternId,
    /// the connecting direction: outgoing or incoming
    direction: PatternDirection,
}

impl Adjacency {
    pub fn new(edge_id: PatternId, end_vertex_id: PatternId, direction: PatternDirection) -> Self {
        Adjacency { edge_id, adj_vertex_id: end_vertex_id, direction }
    }

    pub fn get_edge_id(&self) -> PatternId {
        self.edge_id
    }

    pub fn get_adj_vertex_id(&self) -> PatternId {
        self.adj_vertex_id
    }

    pub fn get_direction(&self) -> PatternDirection {
        self.direction
    }
}

#[derive(Debug, Clone)]
pub struct Pattern {
    /// Key: edge id, Value: struct PatternEdge
    edges: VecMap<PatternEdge>,
    /// Key: vertex id, Value: struct PatternVertex
    vertices: VecMap<PatternVertex>,
    /// Key: edge label id, Value: BTreeSet<edge id>
    edge_label_map: BTreeMap<PatternLabelId, BTreeSet<PatternId>>,
    /// Key: vertex label id, Value: BTreeSet<vertex id>
    vertex_label_map: BTreeMap<PatternLabelId, BTreeSet<PatternId>>,
    /// Key: edge's Tag info, Value: edge id
    edge_tag_map: BiBTreeMap<TagId, PatternId>,
    /// Key: vertex's Tag info, Value: vertex id
    vertex_tag_map: BiBTreeMap<TagId, PatternId>,
    /// Key: edge id, Value: predicate of the edge
    edge_predicate_map: BTreeMap<PatternId, common_pb::Expression>,
    /// Key: vertex id, Value: predicate of the vertex
    vertex_predicate_map: BTreeMap<PatternId, common_pb::Expression>,
    /// Key: vertex id, Value: struct Vec<Adjacency>
    /// - store outgoing adjacent info of each vertex
    out_adjacencies_map: VecMap<Vec<Adjacency>>,
    /// Key: vertex id, Value: Vec<Adjacency>
    /// - stroe incoming adjacent info of each vertex
    in_adjacencies_map: VecMap<Vec<Adjacency>>,
}

/// Initialze a Pattern from just a single Pattern Vertex
///
/// The Pattern Vertex's id and label is kept and all other info is cleared
impl From<PatternVertex> for Pattern {
    fn from(mut vertex: PatternVertex) -> Pattern {
        vertex.rank = 0;
        Pattern {
            edges: VecMap::new(),
            vertices: VecMap::from_iter([(vertex.id, vertex)]),
            edge_label_map: BTreeMap::new(),
            vertex_label_map: BTreeMap::from([(vertex.label, BTreeSet::from([vertex.id]))]),
            edge_tag_map: BiBTreeMap::new(),
            vertex_tag_map: BiBTreeMap::new(),
            edge_predicate_map: BTreeMap::new(),
            vertex_predicate_map: BTreeMap::new(),
            out_adjacencies_map: VecMap::new(),
            in_adjacencies_map: VecMap::new(),
        }
    }
}

/// Initialize a Pattern from a vertor of Pattern Edges
impl TryFrom<Vec<PatternEdge>> for Pattern {
    type Error = IrError;

    fn try_from(edges: Vec<PatternEdge>) -> IrResult<Self> {
        if !edges.is_empty() {
            let mut new_pattern = Pattern {
                edges: VecMap::new(),
                vertices: VecMap::new(),
                edge_label_map: BTreeMap::new(),
                vertex_label_map: BTreeMap::new(),
                edge_tag_map: BiBTreeMap::new(),
                vertex_tag_map: BiBTreeMap::new(),
                edge_predicate_map: BTreeMap::new(),
                vertex_predicate_map: BTreeMap::new(),
                out_adjacencies_map: VecMap::new(),
                in_adjacencies_map: VecMap::new(),
            };
            for edge in edges {
                // Add the new Pattern Edge to the new Pattern
                new_pattern.edges.insert(edge.id, edge);
                let edge_set = new_pattern
                    .edge_label_map
                    .entry(edge.label)
                    .or_insert(BTreeSet::new());
                edge_set.insert(edge.id);
                // Add or update the start vertex to the new Pattern
                new_pattern
                    .vertices
                    .entry(edge.start_v_id)
                    .or_insert(PatternVertex { id: edge.start_v_id, label: edge.start_v_label, rank: 0 });
                new_pattern
                    .vertex_label_map
                    .entry(edge.start_v_label)
                    .or_insert(BTreeSet::new())
                    .insert(edge.start_v_id);
                // Add or update the end vertex to the new Pattern
                new_pattern
                    .vertices
                    .entry(edge.end_v_id)
                    .or_insert(PatternVertex { id: edge.end_v_id, label: edge.end_v_label, rank: 0 });
                new_pattern
                    .vertex_label_map
                    .entry(edge.end_v_label)
                    .or_insert(BTreeSet::new())
                    .insert(edge.end_v_id);
                // Update the vertex adjacencies map info
                // start vertex's outgoing info
                new_pattern
                    .out_adjacencies_map
                    .entry(edge.start_v_id)
                    .or_insert(vec![])
                    .push(Adjacency::new(edge.id, edge.end_v_id, PatternDirection::Out));
                // end vertex's incoming info
                new_pattern
                    .in_adjacencies_map
                    .entry(edge.end_v_id)
                    .or_insert(vec![])
                    .push(Adjacency::new(edge.id, edge.start_v_id, PatternDirection::In));
            }

            new_pattern.vertex_ranking();
            Ok(new_pattern)
        } else {
            Err(IrError::InvalidPattern("Empty pattern".to_string()))
        }
    }
}

impl Pattern {
    pub fn from_pb_pattern(pb_pattern: &pb::Pattern, pattern_meta: &PatternMeta) -> IrResult<Pattern> {
        use pb::pattern::binder::Item as BinderItem;
        // next vertex id assign to the vertex picked from the pb pattern
        let mut next_vertex_id = 0;
        // next edge id assign to the edge picked from the pb pattern
        let mut next_edge_id = 0;
        // pattern edges picked from the pb pattern
        let mut pattern_edges = vec![];
        // record the vertices from the pb pattern having tags
        let mut tag_v_id_map: BTreeMap<TagId, PatternId> = BTreeMap::new();
        // record the label for each vertex from the pb pattern
        let mut id_label_map: BTreeMap<PatternId, PatternLabelId> = BTreeMap::new();
        // record the vertices from the pb pattern has predicates
        let mut v_id_predicate_map: BTreeMap<PatternId, common_pb::Expression> = BTreeMap::new();
        // record the edges from the pb pattern has predicates
        let mut e_id_predicate_map: BTreeMap<PatternId, common_pb::Expression> = BTreeMap::new();
        for sentence in &pb_pattern.sentences {
            if sentence.binders.is_empty() {
                return Err(IrError::MissingData("pb::pattern::sentence.binders".to_string()));
            }
            // pb pattern sentence must have start tag
            let start_tag = get_sentence_start_tag(sentence)?;
            // assgin a vertex id to the start vertex of a pb pattern sentence
            let start_tag_v_id = assign_vertex_id_by_tag(start_tag, &mut tag_v_id_map, &mut next_vertex_id);
            // check whether the start tag label is already determined or not
            let start_tag_label = id_label_map.get(&start_tag_v_id).cloned();
            // it is allowed that the pb pattern sentence doesn't have an end tag
            let end_tag = get_sentence_end_tag(sentence);
            // if the end tag exists, assign the end vertex with an id
            let end_tag_v_id = if let Some(tag) = end_tag {
                Some(assign_vertex_id_by_tag(tag, &mut tag_v_id_map, &mut next_vertex_id))
            } else {
                None
            };
            // check the end tag label is already determined or not
            let end_tag_label = end_tag_v_id.and_then(|v_id| id_label_map.get(&v_id).cloned());
            // record previous pattern edge's destinated vertex's id
            // init as start vertex's id
            let mut pre_dst_vertex_id: PatternId = start_tag_v_id;
            // record previous pattern edge's destinated vertex's label
            // init as start vertex's label
            let mut pre_dst_vertex_label = start_tag_label;
            // find the first edge expand's index and last edge expand's index;
            let last_expand_index = get_sentence_last_expand_index(sentence);
            // iterate over the binders
            for (i, binder) in sentence.binders.iter().enumerate() {
                if let Some(BinderItem::Edge(edge_expand)) = binder.item.as_ref() {
                    // get edge label's id
                    let edge_label = get_edge_expand_label(edge_expand)?;
                    // assign the new pattern edge with a new id
                    let edge_id = assign_id(&mut next_edge_id);
                    // get edge direction
                    let edge_direction = get_edge_expand_direction(edge_expand)?;
                    // add edge predicate
                    if let Some(expr) = get_edge_expand_predicate(edge_expand) {
                        e_id_predicate_map.insert(edge_id, expr.clone());
                    }
                    // assign/pick the souce vertex id and destination vertex id of the pattern edge
                    let src_vertex_id = pre_dst_vertex_id;
                    let dst_vertex_id = assign_expand_dst_vertex_id(
                        i == last_expand_index.unwrap(),
                        end_tag_v_id,
                        get_edge_expand_dst_vertex_tag(edge_expand),
                        &mut tag_v_id_map,
                        &mut next_vertex_id,
                    );
                    pre_dst_vertex_id = dst_vertex_id;
                    // assign vertices labels
                    // firstly, pick all candidate labels that can be assigned to the src/dst vertex
                    let vertex_labels_candis =
                        get_vertex_labels_candies(pattern_meta, edge_label, edge_direction);
                    // check which label candidate can connect to the previous determined partial pattern
                    let required_src_vertex_label = pre_dst_vertex_label;
                    let required_dst_vertex_label =
                        if i == last_expand_index.unwrap() { end_tag_label } else { None };
                    // check whether we find proper src vertex label and dst vertex label
                    let (src_vertex_label, dst_vertex_label, direction) = assign_src_dst_vertex_labels(
                        vertex_labels_candis,
                        required_src_vertex_label,
                        required_dst_vertex_label,
                    )?;
                    id_label_map.insert(src_vertex_id, src_vertex_label);
                    id_label_map.insert(dst_vertex_id, dst_vertex_label);
                    // generate the new pattern edge and add to the pattern_edges_collection
                    let new_pattern_edge = generate_new_pattern_edge(
                        edge_id,
                        edge_label,
                        src_vertex_id,
                        dst_vertex_id,
                        src_vertex_label,
                        dst_vertex_label,
                        direction,
                    );
                    pattern_edges.push(new_pattern_edge);
                    pre_dst_vertex_label = Some(dst_vertex_label);
                } else if let Some(BinderItem::Select(select)) = binder.item.as_ref() {
                    if let Some(predicate) = select.predicate.as_ref() {
                        let vertex_id = pre_dst_vertex_id;
                        if v_id_predicate_map.contains_key(&vertex_id) {
                            v_id_predicate_map
                                .get_mut(&vertex_id)
                                .unwrap()
                                .and_with(predicate);
                        } else {
                            v_id_predicate_map.insert(vertex_id, predicate.clone());
                        }
                    }
                } else {
                    return Err(IrError::MissingData("pb::pattern::binder::Item".to_string()));
                }
            }
        }

        Pattern::try_from(pattern_edges).and_then(|mut pattern| {
            pattern.vertex_tag_map = tag_v_id_map.into_iter().collect();
            pattern.edge_predicate_map = e_id_predicate_map;
            pattern.vertex_predicate_map = v_id_predicate_map;
            Ok(pattern)
        })
    }
}

/// Get the start tag of a pb pattern sentence
/// - Since a pb pattern sentence must have a start tag,
///   if it doesn't have a tag or the tag is illegal ,give Error
fn get_sentence_start_tag(sentence: &pb::pattern::Sentence) -> IrResult<TagId> {
    let tag: ir_common::NameOrId = sentence
        .start
        .as_ref()
        .cloned()
        .ok_or(IrError::MissingData("pb::pattern::Sentence.start".to_string()))?
        .try_into()?;
    match tag {
        ir_common::NameOrId::Id(tag_id) => Ok(tag_id as TagId),
        _ => Err(IrError::TagNotExist(tag)),
    }
}

/// Get the end tag of a pb pattern sentence
/// - it is allowed that a pb pattern sentence doesn't have a end tag
fn get_sentence_end_tag(sentence: &pb::pattern::Sentence) -> Option<TagId> {
    sentence
        .end
        .clone()
        .and_then(|name_or_id| match name_or_id.item {
            Some(common_pb::name_or_id::Item::Id(tag)) => Some(tag as TagId),
            _ => None,
        })
}

/// Get the last edge expand's index of a pb pattern sentence among all of its binders
fn get_sentence_last_expand_index(sentence: &pb::pattern::Sentence) -> Option<usize> {
    match sentence
        .binders
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, binder)| {
            if let Some(pb::pattern::binder::Item::Edge(_)) = binder.item.as_ref() {
                true
            } else {
                false
            }
        })
        .next()
    {
        Some((id, _)) => Some(id),
        _ => None,
    }
}

/// Get the edge expand's label
/// - in current realization, edge_expand only allows to have one label
/// - if it has no label or more than one label, give Error
fn get_edge_expand_label(edge_expand: &pb::EdgeExpand) -> IrResult<PatternLabelId> {
    if edge_expand.is_edge {
        return Err(IrError::Unsupported("Expand only edge is not supported".to_string()));
    }
    if let Some(params) = edge_expand.params.as_ref() {
        // TODO: Support Fuzzy Pattern
        if params.tables.len() == 0 {
            return Err(IrError::Unsupported("FuzzyPattern: no specific edge expand label".to_string()));
        } else if params.tables.len() > 1 {
            return Err(IrError::Unsupported("FuzzyPattern: more than 1 edge expand label".to_string()));
        }
        // get edge label's id
        match params.tables[0].item.as_ref() {
            Some(common_pb::name_or_id::Item::Id(e_label_id)) => Ok(*e_label_id),
            _ => Err(IrError::InvalidPattern("edge expand doesn't have valid label".to_string())),
        }
    } else {
        Err(IrError::MissingData("pb::EdgeExpand.params".to_string()))
    }
}

/// Get the dst vertex's tag(if it has) of the edge expand
fn get_edge_expand_dst_vertex_tag(edge_expand: &pb::EdgeExpand) -> Option<TagId> {
    edge_expand
        .alias
        .clone()
        .and_then(|name_or_id| match name_or_id.item {
            Some(common_pb::name_or_id::Item::Id(tag)) => Some(tag as TagId),
            _ => None,
        })
}

/// Get the predicate(if it has) of the edge expand
fn get_edge_expand_predicate(edge_expand: &pb::EdgeExpand) -> Option<common_pb::Expression> {
    if let Some(params) = edge_expand.params.as_ref() {
        params.predicate.clone()
    } else {
        None
    }
}

/// Get the direction of the edge expand
fn get_edge_expand_direction(edge_expand: &pb::EdgeExpand) -> IrResult<pb::edge_expand::Direction> {
    if edge_expand.direction >= 0 && edge_expand.direction <= 2 {
        unsafe { Ok(std::mem::transmute::<i32, pb::edge_expand::Direction>(edge_expand.direction)) }
    } else {
        Err(IrError::InvalidPattern("Invalid Direction".to_string()))
    }
}

/// Assign a vertex or edge with the next_id, and add the next_id by one
fn assign_id(next_id: &mut PatternId) -> PatternId {
    let id_to_assign = *next_id;
    *next_id += 1;
    id_to_assign
}

/// If the current vertex has tag, check whether the tag is related to an id or not
/// - if it is related, just use the tag's id
/// - else, assign the vertex with a new id and add the (tag, id) relation to the map
fn assign_vertex_id_by_tag(
    vertex_tag: TagId, tag_v_id_map: &mut BTreeMap<TagId, PatternId>, next_vertex_id: &mut PatternId,
) -> PatternId {
    if let Some(v_id) = tag_v_id_map.get(&vertex_tag) {
        *v_id
    } else {
        let id_to_assign = assign_id(next_vertex_id);
        tag_v_id_map.insert(vertex_tag, id_to_assign);
        id_to_assign
    }
}

/// Assign an id the dst vertex of an edge expand
/// - firstly, check whether the edge expand is the tail of the sentence or not
///   - if it is sentence's end vertex
///     - if the sentence's end vertex's id is already assigned, just use it
///     - else, assign it with a new id
///   - else
///     - if the dst vertex is related with the tag, assign its id by tag
///     - else, assign it with a new id
fn assign_expand_dst_vertex_id(
    is_tail: bool, sentence_end_id: Option<PatternId>, dst_vertex_tag: Option<TagId>,
    tag_v_id_map: &mut BTreeMap<TagId, PatternId>, next_vertex_id: &mut PatternId,
) -> PatternId {
    if is_tail {
        if let Some(v_id) = sentence_end_id {
            v_id
        } else {
            assign_id(next_vertex_id)
        }
    } else {
        // check alias tag
        if let Some(tag) = dst_vertex_tag {
            assign_vertex_id_by_tag(tag, tag_v_id_map, next_vertex_id)
        } else {
            assign_id(next_vertex_id)
        }
    }
}

/// Based on the pattern meta info, find all possible vertex labels candidates:
/// (src vertex label, dst vertex label) with the given edge label and edge direction
/// - if the edge direciton is Outgoting:
///   we use (start vertex label, end vertex label) as (src vertex label, dst vertex label)
/// - if the edge direction is Incoming:
///   we use (end vertex label, start vertex label) as (src vertex label, dst vertex label)
/// - if the edge direction is Both:
///   we connect the iterators returned by Outgoing and Incoming together as they all can be the candidates
fn get_vertex_labels_candies(
    pattern_meta: &PatternMeta, edge_label: PatternLabelId, edge_direction: pb::edge_expand::Direction,
) -> DynIter<(PatternLabelId, PatternLabelId, PatternDirection)> {
    match edge_direction {
        pb::edge_expand::Direction::Out => Box::new(
            pattern_meta
                .associated_vlabels_iter_by_elabel(edge_label)
                .map(|(start_v_label, end_v_label)| (start_v_label, end_v_label, PatternDirection::Out)),
        ),
        pb::edge_expand::Direction::In => Box::new(
            pattern_meta
                .associated_vlabels_iter_by_elabel(edge_label)
                .map(|(start_v_label, end_v_label)| (end_v_label, start_v_label, PatternDirection::In)),
        ),
        pb::edge_expand::Direction::Both => Box::new(
            pattern_meta
                .associated_vlabels_iter_by_elabel(edge_label)
                .map(|(start_v_label, end_v_label)| (start_v_label, end_v_label, PatternDirection::Out))
                .chain(
                    pattern_meta
                        .associated_vlabels_iter_by_elabel(edge_label)
                        .map(|(start_v_label, end_v_label)| {
                            (end_v_label, start_v_label, PatternDirection::In)
                        }),
                ),
        ),
    }
}

/// Based on the vertex labels candidates and required src/dst vertex label,
/// assign the src and dst vertex with vertex labels meeting the requirement
///
/// For a chosen candidates:
/// - if the required src label is some, its src vertex label must match the requirement
/// - if the required dst label is some, its dst vertex label must match the requirement
fn assign_src_dst_vertex_labels<T: Iterator<Item = (PatternLabelId, PatternLabelId, PatternDirection)>>(
    mut vertex_labels_candis: T, required_src_label: Option<PatternLabelId>,
    required_dst_label: Option<PatternLabelId>,
) -> IrResult<(PatternLabelId, PatternLabelId, PatternDirection)> {
    (if let (Some(src_label), Some(dst_label)) = (required_src_label, required_dst_label) {
        vertex_labels_candis
            .filter(|&(src_label_candi, dst_label_candi, _)| {
                src_label_candi == src_label && dst_label_candi == dst_label
            })
            .next()
    } else if let Some(src_label) = required_src_label {
        vertex_labels_candis
            .filter(|&(src_label_candi, _, _)| src_label_candi == src_label)
            .next()
    } else if let Some(dst_label) = required_dst_label {
        vertex_labels_candis
            .filter(|&(_, dst_label_candi, _)| dst_label_candi == dst_label)
            .next()
    } else {
        vertex_labels_candis.next()
    })
    .ok_or(IrError::InvalidPattern("Cannot find valid label for some vertices".to_string()))
}

/// Generate a new pattern edge based on the given info
fn generate_new_pattern_edge(
    edge_id: PatternId, edge_label: PatternLabelId, src_vertex_id: PatternId, dst_vertex_id: PatternId,
    src_vertex_label: PatternLabelId, dst_vertex_label: PatternLabelId, direction: PatternDirection,
) -> PatternEdge {
    if let PatternDirection::Out = direction {
        PatternEdge::new(
            edge_id,
            edge_label,
            src_vertex_id,
            dst_vertex_id,
            src_vertex_label,
            dst_vertex_label,
        )
    } else {
        PatternEdge::new(
            edge_id,
            edge_label,
            dst_vertex_id,
            src_vertex_id,
            dst_vertex_label,
            src_vertex_label,
        )
    }
}

/// Iterators of fields of Pattern
impl Pattern {
    /// Iterate Edges
    pub fn edges_iter(&self) -> DynIter<&PatternEdge> {
        Box::new(self.edges.iter().map(|(_, edge)| edge))
    }

    /// Iterate Vertices
    pub fn vertices_iter(&self) -> DynIter<&PatternVertex> {
        Box::new(self.vertices.iter().map(|(_, vertex)| vertex))
    }

    /// Iterate Edges with the given edge label
    pub fn edges_iter_by_label(&self, edge_label: PatternLabelId) -> DynIter<&PatternEdge> {
        match self.edge_label_map.get(&edge_label) {
            Some(edges_set) => Box::new(
                edges_set
                    .iter()
                    .map(move |edge_id| self.edges.get(*edge_id).unwrap()),
            ),
            None => Box::new(std::iter::empty()),
        }
    }

    /// Iterate Vertices with the given vertex label
    pub fn vertices_iter_by_label(&self, vertex_label: PatternLabelId) -> DynIter<&PatternVertex> {
        match self.vertex_label_map.get(&vertex_label) {
            Some(vertices_set) => Box::new(
                vertices_set
                    .iter()
                    .map(move |vertex_id| self.vertices.get(*vertex_id).unwrap()),
            ),
            None => Box::new(std::iter::empty()),
        }
    }

    /// Iterate Edge Labels with Edges has this Label
    pub fn edge_label_map_iter(&self) -> DynIter<(PatternLabelId, &BTreeSet<PatternId>)> {
        Box::new(
            self.edge_label_map
                .iter()
                .map(|(edge_label, edges)| (*edge_label, edges)),
        )
    }

    /// Iterate Vertex Labels with Vertices has this Label
    pub fn vertex_label_map_iter(&self) -> DynIter<(PatternLabelId, &BTreeSet<PatternId>)> {
        Box::new(
            self.vertex_label_map
                .iter()
                .map(|(vertex_label, vertices)| (*vertex_label, vertices)),
        )
    }

    /// Iterate over edges that has tag
    pub fn edges_with_tag_iter(&self) -> DynIter<PatternId> {
        Box::new(self.edge_tag_map.iter().map(|(_, e_id)| *e_id))
    }

    /// Iterate over vertices that has tag
    pub fn vertices_with_tag_iter(&self) -> DynIter<PatternId> {
        Box::new(
            self.vertex_tag_map
                .iter()
                .map(|(_, v_id)| *v_id),
        )
    }

    /// Iterate all outgoing edges from the given vertex
    pub fn out_adjacencies_iter(&self, vertex_id: PatternId) -> DynIter<Adjacency> {
        if let Some(adjacencies) = self.out_adjacencies_map.get(vertex_id) {
            Box::new(adjacencies.iter().cloned())
        } else {
            Box::new(std::iter::empty())
        }
    }

    /// Iterate all incoming edges to the given vertex
    pub fn in_adjacencies_iter(&self, vertex_id: PatternId) -> DynIter<Adjacency> {
        if let Some(adjacencies) = self.in_adjacencies_map.get(vertex_id) {
            Box::new(adjacencies.iter().cloned())
        } else {
            Box::new(std::iter::empty())
        }
    }

    /// Iterate both outgoing and incoming edges of the given vertex
    pub fn adjacencies_iter(&self, vertex_id: PatternId) -> DynIter<Adjacency> {
        Box::new(
            self.out_adjacencies_iter(vertex_id)
                .chain(self.in_adjacencies_iter(vertex_id)),
        )
    }
}

/// Methods to access the fields of a Pattern or get some info from Pattern
impl Pattern {
    /// Get PatternEdge Reference from Edge ID
    pub fn get_edge_from_id(&self, edge_id: PatternId) -> Option<&PatternEdge> {
        self.edges.get(edge_id)
    }

    /// Get PatternEdge Mutable Reference from Edge ID
    pub fn get_edge_mut_from_id(&mut self, edge_id: PatternId) -> Option<&mut PatternEdge> {
        self.edges.get_mut(edge_id)
    }

    /// Get PatternVertex Reference from Vertex ID
    pub fn get_vertex_from_id(&self, vertex_id: PatternId) -> Option<&PatternVertex> {
        self.vertices.get(vertex_id)
    }

    /// Get PatternVertex Mutable Reference from Vertex ID
    pub fn get_vertex_mut_from_id(&mut self, vertex_id: PatternId) -> Option<&mut PatternVertex> {
        self.vertices.get_mut(vertex_id)
    }

    /// Get PatternEdge Reference from Given Tag
    pub fn get_edge_from_tag(&self, edge_tag: TagId) -> Option<&PatternEdge> {
        self.edge_tag_map
            .get_by_left(&edge_tag)
            .and_then(|id| self.edges.get(*id))
    }

    /// Get PatternVertex Reference from Given Tag
    pub fn get_vertex_from_tag(&self, vertex_tag: TagId) -> Option<&PatternEdge> {
        self.vertex_tag_map
            .get_by_left(&vertex_tag)
            .and_then(|id| self.edges.get(*id))
    }

    /// Assign a PatternEdge of the Pattern with the Given Tag
    pub fn add_edge_tag(&mut self, edge_tag: TagId, edge_id: PatternId) {
        self.edge_tag_map
            .insert(edge_tag.clone(), edge_id);
    }

    /// Assign a PatternVertex of th Pattern with the Given Tag
    pub fn add_vertex_tag(&mut self, vertex_tag: TagId, vertex_id: PatternId) {
        self.vertex_tag_map
            .insert(vertex_tag.clone(), vertex_id);
    }

    /// Get Vertex Index from Vertex ID Reference
    pub fn get_vertex_rank(&self, v_id: PatternId) -> PatternRankId {
        self.vertices.get(v_id).unwrap().get_rank()
    }

    /// Get the rank of both start and end vertices of an edge
    pub fn get_edge_vertices_rank(&self, edge_id: PatternId) -> Option<(PatternRankId, PatternRankId)> {
        if let Some(edge) = self.get_edge_from_id(edge_id) {
            let start_v_rank = self.get_vertex_rank(edge.get_start_vertex_id());
            let end_v_rank = self.get_vertex_rank(edge.get_end_vertex_id());
            Some((start_v_rank, end_v_rank))
        } else {
            None
        }
    }

    /// Get the total number of edges in the pattern
    pub fn get_edge_num(&self) -> usize {
        self.edges.len()
    }

    /// Get the total number of vertices in the pattern
    pub fn get_vertex_num(&self) -> usize {
        self.vertices.len()
    }

    /// Get the total number of edge labels in the pattern
    pub fn get_edge_label_num(&self) -> usize {
        self.edge_label_map.len()
    }

    /// Get the total number of vertex labels in the pattern
    pub fn get_vertex_label_num(&self) -> usize {
        self.vertex_label_map.len()
    }

    /// Get the maximum edge label id of the current pattern
    pub fn get_max_edge_label(&self) -> Option<PatternLabelId> {
        match self.edge_label_map.iter().last() {
            Some((max_label, _)) => Some(*max_label),
            None => None,
        }
    }

    /// Get the maximum vertex label id of the current pattern
    pub fn get_max_vertex_label(&self) -> Option<PatternLabelId> {
        match self.vertex_label_map.iter().last() {
            Some((max_label, _)) => Some(*max_label),
            None => None,
        }
    }

    /// Check whether the edge has predicate or not
    pub fn edge_has_predicate(&self, edge_id: PatternId) -> bool {
        self.edge_predicate_map.contains_key(&edge_id)
    }

    /// Check whether the edge has predicate or not
    pub fn vertex_has_predicate(&self, vertex_id: PatternId) -> bool {
        self.vertex_predicate_map
            .contains_key(&vertex_id)
    }

    /// Get the predicate requirement of a PatternEdge
    pub fn get_edge_predicate(&self, edge_id: PatternId) -> Option<&common_pb::Expression> {
        self.edge_predicate_map.get(&edge_id)
    }

    /// Get the predicate requirement of a PatternVertex
    pub fn get_vertex_predicate(&self, vertex_id: PatternId) -> Option<&common_pb::Expression> {
        self.vertex_predicate_map.get(&vertex_id)
    }

    /// Add predicate requirement to a PatternEdge
    pub fn add_edge_predicate(&mut self, edge_id: PatternId, predicate: common_pb::Expression) {
        self.edge_predicate_map
            .insert(edge_id, predicate);
    }

    /// Add predicate requirement to a PatternVertex
    pub fn add_vertex_predicate(&mut self, vertex_id: PatternId, predicate: common_pb::Expression) {
        self.vertex_predicate_map
            .insert(vertex_id, predicate);
    }

    /// Given a vertex label, return all vertices with the label
    pub fn get_vertices_from_label(&self, vertex_label: PatternLabelId) -> Option<&BTreeSet<PatternId>> {
        self.vertex_label_map.get(&vertex_label)
    }

    /// Given an edge label, return all edges with the label
    pub fn get_edges_from_label(&self, edge_label: PatternLabelId) -> Option<&BTreeSet<PatternId>> {
        self.edge_label_map.get(&edge_label)
    }

    pub fn get_vertex_out_degree(&self, vertex_id: PatternId) -> usize {
        if let Some(adjacencies) = self.out_adjacencies_map.get(vertex_id) {
            adjacencies.len()
        } else {
            0
        }
    }

    pub fn get_vertex_in_degree(&self, vertex_id: PatternId) -> usize {
        if let Some(adjacencies) = self.in_adjacencies_map.get(vertex_id) {
            adjacencies.len()
        } else {
            0
        }
    }

    pub fn get_vertex_degree(&self, vertex_id: PatternId) -> usize {
        self.get_vertex_out_degree(vertex_id) + self.get_vertex_in_degree(vertex_id)
    }
}

/// Methods for PatternEdge Reordering inside a Pattern
impl Pattern {
    /// Get the Order of two PatternEdges in a Pattern
    /// Vertex Indices are taken into consideration
    fn cmp_edges(&self, e1_id: PatternId, e2_id: PatternId) -> Ordering {
        if e1_id == e2_id {
            return Ordering::Equal;
        }
        let e1 = self.edges.get(e1_id).unwrap();
        let e2 = self.edges.get(e2_id).unwrap();
        // Compare the label of starting vertex
        match e1.start_v_label.cmp(&e2.start_v_label) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }
        // Compare the label of ending vertex
        match e1.end_v_label.cmp(&e2.end_v_label) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }
        // Compare Edge Label
        match e1.label.cmp(&e2.label) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }
        // Get orders for starting vertex
        let (e1_start_v_rank, e1_end_v_rank) = self
            .get_edge_vertices_rank(e1.get_id())
            .unwrap();
        let (e2_start_v_rank, e2_end_v_rank) = self
            .get_edge_vertices_rank(e2.get_id())
            .unwrap();
        // Compare the order of the starting vertex
        match e1_start_v_rank.cmp(&e2_start_v_rank) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }
        // Compare the order of ending vertex
        match e1_end_v_rank.cmp(&e2_end_v_rank) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }
        // Return as equal if still cannot distinguish
        Ordering::Equal
    }
}

/// Naive Rank Ranking Method
impl Pattern {
    /// Set Rank for Every Vertex within the Pattern
    ///
    /// Initially, all vertices have rank 0
    ///
    /// Basic Idea: Iteratively update the rank locally (neighbor edges vertices) and update the order of neighbor edges
    pub fn vertex_ranking(&mut self) {
        // Get the Neighbor Edges for All Vertices, Sorted Simply By Labels
        let mut vertex_adjacencies_map: HashMap<PatternId, Vec<Adjacency>> =
            self.get_vertex_adjacencies_map();
        // Initially, mark all the vertices as unfixed
        let mut vertices_with_unfixed_rank: HashSet<PatternId> = HashSet::new();
        for vertex in self.vertices_iter() {
            vertices_with_unfixed_rank.insert(vertex.get_id());
        }
        // Set initial ranks by comparing the labels & in/out degrees
        let mut is_rank_changed: bool = self
            .set_rank_by_neighbor_info(&vertex_adjacencies_map, &mut vertices_with_unfixed_rank)
            .unwrap();
        // Keep updating ranks by ranks computed in the last iteration
        loop {
            // Stop until the ranks can no longer be updated
            if !is_rank_changed {
                break;
            }
            // Update the Order of Neighbor Edges Based on the ranks of end vertices only
            self.update_neighbor_edges_map(&mut vertex_adjacencies_map);
            // Update vertex ranks by newly updated ranks in the last iteration
            is_rank_changed = self
                .update_rank(&vertex_adjacencies_map, &mut vertices_with_unfixed_rank)
                .unwrap();
        }
    }

    /// Get neighbor edges of each vertex
    ///
    /// Used for Comparing Vertices when Setting Initial Indices
    ///
    /// The vector of neighbor edges consists of two parts: outgoing edges and incoming edges
    ///
    /// Each neighbor edge element stores 3 values: edge id, target vertex id, and edge direction
    pub fn get_vertex_adjacencies_map(&self) -> HashMap<PatternId, Vec<Adjacency>> {
        let mut vertex_adjacencies_map = HashMap::new();
        for v_id in self.vertices_iter().map(|v| v.id) {
            let mut outgoing_edges = self
                .out_adjacencies_map
                .get(v_id)
                .cloned()
                .unwrap_or(vec![]);
            let mut incoming_edges = self
                .in_adjacencies_map
                .get(v_id)
                .cloned()
                .unwrap_or(vec![]);
            // Sort the edges
            outgoing_edges.sort_by(|adj1, adj2| self.cmp_edges(adj1.get_edge_id(), adj2.get_edge_id()));
            incoming_edges.sort_by(|adj1, adj2| self.cmp_edges(adj1.get_edge_id(), adj2.get_edge_id()));
            // Concat two edge info vector
            outgoing_edges.append(&mut incoming_edges);
            // Insert into the Hashmap
            vertex_adjacencies_map.insert(v_id, outgoing_edges);
        }

        vertex_adjacencies_map
    }

    /// Set Initial Vertex Index by comparing the labels and In/Out Degrees
    ///
    /// Return a bool indicating whether the ranks has changed for this initial rank iteration
    ///
    /// If nothing changed, we conclude that the ranks of all vertices have been set and are stable
    fn set_rank_by_neighbor_info(
        &mut self, vertex_adjacencies_map: &HashMap<PatternId, Vec<Adjacency>>,
        vertices_with_unfixed_rank: &mut HashSet<PatternId>,
    ) -> IrResult<bool> {
        // Mark whether there is a change of vertex rank
        let mut is_rank_changed: bool = false;
        // Stores vertex labels that have been dealth with
        let mut visited_labels: HashSet<PatternLabelId> = HashSet::new();
        // Store vertices that should be removed from the set of unfixed vertices
        let mut vertices_with_fixed_rank: Vec<PatternId> = Vec::new();
        // Store the mapping from vertex id to rank
        let mut vertex_rank_map: HashMap<PatternId, PatternRankId> = HashMap::new();
        for v_id in vertices_with_unfixed_rank.iter() {
            let v_label: PatternLabelId = self
                .get_vertex_from_id(*v_id)
                .unwrap()
                .get_label();
            if visited_labels.contains(&v_label) {
                continue;
            }
            visited_labels.insert(v_label);
            // Collect all vertices with the specified label
            let same_label_vertex_set: &BTreeSet<PatternId> =
                self.get_vertices_from_label(v_label).unwrap();
            let vertex_num = same_label_vertex_set.len();
            // Tranform set to vector
            let mut same_label_vertex_vec: Vec<PatternId> = Vec::with_capacity(vertex_num);
            for vertex_id in same_label_vertex_set.iter() {
                same_label_vertex_vec.push(*vertex_id);
            }
            // Record the rank and is_rank_fixed properties for each vertex
            let mut vertex_rank_vec: Vec<PatternRankId> = vec![0; vertex_num];
            let mut is_rank_fixed_vec: Vec<bool> = vec![true; vertex_num];
            // To compute the exact rank of a vertex, compare it with all vertices with the same label
            for i in 0..vertex_num {
                for j in (i + 1)..vertex_num {
                    match self.cmp_vertices_by_neighbor_info(
                        same_label_vertex_vec[i],
                        same_label_vertex_vec[j],
                        vertex_adjacencies_map,
                    ) {
                        Ordering::Greater => vertex_rank_vec[i] += 1,
                        Ordering::Less => vertex_rank_vec[j] += 1,
                        Ordering::Equal => {
                            is_rank_fixed_vec[i] = false;
                            is_rank_fixed_vec[j] = false;
                        }
                    }
                }
                // Mark vertices that now have fixed rank
                if is_rank_fixed_vec[i] {
                    vertices_with_fixed_rank.push(same_label_vertex_vec[i]);
                }
                // Update Vertex Rank on the map
                vertex_rank_map.insert(same_label_vertex_vec[i], vertex_rank_vec[i]);
            }
        }
        // Remove vertices that have fixed rank
        for v_id in vertices_with_fixed_rank {
            vertices_with_unfixed_rank.remove(&v_id);
        }
        // Update vertex ranks on pattern
        for (v_id, v_rank) in vertex_rank_map.iter() {
            if *v_rank != 0 {
                is_rank_changed = true;
                self.get_vertex_mut_from_id(*v_id)
                    .unwrap()
                    .set_rank(*v_rank);
            }
        }

        Ok(is_rank_changed)
    }

    /// Update vertex ranks by considering ranks only
    ///
    /// Return a bool indicating whether the ranks has changed for this initial rank iteration
    ///
    /// If nothing changed, we conclude that the ranks of all vertices have been set and are stable
    fn update_rank(
        &mut self, vertex_adjacencies_map: &HashMap<PatternId, Vec<Adjacency>>,
        vertices_with_unfixed_rank: &mut HashSet<PatternId>,
    ) -> IrResult<bool> {
        if vertices_with_unfixed_rank.len() == 0 {
            return Ok(false);
        }
        // Mark whether there is a change of vertex rank
        let mut is_rank_changed: bool = false;
        // Stores vertex labels that have been dealt with
        let mut visited_labels: HashSet<PatternLabelId> = HashSet::new();
        // Store vertices that should be removed from unknown vertex set
        // fixed rank means that the vertex has a unique rank and
        // no other vertices with the same label share the same rank with it
        let mut vertices_with_fixed_rank: Vec<PatternId> = Vec::new();
        // Store the mapping from vertex id to its rank
        let mut vertex_rank_map: HashMap<PatternId, PatternRankId> = HashMap::new();
        // We only focus on vertices with unfixed ranks
        for v_id in vertices_with_unfixed_rank.iter() {
            let v_label: PatternLabelId = self
                .get_vertex_from_id(*v_id)
                .unwrap()
                .get_label();
            if visited_labels.contains(&v_label) {
                continue;
            }
            visited_labels.insert(v_label);
            // Collect all the vertices with the given label
            let same_label_vertex_set: &BTreeSet<PatternId> =
                self.get_vertices_from_label(v_label).unwrap();
            // Store vertices with the same rank and the same label
            let mut same_rank_vertex_map: HashMap<PatternRankId, (Vec<PatternId>, Vec<PatternId>)> =
                HashMap::new();
            // Separate vertices according to their ranks
            for vertex_id in same_label_vertex_set.iter() {
                if vertices_with_unfixed_rank.contains(vertex_id) {
                    let v_rank: PatternRankId = self
                        .get_vertex_from_id(*vertex_id)
                        .unwrap()
                        .get_rank();
                    if !same_rank_vertex_map.contains_key(&v_rank) {
                        same_rank_vertex_map.insert(v_rank, (Vec::new(), Vec::new()));
                    }
                    // Mark if anyone of the neighbor vertices have fixed rank
                    let mut has_fixed_rank_neighbor: bool = false;
                    let vertex_neighbor_edges = vertex_adjacencies_map.get(vertex_id).unwrap();
                    // Store vertices with neighbor vertices having fixed ranks in the first element of the tuple
                    // Otherwise, store in the second element of the tuple
                    for adj_v_id in vertex_neighbor_edges
                        .iter()
                        .map(|adj| adj.get_adj_vertex_id())
                    {
                        if !vertices_with_unfixed_rank.contains(&adj_v_id) {
                            has_fixed_rank_neighbor = true;
                            if let Some((same_rank_vertices_with_fixed_rank_neighbor, _)) =
                                same_rank_vertex_map.get_mut(&v_rank)
                            {
                                same_rank_vertices_with_fixed_rank_neighbor.push(*vertex_id);
                            } else {
                                return Err(IrError::Unsupported(
                                    "Failed to find vertices with the same rank".to_string(),
                                ));
                            }
                            break;
                        }
                    }
                    if !has_fixed_rank_neighbor {
                        if let Some((_, same_rank_vertices_without_fixed_rank_neighbor)) =
                            same_rank_vertex_map.get_mut(&v_rank)
                        {
                            same_rank_vertices_without_fixed_rank_neighbor.push(*vertex_id);
                        } else {
                            return Err(IrError::Unsupported(
                                "Failed to find vertices with the same rank".to_string(),
                            ));
                        }
                    }
                }
            }
            // Perform vertex ranking on each groups of vertices with the same label and rank
            for (vertex_set_with_fixed_rank_neighbor, vertex_set_without_fixed_rank_neighbor) in
                same_rank_vertex_map.values()
            {
                // Case-1: All vertices have no fixed rank neighbor
                if vertex_set_with_fixed_rank_neighbor.len() == 0 {
                    let old_rank: PatternRankId = self
                        .get_vertex_from_id(vertex_set_without_fixed_rank_neighbor[0])
                        .unwrap()
                        .get_rank();
                    let vertex_num = vertex_set_without_fixed_rank_neighbor.len();
                    let mut vertex_rank_vec: Vec<PatternRankId> = vec![old_rank; vertex_num];
                    let mut is_rank_fixed_vec: Vec<bool> = vec![true; vertex_num];
                    // To compute the exact rank of a vertex, compare it with all vertices with the same label
                    for i in 0..vertex_num {
                        for j in (i + 1)..vertex_num {
                            match self.cmp_vertices_by_rank(
                                vertex_set_without_fixed_rank_neighbor[i],
                                vertex_set_without_fixed_rank_neighbor[j],
                                vertex_adjacencies_map,
                            ) {
                                Ordering::Greater => vertex_rank_vec[i] += 1,
                                Ordering::Less => vertex_rank_vec[j] += 1,
                                Ordering::Equal => {
                                    is_rank_fixed_vec[i] = false;
                                    is_rank_fixed_vec[j] = false;
                                }
                            }
                        }
                        // Mark vertices that now have fixed rank
                        if is_rank_fixed_vec[i] {
                            vertices_with_fixed_rank.push(vertex_set_without_fixed_rank_neighbor[i]);
                        }
                        // Update Vertex Rank on the map
                        vertex_rank_map
                            .insert(vertex_set_without_fixed_rank_neighbor[i], vertex_rank_vec[i]);
                    }
                }
                // Case-2: There exists vertex having fixed rank neighbor
                else {
                    let old_rank: PatternRankId = self
                        .get_vertex_from_id(vertex_set_with_fixed_rank_neighbor[0])
                        .unwrap()
                        .get_rank();
                    let mut vertices_for_ranking: Vec<PatternId> =
                        vertex_set_with_fixed_rank_neighbor.clone();
                    // Take one vertex that has no fixed rank neighbor to represent all such vertices
                    if vertex_set_without_fixed_rank_neighbor.len() > 0 {
                        vertices_for_ranking.push(vertex_set_without_fixed_rank_neighbor[0]);
                    }
                    let vertex_num = vertices_for_ranking.len();
                    let mut vertex_rank_vec: Vec<PatternRankId> = vec![old_rank; vertex_num];
                    let mut is_rank_fixed_vec: Vec<bool> = vec![true; vertex_num];
                    // To compute the exact rank of a vertex, compare it with all vertices with the same label
                    for i in 0..vertex_num {
                        for j in (i + 1)..vertex_num {
                            match self.cmp_vertices_by_rank(
                                vertices_for_ranking[i],
                                vertices_for_ranking[j],
                                vertex_adjacencies_map,
                            ) {
                                Ordering::Greater => {
                                    if j == vertex_num - 1
                                        && vertex_set_without_fixed_rank_neighbor.len() > 0
                                    {
                                        vertex_rank_vec[i] +=
                                            vertex_set_without_fixed_rank_neighbor.len() as PatternRankId;
                                    } else {
                                        vertex_rank_vec[i] += 1;
                                    }
                                }
                                Ordering::Less => vertex_rank_vec[j] += 1,
                                Ordering::Equal => {
                                    is_rank_fixed_vec[i] = false;
                                    is_rank_fixed_vec[j] = false;
                                }
                            }
                        }
                        // Mark vertices that now have fixed rank
                        if i != vertex_num - 1 && is_rank_fixed_vec[i] {
                            vertices_with_fixed_rank.push(vertices_for_ranking[i]);
                        }
                        if i == vertex_num - 1
                            && vertex_set_without_fixed_rank_neighbor.len() == 0
                            && is_rank_fixed_vec[i]
                        {
                            vertices_with_fixed_rank.push(vertices_for_ranking[i]);
                        }
                    }
                    // Update Vertex Rank on the map
                    for i in 0..vertex_set_with_fixed_rank_neighbor.len() {
                        vertex_rank_map.insert(vertex_set_with_fixed_rank_neighbor[i], vertex_rank_vec[i]);
                    }
                    for j in 0..vertex_set_without_fixed_rank_neighbor.len() {
                        vertex_rank_map.insert(
                            vertex_set_without_fixed_rank_neighbor[j],
                            vertex_rank_vec[vertex_num - 1],
                        );
                    }
                }
            }
        }

        // Remove vertices that have fixed rank
        for v_id in vertices_with_fixed_rank {
            vertices_with_unfixed_rank.remove(&v_id);
        }
        // Update vertex rank on the pattern
        for (v_id, v_rank) in vertex_rank_map.iter() {
            let old_rank: PatternRankId = self
                .get_vertex_from_id(*v_id)
                .unwrap()
                .get_rank();
            if *v_rank != old_rank {
                is_rank_changed = true;
                self.get_vertex_mut_from_id(*v_id)
                    .unwrap()
                    .set_rank(*v_rank);
            }
        }

        Ok(is_rank_changed)
    }

    /// Compare the ranks of two PatternVertices
    ///
    /// Consider labels and out/in degrees only
    ///
    /// Called when setting initial ranks
    fn cmp_vertices_by_neighbor_info(
        &self, v1_id: PatternId, v2_id: PatternId,
        vertex_adjacencies_map: &HashMap<PatternId, Vec<Adjacency>>,
    ) -> Ordering {
        let v1 = self.vertices.get(v1_id).unwrap();
        let v2 = self.vertices.get(v2_id).unwrap();
        match v1.get_label().cmp(&v2.get_label()) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }
        // Compare Vertex Out Degree
        match self
            .get_vertex_out_degree(v1_id)
            .cmp(&self.get_vertex_out_degree(v2_id))
        {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }
        // Compare Vertex In Degree
        match self
            .get_vertex_in_degree(v1_id)
            .cmp(&self.get_vertex_in_degree(v2_id))
        {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }

        let v1_adjacencies = vertex_adjacencies_map.get(&v1_id).unwrap();
        let v2_adjacencies = vertex_adjacencies_map.get(&v2_id).unwrap();
        for adj_index in 0..v1_adjacencies.len() {
            // Compare the label of adjacent vertex
            let v1_adj_v_label = self
                .get_vertex_from_id(v1_adjacencies[adj_index].get_adj_vertex_id())
                .unwrap()
                .get_label();
            let v2_adj_v_label = self
                .get_vertex_from_id(v2_adjacencies[adj_index].get_adj_vertex_id())
                .unwrap()
                .get_label();
            match v1_adj_v_label.cmp(&v2_adj_v_label) {
                Ordering::Less => return Ordering::Less,
                Ordering::Greater => return Ordering::Greater,
                _ => (),
            }

            // Compare the label of adjacent edges
            let v1_adj_edge_label = self
                .get_edge_from_id(v1_adjacencies[adj_index].get_edge_id())
                .unwrap()
                .get_label();
            let v2_adj_edge_label = self
                .get_edge_from_id(v2_adjacencies[adj_index].get_edge_id())
                .unwrap()
                .get_label();
            match v1_adj_edge_label.cmp(&v2_adj_edge_label) {
                Ordering::Less => return Ordering::Less,
                Ordering::Greater => return Ordering::Greater,
                _ => (),
            }
        }

        // Return Equal if Still Cannot Distinguish
        Ordering::Equal
    }

    /// Compare the ranks of two PatternVertices
    ///
    /// Called when updating vertex ranks as only ranks need to be considered
    fn cmp_vertices_by_rank(
        &self, v1_id: PatternId, v2_id: PatternId,
        vertex_adjacencies_map: &HashMap<PatternId, Vec<Adjacency>>,
    ) -> Ordering {
        let v1 = self.vertices.get(v1_id).unwrap();
        let v2 = self.vertices.get(v2_id).unwrap();
        // Compare the ranks
        match v1.get_rank().cmp(&v2.get_rank()) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            _ => (),
        }
        // Compare End Vertex Rank
        let v1_adjacencies = vertex_adjacencies_map.get(&v1_id).unwrap();
        let v2_adjacencies = vertex_adjacencies_map.get(&v2_id).unwrap();
        for adj_index in 0..v1_adjacencies.len() {
            let v1_adj_v_rank: PatternRankId = self
                .get_vertex_from_id(v1_adjacencies[adj_index].get_adj_vertex_id())
                .unwrap()
                .get_rank();
            let v2_adj_v_rank: PatternRankId = self
                .get_vertex_from_id(v2_adjacencies[adj_index].get_adj_vertex_id())
                .unwrap()
                .get_rank();
            match v1_adj_v_rank.cmp(&v2_adj_v_rank) {
                Ordering::Less => return Ordering::Less,
                Ordering::Greater => return Ordering::Greater,
                _ => (),
            }
        }

        // Return Equal if Still Cannot Distinguish
        Ordering::Equal
    }

    // Update the Order of Neighbor Vertices Based on the ranks of end vertices only
    fn update_neighbor_edges_map(&self, vertex_adjacencies_map: &mut HashMap<PatternId, Vec<Adjacency>>) {
        for vertex in self.vertices_iter() {
            vertex_adjacencies_map
                .get_mut(&vertex.get_id())
                .unwrap()
                .sort_by(|e1, e2| {
                    self.get_vertex_from_id(e1.get_adj_vertex_id())
                        .unwrap()
                        .get_rank()
                        .cmp(
                            &self
                                .get_vertex_from_id(e2.get_adj_vertex_id())
                                .unwrap()
                                .get_rank(),
                        )
                });
        }
    }
}

/// DFS Sorting
///
/// Find a unique sequence of edges in DFS order and assign each vertex with a unique DFS id for easier decoding process
impl Pattern {
    /// Return the ID of the starting vertex of DFS.
    ///
    /// In our case, It's the vertex with the smallest label and rank
    fn get_dfs_starting_vertex(&self) -> PatternId {
        // Step-1: Find the smallest vertex label
        let mut min_v_label: PatternLabelId = PatternLabelId::MAX;
        let mut min_label_vertices: &BTreeSet<PatternId> = &BTreeSet::new();
        for (v_label, vertices) in self.vertex_label_map_iter() {
            if v_label < min_v_label {
                min_v_label = v_label;
                min_label_vertices = vertices;
            }
        }
        // Step-2: Find the vertex with the smallest rank
        let mut starting_v_id: PatternId = 0;
        let mut min_v_rank: PatternRankId = PatternRankId::MAX;
        for v_id in min_label_vertices.iter() {
            let current_v_rank: PatternRankId = self
                .get_vertex_from_id(*v_id)
                .unwrap()
                .get_rank();
            if current_v_rank < min_v_rank {
                starting_v_id = *v_id;
                min_v_rank = current_v_rank;
            }
        }

        starting_v_id
    }

    /// Perform DFS Sorting to Pattern Edges Based on Labels and Ranks
    ///
    /// Return a tuple of 2 elements
    ///
    /// dfs_edge_sequence is a vector of edge ids in DFS order
    ///
    /// vertex_dfs_id_map maps from vertex ids to dfs id
    pub fn get_dfs_edge_sequence(&self) -> IrResult<(Vec<PatternId>, HashMap<PatternId, PatternRankId>)> {
        // output edge sequence
        let mut dfs_edge_sequence: Vec<PatternId> = Vec::new();
        // DFS Generation Tree
        let mut vertex_dfs_id_map: HashMap<PatternId, PatternRankId> = HashMap::new();
        // get the starting vertex
        let starting_v_id: PatternId = self.get_dfs_starting_vertex();
        vertex_dfs_id_map.insert(starting_v_id, 0);
        let mut next_free_id: PatternRankId = 1;
        // collect neighbor edges info for each vertex
        let vertex_adjacencies_map = self.get_vertex_adjacencies_map();
        // Record which edges have been visited
        let mut visited_edges: HashSet<PatternId> = HashSet::new();
        // Vertex Stack used for DFS backtracking
        let mut vertex_stack: VecDeque<PatternId> = VecDeque::new();
        vertex_stack.push_back(starting_v_id);
        // Perform DFS on vertices
        while vertex_stack.len() > 0 {
            let current_v_id: PatternId = *vertex_stack.back().unwrap();
            let vertex_adjacencies = vertex_adjacencies_map
                .get(&current_v_id)
                .expect(&format!("Unknown ID {}", current_v_id));
            let mut found_next_edge: bool = false;
            let mut adj_index: usize = 0;
            while adj_index < vertex_adjacencies.len() {
                let mut edge_id = vertex_adjacencies[adj_index].get_edge_id();
                let mut end_v_id = vertex_adjacencies[adj_index].get_adj_vertex_id();
                let e_dir = vertex_adjacencies[adj_index].get_direction();
                if !visited_edges.contains(&edge_id) {
                    found_next_edge = true;
                    // Case-1: Vertex that has not been tranversed has the highesrt priority
                    if !vertex_dfs_id_map.contains_key(&end_v_id) {
                        vertex_dfs_id_map.insert(end_v_id, next_free_id);
                        next_free_id += 1;
                    }
                    // Case-2: Compare the DFS ids between end vertices that have been traversed and with the same ranks
                    // Choose the one with the smallest DFS id
                    else {
                        let mut min_dfs_id: PatternRankId = *vertex_dfs_id_map.get(&end_v_id).unwrap();
                        while adj_index < vertex_adjacencies.len() - 1 {
                            adj_index += 1;
                            let adj_edge_id = vertex_adjacencies[adj_index].get_edge_id();
                            let adj_v_id = vertex_adjacencies[adj_index].get_adj_vertex_id();
                            let adj_edge_dir = vertex_adjacencies[adj_index].get_direction();
                            if visited_edges.contains(&adj_edge_id) {
                                continue;
                            };
                            if adj_edge_dir != e_dir {
                                break;
                            };
                            match self.cmp_edges(edge_id, adj_edge_id) {
                                Ordering::Greater => break,
                                Ordering::Less => break,
                                Ordering::Equal => {
                                    if !vertex_dfs_id_map.contains_key(&adj_v_id) {
                                        vertex_dfs_id_map.insert(adj_v_id, next_free_id);
                                        next_free_id += 1;
                                        // Update
                                        edge_id = adj_edge_id;
                                        end_v_id = adj_v_id;
                                        break;
                                    }

                                    let current_dfs_id: PatternRankId =
                                        *vertex_dfs_id_map.get(&adj_v_id).unwrap();
                                    if current_dfs_id < min_dfs_id {
                                        min_dfs_id = current_dfs_id;
                                        // Update
                                        edge_id = adj_edge_id;
                                        end_v_id = adj_v_id;
                                    }
                                }
                            }
                        }
                    }

                    // Update
                    dfs_edge_sequence.push(edge_id);
                    visited_edges.insert(edge_id);
                    vertex_stack.push_back(end_v_id);
                    break;
                }

                adj_index += 1;
            }

            // If Cannot find the next edge to traverse
            if !found_next_edge {
                vertex_stack.pop_back();
            }
        }

        // Check if dfs sorting fails
        if visited_edges.len() == self.get_edge_num()
            && dfs_edge_sequence.len() == self.get_edge_num()
            && vertex_dfs_id_map.len() == self.get_vertex_num()
        {
            Ok((dfs_edge_sequence, vertex_dfs_id_map))
        } else {
            Err(IrError::Unsupported("Failed when doing dfs sorting to pattern edges".to_string()))
        }
    }
}

/// Methods for Pattern Extension
impl Pattern {
    /// Get all the vertices(id) with the same vertex label and vertex rank
    ///
    /// These vertices are equivalent in the Pattern
    fn get_equivalent_vertices(&self, v_label: PatternLabelId, v_rank: PatternRankId) -> Vec<PatternId> {
        let mut equivalent_vertices = vec![];
        if let Some(vs_with_same_label) = self.vertex_label_map.get(&v_label) {
            for v_id in vs_with_same_label {
                if let Some(vertex) = self.vertices.get(*v_id) {
                    if vertex.rank == v_rank {
                        equivalent_vertices.push(*v_id);
                    }
                }
            }
        }

        equivalent_vertices
    }

    /// Get the legal id for the future incoming vertex
    fn get_next_pattern_vertex_id(&self) -> PatternId {
        let mut new_vertex_id = self.vertices.len() as PatternId;
        while self.vertices.contains_key(new_vertex_id) {
            new_vertex_id += 1;
        }

        new_vertex_id
    }

    /// Get the legal id for the future incoming vertex
    fn get_next_pattern_edge_id(&self) -> PatternId {
        let mut new_edge_id = self.edges.len() as PatternId;
        while self.edges.contains_key(new_edge_id) {
            new_edge_id += 1;
        }

        new_edge_id
    }

    /// Extend the current Pattern to a new Pattern with the given ExtendStep
    /// - If the ExtendStep is not matched with the current Pattern, the function will return None
    /// - Else, it will return the new Pattern after the extension
    ///
    /// The ExtendStep is not mathced with the current Pattern if:
    /// 1. Some extend edges of the ExtendStep cannot find a correponsponding source vertex in current Pattern
    ///    (the required source vertex doesn't exist or already occupied by other extend edges)
    /// 2. Or meet some limitations(e.g. limit the length of Pattern)
    pub fn extend(&self, extend_step: &ExtendStep) -> Option<Pattern> {
        let mut new_pattern = self.clone();
        let target_v_label = extend_step.get_target_v_label();
        let new_pattern_vertex =
            PatternVertex { id: new_pattern.get_next_pattern_vertex_id(), label: target_v_label, rank: 0 };
        for ((v_label, v_rank), extend_edges) in extend_step.iter() {
            // Get all the vertices which can be used to extend with these extend edges
            let vertices_can_use = self.get_equivalent_vertices(*v_label, *v_rank);
            // There's no enough vertices to extend, just return None
            if vertices_can_use.len() < extend_edges.len() {
                return None;
            }
            // Connect each vertex can be use to each extend edge
            for (i, extend_edge) in extend_edges.iter().enumerate() {
                let extend_vertex_id = vertices_can_use[i];
                let extend_dir = extend_edge.get_direction();
                // new pattern edge info
                let (mut start_v_id, mut end_v_id, mut start_v_label, mut end_v_label) = (
                    extend_vertex_id,
                    new_pattern_vertex.id,
                    self.vertices
                        .get(vertices_can_use[i])
                        .unwrap()
                        .label,
                    new_pattern_vertex.label,
                );
                if let PatternDirection::In = extend_dir {
                    std::mem::swap(&mut start_v_id, &mut end_v_id);
                    std::mem::swap(&mut start_v_label, &mut end_v_label);
                }
                let new_pattern_edge = PatternEdge {
                    id: new_pattern.get_next_pattern_edge_id(),
                    label: extend_edge.get_edge_label(),
                    start_v_id,
                    end_v_id,
                    start_v_label,
                    end_v_label,
                };
                if let PatternDirection::Out = extend_dir {
                    // update newly extended pattern vertex's adjacency info
                    new_pattern
                        .in_adjacencies_map
                        .entry(new_pattern_vertex.id)
                        .or_insert(vec![])
                        .push(Adjacency::new(new_pattern_edge.id, extend_vertex_id, PatternDirection::In));
                    // update extend vertex's adjacancy info
                    new_pattern
                        .out_adjacencies_map
                        .entry(extend_vertex_id)
                        .or_insert(vec![])
                        .push(Adjacency::new(
                            new_pattern_edge.id,
                            new_pattern_vertex.id,
                            PatternDirection::Out,
                        ));
                } else {
                    new_pattern
                        .out_adjacencies_map
                        .entry(new_pattern_vertex.id)
                        .or_insert(vec![])
                        .push(Adjacency::new(new_pattern_edge.id, extend_vertex_id, PatternDirection::Out));
                    // update extend vertex's adjacancy info
                    new_pattern
                        .in_adjacencies_map
                        .entry(extend_vertex_id)
                        .or_insert(vec![])
                        .push(Adjacency::new(
                            new_pattern_edge.id,
                            new_pattern_vertex.id,
                            PatternDirection::In,
                        ));
                }
                // Add the new pattern edge info to the new Pattern
                new_pattern
                    .edge_label_map
                    .entry(new_pattern_edge.label)
                    .or_insert(BTreeSet::new())
                    .insert(new_pattern_edge.id);
                new_pattern
                    .edges
                    .insert(new_pattern_edge.id, new_pattern_edge);
            }
        }
        // Add the newly extended pattern vertex to the new pattern
        new_pattern
            .vertex_label_map
            .entry(new_pattern_vertex.label)
            .or_insert(BTreeSet::new())
            .insert(new_pattern_vertex.id);
        new_pattern
            .vertices
            .insert(new_pattern_vertex.id, new_pattern_vertex);
        new_pattern.vertex_ranking();
        Some(new_pattern)
    }

    /// Find all possible ExtendSteps of current pattern based on the given Pattern Meta
    pub fn get_extend_steps(
        &self, pattern_meta: &PatternMeta, same_label_vertex_limit: usize,
    ) -> Vec<ExtendStep> {
        let mut extend_steps = vec![];
        // Get all vertex labels from pattern meta as the possible extend target vertex
        let target_v_labels = pattern_meta.vertex_label_ids_iter();
        // For every possible extend target vertex label, find its all adjacent edges to the current pattern
        for target_v_label in target_v_labels {
            if self
                .vertex_label_map
                .get(&target_v_label)
                .map(|v_ids| v_ids.len())
                .unwrap_or(0)
                >= same_label_vertex_limit
            {
                continue;
            }
            // The collection of extend edges with a source vertex id
            // The source vertex id is used to specify the extend edge is from which vertex of the pattern
            let mut extend_edges_with_src_id = vec![];
            for (_, src_vertex) in &self.vertices {
                // check whether there are some edges between the target vertex and the current source vertex
                let adjacent_edges =
                    pattern_meta.associated_elabels_iter_by_vlabel(src_vertex.label, target_v_label);
                // Transform all the adjacent edges to ExtendEdge and add to extend_edges_with_src_id
                for (adjacent_edge_label, adjacent_edge_dir) in adjacent_edges {
                    let extend_edge = ExtendEdge::new(
                        src_vertex.label,
                        src_vertex.rank,
                        adjacent_edge_label,
                        adjacent_edge_dir,
                    );
                    extend_edges_with_src_id.push((extend_edge, src_vertex.id));
                }
            }
            // Get the subsets of extend_edges_with_src_id, and add every subset to the extend edgess
            // The algorithm is BFS Search
            let extend_edges_set_collection =
                get_subsets(extend_edges_with_src_id, |(_, src_id_for_check), extend_edges_set| {
                    limit_repeated_element_num(
                        src_id_for_check,
                        extend_edges_set.iter().map(|(_, v_id)| v_id),
                        1,
                    )
                });
            for extend_edges in extend_edges_set_collection {
                let extend_step = ExtendStep::new(
                    target_v_label,
                    extend_edges
                        .into_iter()
                        .map(|(extend_edge, _)| extend_edge)
                        .collect(),
                );
                extend_steps.push(extend_step);
            }
        }
        extend_steps
    }

    /// Edit the pattern by connect some edges to the current pattern
    fn add_edge(&mut self, edge: &PatternEdge) -> IrResult<()> {
        // Error that the adding edge already exist
        if self.edges.contains_key(edge.get_id()) {
            return Err(IrError::InvalidCode("The adding edge already existed".to_string()));
        }
        // Error that cannot connect the edge to the pattern
        if let (None, None) = (
            self.get_vertex_from_id(edge.get_start_vertex_id()),
            self.get_vertex_from_id(edge.get_end_vertex_id()),
        ) {
            return Err(IrError::InvalidCode("The adding edge cannot connect to the pattern".to_string()));
        } else if let None = self.get_vertex_from_id(edge.start_v_id) {
            // end vertex already exists in the pattern, use it to connect
            // add start vertex
            self.vertices.insert(
                edge.start_v_id,
                PatternVertex { id: edge.start_v_id, label: edge.start_v_label, rank: 0 },
            );
            // add start vertex label
            self.vertex_label_map
                .entry(edge.start_v_label)
                .or_insert(BTreeSet::new())
                .insert(edge.start_v_id);
        } else if let None = self.get_vertex_from_id(edge.end_v_id) {
            // start vertex already exists in the pattern, use it to connect
            // add end vertex
            self.vertices.insert(
                edge.end_v_id,
                PatternVertex { id: edge.end_v_id, label: edge.end_v_label, rank: 0 },
            );
            self.vertex_label_map
                .entry(edge.end_v_label)
                .or_insert(BTreeSet::new())
                .insert(edge.end_v_id);
        }
        // update start vertex's connection info
        if self
            .get_vertex_from_id(edge.start_v_id)
            .is_some()
        {
            self.out_adjacencies_map
                .entry(edge.start_v_id)
                .or_insert(vec![])
                .push(Adjacency::new(edge.id, edge.end_v_id, PatternDirection::Out));
        }
        // update end vertex's connection info
        if self.get_vertex_from_id(edge.end_v_id).is_some() {
            self.in_adjacencies_map
                .entry(edge.end_v_id)
                .or_insert(vec![])
                .push(Adjacency::new(edge.id, edge.start_v_id, PatternDirection::In));
        }
        // add edge to the pattern
        self.edges.insert(edge.get_id(), edge.clone());
        // add edge label to the pattern
        self.edge_label_map
            .entry(edge.get_label())
            .or_insert(BTreeSet::new())
            .insert(edge.get_id());
        Ok(())
    }

    /// Add a series of edges to the current pattern to get a new pattern
    pub fn extend_by_edges<'a, T>(&self, edges: T) -> Option<Pattern>
    where
        T: Iterator<Item = &'a PatternEdge>,
    {
        let mut new_pattern = self.clone();
        for edge in edges {
            if let Err(_) = new_pattern.add_edge(edge) {
                return None;
            }
        }
        new_pattern.vertex_ranking();
        Some(new_pattern)
    }

    /// Locate a vertex(id) from the pattern based on the given extend step and target pattern code
    pub fn locate_vertex(
        &self, extend_step: &ExtendStep, target_pattern_code: &Vec<u8>, encoder: &Encoder,
    ) -> Option<PatternId> {
        let mut target_vertex_id: Option<PatternId> = None;
        let target_v_label = extend_step.get_target_v_label();
        // mark all the vertices with the same label as the extend step's target vertex as the candidates
        for target_v_cand in self.vertices_iter_by_label(target_v_label) {
            let target_v_cand_id = target_v_cand.id;
            if self.get_vertex_degree(target_v_cand_id) != extend_step.get_extend_edges_num() {
                continue;
            }
            // compare whether the candidate vertex has the same connection info as the extend step
            let cand_src_v_e_label_dir_set: BTreeSet<(PatternLabelId, PatternLabelId, PatternDirection)> =
                self.adjacencies_iter(target_v_cand_id)
                    .map(|adjacency| {
                        (
                            self.get_vertex_from_id(adjacency.get_adj_vertex_id())
                                .unwrap()
                                .get_label(),
                            self.get_edge_from_id(adjacency.get_edge_id())
                                .unwrap()
                                .get_label(),
                            adjacency.get_direction().reverse(),
                        )
                    })
                    .collect();
            let extend_src_v_e_label_dir_set: BTreeSet<(PatternLabelId, PatternLabelId, PatternDirection)> =
                extend_step
                    .extend_edges_iter()
                    .map(|extend_edge| {
                        (
                            extend_edge.get_start_vertex_label(),
                            extend_edge.get_edge_label(),
                            extend_edge.get_direction(),
                        )
                    })
                    .collect();
            // if has the same connection info, check whether the pattern after the removing the target vertex
            // has the same code with the target pattern code
            if cand_src_v_e_label_dir_set == extend_src_v_e_label_dir_set {
                let mut check_pattern = self.clone();
                check_pattern.remove_vertex(target_v_cand.get_id());
                let check_pattern_code: Vec<u8> = Cipher::encode_to(&check_pattern, encoder);
                // same code means successfully locate the vertex
                if check_pattern_code == *target_pattern_code {
                    target_vertex_id = Some(target_v_cand.get_id());
                    break;
                }
            }
        }
        target_vertex_id
    }

    /// Remove a vertex with all its adjacent edges in the current pattern
    pub fn remove_vertex(&mut self, vertex_id: PatternId) {
        if let Some(vertex) = self.get_vertex_from_id(vertex_id) {
            let vertex_label = vertex.get_label();
            let adjacencies: Vec<Adjacency> = self.adjacencies_iter(vertex_id).collect();
            // delete target vertex
            // delete in vertices
            self.vertices.remove(vertex_id);
            // delete in vertex label map
            self.vertex_label_map
                .get_mut(&vertex_label)
                .unwrap()
                .remove(&vertex_id);
            if self
                .vertex_label_map
                .get(&vertex_label)
                .unwrap()
                .len()
                == 0
            {
                self.vertex_label_map.remove(&vertex_label);
            }
            // delete in vertex tag map
            self.vertex_tag_map.remove_by_right(&vertex_id);
            // delete in vertex predicate map
            self.vertex_predicate_map.remove(&vertex_id);
            // delete in vertex adjacencies map
            self.out_adjacencies_map.remove(vertex_id);
            self.in_adjacencies_map.remove(vertex_id);
            for adjacency in adjacencies {
                let adjacent_vertex_id = adjacency.get_adj_vertex_id();
                let adjacent_edge_id = adjacency.get_edge_id();
                let adjacent_edge_label = self
                    .get_edge_from_id(adjacent_edge_id)
                    .unwrap()
                    .get_label();
                // delete adjacent edges
                // delete in edges
                self.edges.remove(adjacent_edge_id);
                // delete in edge label map
                self.edge_label_map
                    .get_mut(&adjacent_edge_label)
                    .unwrap()
                    .remove(&adjacent_edge_id);
                if self
                    .edge_label_map
                    .get(&adjacent_edge_label)
                    .unwrap()
                    .len()
                    == 0
                {
                    self.edge_label_map.remove(&adjacent_edge_label);
                }
                // delete in edge tag map
                self.edge_tag_map
                    .remove_by_right(&adjacent_edge_id);
                // delete in edge predicate map
                self.edge_predicate_map
                    .remove(&adjacent_edge_id);
                // update adjcent vertices's info
                if let PatternDirection::Out = adjacency.get_direction() {
                    self.in_adjacencies_map
                        .get_mut(adjacent_vertex_id)
                        .unwrap()
                        .retain(|adj| adj.get_edge_id() != adjacent_edge_id)
                } else {
                    self.out_adjacencies_map
                        .get_mut(adjacent_vertex_id)
                        .unwrap()
                        .retain(|adj| adj.get_edge_id() != adjacent_edge_id)
                }
            }
            self.vertex_ranking();
        }
    }

    /// Delete a extend step from current pattern to get a new pattern
    ///
    /// The code of the new pattern should be the same as the target pattern code
    pub fn de_extend(
        &self, extend_step: &ExtendStep, target_pattern_code: &Vec<u8>, encoder: &Encoder,
    ) -> Option<Pattern> {
        if let Some(target_vertex_id) = self.locate_vertex(extend_step, target_pattern_code, encoder) {
            let mut new_pattern = self.clone();
            new_pattern.remove_vertex(target_vertex_id);
            Some(new_pattern)
        } else {
            None
        }
    }

    /// Given a vertex id, pick all its neiboring edges and vertices to generate a definite extend step
    pub fn generate_definite_extend_step_by_v_id(
        &self, target_v_id: PatternId,
    ) -> Option<DefiniteExtendStep> {
        if let Some(target_vertex) = self.get_vertex_from_id(target_v_id) {
            let target_v_label = target_vertex.get_label();
            let mut extend_edges = vec![];
            for adjacency in self.adjacencies_iter(target_v_id) {
                let edge_id = adjacency.get_edge_id();
                let dir = adjacency.get_direction();
                let edge = self.get_edge_from_id(edge_id).unwrap();
                if let PatternDirection::In = dir {
                    extend_edges.push(DefiniteExtendEdge::new(
                        edge.get_start_vertex_id(),
                        edge_id,
                        edge.get_label(),
                        PatternDirection::Out,
                    ));
                } else {
                    extend_edges.push(DefiniteExtendEdge::new(
                        edge.get_end_vertex_id(),
                        edge_id,
                        edge.get_label(),
                        PatternDirection::In,
                    ));
                }
            }
            Some(DefiniteExtendStep::new(target_v_id, target_v_label, extend_edges))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use vec_map::VecMap;

    use super::Pattern;
    use super::PatternDirection;
    use crate::catalogue::codec::*;
    use crate::catalogue::pattern::PatternEdge;
    use crate::catalogue::pattern::PatternVertex;
    use crate::catalogue::test_cases::pattern_cases::*;
    use crate::catalogue::PatternId;
    use crate::plan::meta::TagId;

    const TAG_A: TagId = 0;
    const TAG_B: TagId = 1;
    const TAG_C: TagId = 2;
    const TAG_D: TagId = 3;

    /// Test whether the structure of pattern_case1 is the same as our previous description
    #[test]
    fn test_pattern_case1_structure() {
        let pattern_case1 = build_pattern_case1();
        let edges_num = pattern_case1.edges.len();
        assert_eq!(edges_num, 2);
        let vertices_num = pattern_case1.vertices.len();
        assert_eq!(vertices_num, 2);
        let edges_with_label_0 = pattern_case1.edge_label_map.get(&0).unwrap();
        assert_eq!(edges_with_label_0.len(), 2);
        let mut edges_with_label_0_iter = edges_with_label_0.iter();
        assert_eq!(*edges_with_label_0_iter.next().unwrap(), 0);
        assert_eq!(*edges_with_label_0_iter.next().unwrap(), 1);
        let vertices_with_label_0 = pattern_case1.vertex_label_map.get(&0).unwrap();
        assert_eq!(vertices_with_label_0.len(), 2);
        let mut vertices_with_label_0_iter = vertices_with_label_0.iter();
        assert_eq!(*vertices_with_label_0_iter.next().unwrap(), 0);
        assert_eq!(*vertices_with_label_0_iter.next().unwrap(), 1);
        let edge_0 = pattern_case1.edges.get(0).unwrap();
        assert_eq!(edge_0.id, 0);
        assert_eq!(edge_0.label, 0);
        assert_eq!(edge_0.start_v_id, 0);
        assert_eq!(edge_0.end_v_id, 1);
        assert_eq!(edge_0.start_v_label, 0);
        assert_eq!(edge_0.end_v_label, 0);
        let edge_1 = pattern_case1.edges.get(1).unwrap();
        assert_eq!(edge_1.id, 1);
        assert_eq!(edge_1.label, 0);
        assert_eq!(edge_1.start_v_id, 1);
        assert_eq!(edge_1.end_v_id, 0);
        assert_eq!(edge_1.start_v_label, 0);
        assert_eq!(edge_1.end_v_label, 0);
        let vertex_0 = pattern_case1.vertices.get(0).unwrap();
        assert_eq!(vertex_0.id, 0);
        assert_eq!(vertex_0.label, 0);
        assert_eq!(pattern_case1.get_vertex_degree(0), 2);
        let mut vertex_0_adjacent_edges_iter = pattern_case1.adjacencies_iter(0);
        let vertex_0_adjacency_0 = vertex_0_adjacent_edges_iter.next().unwrap();
        assert_eq!(vertex_0_adjacency_0.get_edge_id(), 0);
        assert_eq!(vertex_0_adjacency_0.get_adj_vertex_id(), 1);
        assert_eq!(vertex_0_adjacency_0.get_direction(), PatternDirection::Out);
        let vertex_0_adjacency_1 = vertex_0_adjacent_edges_iter.next().unwrap();
        assert_eq!(vertex_0_adjacency_1.get_edge_id(), 1);
        assert_eq!(vertex_0_adjacency_1.get_adj_vertex_id(), 1);
        assert_eq!(vertex_0_adjacency_1.get_direction(), PatternDirection::In);
        let vertex_1 = pattern_case1.vertices.get(1).unwrap();
        assert_eq!(vertex_1.id, 1);
        assert_eq!(vertex_1.label, 0);
        assert_eq!(pattern_case1.get_vertex_degree(1), 2);
        let mut vertex_1_adjacent_edges_iter = pattern_case1.adjacencies_iter(1);
        let vertex_1_adjacency_0 = vertex_1_adjacent_edges_iter.next().unwrap();
        assert_eq!(vertex_1_adjacency_0.get_edge_id(), 1);
        assert_eq!(vertex_1_adjacency_0.get_adj_vertex_id(), 0);
        assert_eq!(vertex_1_adjacency_0.get_direction(), PatternDirection::Out);
        let vertex_1_adjacency_1 = vertex_1_adjacent_edges_iter.next().unwrap();
        assert_eq!(vertex_1_adjacency_1.get_edge_id(), 0);
        assert_eq!(vertex_1_adjacency_1.get_adj_vertex_id(), 0);
        assert_eq!(vertex_1_adjacency_1.get_direction(), PatternDirection::In);
    }

    #[test]
    fn test_ldbc_pattern_from_pb_case1_structure() {
        let pattern_result = build_ldbc_pattern_from_pb_case1();
        if let Ok(pattern) = pattern_result {
            assert_eq!(pattern.vertices.len(), 3);
            assert_eq!(pattern.edges.len(), 3);
            // 3 Person vertices
            assert_eq!(pattern.vertex_label_map.get(&1).unwrap().len(), 3);
            // 3 knows edges
            assert_eq!(pattern.edge_label_map.get(&12).unwrap().len(), 3);
            // check structure
            // build identical pattern for comparison
            let pattern_edge1 = PatternEdge::new(0, 12, 0, 1, 1, 1);
            let pattern_edge2 = PatternEdge::new(1, 12, 0, 2, 1, 1);
            let pattern_edge3 = PatternEdge::new(2, 12, 1, 2, 1, 1);
            let pattern_for_comparison =
                Pattern::try_from(vec![pattern_edge1, pattern_edge2, pattern_edge3]).unwrap();
            // check whether the two pattern has the same code
            let encoder = Encoder::init(4, 4, 1, 2);
            let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
            let pattern_for_comparison_code: Vec<u8> = pattern_for_comparison.encode_to(&encoder);
            assert_eq!(pattern_code, pattern_for_comparison_code);
            // check Tag
            assert_eq!(pattern.get_vertex_from_tag(TAG_A).unwrap().id, 0);
            assert_eq!(pattern.get_vertex_from_tag(TAG_B).unwrap().id, 1);
            assert_eq!(pattern.get_vertex_from_tag(TAG_C).unwrap().id, 2);
        } else if let Err(error) = pattern_result {
            panic!("Build pattern from pb message failed: {:?}", error)
        }
    }

    #[test]
    fn test_ldbc_pattern_from_pb_case2_structure() {
        let pattern_result = build_ldbc_pattern_from_pb_case2();
        if let Ok(pattern) = pattern_result {
            assert_eq!(pattern.vertices.len(), 3);
            assert_eq!(pattern.edges.len(), 3);
            // 2 Person vertices
            assert_eq!(pattern.vertex_label_map.get(&1).unwrap().len(), 2);
            // 1 University vertex
            assert_eq!(pattern.vertex_label_map.get(&12).unwrap().len(), 1);
            // 1 knows edge
            assert_eq!(pattern.edge_label_map.get(&12).unwrap().len(), 1);
            // 2 studyat edges
            assert_eq!(pattern.edge_label_map.get(&15).unwrap().len(), 2);
            // check structure
            let pattern_edge1 = PatternEdge::new(0, 15, 1, 0, 1, 12);
            let pattern_edge2 = PatternEdge::new(1, 15, 2, 0, 1, 12);
            let pattern_edge3 = PatternEdge::new(2, 12, 1, 2, 1, 1);
            let pattern_for_comparison =
                Pattern::try_from(vec![pattern_edge1, pattern_edge2, pattern_edge3]).unwrap();
            // check whether the two pattern has the same code
            let encoder = Encoder::init(4, 4, 1, 2);
            let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
            let pattern_for_comparison_code: Vec<u8> = pattern_for_comparison.encode_to(&encoder);
            assert_eq!(pattern_code, pattern_for_comparison_code);
            // check Tag
            assert_eq!(pattern.get_vertex_from_tag(TAG_A).unwrap().id, 0);
            assert_eq!(pattern.get_vertex_from_tag(TAG_B).unwrap().id, 1);
            assert_eq!(pattern.get_vertex_from_tag(TAG_C).unwrap().id, 2);
        } else if let Err(error) = pattern_result {
            panic!("Build pattern from pb message failed: {:?}", error)
        }
    }

    #[test]
    fn test_ldbc_pattern_from_pb_case3_structure() {
        let pattern_result = build_ldbc_pattern_from_pb_case3();
        if let Ok(pattern) = pattern_result {
            assert_eq!(pattern.vertices.len(), 4);
            assert_eq!(pattern.edges.len(), 6);
            // 4 Person vertices
            assert_eq!(pattern.vertex_label_map.get(&1).unwrap().len(), 4);
            // 6 knows edges
            assert_eq!(pattern.edge_label_map.get(&12).unwrap().len(), 6);
            // check structure
            // build identical pattern for comparison
            let pattern_edge1 = PatternEdge::new(0, 12, 0, 1, 1, 1);
            let pattern_edge2 = PatternEdge::new(1, 12, 0, 2, 1, 1);
            let pattern_edge3 = PatternEdge::new(2, 12, 1, 2, 1, 1);
            let pattern_edge4 = PatternEdge::new(3, 12, 0, 3, 1, 1);
            let pattern_edge5 = PatternEdge::new(4, 12, 1, 3, 1, 1);
            let pattern_edge6 = PatternEdge::new(5, 12, 2, 3, 1, 1);
            let pattern_for_comparison = Pattern::try_from(vec![
                pattern_edge1,
                pattern_edge2,
                pattern_edge3,
                pattern_edge4,
                pattern_edge5,
                pattern_edge6,
            ])
            .unwrap();
            // check whether the two pattern has the same code
            let encoder = Encoder::init(4, 4, 1, 3);
            let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
            let pattern_for_comparison_code: Vec<u8> = pattern_for_comparison.encode_to(&encoder);
            assert_eq!(pattern_code, pattern_for_comparison_code);
            // check Tag
            assert_eq!(pattern.get_vertex_from_tag(TAG_A).unwrap().id, 0);
            assert_eq!(pattern.get_vertex_from_tag(TAG_B).unwrap().id, 1);
            assert_eq!(pattern.get_vertex_from_tag(TAG_C).unwrap().id, 2);
            assert_eq!(pattern.get_vertex_from_tag(TAG_D).unwrap().id, 3);
        } else if let Err(error) = pattern_result {
            panic!("Build pattern from pb message failed: {:?}", error)
        }
    }

    #[test]
    fn test_ldbc_pattern_from_pb_case4_structure() {
        let pattern_result = build_ldbc_pattern_from_pb_case4();
        if let Ok(pattern) = pattern_result {
            assert_eq!(pattern.vertices.len(), 4);
            assert_eq!(pattern.edges.len(), 4);
            // 2 Person vertices
            assert_eq!(pattern.vertex_label_map.get(&1).unwrap().len(), 2);
            // 1 City vertex
            assert_eq!(pattern.vertex_label_map.get(&9).unwrap().len(), 1);
            // 1 Comment vertex
            assert_eq!(pattern.vertex_label_map.get(&2).unwrap().len(), 1);
            // 1 has creator edge
            assert_eq!(pattern.edge_label_map.get(&0).unwrap().len(), 1);
            // 1 likes edge
            assert_eq!(pattern.edge_label_map.get(&13).unwrap().len(), 1);
            // 2 islocated edges
            assert_eq!(pattern.edge_label_map.get(&11).unwrap().len(), 2);
            // check structure
            // build identical pattern for comparison
            let pattern_edge1 = PatternEdge::new(0, 11, 0, 1, 1, 9);
            let pattern_edge2 = PatternEdge::new(1, 11, 2, 1, 1, 9);
            let pattern_edge3 = PatternEdge::new(2, 13, 0, 3, 1, 2);
            let pattern_edge4 = PatternEdge::new(3, 0, 3, 2, 2, 1);
            let pattern_for_comparison =
                Pattern::try_from(vec![pattern_edge1, pattern_edge2, pattern_edge3, pattern_edge4])
                    .unwrap();
            // check whether the two pattern has the same code
            let encoder = Encoder::init(4, 4, 1, 2);
            let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
            let pattern_for_comparison_code: Vec<u8> = pattern_for_comparison.encode_to(&encoder);
            assert_eq!(pattern_code, pattern_for_comparison_code);
            // check Tag
            assert_eq!(pattern.get_vertex_from_tag(TAG_A).unwrap().id, 0);
            assert_eq!(pattern.get_vertex_from_tag(TAG_B).unwrap().id, 2);
            assert_eq!(pattern.get_vertex_from_tag(TAG_C).unwrap().id, 1);
            assert_eq!(pattern.get_vertex_from_tag(TAG_D).unwrap().id, 3);
        } else if let Err(error) = pattern_result {
            panic!("Build pattern from pb message failed: {:?}", error)
        }
    }

    #[test]
    fn test_ldbc_pattern_from_pb_case5_structure() {
        let pattern_result = build_ldbc_pattern_from_pb_case5();
        if let Ok(pattern) = pattern_result {
            assert_eq!(pattern.vertices.len(), 6);
            assert_eq!(pattern.edges.len(), 6);
            // 6 Person vertices
            assert_eq!(pattern.vertex_label_map.get(&1).unwrap().len(), 6);
            // 6 knows edges
            assert_eq!(pattern.edge_label_map.get(&12).unwrap().len(), 6);
            // check structure
            // build identical pattern for comparison
            let pattern_edge1 = PatternEdge::new(0, 12, 0, 1, 1, 1);
            let pattern_edge2 = PatternEdge::new(1, 12, 2, 1, 1, 1);
            let pattern_edge3 = PatternEdge::new(2, 12, 2, 3, 1, 1);
            let pattern_edge4 = PatternEdge::new(3, 12, 4, 3, 1, 1);
            let pattern_edge5 = PatternEdge::new(4, 12, 4, 5, 1, 1);
            let pattern_edge6 = PatternEdge::new(5, 12, 0, 5, 1, 1);
            let pattern_for_comparison = Pattern::try_from(vec![
                pattern_edge1,
                pattern_edge2,
                pattern_edge3,
                pattern_edge4,
                pattern_edge5,
                pattern_edge6,
            ])
            .unwrap();
            // check whether the two pattern has the same code
            let encoder = Encoder::init(4, 4, 1, 3);
            let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
            let pattern_for_comparison_code: Vec<u8> = pattern_for_comparison.encode_to(&encoder);
            assert_eq!(pattern_code, pattern_for_comparison_code);
            // check Tag
            assert_eq!(pattern.get_vertex_from_tag(TAG_A).unwrap().id, 0);
            assert_eq!(pattern.get_vertex_from_tag(TAG_B).unwrap().id, 1);
            assert_eq!(pattern.get_vertex_from_tag(TAG_C).unwrap().id, 3);
        } else if let Err(error) = pattern_result {
            panic!("Build pattern from pb message failed: {:?}", error)
        }
    }

    #[test]
    fn test_ldbc_pattern_from_pb_case6_structure() {
        let pattern_result = build_ldbc_pattern_from_pb_case6();
        if let Ok(pattern) = pattern_result {
            assert_eq!(pattern.vertices.len(), 6);
            assert_eq!(pattern.edges.len(), 6);
            // 4 Persons vertices
            assert_eq!(pattern.vertex_label_map.get(&1).unwrap().len(), 4);
            // 1 City vertex
            assert_eq!(pattern.vertex_label_map.get(&9).unwrap().len(), 1);
            // 1 Comment vertex
            assert_eq!(pattern.vertex_label_map.get(&2).unwrap().len(), 1);
            // 1 has creator edge
            assert_eq!(pattern.edge_label_map.get(&0).unwrap().len(), 1);
            // 1 likes edge
            assert_eq!(pattern.edge_label_map.get(&13).unwrap().len(), 1);
            // 2 islocated edges
            assert_eq!(pattern.edge_label_map.get(&11).unwrap().len(), 2);
            // 2 knows edges
            assert_eq!(pattern.edge_label_map.get(&12).unwrap().len(), 2);
            // check structure
            // build identical pattern for comparison
            let pattern_edge1 = PatternEdge::new(0, 11, 0, 1, 1, 9);
            let pattern_edge2 = PatternEdge::new(1, 11, 2, 1, 1, 9);
            let pattern_edge3 = PatternEdge::new(2, 12, 2, 3, 1, 1);
            let pattern_edge4 = PatternEdge::new(3, 12, 3, 4, 1, 1);
            let pattern_edge5 = PatternEdge::new(4, 0, 5, 4, 2, 1);
            let pattern_edge6 = PatternEdge::new(5, 13, 0, 5, 1, 2);
            let pattern_for_comparison = Pattern::try_from(vec![
                pattern_edge1,
                pattern_edge2,
                pattern_edge3,
                pattern_edge4,
                pattern_edge5,
                pattern_edge6,
            ])
            .unwrap();
            // check whether the two pattern has the same code
            let encoder = Encoder::init(4, 4, 1, 3);
            let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
            let pattern_for_comparison_code: Vec<u8> = pattern_for_comparison.encode_to(&encoder);
            assert_eq!(pattern_code, pattern_for_comparison_code);
            // check Tag
            assert_eq!(pattern.get_vertex_from_tag(TAG_A).unwrap().id, 0);
            assert_eq!(pattern.get_vertex_from_tag(TAG_B).unwrap().id, 1);
            assert_eq!(pattern.get_vertex_from_tag(TAG_C).unwrap().id, 4);
        } else if let Err(error) = pattern_result {
            panic!("Build pattern from pb message failed: {:?}", error)
        }
    }

    #[test]
    fn set_accurate_rank_case1() {
        let pattern = build_pattern_case1();
        let vertices: VecMap<&PatternVertex> = pattern.vertices_iter().enumerate().collect();
        assert_eq!(vertices.get(0).unwrap().get_rank(), 0);
        assert_eq!(vertices.get(1).unwrap().get_rank(), 0);
    }

    #[test]
    fn set_accurate_rank_case2() {
        let pattern = build_pattern_case2();
        let vertices = &pattern.vertices;
        assert_eq!(vertices.get(0).unwrap().get_rank(), 0);
        assert_eq!(vertices.get(1).unwrap().get_rank(), 0);
        assert_eq!(vertices.get(2).unwrap().get_rank(), 0);
    }

    #[test]
    fn set_accurate_rank_case3() {
        let pattern = build_pattern_case3();
        let vertices = &pattern.vertices;
        assert_eq!(vertices.get(0).unwrap().get_rank(), 1);
        assert_eq!(vertices.get(1).unwrap().get_rank(), 0);
        assert_eq!(vertices.get(2).unwrap().get_rank(), 1);
        assert_eq!(vertices.get(3).unwrap().get_rank(), 0);
    }

    #[test]
    fn set_accurate_rank_case4() {
        let pattern = build_pattern_case4();
        let vertices = &pattern.vertices;
        assert_eq!(vertices.get(0).unwrap().get_rank(), 1);
        assert_eq!(vertices.get(1).unwrap().get_rank(), 0);
        assert_eq!(vertices.get(2).unwrap().get_rank(), 1);
        assert_eq!(vertices.get(3).unwrap().get_rank(), 0);
    }

    #[test]
    fn set_accurate_rank_case5() {
        let pattern = build_pattern_case5();
        let id_vec_a: Vec<PatternId> = vec![100, 200, 300, 400];
        let id_vec_b: Vec<PatternId> = vec![10, 20, 30];
        let id_vec_c: Vec<PatternId> = vec![1, 2, 3];
        let id_vec_d: Vec<PatternId> = vec![1000];
        let vertices = &pattern.vertices;
        // A
        assert_eq!(vertices.get(id_vec_a[0]).unwrap().get_rank(), 1);
        assert_eq!(vertices.get(id_vec_a[1]).unwrap().get_rank(), 3);
        assert_eq!(vertices.get(id_vec_a[2]).unwrap().get_rank(), 0);
        assert_eq!(vertices.get(id_vec_a[3]).unwrap().get_rank(), 2);
        // B
        assert_eq!(vertices.get(id_vec_b[0]).unwrap().get_rank(), 0);
        assert_eq!(vertices.get(id_vec_b[1]).unwrap().get_rank(), 2);
        assert_eq!(vertices.get(id_vec_b[2]).unwrap().get_rank(), 1);
        // C
        assert_eq!(vertices.get(id_vec_c[0]).unwrap().get_rank(), 0);
        assert_eq!(vertices.get(id_vec_c[1]).unwrap().get_rank(), 2);
        assert_eq!(vertices.get(id_vec_c[2]).unwrap().get_rank(), 0);
        // D
        assert_eq!(vertices.get(id_vec_d[0]).unwrap().get_rank(), 0);
    }

    #[test]
    fn rank_ranking_case1() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case1();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case2() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case2();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case3() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case3();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case4() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case4();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
    }

    #[test]
    fn rank_ranking_case5() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case5();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case6() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case6();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case7() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case7();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case8() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case8();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case9() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case9();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case10() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case10();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case11() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case11();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case12() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case12();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B3").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case13() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case13();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case14() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case14();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B2").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B3").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("C0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case15() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case15();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("C0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("C1").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
    }

    #[test]
    fn rank_ranking_case16() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case16();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B1").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("C0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("C1").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("D0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case17() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case17();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            5
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            4
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A4").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A5").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case17_even_num_chain() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case17_even_num_chain();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            5
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            6
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A4").unwrap())
                .unwrap()
                .get_rank(),
            4
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A5").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A6").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn rank_ranking_case17_long_chain() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case17_long_chain();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            5
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            7
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A4").unwrap())
                .unwrap()
                .get_rank(),
            9
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A5").unwrap())
                .unwrap()
                .get_rank(),
            10
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A6").unwrap())
                .unwrap()
                .get_rank(),
            8
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A7").unwrap())
                .unwrap()
                .get_rank(),
            6
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A8").unwrap())
                .unwrap()
                .get_rank(),
            4
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A9").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A10").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn vertex_ranking_case17_special_id_situation_1() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case17_special_id_situation_1();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            5
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            4
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A4").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A5").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn vertex_ranking_case17_special_id_situation_2() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case17_special_id_situation_2();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            5
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            4
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A4").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A5").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn vertex_ranking_case18() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case18();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A4").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A5").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn vertex_ranking_case19() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case19();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            8
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            9
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            2
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A4").unwrap())
                .unwrap()
                .get_rank(),
            1
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A5").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A6").unwrap())
                .unwrap()
                .get_rank(),
            4
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A7").unwrap())
                .unwrap()
                .get_rank(),
            6
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A8").unwrap())
                .unwrap()
                .get_rank(),
            5
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A9").unwrap())
                .unwrap()
                .get_rank(),
            7
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("B0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("C0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("D0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("E0").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn vertex_ranking_case20() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case20();
        let vertices = &pattern.vertices;
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A0").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A1").unwrap())
                .unwrap()
                .get_rank(),
            3
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A2").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A3").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
        assert_eq!(
            vertices
                .get(*vertex_id_map.get("A4").unwrap())
                .unwrap()
                .get_rank(),
            0
        );
    }

    #[test]
    fn dfs_sorting_case1() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case1();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            0
        );
    }

    #[test]
    fn dfs_sorting_case3() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case3();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            2
        );
    }

    #[test]
    fn dfs_sorting_case4() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case4();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A2").unwrap())
                .unwrap(),
            2
        );
    }

    #[test]
    fn dfs_sorting_case6() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case6();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            2
        );
    }

    #[test]
    fn dfs_sorting_case9() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case9();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            3
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B1").unwrap())
                .unwrap(),
            2
        );
    }

    #[test]
    fn dfs_sorting_case11() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case11();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            2
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B1").unwrap())
                .unwrap(),
            3
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B2").unwrap())
                .unwrap(),
            4
        );
    }

    #[test]
    fn dfs_sorting_case13() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case13();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            4
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            5
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A2").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B1").unwrap())
                .unwrap(),
            2
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B2").unwrap())
                .unwrap(),
            3
        );
    }

    #[test]
    fn dfs_sorting_case14() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case14();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            2
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B1").unwrap())
                .unwrap(),
            4
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B2").unwrap())
                .unwrap(),
            5
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B3").unwrap())
                .unwrap(),
            3
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("C0").unwrap())
                .unwrap(),
            6
        );
    }

    #[test]
    fn dfs_sorting_case15() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case15();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            4
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            7
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A2").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A3").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            5
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B1").unwrap())
                .unwrap(),
            2
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B2").unwrap())
                .unwrap(),
            8
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("C0").unwrap())
                .unwrap(),
            6
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("C1").unwrap())
                .unwrap(),
            3
        );
    }

    #[test]
    fn dfs_sorting_case16() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case16();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            5
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            8
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A2").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A3").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            6
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B1").unwrap())
                .unwrap(),
            2
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B2").unwrap())
                .unwrap(),
            9
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("C0").unwrap())
                .unwrap(),
            7
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("C1").unwrap())
                .unwrap(),
            3
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("D0").unwrap())
                .unwrap(),
            4
        );
    }

    #[test]
    fn dfs_sorting_case17() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case17();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            5
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            4
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A2").unwrap())
                .unwrap(),
            3
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A3").unwrap())
                .unwrap(),
            2
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A4").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A5").unwrap())
                .unwrap(),
            0
        );
    }

    #[test]
    fn dfs_sorting_case17_variant_long_chain() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case17_long_chain();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            10
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            9
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A2").unwrap())
                .unwrap(),
            8
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A3").unwrap())
                .unwrap(),
            7
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A4").unwrap())
                .unwrap(),
            6
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A5").unwrap())
                .unwrap(),
            5
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A6").unwrap())
                .unwrap(),
            4
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A7").unwrap())
                .unwrap(),
            3
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A8").unwrap())
                .unwrap(),
            2
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A9").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A10").unwrap())
                .unwrap(),
            0
        );
    }

    #[test]
    fn dfs_sorting_case19() {
        let (pattern, vertex_id_map) = build_pattern_rank_ranking_case19();
        let (_, vertex_dfs_id_map) = pattern.get_dfs_edge_sequence().unwrap();
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A0").unwrap())
                .unwrap(),
            3
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A1").unwrap())
                .unwrap(),
            7
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A2").unwrap())
                .unwrap(),
            0
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A3").unwrap())
                .unwrap(),
            4
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A4").unwrap())
                .unwrap(),
            8
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A5").unwrap())
                .unwrap(),
            11
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A6").unwrap())
                .unwrap(),
            1
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A7").unwrap())
                .unwrap(),
            5
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A8").unwrap())
                .unwrap(),
            9
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("A9").unwrap())
                .unwrap(),
            12
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("B0").unwrap())
                .unwrap(),
            2
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("C0").unwrap())
                .unwrap(),
            10
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("D0").unwrap())
                .unwrap(),
            6
        );
        assert_eq!(
            *vertex_dfs_id_map
                .get(vertex_id_map.get("E0").unwrap())
                .unwrap(),
            13
        );
    }
}
