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

use std::collections::HashMap;

use ascii::AsciiChar;
use ascii::AsciiString;
use ascii::ToAsciiChar;

use crate::catalogue::extend_step::{ExtendEdge, ExtendStep};
use crate::catalogue::pattern::Pattern;
use crate::catalogue::pattern::PatternEdge;
use crate::catalogue::PatternDirection;

pub trait Cipher<T> {
    fn encode_to(&self, encoder: &Encoder) -> T;

    fn decode_from(src_code: T, encoder: &Encoder) -> Self;
}

impl Cipher<Vec<u8>> for Pattern {
    fn encode_to(&self, encoder: &Encoder) -> Vec<u8> {
        let pattern_encode_unit = EncodeUnit::from_pattern(self, encoder);
        pattern_encode_unit.to_vec_u8(8)
    }

    fn decode_from(src_code: Vec<u8>, encoder: &Encoder) -> Self {
        let decode_unit = DecodeUnit::new_for_pattern(encoder);
        let decode_vec = decode_unit.decode_to_vec_i32(&src_code, 8);
        DecodeUnit::to_pattern(&decode_vec)
    }
}

impl Cipher<AsciiString> for Pattern {
    fn encode_to(&self, encoder: &Encoder) -> AsciiString {
        let pattern_encode_unit = EncodeUnit::from_pattern(self, encoder);
        pattern_encode_unit.to_ascii_string()
    }

    fn decode_from(src_code: AsciiString, encoder: &Encoder) -> Self {
        let decode_unit = DecodeUnit::new_for_pattern(encoder);
        let decode_vec = decode_unit.decode_to_vec_i32(src_code.as_bytes(), 7);
        DecodeUnit::to_pattern(&decode_vec)
    }
}

impl Cipher<Vec<u8>> for ExtendStep {
    fn encode_to(&self, encoder: &Encoder) -> Vec<u8> {
        let extend_step_encode_unit = EncodeUnit::from_extend_step(self, encoder);
        extend_step_encode_unit.to_vec_u8(8)
    }

    fn decode_from(src_code: Vec<u8>, encoder: &Encoder) -> Self {
        let decode_unit = DecodeUnit::new_for_extend_step(encoder);
        let decode_vec = decode_unit.decode_to_vec_i32(&src_code, 8);
        DecodeUnit::to_extend_step(&decode_vec)
    }
}

impl Cipher<AsciiString> for ExtendStep {
    fn encode_to(&self, encoder: &Encoder) -> AsciiString {
        let extend_step_encode_unit = EncodeUnit::from_extend_step(self, encoder);
        extend_step_encode_unit.to_ascii_string()
    }

    fn decode_from(src_code: AsciiString, encoder: &Encoder) -> Self {
        let decode_unit = DecodeUnit::new_for_extend_step(encoder);
        let decode_vec = decode_unit.decode_to_vec_i32(src_code.as_bytes(), 7);
        DecodeUnit::to_extend_step(&decode_vec)
    }
}
/// Unique Pattern Identity Encoder
/// Member Variables:
/// Contains the bit number that each variable in the encoding unit occupies
#[derive(Debug, Clone)]
pub struct Encoder {
    edge_label_bit_num: usize,
    vertex_label_bit_num: usize,
    direction_bit_num: usize,
    vertex_index_bit_num: usize,
}

/// Initializers
impl Encoder {
    /// Initialize Encoder with User Definded Parameters
    pub fn init(
        edge_label_bit_num: usize, vertex_label_bit_num: usize, edge_direction_bit_num: usize,
        vertex_index_bit_num: usize,
    ) -> Encoder {
        Encoder {
            edge_label_bit_num,
            vertex_label_bit_num,
            direction_bit_num: edge_direction_bit_num,
            vertex_index_bit_num,
        }
    }

    /// Initialize the Encoder by Analyzing a Pattern
    /// The vertex_index_bit_num can be a user defined value if it is applicable to the pattern
    pub fn init_by_pattern(pattern: &Pattern, vertex_index_bit_num: usize) -> Encoder {
        let min_edge_label_bit_num = pattern.get_min_edge_label_bit_num();
        let min_vertex_label_bit_num = pattern.get_min_vertex_label_bit_num();
        let mut min_vertex_index_bit_num = pattern.get_min_vertex_index_bit_num();
        // Apply the user defined vertex_index_bit_num only if it is larger than the minimum value needed for the pattern
        if vertex_index_bit_num > min_vertex_index_bit_num {
            min_vertex_index_bit_num = vertex_index_bit_num;
        }

        let edge_direction_bit_num = 2;
        Encoder {
            edge_label_bit_num: min_edge_label_bit_num,
            vertex_label_bit_num: min_vertex_label_bit_num,
            direction_bit_num: edge_direction_bit_num,
            vertex_index_bit_num: min_vertex_index_bit_num,
        }
    }
}

/// Mehthods for access fields of Encoder
impl Encoder {
    pub fn get_edge_label_bit_num(&self) -> usize {
        self.edge_label_bit_num
    }

    pub fn get_vertex_label_bit_num(&self) -> usize {
        self.vertex_label_bit_num
    }

    pub fn get_direction_bit_num(&self) -> usize {
        self.direction_bit_num
    }

    pub fn get_vertex_index_bit_num(&self) -> usize {
        self.vertex_index_bit_num
    }
}

/// Methods for Encode and Decode
impl Encoder {
    /// Compute the u8 value for each storage unit (AsciiChar or u8)
    /// Example:
    /// value = 3, value head = 8, value tail = 7, storage_unit_valid_bit_num = 8, storage_unit_index = 0
    /// Our expectation code: |00000001|10000000| (3 = bin(11))
    ///                     (head = 8)^ ^(tail = 7)
    ///                 unit_index = 1  unit_index = 0
    ///  Our goal is to put some parts of the value(3 = bin(11)) to the appointed storage unit (= 0 by index)
    /// At this case, unit_index = 0, we would have this storage unit += 128(bin 10000000) to achieve the goal
    pub fn get_encode_numerical_value(
        value: i32, value_head: usize, value_tail: usize, storage_unit_valid_bit_num: usize,
        storage_unit_index: usize,
    ) -> u8 {
        let mut output: i32;
        // Get the head and tail of the appointed storage unit
        let char_tail = storage_unit_index * storage_unit_valid_bit_num;
        let char_head = (storage_unit_index + 1) * storage_unit_valid_bit_num - 1;
        // Case that the storage unit doesn't contain our value: value|...| or |...|value
        if value_tail > char_head || value_head < char_tail {
            output = 0;
        }
        // Case that the value is completely contained in the sotorage unit: |...value...|
        else if value_tail >= char_tail && value_head <= char_head {
            let offset_bit_num = value_tail - char_tail;
            output = value * (1 << offset_bit_num);
        }
        // Case that the storage unit contains the left part of the value: |...va|lue...
        else if value_tail < char_tail && value_head <= char_head {
            let shift_bit_num = char_tail - value_tail;
            output = value / (1 << shift_bit_num);
        }
        // Case that the storage unit contains the right part of the value: ...va|lue...|
        else if value_tail >= char_tail && value_head > char_head {
            let shift_bit_num = char_head + 1 - value_tail;
            output = value % (1 << shift_bit_num);
            output = output * (1 << (storage_unit_valid_bit_num - shift_bit_num));
        }
        // Case that the storage unit only contains some middle part of the value: ...v|alu|e...
        else if value_tail < char_tail && value_head > char_head {
            let right_shift_bit_num = char_tail - value_tail;
            output = value % (1 << right_shift_bit_num);
            output = output % (1 << storage_unit_valid_bit_num);
        } else {
            panic!("Error in Converting Encode Unit to ASCII String: No Such Value Exists");
        }
        return output as u8;
    }

    /// Truncate some parts from the source code (&[u8]) and transform the truncation into i32
    /// Example:
    /// source code: |00000001|10000000|, head = 8, tail = 7, storage_unit_bit_num = 8
    ///            (head = 8)^ ^(tail = 7)
    /// Our expected decode value = 3 = bin(11)
    pub fn get_decode_value_by_head_tail(
        src_code: &[u8], head: usize, tail: usize, storage_unit_bit_num: usize,
    ) -> i32 {
        if head < tail {
            panic!("The head must be at least larger or equal to tail");
        }
        let mut output;
        //   |00000001|10000000|
        // (head = 8)^ ^(tail = 7)
        // head_index = 0, head_offset = 0
        // tail index = 1, tail_offset = 7
        let head_index = src_code.len() - 1 - (head / storage_unit_bit_num) as usize;
        let head_offset = head % storage_unit_bit_num;
        let tail_index = src_code.len() - 1 - (tail / storage_unit_bit_num) as usize;
        let tail_offset = tail % storage_unit_bit_num;

        if head_index >= src_code.len() || tail_index >= src_code.len() {
            panic!("The head and tail values are out of range");
        }

        // Case that head and tail are in the same storage unit
        if head_index == tail_index {
            output = (src_code[head_index] << (8 - 1 - head_offset) >> (8 - 1 - head_offset + tail_offset))
                as i32;
        }
        // Case that head and tail are on the different storage unit
        else {
            let index_diff = tail_index - head_index;
            output = (src_code[tail_index] as i32) >> tail_offset;
            for i in 1..index_diff {
                output += (src_code[tail_index - i] as i32)
                    << (storage_unit_bit_num - tail_offset + (i - 1) * storage_unit_bit_num);
            }
            output += ((src_code[head_index] << (8 - 1 - head_offset) >> (8 - 1 - head_offset)) as i32)
                << (storage_unit_bit_num - tail_offset + (index_diff - 1) * storage_unit_bit_num);
        }
        output
    }

    /// Get the effective bits of the given source code
    /// Example:
    /// source code: |00001000|00000001|
    /// the effective bots num is 12, as the four 0s can be deleted |(0000)1000|00000001|
    pub fn get_src_code_effective_bit_num(src_code: &[u8], storage_unit_bit_num: usize) -> usize {
        let mut start_pos = 0;
        for i in start_pos..src_code.len() {
            if src_code[i] != 0 {
                break;
            }
            start_pos += 1;
        }
        if start_pos == src_code.len() {
            return 0;
        }
        let mut start_pos_pos = 1;
        for i in 1..storage_unit_bit_num {
            if src_code[start_pos] >> i != 0 {
                start_pos_pos += 1;
            } else {
                break;
            }
        }
        (src_code.len() - start_pos - 1) * storage_unit_bit_num + start_pos_pos
    }
}

/// Design the EnocodeUnit for the abstraction of the encode behavior
/// Example:
/// values = [4, 5, 6, 7]
/// heads = [0, 3, 6, 9]
/// tails = [2, 5, 8, 11]
/// encode value = |0000(111)(1|10)(101)(100)|
pub struct EncodeUnit {
    /// A series of value to be encoded
    values: Vec<i32>,
    /// The heads of these values, one to one correspondence
    heads: Vec<usize>,
    /// The tails of these values, one to one correspondence
    tails: Vec<usize>,
}

/// Initializers
/// Build EncodeUnit for structs which needs to be encoded
impl EncodeUnit {
    pub fn from_pattern_edge(pattern: &Pattern, pattern_edge: &PatternEdge, encoder: &Encoder) -> Self {
        let edge_label = pattern_edge.get_label();
        let start_v_label = pattern_edge.get_start_vertex_label();
        let end_v_label = pattern_edge.get_end_vertex_label();
        let start_v_index = pattern.get_vertex_index(pattern_edge.get_start_vertex_id());
        let end_v_index = pattern.get_vertex_index(pattern_edge.get_end_vertex_id());

        let edge_label_bit_num = encoder.get_edge_label_bit_num();
        let vertex_label_bit_num = encoder.get_vertex_label_bit_num();
        let vertex_index_bit_num = encoder.get_vertex_index_bit_num();

        let values = vec![end_v_index, start_v_index, end_v_label, start_v_label, edge_label];
        let heads = vec![
            vertex_index_bit_num - 1,
            2 * vertex_index_bit_num - 1,
            vertex_label_bit_num + 2 * vertex_index_bit_num - 1,
            2 * vertex_label_bit_num + 2 * vertex_index_bit_num - 1,
            edge_label_bit_num + 2 * vertex_label_bit_num + 2 * vertex_index_bit_num - 1,
        ];
        let tails = vec![
            0,
            vertex_index_bit_num,
            2 * vertex_index_bit_num,
            vertex_label_bit_num + 2 * vertex_index_bit_num,
            2 * vertex_label_bit_num + 2 * vertex_index_bit_num,
        ];
        EncodeUnit { values, heads, tails }
    }

    pub fn from_pattern(pattern: &Pattern, encoder: &Encoder) -> Self {
        let mut pattern_encode_unit =
            EncodeUnit { values: Vec::new(), heads: Vec::new(), tails: Vec::new() };
        let ordered_edges_id = pattern.get_ordered_edges();
        for edge_id in ordered_edges_id {
            let edge = pattern.get_edge_from_id(edge_id).unwrap();

            let edge_encode_unit = EncodeUnit::from_pattern_edge(pattern, edge, encoder);
            pattern_encode_unit.extend_by_another_unit(&edge_encode_unit);
        }
        println!("");
        pattern_encode_unit
    }

    pub fn from_extend_edge(extend_edge: &ExtendEdge, encoder: &Encoder) -> Self {
        let start_v_label = extend_edge.get_start_vertex_label();
        let start_v_index = extend_edge.get_start_vertex_index();
        let edge_label = extend_edge.get_edge_label();
        let dir = extend_edge.get_direction();

        let vertex_label_bit_num = encoder.get_vertex_label_bit_num();
        let vertex_index_bit_num = encoder.get_vertex_index_bit_num();
        let edge_label_bit_num = encoder.get_edge_label_bit_num();
        let direction_bit_num = encoder.get_direction_bit_num();

        let values = vec![dir as i32, edge_label, start_v_index, start_v_label];
        let heads = vec![
            direction_bit_num - 1,
            edge_label_bit_num + direction_bit_num - 1,
            vertex_index_bit_num + edge_label_bit_num + direction_bit_num - 1,
            vertex_label_bit_num + vertex_index_bit_num + edge_label_bit_num + direction_bit_num - 1,
        ];
        let tails = vec![
            0,
            direction_bit_num,
            edge_label_bit_num + direction_bit_num,
            vertex_index_bit_num + edge_label_bit_num + direction_bit_num,
        ];
        EncodeUnit { values, heads, tails }
    }

    pub fn from_extend_step(extend_step: &ExtendStep, encoder: &Encoder) -> Self {
        let mut extend_step_encode_unit =
            EncodeUnit { values: Vec::new(), heads: Vec::new(), tails: Vec::new() };
        for (_, extend_edges) in extend_step.iter() {
            for extend_edge in extend_edges {
                let extend_edge_encode_unit = EncodeUnit::from_extend_edge(extend_edge, encoder);
                extend_step_encode_unit.extend_by_another_unit(&extend_edge_encode_unit);
            }
        }
        extend_step_encode_unit.extend_by_value_and_length(
            extend_step.get_target_v_label(),
            encoder.get_vertex_label_bit_num(),
        );
        extend_step_encode_unit
    }
}

/// Methods for access some fields and get some info from EncodeUnit
impl EncodeUnit {
    pub fn get_bits_num(&self) -> usize {
        let unit_len = self.values.len();
        if unit_len == 0 {
            return 0;
        }
        self.heads[unit_len] + 1
    }

    pub fn get_values(&self) -> &Vec<i32> {
        &self.values
    }

    pub fn get_heads(&self) -> &Vec<usize> {
        &self.heads
    }

    pub fn get_tails(&self) -> &Vec<usize> {
        &self.tails
    }
}

impl EncodeUnit {
    /// Transform an EncodeUnit to a Vec<u8> code
    pub fn to_vec_u8(&self, storage_unit_bit_num: usize) -> Vec<u8> {
        let unit_len = self.values.len();
        // self.heads[unit_len - 1] (+ 1) add one for extra bits indicating the end of the code
        let storage_unit_num = (self.heads[unit_len - 1] + 1) / storage_unit_bit_num + 1;
        let mut encode_vec = Vec::with_capacity(storage_unit_num as usize);
        for i in (0..storage_unit_num).rev() {
            let mut unit_value: u8 = 0;
            for j in 0..self.values.len() {
                let value = self.values[j];
                let head = self.heads[j];
                let tail = self.tails[j];
                unit_value +=
                    Encoder::get_encode_numerical_value(value, head, tail, storage_unit_bit_num, i);
            }
            encode_vec.push(unit_value);
        }
        // add add one for extra bits indicating the end of the code
        encode_vec[0] += Encoder::get_encode_numerical_value(
            1,
            self.heads[unit_len - 1] + 1,
            self.heads[unit_len - 1] + 1,
            storage_unit_bit_num,
            storage_unit_num - 1,
        );
        encode_vec
    }

    /// Transform an EncodeUnit to an AsciiString
    pub fn to_ascii_string(&self) -> AsciiString {
        let encode_vec: Vec<AsciiChar> = self
            .to_vec_u8(7)
            .iter()
            .map(|ch| ch.to_ascii_char().unwrap())
            .collect();
        AsciiString::from(encode_vec)
    }
}

/// Methods for EncodeUnit to extend
impl EncodeUnit {
    /// Add a new value to this EncodeUnit
    /// The head and tail info are also added based on the given length
    pub fn extend_by_value_and_length(&mut self, value: i32, length: usize) {
        let self_unit_len = self.values.len();
        self.values.push(value);
        let new_start = if self_unit_len == 0 { 0 } else { self.heads[self_unit_len - 1] + 1 };
        self.heads.push(new_start + length - 1);
        self.tails.push(new_start);
    }

    /// Extend this EncodeUnit by another EncodeUnit
    /// another EncodeUnit's value will be added to this EncodeUnit
    /// another EncodeUnit's head and tails will be modified based on the new start and then added to this EncodeUnit
    pub fn extend_by_another_unit(&mut self, other: &EncodeUnit) {
        let self_unit_len = self.values.len();
        self.values.extend(other.get_values());
        let new_start = if self_unit_len == 0 { 0 } else { self.heads[self_unit_len - 1] + 1 };
        let extend_heads: Vec<usize> = other
            .get_heads()
            .into_iter()
            .map(|head| head + new_start)
            .collect();
        let extend_tails: Vec<usize> = other
            .get_tails()
            .into_iter()
            .map(|tail| tail + new_start)
            .collect();
        self.heads.extend(&extend_heads);
        self.tails.extend(&extend_tails);
    }
}

/// Design the DecodeUnit for the abstraction of decode behavior
/// We assume that the code is organized by several units and an extra parts
/// Example:
/// As for the ExtendStep, its code is like:
/// vertex(edge)(edge)(edge)......, the vertex is the extra parts, the edge is the repeated unit
/// For both units and extra parts, there are some fields which occupy some bits, like:
/// edge:    001      010           011           100
///       direction edge_label vertex_index vertex label
/// unit_bits store each field's bit num
/// extra bits store each field's bit num of extra part
pub struct DecodeUnit {
    /// Bits num of one unit
    unit_bits: Vec<usize>,
    /// Bits num of extra parts of the code
    extra_bits: Vec<usize>,
}

/// Initializers
impl DecodeUnit {
    pub fn new_for_pattern(encoder: &Encoder) -> Self {
        let vertex_label_bit_num = encoder.get_vertex_label_bit_num();
        let vertex_index_bit_num = encoder.get_vertex_index_bit_num();
        let edge_label_bit_num = encoder.get_edge_label_bit_num();
        DecodeUnit {
            unit_bits: vec![
                vertex_index_bit_num,
                vertex_index_bit_num,
                vertex_label_bit_num,
                vertex_label_bit_num,
                edge_label_bit_num,
            ],
            // Pattern has no extra parts
            extra_bits: vec![],
        }
    }

    pub fn new_for_extend_step(encoder: &Encoder) -> Self {
        let vertex_label_bit_num = encoder.get_vertex_label_bit_num();
        let vertex_index_bit_num = encoder.get_vertex_index_bit_num();
        let edge_label_bit_num = encoder.get_edge_label_bit_num();
        let direction_bit_num = encoder.get_direction_bit_num();
        DecodeUnit {
            unit_bits: vec![
                direction_bit_num,
                edge_label_bit_num,
                vertex_index_bit_num,
                vertex_label_bit_num,
            ],
            // target vertex is the extra parts of extend step
            extra_bits: vec![vertex_label_bit_num],
        }
    }
}

/// Methods for access some fields of DecodeUnit
impl DecodeUnit {
    pub fn get_unit_bits(&self) -> &Vec<usize> {
        &self.unit_bits
    }

    pub fn get_extra_bits(&self) -> &Vec<usize> {
        &self.extra_bits
    }
}

/// Methods for decode
impl DecodeUnit {
    /// Decode a &[u8] source code to the Vec<i32> decode value
    pub fn decode_to_vec_i32(&self, src_code: &[u8], storage_unit_bit_num: usize) -> Vec<i32> {
        let mut decoded_vec = Vec::new();
        let bit_per_extend_edge: usize = self.unit_bits.iter().sum();
        // - 1 means delete tbe bit indicating the end of the code
        let src_code_bit_sum = Encoder::get_src_code_effective_bit_num(&src_code, storage_unit_bit_num) - 1;

        let mut unit_tail: usize = 0;
        let mut unit_head: usize = bit_per_extend_edge - 1;

        let mut decode_unit_to_vec = |unit: &Vec<usize>, tail| {
            if unit.len() == 0 {
                return;
            }
            let mut heads = vec![0; unit.len()];
            heads[0] = unit[0] + tail - 1;
            for i in 1..unit.len() {
                heads[i] = heads[i - 1] + unit[i]
            }

            let mut tails = vec![0; unit.len()];
            tails[0] = tail;
            for i in 1..unit.len() {
                tails[i] = tails[i - 1] + unit[i - 1];
            }

            for i in 0..unit.len() {
                let docoded_value = Encoder::get_decode_value_by_head_tail(
                    &src_code,
                    heads[i],
                    tails[i],
                    storage_unit_bit_num,
                );
                decoded_vec.push(docoded_value);
            }
        };

        while unit_head < src_code_bit_sum {
            decode_unit_to_vec(&self.unit_bits, unit_tail);
            unit_tail += bit_per_extend_edge;
            unit_head += bit_per_extend_edge;
        }
        decode_unit_to_vec(&self.extra_bits, unit_tail);
        decoded_vec
    }

    /// Transform a &[i32] decide value to a ExtendStep
    pub fn to_extend_step(decode_vec: &[i32]) -> ExtendStep {
        if decode_vec.len() % 4 != 1 {
            panic!("The length of decode vector doesn's satisfy the requirement of extend step decode");
        }
        let mut extend_edges = Vec::with_capacity(decode_vec.len() / 4);
        for i in (0..decode_vec.len() - 4).step_by(4) {
            let dir = if decode_vec[i] == 0 { PatternDirection::Out } else { PatternDirection::In };
            let edge_label = decode_vec[i + 1];
            let start_v_index = decode_vec[i + 2];
            let start_v_label = decode_vec[i + 3];
            extend_edges.push(ExtendEdge::new(start_v_label, start_v_index, edge_label, dir));
        }
        let target_v_label = *decode_vec.last().unwrap();
        ExtendStep::from((target_v_label, extend_edges))
    }

    /// Transform a &[i32] decode value to a Pattern
    pub fn to_pattern(decode_vec: &[i32]) -> Pattern {
        if decode_vec.len() % 5 != 0 {
            panic!("The length of decode vector doesn's satisfy the requirement of pattern decode");
        }
        let mut pattern_edges = Vec::with_capacity(decode_vec.len() / 5);
        let mut vertices_label_index_id_map = HashMap::new();
        for i in (0..decode_vec.len()).step_by(5) {
            let end_v_index = decode_vec[i];
            let start_v_index = decode_vec[i + 1];
            let end_v_label = decode_vec[i + 2];
            let start_v_label = decode_vec[i + 3];
            let edge_label = decode_vec[i + 4];
            let edge_id = (i / 5) as i32;
            let start_v_id = if vertices_label_index_id_map.contains_key(&(start_v_label, start_v_index)) {
                *vertices_label_index_id_map
                    .get(&(start_v_label, start_v_index))
                    .unwrap()
            } else {
                let v_id = vertices_label_index_id_map.len() as i32;
                vertices_label_index_id_map.insert((start_v_label, start_v_index), v_id);
                v_id
            };
            let end_v_id = if vertices_label_index_id_map.contains_key(&(end_v_label, end_v_index)) {
                *vertices_label_index_id_map
                    .get(&(end_v_label, end_v_index))
                    .unwrap()
            } else {
                let v_id = vertices_label_index_id_map.len() as i32;
                vertices_label_index_id_map.insert((end_v_label, end_v_index), v_id);
                v_id
            };
            pattern_edges.push(PatternEdge::new(
                edge_id,
                edge_label,
                start_v_id,
                end_v_id,
                start_v_label,
                end_v_label,
            ));
        }
        let mut pattern = Pattern::from(pattern_edges);
        for ((_, index), id) in vertices_label_index_id_map {
            pattern
                .get_vertex_mut_from_id(id)
                .unwrap()
                .set_index(index);
        }
        pattern
    }
}

/// Unit Testing
#[cfg(test)]
mod tests {
    use ascii::{self, AsciiString, ToAsciiChar};

    use crate::catalogue::codec::*;
    use crate::catalogue::pattern::*;
    use crate::catalogue::test_cases::extend_step_cases::*;
    use crate::catalogue::test_cases::pattern_cases::*;

    /// ### Generate AsciiString from Vector
    fn generate_asciistring_from_vec(vec: &[u8]) -> AsciiString {
        let mut output = AsciiString::new();
        for value in vec {
            output.push(value.to_ascii_char().unwrap());
        }
        output
    }

    #[test]
    fn test_create_encode_unit_from_edge() {
        let pattern = build_pattern_case6();
        let edge1 = pattern.get_edge_from_id(0).unwrap();
        let edge2 = pattern.get_edge_from_id(1).unwrap();
        let encoder = Encoder::init_by_pattern(&pattern, 5);
        let encode_unit_1 = EncodeUnit::from_pattern_edge(&pattern, edge1, &encoder);
        assert_eq!(encode_unit_1.values[4], 1);
        assert_eq!(encode_unit_1.values[3], 1);
        assert_eq!(encode_unit_1.values[2], 2);
        assert_eq!(encode_unit_1.values[1], 0);
        assert_eq!(encode_unit_1.values[0], 0);
        let encode_unit_2 = EncodeUnit::from_pattern_edge(&pattern, edge2, &encoder);
        assert_eq!(encode_unit_2.values[4], 2);
        assert_eq!(encode_unit_2.values[3], 1);
        assert_eq!(encode_unit_2.values[2], 3);
        assert_eq!(encode_unit_2.values[1], 0);
        assert_eq!(encode_unit_2.values[0], 0);
    }

    #[test]
    fn test_initialize_encoder_from_parameter_case1() {
        let encoder = Encoder::init(2, 3, 4, 5);
        assert_eq!(encoder.edge_label_bit_num, 2);
        assert_eq!(encoder.vertex_label_bit_num, 3);
        assert_eq!(encoder.direction_bit_num, 4);
        assert_eq!(encoder.vertex_index_bit_num, 5);
    }

    #[test]
    fn test_initialize_encoder_from_parameter_case2() {
        let encoder = Encoder::init(2, 2, 2, 2);
        assert_eq!(encoder.edge_label_bit_num, 2);
        assert_eq!(encoder.vertex_label_bit_num, 2);
        assert_eq!(encoder.direction_bit_num, 2);
        assert_eq!(encoder.vertex_index_bit_num, 2);
    }

    #[test]
    fn test_initialize_encoder_from_pattern_case6() {
        let pattern = build_pattern_case6();
        let default_vertex_index_bit_num = 0;
        let encoder = Encoder::init_by_pattern(&pattern, default_vertex_index_bit_num);
        assert_eq!(encoder.edge_label_bit_num, 2);
        assert_eq!(encoder.vertex_label_bit_num, 2);
        assert_eq!(encoder.direction_bit_num, 2);
        assert_eq!(encoder.vertex_index_bit_num, 1);
    }

    #[test]
    fn test_initialize_encoder_from_pattern_case7() {
        let pattern = build_pattern_case7();
        let default_vertex_index_bit_num = 2;
        let encoder = Encoder::init_by_pattern(&pattern, default_vertex_index_bit_num);
        assert_eq!(encoder.edge_label_bit_num, 3);
        assert_eq!(encoder.vertex_label_bit_num, 3);
        assert_eq!(encoder.direction_bit_num, 2);
        assert_eq!(encoder.vertex_index_bit_num, 2);
    }

    #[test]
    fn encode_unit_to_ascii_string() {
        let pattern = build_pattern_case6();
        let edge1 = pattern.get_edge_from_id(0).unwrap();
        let edge2 = pattern.get_edge_from_id(1).unwrap();
        let encoder = Encoder::init(2, 2, 2, 2);
        let encode_unit_1 = EncodeUnit::from_pattern_edge(&pattern, edge1, &encoder);
        let encode_string_1 = encode_unit_1.to_ascii_string();
        let expected_encode_string_1: AsciiString = generate_asciistring_from_vec(&vec![10, 96]);
        assert_eq!(encode_string_1.len(), 2);
        assert_eq!(encode_string_1, expected_encode_string_1);
        let encode_unit_2 = EncodeUnit::from_pattern_edge(&pattern, edge2, &encoder);
        let encode_string_2 = encode_unit_2.to_ascii_string();
        let expected_encode_string_2: AsciiString = generate_asciistring_from_vec(&vec![12, 112]);
        assert_eq!(encode_string_2.len(), 2);
        assert_eq!(encode_string_2, expected_encode_string_2);
    }

    #[test]
    fn encode_unit_to_vec_u8() {
        let pattern = build_pattern_case6();
        let edge1 = pattern.get_edge_from_id(0).unwrap();
        let edge2 = pattern.get_edge_from_id(1).unwrap();
        let encoder = Encoder::init(2, 2, 2, 2);
        let encode_unit_1 = EncodeUnit::from_pattern_edge(&pattern, edge1, &encoder);
        let encode_vec_1 = encode_unit_1.to_vec_u8(8);
        let expected_encode_vec_1: Vec<u8> = vec![5, 96];
        assert_eq!(encode_vec_1.len(), 2);
        assert_eq!(encode_vec_1, expected_encode_vec_1);
        let encode_unit_2 = EncodeUnit::from_pattern_edge(&pattern, edge2, &encoder);
        let encode_vec_2 = encode_unit_2.to_vec_u8(8);
        let expected_encode_vec_2: Vec<u8> = vec![6, 112];
        assert_eq!(encode_vec_2.len(), 2);
        assert_eq!(encode_vec_2, expected_encode_vec_2);
    }

    #[test]
    fn encode_pattern_to_asciistring_case_6() {
        let pattern = build_pattern_case6();
        let pattern_edge1 = PatternEdge::new(0, 1, 0, 1, 1, 2);
        let pattern_edge2 = PatternEdge::new(1, 2, 0, 2, 1, 3);
        let encoder = Encoder::init(2, 2, 2, 2);
        let encode_value = <Pattern as Cipher<AsciiString>>::encode_to(&pattern, &encoder);
        let mut connect_encode_unit = EncodeUnit::from_pattern_edge(&pattern, &pattern_edge1, &encoder);
        connect_encode_unit.extend_by_another_unit(&EncodeUnit::from_pattern_edge(
            &pattern,
            &pattern_edge2,
            &encoder,
        ));
        let expected_encode_value = connect_encode_unit.to_ascii_string();
        assert_eq!(encode_value, expected_encode_value);
    }

    #[test]
    fn encode_pattern_to_vec_u8_case_6() {
        let pattern = build_pattern_case6();
        let pattern_edge1 = PatternEdge::new(0, 1, 0, 1, 1, 2);
        let pattern_edge2 = PatternEdge::new(1, 2, 0, 2, 1, 3);
        let encoder = Encoder::init(2, 2, 2, 2);
        let encode_value = <Pattern as Cipher<Vec<u8>>>::encode_to(&pattern, &encoder);
        let mut connect_encode_unit = EncodeUnit::from_pattern_edge(&pattern, &pattern_edge1, &encoder);
        connect_encode_unit.extend_by_another_unit(&EncodeUnit::from_pattern_edge(
            &pattern,
            &pattern_edge2,
            &encoder,
        ));
        let expected_encode_value = connect_encode_unit.to_vec_u8(8);
        assert_eq!(encode_value, expected_encode_value);
    }

    #[test]
    fn test_get_decode_value_by_head_tail_vec8() {
        let src_code: Vec<u8> = vec![95, 115, 87];
        // inside one unit
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 0, 0, 8);
        assert_eq!(picked_value, 1);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 15, 15, 8);
        assert_eq!(picked_value, 0);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 1, 0, 8);
        assert_eq!(picked_value, 3);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 2, 1, 8);
        assert_eq!(picked_value, 3);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 7, 0, 8);
        assert_eq!(picked_value, 87);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 15, 8, 8);
        assert_eq!(picked_value, 115);
        // neighboring units
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 8, 7, 8);
        assert_eq!(picked_value, 2);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 9, 6, 8);
        assert_eq!(picked_value, 13);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 8, 4, 8);
        assert_eq!(picked_value, 21);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 13, 4, 8);
        assert_eq!(picked_value, 821);
        // crossing one unit
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 16, 7, 8);
        assert_eq!(picked_value, 742);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 16, 6, 8);
        assert_eq!(picked_value, 1485);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 18, 2, 8);
        assert_eq!(picked_value, 122069);
    }

    #[test]
    fn test_get_decode_value_by_head_tail_asciistring() {
        let src_code: Vec<u8> = vec![95, 115, 87];
        // inside one unit
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 0, 0, 7);
        assert_eq!(picked_value, 1);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 13, 13, 7);
        assert_eq!(picked_value, 1);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 1, 0, 7);
        assert_eq!(picked_value, 3);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 2, 1, 7);
        assert_eq!(picked_value, 3);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 6, 0, 7);
        assert_eq!(picked_value, 87);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 13, 7, 7);
        assert_eq!(picked_value, 115);
        // neighboring units
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 7, 6, 7);
        assert_eq!(picked_value, 3);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 9, 6, 7);
        assert_eq!(picked_value, 7);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 8, 4, 7);
        assert_eq!(picked_value, 29);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 13, 4, 7);
        assert_eq!(picked_value, 925);
        // crossing one unit
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 14, 6, 7);
        assert_eq!(picked_value, 487);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 16, 6, 7);
        assert_eq!(picked_value, 2023);
        let picked_value = Encoder::get_decode_value_by_head_tail(&src_code, 18, 2, 7);
        assert_eq!(picked_value, 130677);
    }

    #[test]
    fn test_decode_from_encode_unit_to_vec_u8() {
        let pattern = build_pattern_case6();
        let edge1 = pattern.get_edge_from_id(0).unwrap();
        let edge2 = pattern.get_edge_from_id(1).unwrap();
        let encoder = Encoder::init(2, 2, 2, 2);
        let encode_unit_1 = EncodeUnit::from_pattern_edge(&pattern, edge1, &encoder);
        let encode_vec_1 = encode_unit_1.to_vec_u8(8);
        let encode_unit_2 = EncodeUnit::from_pattern_edge(&pattern, edge2, &encoder);
        let encode_vec_2 = encode_unit_2.to_vec_u8(8);
        assert_eq!(Encoder::get_decode_value_by_head_tail(&encode_vec_1, 9, 8, 8), edge1.get_label());
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_1, 7, 6, 8),
            edge1.get_start_vertex_label()
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_1, 5, 4, 8),
            edge1.get_end_vertex_label()
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_1, 3, 2, 8),
            pattern.get_vertex_index(edge1.get_start_vertex_id())
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_1, 1, 0, 8),
            pattern.get_vertex_index(edge1.get_end_vertex_id())
        );
        assert_eq!(Encoder::get_decode_value_by_head_tail(&encode_vec_2, 9, 8, 8), edge2.get_label());
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_2, 7, 6, 8),
            edge2.get_start_vertex_label()
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_2, 5, 4, 8),
            edge2.get_end_vertex_label()
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_2, 3, 2, 8),
            pattern.get_vertex_index(edge2.get_start_vertex_id())
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_2, 1, 0, 8),
            pattern.get_vertex_index(edge2.get_end_vertex_id())
        );
    }

    #[test]
    fn test_decode_from_encode_unit_to_asciistring() {
        let pattern = build_pattern_case6();
        let edge1 = pattern.get_edge_from_id(0).unwrap();
        let edge2 = pattern.get_edge_from_id(1).unwrap();
        let encoder = Encoder::init(2, 2, 2, 2);
        let encode_unit_1 = EncodeUnit::from_pattern_edge(&pattern, edge1, &encoder);
        let encode_string_1 = encode_unit_1.to_ascii_string();
        let encode_unit_2 = EncodeUnit::from_pattern_edge(&pattern, edge2, &encoder);
        let encode_string_2 = encode_unit_2.to_ascii_string();
        let encode_vec_1: Vec<u8> = encode_string_1
            .into_iter()
            .map(|ch| ch.as_byte())
            .collect();
        let encode_vec_2: Vec<u8> = encode_string_2
            .into_iter()
            .map(|ch| ch.as_byte())
            .collect();
        assert_eq!(Encoder::get_decode_value_by_head_tail(&encode_vec_1, 9, 8, 7), edge1.get_label());
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_1, 7, 6, 7),
            edge1.get_start_vertex_label()
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_1, 5, 4, 7),
            edge1.get_end_vertex_label()
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_1, 3, 2, 7),
            pattern.get_vertex_index(edge1.get_start_vertex_id())
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_1, 1, 0, 7),
            pattern.get_vertex_index(edge1.get_end_vertex_id())
        );
        assert_eq!(Encoder::get_decode_value_by_head_tail(&encode_vec_2, 9, 8, 7), edge2.get_label());
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_2, 7, 6, 7),
            edge2.get_start_vertex_label()
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_2, 5, 4, 7),
            edge2.get_end_vertex_label()
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_2, 3, 2, 7),
            pattern.get_vertex_index(edge2.get_start_vertex_id())
        );
        assert_eq!(
            Encoder::get_decode_value_by_head_tail(&encode_vec_2, 1, 0, 7),
            pattern.get_vertex_index(edge2.get_end_vertex_id())
        );
    }

    #[test]
    fn test_encode_decode_pattern_case1_vec_u8() {
        let pattern = build_pattern_case1();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case1_ascii_string() {
        let pattern = build_pattern_case1();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: AsciiString = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case2_vec_u8() {
        let pattern = build_pattern_case2();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case2_ascii_string() {
        let pattern = build_pattern_case2();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: AsciiString = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case3_vec_u8() {
        let pattern = build_pattern_case3();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case3_ascii_string() {
        let pattern = build_pattern_case3();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: AsciiString = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case4_vec_u8() {
        let pattern = build_pattern_case4();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case4_ascii_string() {
        let pattern = build_pattern_case4();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: AsciiString = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case5_vec_u8() {
        let pattern = build_pattern_case5();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case5_ascii_string() {
        let pattern = build_pattern_case5();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: AsciiString = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case6_vec_u8() {
        let pattern = build_pattern_case6();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case6_ascii_string() {
        let pattern = build_pattern_case6();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: AsciiString = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case7_vec_u8() {
        let pattern = build_pattern_case7();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: Vec<u8> = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_pattern_case7_ascii_string() {
        let pattern = build_pattern_case7();
        let encoder = Encoder::init_by_pattern(&pattern, 2);
        let pattern_code: AsciiString = pattern.encode_to(&encoder);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case1_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case1();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case1();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case1_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case1();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case1();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case2_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case2();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case2();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case2_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case2();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case2();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case3_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case3();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case3();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case3_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case3();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case3();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case4_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case4();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case4();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case4_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case4();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case4();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case5_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case5();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case5();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case5_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case5();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case5();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case6_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case6();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case6();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case6_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case6();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case6();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case7_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case7();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case7();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case7_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case7();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case7();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case8_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case8();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case8();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case8_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case8();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case8();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case9_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case9();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case9();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case9_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case9();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case9();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case10_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case10();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case10();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case10_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case10();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case10();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case11_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case11();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case11();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case11_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case11();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case11();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case12_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case12();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case12();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case12_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case12();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case12();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case13_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case13();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case13();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case13_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case13();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case13();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case14_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case14();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case14();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case14_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case14();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case14();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case15_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case15();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case15();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case15_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case15();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case15();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case16_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case16();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case16();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case16_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case16();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case16();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case17_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case17();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case17();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case17_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case17();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case17();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case18_vec_u8() {
        let (mut pattern, _) = build_pattern_index_ranking_case18();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: Vec<u8> = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case18();
        pattern.index_ranking();
        let pattern_code2: Vec<u8> = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: Vec<u8> = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_index_ranking_case18_ascii_string() {
        let (mut pattern, _) = build_pattern_index_ranking_case18();
        pattern.index_ranking();
        let encoder = Encoder::init_by_pattern(&pattern, 4);
        let pattern_code1: AsciiString = pattern.encode_to(&encoder);
        let (mut pattern, _) = build_pattern_index_ranking_case18();
        pattern.index_ranking();
        let pattern_code2: AsciiString = pattern.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code2);
        let pattern_from_decode: Pattern = Cipher::decode_from(pattern_code1.clone(), &encoder);
        let pattern_code_from_decode: AsciiString = pattern_from_decode.encode_to(&encoder);
        assert_eq!(pattern_code1, pattern_code_from_decode);
    }

    #[test]
    fn test_encode_decode_extend_step_case2_vec_u8() {
        let extend_step_1 = build_extend_step_case2();
        let encoder = Encoder::init(2, 2, 2, 2);
        let extend_step_1_code: Vec<u8> = extend_step_1.encode_to(&encoder);
        let extend_step_1_from_decode: ExtendStep = Cipher::decode_from(extend_step_1_code, &encoder);
        assert_eq!(extend_step_1.get_target_v_label(), extend_step_1_from_decode.get_target_v_label());
        assert_eq!(extend_step_1.get_extend_edges_num(), extend_step_1_from_decode.get_extend_edges_num());
        assert_eq!(
            extend_step_1
                .get_extend_edges_by_start_v(1, 0)
                .unwrap(),
            extend_step_1_from_decode
                .get_extend_edges_by_start_v(1, 0)
                .unwrap()
        );
        assert_eq!(
            extend_step_1
                .get_extend_edges_by_start_v(1, 1)
                .unwrap(),
            extend_step_1_from_decode
                .get_extend_edges_by_start_v(1, 1)
                .unwrap()
        );
        assert_eq!(
            extend_step_1
                .get_extend_edges_by_start_v(2, 0)
                .unwrap(),
            extend_step_1_from_decode
                .get_extend_edges_by_start_v(2, 0)
                .unwrap()
        );
    }

    #[test]
    fn test_encode_decode_extend_step_case2_ascii_string() {
        let extend_step_1 = build_extend_step_case2();
        let encoder = Encoder::init(2, 2, 2, 2);
        let extend_step_1_code: AsciiString = extend_step_1.encode_to(&encoder);
        let extend_step_1_from_decode: ExtendStep = Cipher::decode_from(extend_step_1_code, &encoder);
        assert_eq!(extend_step_1.get_target_v_label(), extend_step_1_from_decode.get_target_v_label());
        assert_eq!(extend_step_1.get_extend_edges_num(), extend_step_1_from_decode.get_extend_edges_num());
        assert_eq!(
            extend_step_1
                .get_extend_edges_by_start_v(1, 0)
                .unwrap(),
            extend_step_1_from_decode
                .get_extend_edges_by_start_v(1, 0)
                .unwrap()
        );
        assert_eq!(
            extend_step_1
                .get_extend_edges_by_start_v(1, 1)
                .unwrap(),
            extend_step_1_from_decode
                .get_extend_edges_by_start_v(1, 1)
                .unwrap()
        );
        assert_eq!(
            extend_step_1
                .get_extend_edges_by_start_v(2, 0)
                .unwrap(),
            extend_step_1_from_decode
                .get_extend_edges_by_start_v(2, 0)
                .unwrap()
        );
    }
}
