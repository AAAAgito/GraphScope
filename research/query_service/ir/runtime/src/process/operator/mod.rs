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

pub mod filter;
pub mod flatmap;
pub mod join;
pub mod keyed;
pub mod map;
pub mod shuffle;
pub mod sink;
pub mod sort;
pub mod source;

use crate::error::FnExecError;
use crate::graph::element::Element;
use crate::graph::property::{Details, PropKey};
use crate::process::record::{Entry, ObjectElement, Record};
use ir_common::error::ParsePbError;
use ir_common::generated::common as common_pb;
use ir_common::NameOrId;
use pegasus::codec::{Decode, Encode, ReadExt, WriteExt};
use std::convert::TryFrom;
use std::sync::Arc;

#[derive(Clone, Debug, Default)]
pub struct TagKey {
    tag: Option<NameOrId>,
    key: Option<PropKey>,
}

impl TagKey {
    /// This is for key generation, which generate the key of the input Record according to the tag_key field
    pub fn get_entry(&self, input: &Record) -> Result<Arc<Entry>, FnExecError> {
        let entry = input
            .get(self.tag.as_ref())
            .ok_or(FnExecError::get_tag_error("Get tag failed since it refers to an empty entry"))?
            .clone();
        if let Some(key) = self.key.as_ref() {
            if let Some(element) = entry.as_graph_element() {
                let details = element.details().ok_or(FnExecError::get_tag_error(
                    "Get key failed since get details from a graph element failed",
                ))?;
                let properties = details
                    .get(key)
                    .ok_or(FnExecError::get_tag_error(
                        "Get key failed since get prop_key from a graph element failed",
                    ))?
                    .try_to_owned()
                    .ok_or(FnExecError::UnExpectedData("unable to own the `BorrowObject`".to_string()))?;
                Ok(Arc::new(ObjectElement::Prop(properties).into()))
            } else {
                Err(FnExecError::get_tag_error(
                    "Get key failed when attempt to get prop_key from a non-graph element",
                ))
            }
        } else {
            Ok(entry)
        }
    }
}

impl TryFrom<common_pb::Variable> for TagKey {
    type Error = ParsePbError;

    fn try_from(v: common_pb::Variable) -> Result<Self, Self::Error> {
        let tag = if let Some(tag) = v.tag { Some(NameOrId::try_from(tag)?) } else { None };
        let prop = if let Some(prop) = v.property { Some(PropKey::try_from(prop)?) } else { None };
        Ok(TagKey { tag, key: prop })
    }
}

impl Encode for TagKey {
    fn write_to<W: WriteExt>(&self, writer: &mut W) -> std::io::Result<()> {
        match (&self.tag, &self.key) {
            (Some(tag), Some(key)) => {
                writer.write_u8(0)?;
                tag.write_to(writer)?;
                key.write_to(writer)?;
            }
            (Some(tag), None) => {
                writer.write_u8(1)?;
                tag.write_to(writer)?;
            }
            (None, Some(key)) => {
                writer.write_u8(2)?;
                key.write_to(writer)?;
            }
            (None, None) => {
                writer.write_u8(3)?;
            }
        }
        Ok(())
    }
}

impl Decode for TagKey {
    fn read_from<R: ReadExt>(reader: &mut R) -> std::io::Result<Self> {
        let opt = reader.read_u8()?;
        match opt {
            0 => {
                let tag = <NameOrId>::read_from(reader)?;
                let key = <PropKey>::read_from(reader)?;
                Ok(TagKey { tag: Some(tag), key: Some(key) })
            }
            1 => {
                let tag = <NameOrId>::read_from(reader)?;
                Ok(TagKey { tag: Some(tag), key: None })
            }
            2 => {
                let key = <PropKey>::read_from(reader)?;
                Ok(TagKey { tag: None, key: Some(key) })
            }
            3 => Ok(TagKey { tag: None, key: None }),
            _ => Err(std::io::Error::new(std::io::ErrorKind::Other, "unreachable")),
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::HashMap;

    use dyn_type::Object;

    use super::*;
    use crate::graph::element::{GraphElement, Vertex};
    use crate::graph::property::{DefaultDetails, DynDetails};
    use crate::process::record::RecordElement;
    use ir_common::KeyId;

    fn init_vertex1() -> Vertex {
        let map1: HashMap<NameOrId, Object> =
            vec![("id".into(), object!(1)), ("age".into(), object!(29)), ("name".into(), object!("marko"))]
                .into_iter()
                .collect();
        Vertex::new(DynDetails::new(DefaultDetails::with_property(1, "person".into(), map1)))
    }

    fn init_vertex2() -> Vertex {
        let map2: HashMap<NameOrId, Object> =
            vec![("id".into(), object!(2)), ("age".into(), object!(27)), ("name".into(), object!("vadas"))]
                .into_iter()
                .collect();
        Vertex::new(DynDetails::new(DefaultDetails::with_property(2, "person".into(), map2)))
    }

    fn init_record() -> Record {
        let vertex1 = init_vertex1();
        let vertex2 = init_vertex2();
        let object3 = ObjectElement::Count(10);

        let mut record = Record::new(vertex1, None);
        record.append(vertex2, Some((0 as KeyId).into()));
        record.append(object3, Some((1 as KeyId).into()));
        record
    }

    pub fn init_source() -> Vec<Record> {
        let v1 = init_vertex1();
        let v2 = init_vertex2();
        let r1 = Record::new(v1, None);
        let r2 = Record::new(v2, None);
        vec![r1, r2]
    }

    pub fn init_source_with_tag() -> Vec<Record> {
        let v1 = init_vertex1();
        let v2 = init_vertex2();
        let r1 = Record::new(v1, Some("a".into()));
        let r2 = Record::new(v2, Some("a".into()));
        vec![r1, r2]
    }

    #[test]
    fn test_get_none_tag_entry() {
        let tag_key = TagKey { tag: None, key: None };
        let expected = init_vertex1();
        let record = init_record();
        let entry = tag_key.get_entry(&record).unwrap();
        if let Some(element) = entry.as_graph_element() {
            assert_eq!(element.id(), expected.id());
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_get_tag_entry() {
        let tag_key = TagKey { tag: Some((0 as KeyId).into()), key: None };
        let expected = init_vertex2();
        let record = init_record();
        let entry = tag_key.get_entry(&record).unwrap();
        if let Some(element) = entry.as_graph_element() {
            assert_eq!(element.id(), expected.id());
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_get_tag_key_entry() {
        let tag_key = TagKey { tag: Some((0 as KeyId).into()), key: Some(PropKey::Key("age".into())) };
        let expected = 27;
        let record = init_record();
        let entry = tag_key.get_entry(&record).unwrap();
        match entry.as_ref() {
            Entry::Element(RecordElement::OffGraph(ObjectElement::Prop(obj))) => {
                assert_eq!(obj.clone(), object!(expected));
            }
            _ => {
                assert!(false);
            }
        }
    }
}
