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
//!
//!

mod common;

#[cfg(test)]
mod test {
    use std::sync::Arc;

    use graph_proxy::{create_demo_graph, SimplePartition};
    use ir_common::generated::algebra as pb;
    use ir_common::generated::common as common_pb;
    use ir_common::NameOrId;
    use pegasus::api::{Map, Sink};
    use pegasus::JobConf;
    use runtime::expr::str_to_expr_pb;
    use runtime::graph::element::{Element, GraphElement};
    use runtime::graph::property::Details;
    use runtime::process::operator::flatmap::FlatMapFuncGen;
    use runtime::process::operator::map::FilterMapFuncGen;
    use runtime::process::operator::source::SourceOperator;
    use runtime::process::record::Record;

    // g.V()
    fn source_gen(alias: Option<common_pb::NameOrId>) -> Box<dyn Iterator<Item = Record> + Send> {
        create_demo_graph();
        let scan_opr_pb = pb::Scan { scan_opt: 0, alias, params: None, idx_predicate: None };
        let mut source_opr_pb =
            pb::logical_plan::Operator { opr: Some(pb::logical_plan::operator::Opr::Scan(scan_opr_pb)) };
        let source =
            SourceOperator::new(&mut source_opr_pb, 1, 1, Arc::new(SimplePartition { num_servers: 1 }))
                .unwrap();
        source.gen_source(0).unwrap()
    }

    // g.V().out('knows').as('a')
    #[test]
    fn auxilia_simple_alias_test() {
        let expand_opr = pb::EdgeExpand {
            base: Some(pb::ExpandBase {
                v_tag: None,
                direction: 0,
                params: Some(pb::QueryParams {
                    table_names: vec![common_pb::NameOrId::from("knows".to_string())],
                    columns: vec![],
                    limit: None,
                    predicate: None,
                    requirements: vec![],
                }),
            }),
            is_edge: false,
            alias: None,
        };

        let auxilia_opr = pb::Auxilia {
            tag: None,
            params: Some(pb::QueryParams {
                table_names: vec![],
                columns: vec![],
                limit: None,
                predicate: None,
                requirements: vec![],
            }),
            alias: Some("a".to_string().into()),
        };

        let conf = JobConf::new("auxilia_simple_alias_test");
        let mut result = pegasus::run(conf, || {
            let expand = expand_opr.clone();
            let auxilia = auxilia_opr.clone();
            |input, output| {
                let mut stream = input.input_from(source_gen(None))?;
                let flatmap_func = expand.gen_flat_map().unwrap();
                stream = stream.flat_map(move |input| flatmap_func.exec(input))?;
                let filter_map_func = auxilia.gen_filter_map().unwrap();
                stream = stream.filter_map(move |input| filter_map_func.exec(input))?;
                stream.sink_into(output)
            }
        })
        .expect("build job failure");

        let expected_ids = vec![2, 4];
        let mut result_ids = vec![];
        while let Some(Ok(record)) = result.next() {
            if let Some(element) = record
                .get(Some(&"a".to_string().into()))
                .unwrap()
                .as_graph_element()
            {
                result_ids.push(element.id());
            }
        }
        result_ids.sort();
        assert_eq!(result_ids, expected_ids)
    }

    // g.V().out('knows').values('name')  // must obtain the name property
    #[test]
    fn auxilia_get_property_test() {
        let expand_opr = pb::EdgeExpand {
            base: Some(pb::ExpandBase {
                v_tag: None,
                direction: 0,
                params: Some(pb::QueryParams {
                    table_names: vec![common_pb::NameOrId::from("knows".to_string())],
                    columns: vec![],
                    limit: None,
                    predicate: None,
                    requirements: vec![],
                }),
            }),
            is_edge: false,
            alias: None,
        };

        let auxilia_opr = pb::Auxilia {
            tag: None,
            params: Some(pb::QueryParams {
                table_names: vec![],
                columns: vec![common_pb::NameOrId::from("name".to_string())],
                limit: None,
                predicate: None,
                requirements: vec![],
            }),
            alias: None,
        };

        let conf = JobConf::new("auxilia_get_property_test");
        let mut result = pegasus::run(conf, || {
            let expand = expand_opr.clone();
            let auxilia = auxilia_opr.clone();
            |input, output| {
                let mut stream = input.input_from(source_gen(None))?;
                let flatmap_func = expand.gen_flat_map().unwrap();
                stream = stream.flat_map(move |input| flatmap_func.exec(input))?;
                let filter_map_func = auxilia.gen_filter_map().unwrap();
                stream = stream.filter_map(move |input| filter_map_func.exec(input))?;
                stream.sink_into(output)
            }
        })
        .expect("build job failure");

        let expected_ids_with_prop = vec![(2, "vadas".to_string().into()), (4, "josh".to_string().into())];
        let mut result_ids_with_prop = vec![];
        while let Some(Ok(record)) = result.next() {
            if let Some(element) = record.get(None).unwrap().as_graph_element() {
                result_ids_with_prop.push((
                    element.id(),
                    element
                        .details()
                        .unwrap()
                        .get_property(&NameOrId::Str("name".to_string()))
                        .unwrap()
                        .try_to_owned()
                        .unwrap(),
                ));
            }
        }
        result_ids_with_prop.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        assert_eq!(result_ids_with_prop, expected_ids_with_prop)
    }

    // g.V().out('knows').has('name', "vadas")
    #[test]
    fn auxilia_filter_test() {
        let expand_opr = pb::EdgeExpand {
            base: Some(pb::ExpandBase {
                v_tag: None,
                direction: 0,
                params: Some(pb::QueryParams {
                    table_names: vec![common_pb::NameOrId::from("knows".to_string())],
                    columns: vec![],
                    limit: None,
                    predicate: None,
                    requirements: vec![],
                }),
            }),
            is_edge: false,
            alias: None,
        };

        let auxilia_opr = pb::Auxilia {
            tag: None,
            params: Some(pb::QueryParams {
                table_names: vec![],
                columns: vec![common_pb::NameOrId::from("name".to_string())],
                limit: None,
                predicate: str_to_expr_pb("@.name==\"vadas\"".to_string()).ok(),
                requirements: vec![],
            }),
            alias: None,
        };

        let conf = JobConf::new("auxilia_filter_test");
        let mut result = pegasus::run(conf, || {
            let expand = expand_opr.clone();
            let auxilia = auxilia_opr.clone();
            |input, output| {
                let mut stream = input.input_from(source_gen(None))?;
                let flatmap_func = expand.gen_flat_map().unwrap();
                stream = stream.flat_map(move |input| flatmap_func.exec(input))?;
                let filter_map_func = auxilia.gen_filter_map().unwrap();
                stream = stream.filter_map(move |input| filter_map_func.exec(input))?;
                stream.sink_into(output)
            }
        })
        .expect("build job failure");

        let expected_ids_with_prop = vec![(2, "vadas".to_string().into())];
        let mut result_ids_with_prop = vec![];
        while let Some(Ok(record)) = result.next() {
            if let Some(element) = record.get(None).unwrap().as_graph_element() {
                result_ids_with_prop.push((
                    element.id(),
                    element
                        .details()
                        .unwrap()
                        .get_property(&NameOrId::Str("name".to_string()))
                        .unwrap()
                        .try_to_owned()
                        .unwrap(),
                ));
            }
        }
        result_ids_with_prop.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        assert_eq!(result_ids_with_prop, expected_ids_with_prop)
    }

    // g.V().out('knows').has("name", "vadas").as('a')
    #[test]
    fn auxilia_alias_test() {
        let expand_opr = pb::EdgeExpand {
            base: Some(pb::ExpandBase {
                v_tag: None,
                direction: 0,
                params: Some(pb::QueryParams {
                    table_names: vec![common_pb::NameOrId::from("knows".to_string())],
                    columns: vec![],
                    limit: None,
                    predicate: None,
                    requirements: vec![],
                }),
            }),
            is_edge: false,
            alias: None,
        };

        let auxilia_opr = pb::Auxilia {
            tag: None,
            params: Some(pb::QueryParams {
                table_names: vec![],
                columns: vec![common_pb::NameOrId::from("name".to_string())],
                limit: None,
                predicate: str_to_expr_pb("@.name==\"vadas\"".to_string()).ok(),
                requirements: vec![],
            }),
            alias: Some(common_pb::NameOrId::from("a".to_string())),
        };

        let conf = JobConf::new("auxilia_alias_test");
        let mut result = pegasus::run(conf, || {
            let expand = expand_opr.clone();
            let auxilia = auxilia_opr.clone();
            |input, output| {
                let mut stream = input.input_from(source_gen(None))?;
                let flatmap_func = expand.gen_flat_map().unwrap();
                stream = stream.flat_map(move |input| flatmap_func.exec(input))?;
                let filter_map_func = auxilia.gen_filter_map().unwrap();
                stream = stream.filter_map(move |input| filter_map_func.exec(input))?;
                stream.sink_into(output)
            }
        })
        .expect("build job failure");

        let expected_ids = vec![2];
        let mut result_ids = vec![];
        while let Some(Ok(record)) = result.next() {
            if let Some(element) = record
                .get(Some(&NameOrId::Str("a".to_string())))
                .unwrap()
                .as_graph_element()
            {
                result_ids.push(element.id());
            }
        }
        result_ids.sort();
        assert_eq!(result_ids, expected_ids)
    }
}
