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

use crate::error::{FnExecError, FnGenResult};
use crate::expr::eval::Evaluator;
use crate::process::operator::filter::FilterFuncGen;
use crate::process::record::Record;
use ir_common::error::ParsePbError;
use ir_common::generated::algebra as algebra_pb;
use pegasus::api::function::{FilterFunction, FnResult};
use std::convert::TryInto;

#[derive(Debug)]
struct SelectOperator {
    pub filter: Evaluator,
}

impl FilterFunction<Record> for SelectOperator {
    fn test(&self, input: &Record) -> FnResult<bool> {
        let res = self
            .filter
            .eval_bool(Some(input))
            .map_err(|e| FnExecError::from(e))?;
        Ok(res)
    }
}

impl FilterFuncGen for algebra_pb::Select {
    fn gen_filter(self) -> FnGenResult<Box<dyn FilterFunction<Record>>> {
        if let Some(predicate) = self.predicate {
            let select_operator = SelectOperator { filter: predicate.try_into()? };
            debug!("Runtime select operator: {:?}", select_operator);
            Ok(Box::new(select_operator))
        } else {
            Err(ParsePbError::EmptyFieldError("empty select pb".to_string()).into())
        }
    }
}

#[cfg(test)]
mod tests {
    use ir_common::generated::algebra as pb;
    use ir_common::NameOrId;
    use pegasus::api::{Filter, Sink};
    use pegasus::result::ResultStream;
    use pegasus::JobConf;

    use crate::expr::str_to_expr_pb;
    use crate::graph::element::{Element, GraphElement};
    use crate::graph::property::Details;
    use crate::process::operator::filter::FilterFuncGen;
    use crate::process::operator::tests::init_source;
    use crate::process::record::Record;

    fn select_test(source: Vec<Record>, select_opr_pb: pb::Select) -> ResultStream<Record> {
        let conf = JobConf::new("select_test");
        let result = pegasus::run(conf, || {
            let source = source.clone();
            let select_opr_pb = select_opr_pb.clone();
            |input, output| {
                let mut stream = input.input_from(source)?;
                let select_func = select_opr_pb.gen_filter().unwrap();
                stream = stream.filter(move |i| select_func.test(i))?;
                stream.sink_into(output)
            }
        })
        .expect("build job failure");

        result
    }

    // g.V().has("id",gt(1))
    #[test]
    fn select_test_01() {
        let select_opr_pb = pb::Select { predicate: Some(str_to_expr_pb("@.id > 1".to_string()).unwrap()) };
        let mut result = select_test(init_source(), select_opr_pb);
        let mut count = 0;
        while let Some(Ok(record)) = result.next() {
            if let Some(element) = record.get(None).unwrap().as_graph_element() {
                assert!(element.id() > 1)
            }
            count += 1;
        }

        assert_eq!(count, 1);
    }

    // g.V().has("name","marko")
    #[test]
    fn select_test_02() {
        let select_opr_pb =
            pb::Select { predicate: Some(str_to_expr_pb("@.name == \"marko\"".to_string()).unwrap()) };
        let mut result = select_test(init_source(), select_opr_pb);
        let mut count = 0;
        while let Some(Ok(record)) = result.next() {
            if let Some(element) = record.get(None).unwrap().as_graph_element() {
                {
                    assert_eq!(
                        element
                            .details()
                            .unwrap()
                            .get_property(&NameOrId::Str("name".to_string()))
                            .unwrap()
                            .try_to_owned()
                            .unwrap(),
                        object!("marko")
                    );
                }
                count += 1;
            }
            assert_eq!(count, 1);
        }
    }
}