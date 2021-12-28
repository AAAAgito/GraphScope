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

use std::cell::RefCell;
use std::convert::{TryFrom, TryInto};

use dyn_type::arith::Exp;
use dyn_type::{BorrowObject, Object};
use ir_common::error::{ParsePbError, ParsePbResult};
use ir_common::generated::common as pb;
use ir_common::NameOrId;

use crate::expr::{ExprEvalError, ExprEvalResult};
use crate::graph::element::Element;
use crate::graph::property::{Details, PropKey};
use std::collections::BTreeMap;

/// The trait to define evaluating an expression
pub trait Evaluate {
    fn eval<E: Element, C: Context<E>>(&self, context: Option<&C>) -> ExprEvalResult<Object>;
}

#[derive(Debug)]
pub struct Evaluator {
    /// A suffix-tree-based expression for evaluating
    suffix_tree: Vec<InnerOpr>,
    /// A stack for evaluating the suffix-tree-based expression
    /// Wrap it in a `RefCell` to avoid conflict mutable reference
    stack: RefCell<Vec<Object>>,
}

unsafe impl Sync for Evaluator {}

/// An inner representation of `pb::ExprOpr` for one-shot translation of `pb::ExprOpr`.
#[derive(Debug, Clone)]
pub(crate) enum InnerOpr {
    Logical(pb::Logical),
    Arith(pb::Arithmetic),
    Const(Option<Object>),
    Var { tag: Option<NameOrId>, prop_key: Option<PropKey> },
    Vars(Vec<InnerOpr>),
    VarMap(Vec<InnerOpr>),
}

impl ToString for InnerOpr {
    fn to_string(&self) -> String {
        match self {
            InnerOpr::Logical(logical) => format!("{:?}", logical),
            InnerOpr::Arith(arith) => format!("{:?}", arith),
            InnerOpr::Const(c) => format!("{:?}", c),
            InnerOpr::Var { tag, prop_key } => {
                if let Some(p) = prop_key {
                    format!("{:?}.{:?})", tag, p)
                } else {
                    format!("{:?})", tag)
                }
            }
            InnerOpr::Vars(vars) => format!("Vars ({:?})", vars),
            InnerOpr::VarMap(vars) => format!("Vars' map ({:?})", vars),
        }
    }
}

/// A string representation of `InnerOpr`
#[derive(Debug, Clone, PartialEq)]
pub struct OperatorDesc(String);

impl From<InnerOpr> for OperatorDesc {
    fn from(inner: InnerOpr) -> Self {
        Self::from(&inner)
    }
}

impl From<&InnerOpr> for OperatorDesc {
    fn from(inner: &InnerOpr) -> Self {
        Self(inner.to_string())
    }
}

/// A `Context` gives the behavior of obtaining a certain tag from the runtime
/// for evaluating variables in an expression.
pub trait Context<E: Element> {
    fn get(&self, _tag: Option<&NameOrId>) -> Option<&E> {
        None
    }
}

pub struct NoneContext {}

impl Context<()> for NoneContext {}

impl TryFrom<pb::Expression> for Evaluator {
    type Error = ParsePbError;

    fn try_from(suffix_tree: pb::Expression) -> ParsePbResult<Self>
    where
        Self: Sized,
    {
        let mut inner_tree: Vec<InnerOpr> = Vec::with_capacity(suffix_tree.operators.len());
        for unit in suffix_tree.operators {
            inner_tree.push(InnerOpr::try_from(unit)?);
        }
        Ok(Self { suffix_tree: inner_tree, stack: RefCell::new(vec![]) })
    }
}

fn apply_arith<'a>(
    arith: &pb::Arithmetic, a: BorrowObject<'a>, b: BorrowObject<'a>,
) -> ExprEvalResult<Object> {
    use pb::Arithmetic::*;
    Ok(match arith {
        Add => Object::Primitive(a.as_primitive()? + b.as_primitive()?),
        Sub => Object::Primitive(a.as_primitive()? - b.as_primitive()?),
        Mul => Object::Primitive(a.as_primitive()? * b.as_primitive()?),
        Div => Object::Primitive(a.as_primitive()? / b.as_primitive()?),
        Mod => Object::Primitive(a.as_primitive()? % b.as_primitive()?),
        Exp => Object::Primitive(a.as_primitive()?.exp(b.as_primitive()?)),
    })
}

fn apply_logical<'a>(
    logical: &pb::Logical, a: BorrowObject<'a>, b_opt: Option<BorrowObject<'a>>,
) -> ExprEvalResult<Object> {
    use pb::Logical::*;
    if logical == &Not {
        return Ok((!a.as_bool()?).into());
    } else {
        if b_opt.is_some() {
            let b = b_opt.unwrap();
            match logical {
                Eq => Ok((a == b).into()),
                Ne => Ok((a != b).into()),
                Lt => Ok((a < b).into()),
                Le => Ok((a <= b).into()),
                Gt => Ok((a > b).into()),
                Ge => Ok((a >= b).into()),
                And => Ok((a.as_bool()? && b.as_bool()?).into()),
                Or => Ok((a.as_bool()? || b.as_bool()?).into()),
                Within => Ok(b.contains(&a).into()),
                Without => Ok((!b.contains(&a)).into()),
                Not => unreachable!(),
            }
        } else {
            Err(ExprEvalError::MissingOperands(InnerOpr::Logical(*logical).into()))
        }
    }
}

// Private api
impl Evaluator {
    /// Evaluate simple expression that contains less than three operators
    /// without using the stack.
    fn eval_without_stack<E: Element, C: Context<E>>(&self, context: Option<&C>) -> ExprEvalResult<Object> {
        assert!(self.suffix_tree.len() <= 3);
        let _first = self.suffix_tree.get(0);
        let _second = self.suffix_tree.get(1);
        let _third = self.suffix_tree.get(2);
        if self.suffix_tree.is_empty() {
            Err(ExprEvalError::EmptyExpression)
        } else if self.suffix_tree.len() == 1 {
            _first.unwrap().eval(context)
        } else if self.suffix_tree.len() == 2 {
            let first = _first.unwrap();
            let second = _second.unwrap();
            if let InnerOpr::Logical(logical) = second {
                apply_logical(logical, first.eval(context)?.as_borrow(), None)
            } else {
                if !second.is_operand() {
                    Err(ExprEvalError::MissingOperands(second.into()))
                } else {
                    Err(ExprEvalError::OtherErr("invalid expression".to_string()))
                }
            }
        } else {
            let first = _first.unwrap();
            let second = _second.unwrap();
            let third = _third.unwrap();

            if let InnerOpr::Logical(logical) = third {
                apply_logical(
                    logical,
                    first.eval(context)?.as_borrow(),
                    Some(second.eval(context)?.as_borrow()),
                )
            } else if let InnerOpr::Arith(arith) = third {
                apply_arith(arith, first.eval(context)?.as_borrow(), second.eval(context)?.as_borrow())
            } else {
                Err(ExprEvalError::OtherErr("invalid expression".to_string()))
            }
        }
    }
}

impl Evaluate for Evaluator {
    /// Evaluate an expression with an optional context. The context must implement the
    /// provided trait `[Context]`, that can get an `[crate::graph::element::Element]`
    /// using a given key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dyn_type::Object;
    /// # use ir_common::NameOrId;
    /// # use runtime::expr::eval::{Context, Evaluator, Evaluate};
    /// # use runtime::graph::element::Vertex;
    /// # use runtime::graph::property::{DefaultDetails, DynDetails};
    /// # use std::collections::HashMap;
    /// # use std::convert::TryFrom;
    /// # use ir_common::expr_parse::str_to_suffix_expr_pb;
    ///
    /// struct Vertices {
    ///     vec: Vec<Vertex>,
    /// }
    ///
    /// impl Context<Vertex> for Vertices {
    ///     fn get(&self, key: Option<&NameOrId>) -> Option<&Vertex> {
    ///        match key {
    ///             Some(NameOrId::Id(i)) => self.vec.get(*i as usize),
    ///             _ => None
    ///         }
    ///     }
    /// }
    ///
    /// let map: HashMap<NameOrId, Object> = vec![
    ///         (NameOrId::from("age".to_string()), 12.into()),
    ///         (NameOrId::from("birthday".to_string()), 19900416.into()),
    ///     ]
    ///     .into_iter()
    ///     .collect();
    ///
    ///     let ctxt = Vertices {
    ///         vec: vec![
    ///             Vertex::new(DynDetails::new(DefaultDetails::with_property(
    ///                 1,
    ///                 NameOrId::from(1),
    ///                 map.clone(),
    ///             ))),
    ///             Vertex::new(DynDetails::new(DefaultDetails::with_property(
    ///                 2,
    ///                 NameOrId::from(2),
    ///                 map.clone(),
    ///             ))),
    ///         ],
    ///     };
    ///
    /// let suffix_tree = str_to_suffix_expr_pb("@0.age == @1.age".to_string()).unwrap();
    /// let eval = Evaluator::try_from(suffix_tree).unwrap();
    ///
    /// assert!(eval.eval::<_, _>(Some(&ctxt)).unwrap().as_bool().unwrap())
    /// ```
    fn eval<E: Element, C: Context<E>>(&self, context: Option<&C>) -> ExprEvalResult<Object> {
        let mut stack = self.stack.borrow_mut();
        if self.suffix_tree.len() <= 3 {
            return self.eval_without_stack(context);
        }
        stack.clear();
        for opr in &self.suffix_tree {
            if opr.is_operand() {
                stack.push(opr.eval(context)?);
            } else {
                if let Some(first) = stack.pop() {
                    let first_borrow = first.as_borrow();
                    let rst = match opr {
                        InnerOpr::Logical(logical) => {
                            if logical == &pb::Logical::Not {
                                apply_logical(logical, first_borrow, None)
                            } else {
                                if let Some(second) = stack.pop() {
                                    apply_logical(logical, second.as_borrow(), Some(first_borrow))
                                } else {
                                    Err(ExprEvalError::OtherErr("invalid expression".to_string()))
                                }
                            }
                        }
                        InnerOpr::Arith(arith) => {
                            if let Some(second) = stack.pop() {
                                apply_arith(arith, second.as_borrow(), first_borrow)
                            } else {
                                Err(ExprEvalError::OtherErr("invalid expression".to_string()))
                            }
                        }
                        _ => unreachable!(),
                    };
                    stack.push((rst?).into());
                }
            }
        }

        if stack.len() == 1 {
            Ok(stack.pop().unwrap())
        } else {
            Err("invalid expression".into())
        }
    }
}

impl Evaluator {
    /// Reset the status of the evaluator for further evaluation
    pub fn reset(&self) {
        self.stack.borrow_mut().clear();
    }

    pub fn eval_bool<E: Element, C: Context<E>>(&self, context: Option<&C>) -> ExprEvalResult<bool> {
        Ok(self.eval(context)?.as_bool()?)
    }
}

impl TryFrom<pb::ExprOpr> for InnerOpr {
    type Error = ParsePbError;

    fn try_from(unit: pb::ExprOpr) -> ParsePbResult<Self>
    where
        Self: Sized,
    {
        use pb::expr_opr::Item::*;
        if let Some(item) = unit.item {
            match item {
                Logical(logical) => {
                    Ok(Self::Logical(unsafe { std::mem::transmute::<_, pb::Logical>(logical) }))
                }
                Arith(arith) => Ok(Self::Arith(unsafe { std::mem::transmute::<_, pb::Arithmetic>(arith) })),
                Const(c) => Ok(Self::Const(c.try_into()?)),
                Var(var) => {
                    let (_tag, _property) = (var.tag, var.property);
                    let tag = if let Some(tag) = _tag { Some(NameOrId::try_from(tag)?) } else { None };
                    if let Some(property) = _property {
                        Ok(Self::Var { tag, prop_key: Some(PropKey::try_from(property)?) })
                    } else {
                        Ok(Self::Var { tag, prop_key: None })
                    }
                }
                Vars(vars) => {
                    let mut vec = Vec::with_capacity(vars.keys.len());
                    for var in vars.keys {
                        let var_opr: InnerOpr =
                            pb::ExprOpr { item: Some(pb::expr_opr::Item::Var(var)) }.try_into()?;
                        vec.push(var_opr);
                    }
                    Ok(Self::Vars(vec))
                }
                VarMap(vars) => {
                    let mut vec = Vec::with_capacity(vars.keys.len());
                    for var in vars.keys {
                        let var_opr: InnerOpr =
                            pb::ExprOpr { item: Some(pb::expr_opr::Item::Var(var)) }.try_into()?;
                        vec.push(var_opr);
                    }
                    Ok(Self::VarMap(vec))
                }
                _ => Err(ParsePbError::ParseError("invalid operator of braces".to_string())),
            }
        } else {
            Err(ParsePbError::from("empty value provided"))
        }
    }
}

impl Evaluate for InnerOpr {
    fn eval<E: Element, C: Context<E>>(&self, context: Option<&C>) -> ExprEvalResult<Object> {
        let obj_opt = self.eval_as_object(context)?;
        obj_opt.ok_or(ExprEvalError::NoneOperand(OperatorDesc("evaluate object as `None`".to_string())))
    }
}

impl InnerOpr {
    pub fn eval_as_object<E: Element, C: Context<E>>(
        &self, context: Option<&C>,
    ) -> ExprEvalResult<Option<Object>> {
        match self {
            Self::Const(c_opt) => Ok(if let Some(opt) = c_opt { Some(opt.clone()) } else { None }),
            Self::Var { tag, prop_key } => {
                if let Some(ctxt) = context {
                    let mut result = Ok(None);
                    if let Some(element) = ctxt.get(tag.as_ref()) {
                        if let Some(property) = prop_key {
                            if let Some(details) = element.details() {
                                result = Ok(details
                                    .get(property)
                                    .and_then(|obj| obj.try_to_owned()));
                            }
                        } else {
                            result = Ok(element.as_borrow_object().try_to_owned())
                        }
                    }

                    result
                } else {
                    Err(ExprEvalError::MissingContext(self.into()))
                }
            }
            Self::Vars(vars) => {
                let mut vec = Vec::with_capacity(vars.len());
                for var in vars {
                    if let Some(obj) = var.eval_as_object(context)? {
                        vec.push(obj);
                    } else {
                        return Ok(None);
                    }
                }
                Ok(Some(Object::Vector(vec)))
            }
            Self::VarMap(vars) => {
                let mut map = BTreeMap::new();
                for var in vars {
                    if let Some(obj) = var.eval_as_object(context)? {
                        // TODO(may want to use other strings)
                        map.insert(var.to_string().into(), obj);
                    } else {
                        return Ok(None);
                    }
                }
                Ok(Some(Object::KV(map)))
            }
            _ => Err(ExprEvalError::UnmatchedOperator(self.into())),
        }
    }

    pub fn is_operand(&self) -> bool {
        match self {
            InnerOpr::Const(_) | InnerOpr::Var { .. } | InnerOpr::Vars(_) => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ir_common::expr_parse::str_to_suffix_expr_pb;

    use super::*;
    use crate::graph::element::Vertex;
    use crate::graph::property::{DefaultDetails, DynDetails};

    struct Vertices {
        vec: Vec<Vertex>,
    }
    impl Context<Vertex> for Vertices {
        fn get(&self, key: Option<&NameOrId>) -> Option<&Vertex> {
            match key {
                Some(NameOrId::Id(i)) => self.vec.get(*i as usize),
                _ => None,
            }
        }
    }

    fn prepare_context() -> Vertices {
        let map1: HashMap<NameOrId, Object> = vec![
            (NameOrId::from("age".to_string()), 31.into()),
            (NameOrId::from("birthday".to_string()), 19900416.into()),
            (NameOrId::from("name".to_string()), "John".to_string().into()),
            (
                NameOrId::from("hobbies".to_string()),
                vec!["football".to_string(), "guitar".to_string()].into(),
            ),
        ]
        .into_iter()
        .collect();
        let map2: HashMap<NameOrId, Object> = vec![
            (NameOrId::from("age".to_string()), 26.into()),
            (NameOrId::from("birthday".to_string()), 19950816.into()),
            (NameOrId::from("name".to_string()), "Nancy".to_string().into()),
        ]
        .into_iter()
        .collect();
        Vertices {
            vec: vec![
                Vertex::new(DynDetails::new(DefaultDetails::with_property(1, NameOrId::from(9), map1))),
                Vertex::new(DynDetails::new(DefaultDetails::with_property(2, NameOrId::from(11), map2))),
            ],
        }
    }

    #[test]
    fn test_eval_simple() {
        let cases: Vec<&str> = vec![
            "7 + 3",          // 10
            "7.0 + 3",        // 10.0
            "7 * 3",          // 21
            "7 / 3",          // 2
            "7 ^ 3",          // 343
            "7 ^ -3",         // 1 / 343
            "7 % 3",          // 1
            "7 -3",           // 4
            "-3 + 7",         // 4
            "-3",             // -3
            "-3.0",           // -3.0
            "false",          // false
            "!true",          // false
            "!10",            // false
            "!0",             // true
            "true || true",   // true
            "true || false",  // true
            "false || false", // false
            "true && true",   // true
            "true && false",  // false
            "1 > 2",          // false
            "1 < 2",          // true
            "1 >= 2",         // false
            "2 <= 2",         // true,
            "2 == 2",         // true
            "1.0 > 2.0",      // false
        ];

        let expected: Vec<Object> = vec![
            object!(10),
            object!(10.0),
            object!(21),
            object!(2),
            object!(343),
            object!(1.0 / 343.0),
            object!(1),
            object!(4),
            object!(4),
            object!(-3),
            object!(-3.0),
            object!(false),
            object!(false),
            object!(false),
            object!(true),
            object!(true),
            object!(true),
            object!(false),
            object!(true),
            object!(false),
            object!(false),
            object!(true),
            object!(false),
            object!(true),
            object!(true),
            object!(false),
        ];

        for (case, expected) in cases.into_iter().zip(expected.into_iter()) {
            let eval = Evaluator::try_from(str_to_suffix_expr_pb(case.to_string()).unwrap()).unwrap();
            assert_eq!(eval.eval::<(), NoneContext>(None).unwrap(), expected);
        }
    }

    #[test]
    fn test_eval_contains() {
        let cases: Vec<&str> = vec![
            "10 within [10, 9, 8, 7]",                                                // true
            "[10, 7] within [10, 9, 8, 7]",                                           // true
            "[10, 6] within [10, 9, 8, 7]",                                           // false
            "[10, 6] without [10, 9, 8, 7]",                                          // true
            "10.0 within [10.0, 9.0, 8.0, 7.0]",                                      // true
            "[10.0, 7.0] within [10.0, 9.0, 8.0, 7.0]",                               // true
            "[10.0, 6.0] within [10.0, 9.0, 8.0, 7.0]",                               // false
            "[10.0, 6.0] without [10.0, 9.0, 8.0, 7.0]",                              // true
            "\"a\" within [\"a\", \"b\", \"c\", \"d\"]",                              // true
            "[\"f\"] within [\"a\", \"b\", \"c\", \"d\"]",                            // false
            "[\"f\"] without [\"a\", \"b\", \"c\", \"d\"]",                           // true
            "10 within [10, 9, 8, 7] && [\"f\"] within [\"a\", \"b\", \"c\", \"d\"]", // false
            "(3 + 7) within [10, 9, 8, 7] || [\"f\"] within [\"a\", \"b\", \"c\", \"d\"]", // true
        ];

        let expected: Vec<Object> = vec![
            object!(true),
            object!(true),
            object!(false),
            object!(true),
            object!(true),
            object!(true),
            object!(false),
            object!(true),
            object!(true),
            object!(false),
            object!(true),
            object!(false),
            object!(true),
        ];

        for (case, expected) in cases.into_iter().zip(expected.into_iter()) {
            let eval = Evaluator::try_from(str_to_suffix_expr_pb(case.to_string()).unwrap()).unwrap();
            assert_eq!(eval.eval::<(), NoneContext>(None).unwrap(), expected);
        }
    }

    #[test]
    fn test_eval_complex() {
        let cases: Vec<&str> = vec![
            "(-10)",                                 // -10
            "2 * 2 - 3",                             // 1
            "2 * (2 - 3)",                           // -2
            "6 / 2 - 3",                             // 0
            "6 / (2 - 3)",                           // -6
            "2 * 1e-3",                              // 0.002
            "1 > 2 && 1 < 3",                        // false
            "1 > 2 || 1 < 3",                        // true
            "2 ^ 10 > 10",                           // true
            "2 / 5 ^ 2",                             // 0
            "2.0 / 5 ^ 2",                           // 2.0 / 25
            "((1 + 2) * 3) / (7 * 8) + 12.5 / 10.1", // 1.2376237623762376
            "((1 + 2) * 3) / 7 * 8 + 12.5 / 10.1",   // 9.237623762376238
            "((1 + 2) * 3) / 7 * 8 + 12.5 / 10.1 \
                == ((1 + 2) * 3) / (7 * 8) + 12.5 / 10.1", // false
        ];

        let expected: Vec<Object> = vec![
            object!(-10),
            object!(1),
            object!(-2),
            object!(0),
            object!(-6),
            object!(0.002),
            object!(false),
            object!(true),
            object!(true),
            object!(0),
            object!(2.0 / 25.0),
            object!(1.2376237623762376),
            object!(9.237623762376238),
            object!(false),
        ];

        for (case, expected) in cases.into_iter().zip(expected.into_iter()) {
            let eval = Evaluator::try_from(str_to_suffix_expr_pb(case.to_string()).unwrap()).unwrap();
            assert_eq!(eval.eval::<(), NoneContext>(None).unwrap(), expected);
        }
    }

    #[test]
    fn test_eval_variable() {
        // [v0: id = 1, label = 9, age = 31, name = John, birthday = 19900416, hobbies = [football, guitar]]
        // [v1: id = 2, label = 11, age = 26, name = Jimmy, birthday = 19950816]
        let ctxt = prepare_context();
        let cases: Vec<&str> = vec![
            "@0.~id",                                      // 1
            "@1.~label",                                   // 1
            "@0.~id < @1.~id",                             // true
            "@0.birthday > @1.birthday",                   // false
            "@0.~label == @1.~label",                      // false
            "@0.name != @1.name",                          // true
            "@0.name == \"John\"",                         // true
            "@0.name == \"John\" && @1.name == \"Jimmy\"", // false
            "@0.age + @0.birthday / 10000 == \
                            @1.age + @1.birthday / 10000", // true
            "@0.hobbies within [\"football\", \"guitar\", \"chess\"]", // true
            "[@0.name, @0.age]",                           // [\"John\"", 31]
            // "{@0.name, @0.age}"              // {"name": "John", "age": 31}
        ];

        let expected: Vec<Object> = vec![
            object!(1),
            object!(11),
            object!(true),
            object!(false),
            object!(false),
            object!(true),
            object!(true),
            object!(false),
            object!(true),
            object!(true),
            Object::Vector(vec![object!("John"), object!(31)]),
            // Object::KV(vec![(object!("0.name"), object!("John")), (object!("0.age"), object!(31))]
            //    .into_iter().collect())
        ];

        for (case, expected) in cases.into_iter().zip(expected.into_iter()) {
            let eval = Evaluator::try_from(str_to_suffix_expr_pb(case.to_string()).unwrap()).unwrap();
            assert_eq!(eval.eval::<_, Vertices>(Some(&ctxt)).unwrap(), expected);
        }
    }

    #[test]
    fn test_eval_errors() {
        let cases: Vec<&str> = vec![
            "@2",
            "@2",
            "@1.nonexistent",
            "+",
            "1 + ",
            "1 1",
            "1 1 2",
            "1 1 + 2",
            "1 + @1.age * 1 1 - 1 - 5",
        ];
        let ctxt = prepare_context();

        let expected: Vec<ExprEvalError> = vec![
            // Evaluate variable without providing the context
            ExprEvalError::MissingContext(InnerOpr::Var { tag: Some(2.into()), prop_key: None }.into()),
            // obtain non-value from the context
            ExprEvalError::NoneOperand(OperatorDesc("evaluate object as `None`".to_string())),
            // obtain non-value from the context
            ExprEvalError::NoneOperand(OperatorDesc("evaluate object as `None`".to_string())),
            // try to evaluate neither a variable nor a const
            ExprEvalError::UnmatchedOperator(InnerOpr::Arith(pb::Arithmetic::Add).into()),
            ExprEvalError::MissingOperands(InnerOpr::Arith(pb::Arithmetic::Add).into()),
            ExprEvalError::OtherErr("invalid expression".to_string()),
            ExprEvalError::OtherErr("invalid expression".to_string()),
            ExprEvalError::OtherErr("invalid expression".to_string()),
            ExprEvalError::OtherErr("invalid expression".to_string()),
        ];

        let mut is_context = false;
        for (case, expected) in cases.into_iter().zip(expected.into_iter()) {
            let eval = Evaluator::try_from(str_to_suffix_expr_pb(case.to_string()).unwrap()).unwrap();
            assert_eq!(
                if is_context {
                    eval.eval::<_, Vertices>(Some(&ctxt))
                        .err()
                        .unwrap()
                } else {
                    eval.eval::<_, NoneContext>(None).err().unwrap()
                },
                expected
            );
            is_context = true;
        }
    }
}
