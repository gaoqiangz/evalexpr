use crate::function::builtin::builtin_function;

use crate::{context::Context, error::*, value::Value, ContextWithMutableVariables};

mod display;

/// An enum that represents operators in the operator tree.
#[derive(Debug, PartialEq, Clone)]
pub enum Operator {
    /// A root node in the operator tree.
    /// The whole expression is stored under a root node, as well as each subexpression surrounded by parentheses.
    RootNode,

    /// A binary addition operator.
    Add,
    /// A binary subtraction operator.
    Sub,
    /// A unary negation operator.
    Neg,
    /// A suffix unary percentage operator.
    #[cfg(feature = "percent_operator_is_percentage")]
    Percentage,
    /// A binary multiplication operator.
    Mul,
    /// A binary division operator.
    Div,
    /// A binary modulo operator.
    #[cfg(not(feature = "percent_operator_is_percentage"))]
    Mod,
    /// A binary exponentiation operator.
    Exp,

    /// A binary equality comparator.
    Eq,
    /// A binary inequality comparator.
    Neq,
    /// A binary greater-than comparator.
    Gt,
    /// A binary lower-than comparator.
    Lt,
    /// A binary greater-than-or-equal comparator.
    Geq,
    /// A binary lower-than-or-equal comparator.
    Leq,
    /// A binary logical and operator.
    And,
    /// A binary logical or operator.
    Or,
    /// A binary logical not operator.
    Not,

    /// A binary in comparator.
    #[cfg(feature = "in_operator")]
    In,
    /// A binary not in comparator.
    #[cfg(feature = "in_operator")]
    NotIn,

    /// A binary assignment operator.
    Assign,
    /// A binary add-assign operator.
    AddAssign,
    /// A binary subtract-assign operator.
    SubAssign,
    /// A binary multiply-assign operator.
    MulAssign,
    /// A binary divide-assign operator.
    DivAssign,
    /// A binary modulo-assign operator.
    #[cfg(not(feature = "percent_operator_is_percentage"))]
    ModAssign,
    /// A binary exponentiate-assign operator.
    ExpAssign,
    /// A binary and-assign operator.
    AndAssign,
    /// A binary or-assign operator.
    OrAssign,

    /// An n-ary tuple constructor.
    Tuple,
    /// An n-ary subexpression chain.
    Chain,

    /// A constant value.
    Const {
        /** The value of the constant. */
        value: Value,
    },
    /// A write to a variable identifier.
    VariableIdentifierWrite {
        /// The identifier of the variable.
        identifier: String,
    },
    /// A read from a variable identifier.
    VariableIdentifierRead {
        /// The identifier of the variable.
        identifier: String,
    },
    /// A function identifier.
    FunctionIdentifier {
        /// The identifier of the function.
        identifier: String,
    },
}

impl Operator {
    pub(crate) fn value(value: Value) -> Self {
        Operator::Const { value }
    }

    pub(crate) fn variable_identifier_write(identifier: String) -> Self {
        Operator::VariableIdentifierWrite { identifier }
    }

    pub(crate) fn variable_identifier_read(identifier: String) -> Self {
        Operator::VariableIdentifierRead { identifier }
    }

    pub(crate) fn function_identifier(identifier: String) -> Self {
        Operator::FunctionIdentifier { identifier }
    }

    /// Returns the precedence of the operator.
    /// A high precedence means that the operator has priority to be deeper in the tree.
    pub(crate) const fn precedence(&self) -> i32 {
        use crate::operator::Operator::*;
        match self {
            RootNode => 200,

            Add | Sub => 95,
            Neg => 110,

            #[cfg(feature = "percent_operator_is_percentage")]
            Percentage => 110,

            Mul | Div => 100,
            #[cfg(not(feature = "percent_operator_is_percentage"))]
            Mod => 100,

            Exp => 120,

            Eq | Neq | Gt | Lt | Geq | Leq => 80,
            And => 75,
            Or => 70,
            Not => 110,

            #[cfg(feature = "in_operator")]
            In | NotIn => 80,

            Assign | AddAssign | SubAssign | MulAssign | DivAssign | ExpAssign | AndAssign
            | OrAssign => 50,

            #[cfg(not(feature = "percent_operator_is_percentage"))]
            ModAssign => 50,

            Tuple => 40,
            Chain => 0,

            Const { .. } => 200,
            VariableIdentifierWrite { .. } | VariableIdentifierRead { .. } => 200,
            FunctionIdentifier { .. } => 190,
        }
    }

    /// Returns true if chains of operators with the same precedence as this one should be evaluated left-to-right,
    /// and false if they should be evaluated right-to-left.
    /// Left-to-right chaining has priority if operators with different order but same precedence are chained.
    pub(crate) const fn is_left_to_right(&self) -> bool {
        use crate::operator::Operator::*;
        !matches!(self, Assign | FunctionIdentifier { .. })
    }

    /// Returns true if chains of this operator should be flattened into one operator with many arguments.
    pub(crate) const fn is_sequence(&self) -> bool {
        use crate::operator::Operator::*;
        matches!(self, Tuple | Chain)
    }

    /// True if this operator is a leaf, meaning it accepts no arguments.
    // Make this a const fn as soon as whatever is missing gets stable (issue #57563)
    pub(crate) fn is_leaf(&self) -> bool {
        self.max_argument_amount() == Some(0)
    }

    /// Returns the maximum amount of arguments required by this operator.
    pub(crate) const fn max_argument_amount(&self) -> Option<usize> {
        use crate::operator::Operator::*;
        match self {
            Add | Sub | Mul | Div | Exp | Eq | Neq | Gt | Lt | Geq | Leq | And | Or | Assign
            | AddAssign | SubAssign | MulAssign | DivAssign | ExpAssign | AndAssign | OrAssign => {
                Some(2)
            },

            #[cfg(feature = "percent_operator_is_percentage")]
            Percentage => Some(1),

            #[cfg(not(feature = "percent_operator_is_percentage"))]
            Mod | ModAssign => Some(2),

            #[cfg(feature = "in_operator")]
            In | NotIn => Some(2),

            Tuple | Chain => None,
            Not | Neg | RootNode => Some(1),
            Const { .. } => Some(0),
            VariableIdentifierWrite { .. } | VariableIdentifierRead { .. } => Some(0),
            FunctionIdentifier { .. } => Some(1),
        }
    }

    /// Returns true if this operator is prefix unary, i.e. it requires exactly one argument.
    pub(crate) fn is_prefix_unary(&self) -> bool {
        self.max_argument_amount() == Some(1) && *self != Operator::RootNode && {
            #[cfg(feature = "percent_operator_is_percentage")]
            {
                *self != Operator::Percentage
            }
            #[cfg(not(feature = "percent_operator_is_percentage"))]
            {
                true
            }
        }
    }

    /// Returns true if this operator is suffix unary, i.e. it requires exactly one argument.
    #[allow(dead_code)]
    #[cfg(feature = "percent_operator_is_percentage")]
    pub(crate) fn is_suffix_unary(&self) -> bool {
        self.max_argument_amount() == Some(1) && *self == Operator::Percentage
    }

    /// Evaluates the operator with the given arguments and context.
    pub(crate) fn eval<C: Context>(
        &self,
        arguments: &[Value],
        context: &C,
    ) -> EvalexprResult<Value> {
        use crate::operator::Operator::*;
        match self {
            RootNode => {
                if let Some(first) = arguments.first() {
                    Ok(first.clone())
                } else {
                    Ok(Value::Empty)
                }
            },
            Add => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                expect_number_or_string(&arguments[0])?;
                expect_number_or_string(&arguments[1])?;

                if let (Ok(a), Ok(b)) = (arguments[0].as_string(), arguments[1].as_string()) {
                    let mut result = String::with_capacity(a.len() + b.len());
                    result.push_str(&a);
                    result.push_str(&b);
                    Ok(Value::String(result))
                } else if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                    let result = a.checked_add(b);
                    if let Some(result) = result {
                        Ok(Value::Int(result))
                    } else {
                        Err(EvalexprError::addition_error(
                            arguments[0].clone(),
                            arguments[1].clone(),
                        ))
                    }
                } else if let (Ok(a), Ok(b)) = (arguments[0].as_number(), arguments[1].as_number())
                {
                    #[cfg(feature = "decimal_support")]
                    {
                        let result = a.checked_add(b);
                        if let Some(result) = result {
                            Ok(Value::Float(result))
                        } else {
                            Err(EvalexprError::addition_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    }
                    #[cfg(not(feature = "decimal_support"))]
                    {
                        Ok(Value::Float(a + b))
                    }
                } else {
                    Err(EvalexprError::wrong_type_combination(
                        self.clone(),
                        vec![
                            arguments.get(0).unwrap().into(),
                            arguments.get(1).unwrap().into(),
                        ],
                    ))
                }
            },
            Sub => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                #[cfg(feature = "decimal_support")]
                {
                    if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                        let result = a.checked_sub(b);
                        if let Some(result) = result {
                            Ok(Value::Int(result))
                        } else {
                            Err(EvalexprError::subtraction_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    } else {
                        let a = arguments[0].as_number()?;
                        let b = arguments[1].as_number()?;
                        let result = a.checked_sub(b);
                        if let Some(result) = result {
                            Ok(Value::Float(result))
                        } else {
                            Err(EvalexprError::subtraction_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    }
                }
                #[cfg(not(feature = "decimal_support"))]
                {
                    arguments[0].as_number()?;
                    arguments[1].as_number()?;

                    if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                        let result = a.checked_sub(b);
                        if let Some(result) = result {
                            Ok(Value::Int(result))
                        } else {
                            Err(EvalexprError::subtraction_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    } else {
                        Ok(Value::Float(
                            arguments[0].as_number()? - arguments[1].as_number()?,
                        ))
                    }
                }
            },
            Neg => {
                expect_operator_argument_amount(arguments.len(), 1)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                arguments[0].as_number()?;

                if let Ok(a) = arguments[0].as_int() {
                    let result = a.checked_neg();
                    if let Some(result) = result {
                        Ok(Value::Int(result))
                    } else {
                        Err(EvalexprError::negation_error(arguments[0].clone()))
                    }
                } else {
                    Ok(Value::Float(-arguments[0].as_number()?))
                }
            },
            #[cfg(feature = "percent_operator_is_percentage")]
            Percentage => {
                expect_operator_argument_amount(arguments.len(), 1)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                #[cfg(feature = "decimal_support")]
                {
                    if let Some(result) = arguments[0].as_number()?.checked_div(100.into()) {
                        Ok(Value::Float(result))
                    } else {
                        Err(EvalexprError::division_error(
                            arguments[0].clone(),
                            Value::Float(100.into()),
                        ))
                    }
                }
                #[cfg(not(feature = "decimal_support"))]
                {
                    Ok(Value::Float(arguments[0].as_number()? / 100.0))
                }
            },
            Mul => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                #[cfg(feature = "decimal_support")]
                {
                    if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                        let result = a.checked_mul(b);
                        if let Some(result) = result {
                            Ok(Value::Int(result))
                        } else {
                            Err(EvalexprError::multiplication_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    } else {
                        let a = arguments[0].as_number()?;
                        let b = arguments[1].as_number()?;
                        let result = a.checked_mul(b);
                        if let Some(result) = result {
                            Ok(Value::Float(result))
                        } else {
                            Err(EvalexprError::multiplication_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    }
                }
                #[cfg(not(feature = "decimal_support"))]
                {
                    arguments[0].as_number()?;
                    arguments[1].as_number()?;

                    if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                        let result = a.checked_mul(b);
                        if let Some(result) = result {
                            Ok(Value::Int(result))
                        } else {
                            Err(EvalexprError::multiplication_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    } else {
                        Ok(Value::Float(
                            arguments[0].as_number()? * arguments[1].as_number()?,
                        ))
                    }
                }
            },
            Div => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                #[cfg(feature = "decimal_support")]
                {
                    if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                        let result = a.checked_div(b);
                        if let Some(result) = result {
                            Ok(Value::Int(result))
                        } else {
                            Err(EvalexprError::division_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    } else {
                        let a = arguments[0].as_number()?;
                        let b = arguments[1].as_number()?;
                        let result = a.checked_div(b);
                        if let Some(result) = result {
                            Ok(Value::Float(result))
                        } else {
                            Err(EvalexprError::division_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    }
                }
                #[cfg(not(feature = "decimal_support"))]
                {
                    arguments[0].as_number()?;
                    arguments[1].as_number()?;

                    if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                        let result = a.checked_div(b);
                        if let Some(result) = result {
                            Ok(Value::Int(result))
                        } else {
                            Err(EvalexprError::division_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    } else {
                        Ok(Value::Float(
                            arguments[0].as_number()? / arguments[1].as_number()?,
                        ))
                    }
                }
            },
            #[cfg(not(feature = "percent_operator_is_percentage"))]
            Mod => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                #[cfg(feature = "decimal_support")]
                {
                    if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                        let result = a.checked_rem(b);
                        if let Some(result) = result {
                            Ok(Value::Int(result))
                        } else {
                            Err(EvalexprError::modulation_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    } else {
                        let a = arguments[0].as_number()?;
                        let b = arguments[1].as_number()?;
                        let result = a.checked_rem(b);
                        if let Some(result) = result {
                            Ok(Value::Float(result))
                        } else {
                            Err(EvalexprError::modulation_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    }
                }
                #[cfg(not(feature = "decimal_support"))]
                {
                    arguments[0].as_number()?;
                    arguments[1].as_number()?;

                    if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                        let result = a.checked_rem(b);
                        if let Some(result) = result {
                            Ok(Value::Int(result))
                        } else {
                            Err(EvalexprError::modulation_error(
                                arguments[0].clone(),
                                arguments[1].clone(),
                            ))
                        }
                    } else {
                        Ok(Value::Float(
                            arguments[0].as_number()? % arguments[1].as_number()?,
                        ))
                    }
                }
            },
            Exp => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                arguments[0].as_number()?;
                arguments[1].as_number()?;

                Ok({
                    #[cfg(feature = "decimal_support")]
                    {
                        use rust_decimal::prelude::*;
                        Value::Float(
                            arguments[0]
                                .as_number()?
                                .checked_powd(arguments[1].as_number()?)
                                //FIXME
                                //`rust_decimal` doesn't support `INFINITY` yet
                                //issue: https://github.com/paupino/rust-decimal/issues/466
                                .unwrap_or(Decimal::MAX),
                        )
                    }
                    #[cfg(not(feature = "decimal_support"))]
                    Value::Float(arguments[0].as_number()?.powf(arguments[1].as_number()?))
                })
            },
            Eq => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                if arguments[0] == arguments[1] {
                    Ok(Value::Boolean(true))
                } else if let (Ok(a), Ok(b)) = (arguments[0].as_number(), arguments[1].as_number())
                {
                    Ok(Value::Boolean(a == b))
                } else {
                    Ok(Value::Boolean(false))
                }
            },
            Neq => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                if arguments[0] == arguments[1] {
                    Ok(Value::Boolean(false))
                } else if let (Ok(a), Ok(b)) = (arguments[0].as_number(), arguments[1].as_number())
                {
                    Ok(Value::Boolean(a != b))
                } else {
                    Ok(Value::Boolean(true))
                }
            },
            Gt => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                expect_number_or_string(&arguments[0])?;
                expect_number_or_string(&arguments[1])?;

                if let (Ok(a), Ok(b)) = (arguments[0].as_string(), arguments[1].as_string()) {
                    Ok(Value::Boolean(a > b))
                } else if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                    Ok(Value::Boolean(a > b))
                } else {
                    Ok(Value::Boolean(
                        arguments[0].as_number()? > arguments[1].as_number()?,
                    ))
                }
            },
            Lt => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                expect_number_or_string(&arguments[0])?;
                expect_number_or_string(&arguments[1])?;

                if let (Ok(a), Ok(b)) = (arguments[0].as_string(), arguments[1].as_string()) {
                    Ok(Value::Boolean(a < b))
                } else if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                    Ok(Value::Boolean(a < b))
                } else {
                    Ok(Value::Boolean(
                        arguments[0].as_number()? < arguments[1].as_number()?,
                    ))
                }
            },
            Geq => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                expect_number_or_string(&arguments[0])?;
                expect_number_or_string(&arguments[1])?;

                if let (Ok(a), Ok(b)) = (arguments[0].as_string(), arguments[1].as_string()) {
                    Ok(Value::Boolean(a >= b))
                } else if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                    Ok(Value::Boolean(a >= b))
                } else {
                    Ok(Value::Boolean(
                        arguments[0].as_number()? >= arguments[1].as_number()?,
                    ))
                }
            },
            Leq => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                expect_number_or_string(&arguments[0])?;
                expect_number_or_string(&arguments[1])?;

                if let (Ok(a), Ok(b)) = (arguments[0].as_string(), arguments[1].as_string()) {
                    Ok(Value::Boolean(a <= b))
                } else if let (Ok(a), Ok(b)) = (arguments[0].as_int(), arguments[1].as_int()) {
                    Ok(Value::Boolean(a <= b))
                } else {
                    Ok(Value::Boolean(
                        arguments[0].as_number()? <= arguments[1].as_number()?,
                    ))
                }
            },
            And => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                let a = arguments[0].as_boolean()?;
                let b = arguments[1].as_boolean()?;

                Ok(Value::Boolean(a && b))
            },
            Or => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() {
                        if arguments[1].as_boolean()? {
                            return Ok(Value::Boolean(true));
                        } else {
                            return Ok(Value::Empty);
                        }
                    } else if arguments[1].is_empty() {
                        if arguments[0].as_boolean()? {
                            return Ok(Value::Boolean(true));
                        } else {
                            return Ok(Value::Empty);
                        }
                    }
                }
                let a = arguments[0].as_boolean()?;
                let b = arguments[1].as_boolean()?;

                Ok(Value::Boolean(a || b))
            },
            Not => {
                expect_operator_argument_amount(arguments.len(), 1)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                let a = arguments[0].as_boolean()?;

                Ok(Value::Boolean(!a))
            },
            #[cfg(feature = "in_operator")]
            In => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                let set = arguments[1].as_tuple()?;
                for item in set {
                    if arguments[0] == item {
                        return Ok(Value::Boolean(true));
                    } else if let (Ok(a), Ok(b)) = (arguments[0].as_number(), item.as_number()) {
                        if a == b {
                            return Ok(Value::Boolean(true));
                        }
                    }
                }
                Ok(Value::Boolean(false))
            },
            #[cfg(feature = "in_operator")]
            NotIn => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                #[cfg(feature = "empty_is_null")]
                {
                    if arguments[0].is_empty() || arguments[1].is_empty() {
                        return Ok(Value::Empty);
                    }
                }
                let set = arguments[1].as_tuple()?;
                for item in set {
                    if arguments[0] == item {
                        return Ok(Value::Boolean(false));
                    } else if let (Ok(a), Ok(b)) = (arguments[0].as_number(), item.as_number()) {
                        if a == b {
                            return Ok(Value::Boolean(false));
                        }
                    }
                }
                Ok(Value::Boolean(true))
            },
            Assign | AddAssign | SubAssign | MulAssign | DivAssign | ExpAssign | AndAssign
            | OrAssign => Err(EvalexprError::ContextNotMutable),
            #[cfg(not(feature = "percent_operator_is_percentage"))]
            ModAssign => Err(EvalexprError::ContextNotMutable),

            Tuple => Ok(Value::Tuple(arguments.into())),
            Chain => {
                if arguments.is_empty() {
                    return Err(EvalexprError::wrong_operator_argument_amount(0, 1));
                }

                Ok(arguments.last().cloned().unwrap_or(Value::Empty))
            },
            Const { value } => {
                expect_operator_argument_amount(arguments.len(), 0)?;

                Ok(value.clone())
            },
            VariableIdentifierWrite { identifier } => {
                expect_operator_argument_amount(arguments.len(), 0)?;

                Ok(identifier.clone().into())
            },
            VariableIdentifierRead { identifier } => {
                expect_operator_argument_amount(arguments.len(), 0)?;

                if let Some(value) = context.get_value(identifier).cloned() {
                    Ok(value)
                } else {
                    Err(EvalexprError::VariableIdentifierNotFound(
                        identifier.clone(),
                    ))
                }
            },
            FunctionIdentifier { identifier } => {
                expect_operator_argument_amount(arguments.len(), 1)?;
                let arguments = &arguments[0];

                match context.call_function(identifier, arguments) {
                    Err(EvalexprError::FunctionIdentifierNotFound(_))
                        if !context.are_builtin_functions_disabled() =>
                    {
                        if let Some(builtin_function) = builtin_function(identifier) {
                            builtin_function.call(arguments)
                        } else {
                            Err(EvalexprError::FunctionIdentifierNotFound(
                                identifier.clone(),
                            ))
                        }
                    },
                    result => result,
                }
            },
        }
    }

    /// Evaluates the operator with the given arguments and mutable context.
    pub(crate) fn eval_mut<C: ContextWithMutableVariables>(
        &self,
        arguments: &[Value],
        context: &mut C,
    ) -> EvalexprResult<Value> {
        use crate::operator::Operator::*;
        match self {
            Assign => {
                expect_operator_argument_amount(arguments.len(), 2)?;
                let target = arguments[0].as_string()?;
                context.set_value(target, arguments[1].clone())?;

                Ok(Value::Empty)
            },
            AddAssign | SubAssign | MulAssign | DivAssign | ExpAssign | AndAssign | OrAssign => {
                expect_operator_argument_amount(arguments.len(), 2)?;

                let target = arguments[0].as_string()?;
                let left_value = Operator::VariableIdentifierRead {
                    identifier: target.clone(),
                }
                .eval(&Vec::new(), context)?;
                let arguments = vec![left_value, arguments[1].clone()];

                let result = match self {
                    AddAssign => Operator::Add.eval(&arguments, context),
                    SubAssign => Operator::Sub.eval(&arguments, context),
                    MulAssign => Operator::Mul.eval(&arguments, context),
                    DivAssign => Operator::Div.eval(&arguments, context),
                    ExpAssign => Operator::Exp.eval(&arguments, context),
                    AndAssign => Operator::And.eval(&arguments, context),
                    OrAssign => Operator::Or.eval(&arguments, context),
                    _ => unreachable!(
                        "Forgot to add a match arm for an assign operation: {}",
                        self
                    ),
                }?;
                context.set_value(target, result)?;

                Ok(Value::Empty)
            },
            #[cfg(not(feature = "percent_operator_is_percentage"))]
            ModAssign => {
                expect_operator_argument_amount(arguments.len(), 2)?;

                let target = arguments[0].as_string()?;
                let left_value = Operator::VariableIdentifierRead {
                    identifier: target.clone(),
                }
                .eval(&Vec::new(), context)?;
                let arguments = vec![left_value, arguments[1].clone()];

                let result = Operator::Mod.eval(&arguments, context)?;
                context.set_value(target, result)?;

                Ok(Value::Empty)
            },
            _ => self.eval(arguments, context),
        }
    }
}
