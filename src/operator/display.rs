#![cfg(not(tarpaulin_include))]

use std::fmt::{Display, Error, Formatter};

use crate::operator::*;

impl Display for Operator {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use crate::operator::Operator::*;
        match self {
            RootNode => Ok(()),
            Add => write!(f, "+"),
            Sub => write!(f, "-"),
            Neg => write!(f, "-"),
            #[cfg(feature = "percent_operator_is_percentage")]
            Percentage => write!(f, "%"),
            Mul => write!(f, "*"),
            Div => write!(f, "/"),
            #[cfg(not(feature = "percent_operator_is_percentage"))]
            Mod => write!(f, "%"),
            Exp => write!(f, "^"),

            Eq => write!(f, "=="),
            Neq => write!(f, "!="),
            Gt => write!(f, ">"),
            Lt => write!(f, "<"),
            Geq => write!(f, ">="),
            Leq => write!(f, "<="),
            And => write!(f, "&&"),
            Or => write!(f, "||"),
            Not => write!(f, "!"),

            #[cfg(feature = "in_operator")]
            In => write!(f, "=:"),
            #[cfg(feature = "in_operator")]
            NotIn => write!(f, "!:"),
            #[cfg(feature = "in_operator")]
            GtIn => write!(f, ">:"),
            #[cfg(feature = "in_operator")]
            LtIn => write!(f, "<:"),
            #[cfg(feature = "in_operator")]
            AndIn => write!(f, "&:"),
            #[cfg(feature = "in_operator")]
            OrIn => write!(f, "|:"),

            Assign => write!(f, " = "),
            AddAssign => write!(f, " += "),
            SubAssign => write!(f, " -= "),
            MulAssign => write!(f, " *= "),
            DivAssign => write!(f, " /= "),
            #[cfg(not(feature = "percent_operator_is_percentage"))]
            ModAssign => write!(f, " %= "),
            ExpAssign => write!(f, " ^= "),
            AndAssign => write!(f, " &&= "),
            OrAssign => write!(f, " ||= "),

            Tuple => write!(f, ", "),
            Chain => write!(f, "; "),

            Const { value } => write!(f, "{}", value),
            VariableIdentifierWrite { identifier } | VariableIdentifierRead { identifier } => {
                write!(f, "{}", identifier)
            },
            FunctionIdentifier { identifier } => write!(f, "{}", identifier),
        }
    }
}
