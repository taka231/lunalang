use crate::typeinfer::Type;
use std::error::Error;
use std::fmt;
use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeInferError {
    UnifyError(Type, Type),
    OccurError(u64, Type),
    UnimplementedOperatorError(String),
    UndefinedVariable(String),
}

impl Display for TypeInferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnifyError(t1, t2) => write!(f, "type error: Cannot unify {} to {}", t1, t2),
            Self::OccurError(n, t) => write!(f, "type error: {} is occur in type {}", n, t),
            Self::UnimplementedOperatorError(op) => {
                write!(f, "type error: {} is unimplemented", op)
            }
            Self::UndefinedVariable(var) => {
                write!(f, "type error: {} is an undefined variable", var)
            }
        }
    }
}

impl Error for TypeInferError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    InternalTypeError,
    UnimplementedOperatorError(String),
    UndefinedVariable(String),
}

impl Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InternalTypeError => write!(f, "eval error: InternalTypeError"),
            Self::UnimplementedOperatorError(op) => {
                write!(f, "eval error: {} is unimplemented", op)
            }
            Self::UndefinedVariable(var) => {
                write!(f, "eval error: {} is an undefined variable", var)
            }
        }
    }
}

impl Error for EvalError {}
