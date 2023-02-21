use crate::typeinfer::Type;
use std::fmt;
use std::fmt::Display;

pub trait Error {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeInferError {
    UnifyError(Type, Type),
    OccurError(u64, Type),
}

impl Display for TypeInferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnifyError(t1, t2) => write!(f, "Cannot unify {} to {}", t1, t2),
            Self::OccurError(n, t) => write!(f, "{} is occur in type {}", n, t),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    InternalTypeError,
    UnimplementedOperatorError(String),
}

impl Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InternalTypeError => write!(f, "InternalTypeError"),
            Self::UnimplementedOperatorError(op) => write!(f, "{} is unimplemented", op),
        }
    }
}
