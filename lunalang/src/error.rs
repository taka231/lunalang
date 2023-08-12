use crate::types::Type;
use std::error::Error;
use std::fmt;
use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeInferError {
    UnifyError(Type, Type),
    OccurError(u64, Type),
    UnimplementedOperatorError(String),
    UndefinedVariable(String),
    UndefinedType(String),
    TypeAlreadyDefined(String),
    InvalidArgumentPatternError(usize, usize),
    VariantDoesNotHaveConstructor(Type, String),
    ExpectedVariatButGot(Type),
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
            Self::InvalidArgumentPatternError(expected, fact) => {
                write!(
                    f,
                    "type error: {} arguments were expected but got {}.",
                    expected, fact
                )
            }
            Self::ExpectedVariatButGot(ty) => {
                write!(f, "type error: expected variant but got {}", ty)
            }
            Self::VariantDoesNotHaveConstructor(ty, name) => {
                write!(f, "type error: {} does not have constructor {}", ty, name)
            }
            Self::UndefinedType(ty) => {
                write!(f, "type error: {} is an undefined type", ty)
            }
            Self::TypeAlreadyDefined(name) => {
                write!(f, "type error: type name {} is already used", name)
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
    NotMatchAnyPattern,
    RecursionLimitExceeded,
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
            Self::NotMatchAnyPattern => {
                write!(f, "does not match any pattern")
            }
            Self::RecursionLimitExceeded => {
                write!(f, "recursion limit exceeded")
            }
        }
    }
}

impl Error for EvalError {}
