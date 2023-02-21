use crate::typeinfer::Type;

pub trait Error {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeInferError {
    UnifyError(Type, Type),
    OccurError(u64, Type),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    InternalTypeError,
    UnimplementedOperatorError(String),
}
