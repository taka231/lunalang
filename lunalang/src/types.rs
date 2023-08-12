use std::{cell::RefCell, fmt::Display, rc::Rc};

use crate::error::TypeInferError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    TType(String),
    TFun(Box<Type>, Box<Type>),
    TVar(u64, Rc<RefCell<u64>>, Rc<RefCell<Option<Type>>>),
    TQVar(u64),
    TRecVar(u64),
    TRec(Box<Type>),
    TVector(Box<Type>),
    TRef(Box<Type>),
    TVariant(Vec<(String, Vec<Type>)>),
}

impl Type {
    pub fn ttype(ty: impl Into<String>) -> Type {
        Type::TType(ty.into())
    }

    pub fn variant_to_type(&self, name: &str) -> Result<Vec<Type>, TypeInferError> {
        match self.simplify() {
            Type::TVariant(variants) => variants
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, tys)| tys.clone())
                .ok_or_else(|| {
                    TypeInferError::VariantDoesNotHaveConstructor(self.clone(), name.to_owned())
                }),
            _ => Err(TypeInferError::ExpectedVariatButGot(self.clone())),
        }
    }

    pub fn unfold(&self, ty: &Type) -> Type {
        fn go(t: &Type, ty: &Type) -> Type {
            match t {
                Type::TType(name) => Type::TType(name.clone()),
                Type::TFun(t1, t2) => Type::fun(go(&*t1, ty), go(&*t2, ty)),
                Type::TVar(n, level, r) => Type::TVar(*n, Rc::clone(level), Rc::clone(r)),
                Type::TQVar(n) => Type::TQVar(*n),
                Type::TRecVar(_) => ty.clone(),
                Type::TRec(t) => go(&*t, ty),
                Type::TVector(t) => Type::TVector(Box::new(go(&*t, ty))),
                Type::TRef(t) => Type::TRef(Box::new(go(&*t, ty))),
                Type::TVariant(variants) => Type::TVariant(
                    variants
                        .iter()
                        .map(|(name, tys)| {
                            (name.to_owned(), tys.iter().map(|t| go(&t, ty)).collect())
                        })
                        .collect(),
                ),
            }
        }
        match self.simplify() {
            Type::TRec(t) => go(&t, ty),
            _ => self.clone(),
        }
    }

    pub fn fold_variant(&self) -> Type {
        match self.simplify() {
            Type::TVariant(variants) => {
                for (_, tys) in &variants {
                    for ty in tys {
                        match ty {
                            Type::TRec(_) => {
                                if self == &ty.unfold(ty) {
                                    return ty.clone();
                                }
                            }

                            _ => {}
                        }
                    }
                }
                return Type::TVariant(variants);
            }
            t => t.clone(),
        }
    }

    pub fn fun(t1: Type, t2: Type) -> Type {
        Type::TFun(Box::new(t1), Box::new(t2))
    }

    pub fn simplify(&self) -> Self {
        match self {
            t @ Type::TVar(n, level, ty) => match &*Rc::clone(ty).borrow() {
                Some(ty) => ty.simplify(),
                None => t.clone(),
            },
            Type::TFun(t1, t2) => Type::fun(t1.simplify(), t2.simplify()),
            Type::TQVar(n) => Type::TQVar(*n),
            Type::TVector(ty) => Type::TVector(Box::new(ty.simplify())),
            Type::TRef(ty) => Type::TRef(Box::new(ty.simplify())),
            Type::TType(ty) => Type::TType(ty.to_owned()),
            Type::TVariant(variants) => Type::TVariant(
                variants
                    .iter()
                    .map(|(name, tys)| {
                        (
                            name.to_owned(),
                            tys.iter().map(|ty| ty.simplify()).collect(),
                        )
                    })
                    .collect(),
            ),
            Type::TRecVar(n) => Type::TRecVar(*n),
            Type::TRec(ty) => Type::TRec(Box::new(ty.simplify())),
        }
    }

    pub fn separate_to_args_and_resulttype(&self) -> (Vec<Type>, Type) {
        let mut ty = self.simplify();
        let mut args = vec![];
        loop {
            match ty {
                Self::TFun(ty1, ty2) => {
                    args.push(*ty1);
                    ty = *ty2
                }
                _ => break,
            }
        }
        (args, ty)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.simplify() {
            Type::TVar(n, level, _) => write!(f, "_a{}({})", n, level.borrow()),
            Type::TFun(t1, t2) => write!(f, "({}) -> {}", t1, t2),
            Type::TQVar(n) => write!(f, "a{}", n),
            Type::TVector(ty) => write!(f, "Vector[{}]", ty),
            Type::TRef(ty) => write!(f, "Ref[{}]", ty),
            Type::TType(ty) => write!(f, "{}", ty),
            Type::TVariant(variants) => write!(
                f,
                "<{}>",
                variants
                    .iter()
                    .map(|(name, tys)| {
                        format!(
                            "{}({})",
                            name,
                            tys.iter()
                                .map(|ty| ty.to_string())
                                .collect::<Vec<String>>()
                                .join(", ")
                        )
                    })
                    .collect::<Vec<String>>()
                    .join(" | ")
            ),
            Type::TRecVar(n) => write!(f, "_rec{}", n),
            Type::TRec(ty) => write!(f, "μ({})", ty),
        }
    }
}
