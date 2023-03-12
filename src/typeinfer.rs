use crate::ast::{Expr, Statement, Statements};
use crate::error::TypeInferError;
use std::collections::HashMap;
use std::fmt;
use std::{borrow::Borrow, cell::RefCell, fmt::Display, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    TInt,
    TBool,
    TVar(u64, Rc<RefCell<Option<Type>>>),
}

impl Type {
    fn simplify(&self) -> Self {
        match self {
            t @ Self::TVar(n, ty) => match (**ty).borrow().clone() {
                Some(ty) => ty.simplify(),
                None => t.clone(),
            },
            ty => ty.clone(),
        }
    }
}

struct TypeEnv {
    env: HashMap<String, Type>,
}

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv {
            env: HashMap::new(),
        }
    }
    pub fn get(&self, name: String) -> Result<Type, TypeInferError> {
        match self.env.get(&name) {
            Some(ty) => Ok(ty.clone()),
            None => Err(TypeInferError::UndefinedVariable(name)),
        }
    }
    pub fn insert(&mut self, name: String, val: Type) {
        self.env.insert(name, val);
    }
}

pub struct TypeInfer {
    env: TypeEnv,
    unassigned_num: u64,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::TInt => write!(f, "{}", "Int"),
            Type::TBool => write!(f, "{}", "Bool"),
            Type::TVar(n, t) => match *(**t).borrow() {
                Some(ref t) => t.fmt(f),
                None => write!(f, "{}", n),
            },
        }
    }
}

impl TypeInfer {
    pub fn new() -> Self {
        TypeInfer {
            env: TypeEnv::new(),
            unassigned_num: 0,
        }
    }
    pub fn newTVar(&mut self) -> Type {
        let ty = Type::TVar(self.unassigned_num, Rc::new(RefCell::new(None)));
        self.unassigned_num += 1;
        ty
    }
    pub fn typeinfer_expr(&self, ast: &Expr) -> Result<Type, TypeInferError> {
        match ast {
            Expr::EInt(_) => Ok(Type::TInt),
            Expr::EBinOp(op, e1, e2) => match &op as &str {
                "+" | "-" | "*" | "/" => {
                    unify(Type::TInt, self.typeinfer_expr(e1)?)?;
                    unify(Type::TInt, self.typeinfer_expr(e2)?)?;
                    Ok(Type::TInt)
                }
                "<" | ">" | "<=" | ">=" | "==" | "!=" => {
                    unify(Type::TInt, self.typeinfer_expr(e1)?)?;
                    unify(Type::TInt, self.typeinfer_expr(e2)?)?;
                    Ok(Type::TBool)
                }
                _ => Err(TypeInferError::UnimplementedOperatorError(op.clone())),
            },
            Expr::EIf(cond, e1, e2) => {
                unify(Type::TBool, self.typeinfer_expr(cond)?)?;
                let t = self.typeinfer_expr(e1)?;
                unify(t.clone(), self.typeinfer_expr(e2)?)?;
                Ok(t)
            }
            Expr::EVar(ident) => self.env.get(ident.to_string()),
        }
    }
    pub fn typeinfer_statement(&mut self, ast: &Statement) -> Result<(), TypeInferError> {
        match ast {
            Statement::Assign(name, e) => {
                let ty = self.newTVar();
                self.env.insert(name.to_string(), ty.clone());
                let inferred_ty = self.typeinfer_expr(e)?;
                unify(ty, inferred_ty)?;
            }
        }
        Ok(())
    }
    pub fn typeinfer_statements(&mut self, asts: &Statements) -> Result<(), TypeInferError> {
        for ast in asts {
            self.typeinfer_statement(ast)?;
        }
        Ok(())
    }
}

#[test]
fn typeinfer_expr_test() {
    use crate::parser::parser_expr;
    let typeinfer = TypeInfer::new();
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("1+1").unwrap().1),
        Ok(Type::TInt)
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("3<2").unwrap().1),
        Ok(Type::TBool)
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("if (3>2) 1 else 2").unwrap().1),
        Ok(Type::TInt)
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("if (3>2) 1 else 3>2").unwrap().1),
        Err(TypeInferError::UnifyError(Type::TInt, Type::TBool))
    );
}

#[test]
fn typeinfer_statements_test() {
    use crate::parser::parser_statements;
    fn typeinfer_statements_test_helper(str: &str, name: &str, ty: Result<Type, TypeInferError>) {
        let mut typeinfer = TypeInfer::new();
        typeinfer.typeinfer_statements(&parser_statements(str).unwrap().1);
        assert_eq!(
            typeinfer.env.get(name.to_string()).map(|t| t.simplify()),
            ty
        )
    }
    typeinfer_statements_test_helper("let a = 1;", "a", Ok(Type::TInt));
    typeinfer_statements_test_helper("let a = 1; let b = a + 1;", "b", Ok(Type::TInt));
    typeinfer_statements_test_helper(
        "let a = 1; let b = if (a == 1) 3 > 2 else 4 < 2;",
        "b",
        Ok(Type::TBool),
    );
}

fn unify(t1: Type, t2: Type) -> Result<(), TypeInferError> {
    match (t1, t2) {
        (t1, t2) if t1 == t2 => Ok(()),
        (Type::TVar(n1, _), Type::TVar(n2, _)) if n1 == n2 => Ok(()),
        (Type::TVar(_, t1), t2) if (*t1).borrow().is_some() => unify(unwrap_all(t1), t2),
        (t1, Type::TVar(_, t2)) if (*t2).borrow().is_some() => unify(t1, unwrap_all(t2)),
        (Type::TVar(n1, t1), t2) => {
            if occur(n1, t2.clone()) {
                Err(TypeInferError::OccurError(n1, t2))
            } else {
                *(*t1).borrow_mut() = Some(t2);
                Ok(())
            }
        }
        (t1, Type::TVar(n2, t2)) => {
            if occur(n2, t1.clone()) {
                Err(TypeInferError::OccurError(n2, t1))
            } else {
                *(*t2).borrow_mut() = Some(t1);
                Ok(())
            }
        }
        (t1, t2) => Err(TypeInferError::UnifyError(t1, t2)),
    }
}

fn unwrap_all(t: Rc<RefCell<Option<Type>>>) -> Type {
    (*t).borrow().as_ref().unwrap().clone()
}

fn occur(n: u64, t: Type) -> bool {
    match (n, t) {
        (_, Type::TInt) => false,
        (_, Type::TBool) => false,
        (n, Type::TVar(m, _)) if n == m => true,
        (n, Type::TVar(_, t1)) => match *(*t1).borrow() {
            Some(ref t1) => occur(n, t1.clone()),
            None => false,
        },
    }
}
