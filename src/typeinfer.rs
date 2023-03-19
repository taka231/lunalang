use crate::ast::{Expr, Statement, Statements};
use crate::error::TypeInferError;
use std::collections::HashMap;
use std::{cell::RefCell, fmt::Display, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    TInt,
    TBool,
    TFun(Box<Type>, Box<Type>),
    TVar(u64, Rc<RefCell<Option<Type>>>),
}

fn t_fun(t1: Type, t2: Type) -> Type {
    Type::TFun(Box::new(t1), Box::new(t2))
}

impl Type {
    fn simplify(&self) -> Self {
        match self {
            t @ Self::TVar(n, ty) => match (**ty).borrow().clone() {
                Some(ty) => ty.simplify(),
                None => t.clone(),
            },
            Type::TFun(t1, t2) => t_fun(t1.simplify(), t2.simplify()),
            Type::TInt => Type::TInt,
            Type::TBool => Type::TBool,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeEnv {
    env: HashMap<String, Type>,
    outer: Option<Rc<RefCell<TypeEnv>>>,
}

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv {
            env: HashMap::new(),
            outer: None,
        }
    }
    pub fn get(&self, name: String) -> Result<Type, TypeInferError> {
        match self.env.get(&name) {
            Some(ty) => Ok(ty.clone()),
            None => match &self.outer {
                None => Err(TypeInferError::UndefinedVariable(name)),
                Some(env) => env.borrow().get(name),
            },
        }
    }
    pub fn insert(&mut self, name: String, val: Type) {
        self.env.insert(name, val);
    }
    pub fn new_enclosed_env(env: Rc<RefCell<TypeEnv>>) -> Self {
        TypeEnv {
            env: HashMap::new(),
            outer: Some(env),
        }
    }
}

pub struct TypeInfer {
    env: Rc<RefCell<TypeEnv>>,
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
            Type::TFun(t1, t2) => write!(f, "{} -> {}", t1, t2),
        }
    }
}

impl TypeInfer {
    pub fn new() -> Self {
        TypeInfer {
            env: Rc::new(RefCell::new(TypeEnv::new())),
            unassigned_num: 0,
        }
    }
    fn from(env: TypeEnv, unassigned_num: u64) -> Self {
        TypeInfer {
            env: Rc::new(RefCell::new(env)),
            unassigned_num,
        }
    }
    pub fn newTVar(&mut self) -> Type {
        let ty = Type::TVar(self.unassigned_num, Rc::new(RefCell::new(None)));
        self.unassigned_num += 1;
        ty
    }
    pub fn typeinfer_expr(&mut self, ast: &Expr) -> Result<Type, TypeInferError> {
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
            Expr::EVar(ident) => self.env.borrow().get(ident.to_string()),
            Expr::EFun(arg, e) => {
                let mut typeinfer = TypeInfer::from(
                    TypeEnv::new_enclosed_env(Rc::clone(&self.env)),
                    self.unassigned_num,
                );
                let ty = self.newTVar();
                typeinfer
                    .env
                    .borrow_mut()
                    .insert(arg.to_string(), ty.clone());
                let result_ty = typeinfer.typeinfer_expr(e)?;
                self.unassigned_num = typeinfer.unassigned_num;
                Ok(t_fun(ty, result_ty))
            }
        }
    }
    pub fn typeinfer_statement(&mut self, ast: &Statement) -> Result<(), TypeInferError> {
        match ast {
            Statement::Assign(name, e) => {
                let ty = self.newTVar();
                self.env.borrow_mut().insert(name.to_string(), ty.clone());
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
    let mut typeinfer = TypeInfer::new();
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
            Rc::clone(&typeinfer.env)
                .borrow()
                .get(name.to_string())
                .map(|t| t.simplify()),
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
    typeinfer_statements_test_helper(
        "let add(a, b) = a + b;",
        "add",
        Ok(t_fun(Type::TInt, t_fun(Type::TInt, Type::TInt))),
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
        (Type::TFun(tyA1, tyA2), Type::TFun(tyB1, tyB2)) => {
            unify(*tyA1, *tyB1)?;
            unify(*tyA2, *tyB2)
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
        (n, Type::TFun(t1, t2)) => occur(n, *t1) || occur(n, *t2),
    }
}
