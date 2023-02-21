use std::{borrow::Borrow, cell::RefCell, rc::Rc};

use crate::ast::Expr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    TInt,
    TBool,
    TVar(u64, Rc<RefCell<Option<Type>>>),
}

pub fn typeinfer_expr(ast: &Expr) -> Result<Type, String> {
    match ast {
        Expr::EInt(_) => Ok(Type::TInt),
        Expr::EBinOp(op, e1, e2) => match &op as &str {
            "+" | "-" | "*" | "/" => {
                unify(Type::TInt, typeinfer_expr(e1)?)?;
                unify(Type::TInt, typeinfer_expr(e2)?)?;
                Ok(Type::TInt)
            }
            "<" | ">" | "<=" | ">=" | "==" | "!=" => {
                unify(Type::TInt, typeinfer_expr(e1)?)?;
                unify(Type::TInt, typeinfer_expr(e2)?)?;
                Ok(Type::TBool)
            }
            _ => Err("unimplemented operator".to_string()),
        },
        Expr::EIf(cond, e1, e2) => {
            unify(Type::TBool, typeinfer_expr(cond)?)?;
            let t = typeinfer_expr(e1)?;
            unify(t.clone(), typeinfer_expr(e2)?)?;
            Ok(t)
        }
    }
}

#[test]
fn typeinfer_expr_test() {
    use crate::parser::parser_expr;
    assert_eq!(
        typeinfer_expr(&parser_expr("1+1").unwrap().1),
        Ok(Type::TInt)
    );
    assert_eq!(
        typeinfer_expr(&parser_expr("3<2").unwrap().1),
        Ok(Type::TBool)
    );
    assert_eq!(
        typeinfer_expr(&parser_expr("if (3>2) 1 else 2").unwrap().1),
        Ok(Type::TInt)
    );
    assert_eq!(
        typeinfer_expr(&parser_expr("if (3>2) 1 else 3>2").unwrap().1),
        Err("unify error!".to_string())
    );
}

fn unify(t1: Type, t2: Type) -> Result<(), String> {
    match (t1, t2) {
        (t1, t2) if t1 == t2 => Ok(()),
        (Type::TVar(n1, _), Type::TVar(n2, _)) if n1 == n2 => Ok(()),
        (Type::TVar(_, t1), t2) if (*t1).borrow().is_some() => unify(unwrap_all(t1), t2),
        (t1, Type::TVar(_, t2)) if (*t2).borrow().is_some() => unify(t1, unwrap_all(t2)),
        (Type::TVar(n1, t1), t2) => {
            if occur(n1, t2.clone()) {
                Err("occur error!".to_string())
            } else {
                *(*t1).borrow_mut() = Some(t2);
                Ok(())
            }
        }
        (t1, Type::TVar(n2, t2)) => {
            if occur(n2, t1.clone()) {
                Err("occur error!".to_string())
            } else {
                *(*t2).borrow_mut() = Some(t1);
                Ok(())
            }
        }
        (t1, t2) => Err("unify error!".to_string()),
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
