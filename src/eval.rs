use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{Expr, Statement, Statements};
use crate::error::EvalError;
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum Value {
    VInt(i64),
    VBool(bool),
    VFun(String, Expr, Environment),
    VString(String),
}

fn v_int(n: i64) -> Value {
    Value::VInt(n)
}

fn v_bool(b: bool) -> Value {
    Value::VBool(b)
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub struct Environment {
    env: HashMap<String, Value>,
    outer: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            env: HashMap::new(),
            outer: None,
        }
    }
    pub fn get(&self, name: &str) -> Result<Value, EvalError> {
        match self.env.get(name) {
            Some(value) => Ok(value.clone()),
            None => match &self.outer {
                None => Err(EvalError::UndefinedVariable(name.to_owned())),
                Some(env) => env.borrow().get(name),
            },
        }
    }
    pub fn insert(&mut self, name: String, val: Value) {
        self.env.insert(name, val);
    }
    pub fn new_enclosed_env(env: Rc<RefCell<Environment>>) -> Self {
        Environment {
            env: HashMap::new(),
            outer: Some(env),
        }
    }
}

pub struct Eval {
    env: Rc<RefCell<Environment>>,
}

impl Eval {
    pub fn new() -> Eval {
        let env = Environment::new();
        Eval {
            env: Rc::new(RefCell::new(env)),
        }
    }
    fn from(env: Environment) -> Eval {
        Eval {
            env: Rc::new(RefCell::new(env)),
        }
    }
    pub fn eval_expr(&self, ast: Expr) -> Result<Value, EvalError> {
        match ast {
            Expr::EBinOp(op, e1, e2) => {
                let v1 = self.eval_expr(*e1)?;
                let v2 = self.eval_expr(*e2)?;
                match (v1, v2) {
                    (Value::VInt(n1), Value::VInt(n2)) => match &op as &str {
                        "+" => Ok(v_int(n1 + n2)),
                        "-" => Ok(v_int(n1 - n2)),
                        "*" => Ok(v_int(n1 * n2)),
                        "/" => Ok(v_int(n1 / n2)),
                        "<" => Ok(v_bool(n1 < n2)),
                        ">" => Ok(v_bool(n1 > n2)),
                        "<=" => Ok(v_bool(n1 <= n2)),
                        ">=" => Ok(v_bool(n1 >= n2)),
                        "==" => Ok(v_bool(n1 == n2)),
                        "!=" => Ok(v_bool(n1 != n2)),
                        _ => Err(EvalError::UnimplementedOperatorError(op)),
                    },
                    (_, _) => Err(EvalError::InternalTypeError),
                }
            }
            Expr::EInt(n) => Ok(v_int(n)),
            Expr::EIf(cond, e1, e2) => {
                let cond = self.eval_expr(*cond)?;
                match cond {
                    Value::VBool(true) => self.eval_expr(*e1),
                    Value::VBool(false) => self.eval_expr(*e2),
                    _ => Err(EvalError::InternalTypeError),
                }
            }
            Expr::EVar(ident) => self.env.borrow().get(&ident),
            Expr::EFun(arg, e) => Ok(Value::VFun(
                arg,
                *e,
                Environment::new_enclosed_env(Rc::clone(&self.env)),
            )),
            Expr::EFunApp(e1, e2) => {
                let v1 = self.eval_expr(*e1)?;
                let v2 = self.eval_expr(*e2)?;
                match v1 {
                    Value::VFun(arg, expr, env) => {
                        let eval = Eval::from(env);
                        eval.env.borrow_mut().insert(arg, v2);
                        eval.eval_expr(expr)
                    }
                    _ => Err(EvalError::InternalTypeError),
                }
            }
            Expr::EString(str) => Ok(Value::VString(str)),
            Expr::EUnit => todo!(),
        }
    }
    pub fn eval_statement(&self, ast: Statement) -> Result<(), EvalError> {
        match ast {
            Statement::Assign(name, e) => {
                let val = self.eval_expr(e)?;
                Ok(self.env.borrow_mut().insert(name, val))
            }
        }
    }
    pub fn eval_statements(&self, asts: Statements) -> Result<(), EvalError> {
        for ast in asts {
            self.eval_statement(ast)?;
        }
        Ok(())
    }
    pub fn eval_main(&self) -> Result<Value, EvalError> {
        self.env.borrow().get("main")
    }
}

fn test_eval_expr_helper(str: &str, v: Result<Value, EvalError>) {
    use crate::parser::parser_expr;
    let eval = Eval::new();
    assert_eq!(eval.eval_expr(parser_expr(str).unwrap().1), v)
}

#[test]
fn test_op_expr() {
    test_eval_expr_helper("3*3+4*4", Ok(v_int(25)));
    test_eval_expr_helper("4+(6/3)-2", Ok(v_int(4)));
    test_eval_expr_helper("2+4/2/2", Ok(v_int(3)));
    test_eval_expr_helper("3>2", Ok(v_bool(true)));
    test_eval_expr_helper("3<2", Ok(v_bool(false)));
    test_eval_expr_helper("2>=2", Ok(v_bool(true)));
    test_eval_expr_helper("2<=3", Ok(v_bool(true)));
    test_eval_expr_helper("2==3", Ok(v_bool(false)));
    test_eval_expr_helper("2!=3", Ok(v_bool(true)));
}

#[test]
fn test_if_expr() {
    test_eval_expr_helper("if (3>2) 1 else 2", Ok(v_int(1)));
    test_eval_expr_helper("if (3<2) 1 else 2", Ok(v_int(2)));
    test_eval_expr_helper("if (3<2) 1 else if (4==4) 2 else 3", Ok(v_int(2)));
}

#[test]
fn test_string_expr() {
    test_eval_expr_helper(
        r#""Hello, world!""#,
        Ok(Value::VString("Hello, world!".to_owned())),
    )
}

fn test_eval_statements_helper(str: &str, v: Result<Value, EvalError>) {
    use crate::parser::parser_statements;
    let mut eval = Eval::new();
    eval.eval_statements(parser_statements(str).unwrap().1);
    assert_eq!(eval.eval_main(), v)
}

#[test]
fn test_eval_statements() {
    test_eval_statements_helper("let main = 4;", Ok(v_int(4)));
    test_eval_statements_helper("let a = 3; let b = 4; let main = a + b;", Ok(v_int(7)));
    test_eval_statements_helper("let add(a, b) = a + b; let main = add(2, 3);", Ok(v_int(5)));
}

#[test]
fn test_high_order_function() {
    test_eval_statements_helper(
        "let double(f, x) = f(f(x)); let succ(n) = n + 1; let main = double(succ, 3);",
        Ok(v_int(5)),
    );
}

#[test]
fn test_recursive_function() {
    test_eval_statements_helper(
        "let fact(n) = if (n==1) 1 else n * fact(n-1); let main = fact(3);",
        Ok(v_int(6)),
    );
    test_eval_statements_helper(
        "let fib(n) = if (n==1) 1 else if (n==2) 1 else fib(n-1) + fib(n-2); let main = fib(5);",
        Ok(v_int(5)),
    );
}
