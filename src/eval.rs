use std::collections::HashMap;

use crate::ast::{Expr, Statement, Statements};
use crate::error::EvalError;
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum Value {
    VInt(i64),
    VBool(bool),
}

fn v_int(n: i64) -> Value {
    Value::VInt(n)
}

fn v_bool(b: bool) -> Value {
    Value::VBool(b)
}

pub struct Environment {
    env: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            env: HashMap::new(),
        }
    }
    pub fn get(&self, name: String) -> Result<Value, EvalError> {
        match self.env.get(&name) {
            Some(value) => Ok(value.clone()),
            None => Err(EvalError::UndefinedVariable(name)),
        }
    }
    pub fn insert(&mut self, name: String, val: Value) {
        self.env.insert(name, val);
    }
}

pub struct Eval {
    env: Environment,
}

impl Eval {
    pub fn new() -> Eval {
        let env = Environment::new();
        Eval { env }
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
        }
    }
    pub fn eval_statement(&mut self, ast: Statement) -> Result<(), EvalError> {
        match ast {
            Statement::Assign(name, e) => {
                let val = self.eval_expr(e)?;
                Ok(self.env.insert(name, val))
            }
        }
    }
    pub fn eval_statements(&mut self, asts: Statements) -> Result<(), EvalError> {
        for ast in asts {
            self.eval_statement(ast)?;
        }
        Ok(())
    }
    pub fn eval_main(&self) -> Result<Value, EvalError> {
        self.env.get("main".to_string())
    }
}

#[test]
fn test_eval_expr() {
    use crate::parser::parser_expr;
    fn test_eval_expr_helper(str: &str, v: Result<Value, EvalError>) {
        let eval = Eval::new();
        assert_eq!(eval.eval_expr(parser_expr(str).unwrap().1), v)
    }
    test_eval_expr_helper("3*3+4*4", Ok(v_int(25)));
    test_eval_expr_helper("4+(6/3)-2", Ok(v_int(4)));
    test_eval_expr_helper("2+4/2/2", Ok(v_int(3)));
    test_eval_expr_helper("3>2", Ok(v_bool(true)));
    test_eval_expr_helper("3<2", Ok(v_bool(false)));
    test_eval_expr_helper("2>=2", Ok(v_bool(true)));
    test_eval_expr_helper("2<=3", Ok(v_bool(true)));
    test_eval_expr_helper("2==3", Ok(v_bool(false)));
    test_eval_expr_helper("2!=3", Ok(v_bool(true)));
    test_eval_expr_helper("if (3>2) 1 else 2", Ok(v_int(1)));
    test_eval_expr_helper("if (3<2) 1 else 2", Ok(v_int(2)));
    test_eval_expr_helper("if (3<2) 1 else if (4==4) 2 else 3", Ok(v_int(2)));
}

#[test]
fn test_eval_statements() {
    use crate::parser::parser_statements;
    fn test_eval_statements_helper(str: &str, v: Result<Value, EvalError>) {
        let mut eval = Eval::new();
        eval.eval_statements(parser_statements(str).unwrap().1);
        assert_eq!(eval.eval_main(), v)
    }
    test_eval_statements_helper("let main = 4;", Ok(v_int(4)));
}
