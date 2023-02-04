use crate::ast::Expr;
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum Value {
    VInt(i64),
}

fn v_int(n: i64) -> Value {
    Value::VInt(n)
}

pub struct Eval {}

impl Eval {
    fn new() -> Eval {
        Eval {}
    }
    fn eval_expr(&self, ast: Expr) -> Result<Value, &str> {
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
                        _ => Err("unimplemented operator"),
                    },
                }
            }
            Expr::EInt(n) => Ok(v_int(n)),
        }
    }
}

#[test]
fn test_eval_expr() {
    use crate::parser::parser_expr;
    use std::collections::HashMap;
    fn test_eval_expr_helper(str: &str, v: Result<Value, &str>) {
        let hashmap: HashMap<_, _> = vec![
            ("+".to_string(), 6),
            ("-".to_string(), 6),
            ("*".to_string(), 7),
            ("/".to_string(), 7),
        ]
        .iter()
        .map(|x| x.clone())
        .collect();
        let eval = Eval::new();
        assert_eq!(eval.eval_expr(parser_expr(str, &hashmap).unwrap().1), v)
    }
    test_eval_expr_helper("3*3+4*4", Ok(v_int(25)));
    test_eval_expr_helper("4+(6/3)-2", Ok(v_int(4)));
}
