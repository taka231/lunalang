use crate::ast::Expr;
use crate::eval::{Eval, Value};
use crate::parser::{parser_expr, PRIORITY_HASHMAP};
use std::io;
pub fn repl() {
    println!("Welcome to lunalang repl!");
    let eval = Eval::new();
    loop {
        let mut program = String::new();
        io::stdin()
            .read_line(&mut program)
            .expect("Failed to read line.");
        if program == ":q\n" {
            break;
        }
        let ast = parser_expr(&program, &PRIORITY_HASHMAP);
        match ast {
            Ok((_, ast)) => {
                let result = eval.eval_expr(ast);
                println!("{:?}", result);
            }
            Err(err) => {
                println!("{:?}", err);
            }
        }
    }
}
