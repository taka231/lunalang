use crate::ast::Expr;
use crate::eval::{Eval, Value};
use crate::parser::parser_expr;
use crate::typeinfer::typeinfer_expr;
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
        let mut is_typecheck = false;
        if program.starts_with(":t") {
            program = program[2..].to_string();
            is_typecheck = true;
        }
        let ast = parser_expr(&program);
        match ast {
            Ok((_, ast)) => {
                let ty = typeinfer_expr(&ast);
                if let Err(err) = ty {
                    println!("type error: {}", err);
                    continue;
                }
                if is_typecheck {
                    println!("{:?}", ty.unwrap());
                    continue;
                }
                let result = eval.eval_expr(ast);
                println!("{:?}", result);
            }
            Err(err) => {
                println!("{:?}", err);
            }
        }
    }
}
