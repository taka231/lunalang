use crate::ast::{Expr, StatementOrExpr};
use crate::eval::{Eval, Value};
use crate::parser::{keyword, parser_expr, parser_for_repl, parser_statement_or_expr, symbol};
use crate::typeinfer::TypeInfer;
use std::io::{self, Write};

pub struct REPL {
    eval: Eval,
    typeinfer: TypeInfer,
    is_typecheck: bool,
    program: String,
}

impl REPL {
    fn new() -> Self {
        REPL {
            eval: Eval::new(),
            typeinfer: TypeInfer::new(),
            is_typecheck: false,
            program: "".to_string(),
        }
    }
    fn welcome(&self) {
        println!("Welcome to lunalang repl!");
    }
    fn prompt(&self) {
        print!(">>");
        io::stdout().flush().unwrap();
    }
    fn input(&mut self) {
        let mut program = String::new();
        io::stdin()
            .read_line(&mut program)
            .expect("Failed to read line.");
        self.program = program;
        self.is_typecheck = false;
    }
    fn is_quit(&self) -> bool {
        symbol(":q")(&self.program).is_ok()
    }
    fn parse_typecheck(&mut self) {
        let result = symbol(":t")(&self.program);
        match result {
            Ok((input, _)) => {
                self.program = input.to_string();
                self.is_typecheck = true
            }
            Err(_) => self.is_typecheck = false,
        }
    }
}

pub fn repl() {
    let mut repl = REPL::new();
    repl.welcome();
    loop {
        repl.prompt();
        repl.input();
        if repl.is_quit() {
            break;
        }
        repl.parse_typecheck();
        let ast = parser_for_repl(&repl.program);
        match ast {
            Ok((_, StatementOrExpr::Expr(ast))) => {
                let ty = repl.typeinfer.typeinfer_expr(&ast);
                if let Err(err) = ty {
                    println!("{}", err);
                    continue;
                }
                if repl.is_typecheck {
                    println!("{}", ty.unwrap());
                    continue;
                }
                let result = repl.eval.eval_expr(ast);
                println!("{:?}", result);
            }
            Ok((_, StatementOrExpr::Statement(stmt))) => {
                match repl.typeinfer.typeinfer_statement(&stmt) {
                    Ok(()) => match repl.eval.eval_statement(stmt) {
                        Ok(()) => (),
                        Err(err) => println!("{}", err),
                    },
                    Err(err) => println!("{}", err),
                }
            }
            Err(err) => {
                println!("{}", err);
            }
        }
    }
}
