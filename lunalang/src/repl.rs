use crate::ast::StatementOrExpr_;
use crate::eval::{Eval, Mode};
use crate::parser::{parser_for_repl, symbol};
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
            eval: Eval::new(Mode::Repl),
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
        match ast.map(|e| (e.0, e.1.inner)) {
            Ok((_, StatementOrExpr_::Expr(ast))) => {
                let ast = repl.typeinfer.typeinfer_expr(&ast, None);
                if let Err(err) = ast {
                    println!("{}", err);
                    continue;
                }
                if repl.is_typecheck {
                    println!("{}", ast.unwrap().ty);
                    continue;
                }
                let result = repl.eval.eval_expr(ast.unwrap());
                match result {
                    Ok(e) => println!("{}", e),
                    Err(err) => println!("{}", err),
                }
            }
            Ok((_, StatementOrExpr_::Statement(stmt))) => {
                match repl.typeinfer.typeinfer_statement(&stmt) {
                    Ok(stmt) => match repl.eval.eval_statement(stmt) {
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
