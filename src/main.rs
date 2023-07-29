use std::{error::Error, fs::File, io::Read, path::Path};

use argopt;
use lunalang::{eval::Eval, parser::parser_statements, repl::repl, typeinfer::TypeInfer};

#[argopt::cmd]
fn main(file_name: Option<String>) {
    match file_name {
        Some(file_name) => match exec_file(file_name) {
            Ok(_) => return,
            Err(err) => println!("{}", err),
        },
        None => repl(),
    }
}

fn exec_file(file_name: String) -> Result<(), Box<dyn Error>> {
    let path = Path::new(&file_name);
    let display = path.display();

    let mut file = match File::open(&path) {
        Err(why) => panic!("couldn't open {}: {}", display, why),
        Ok(file) => file,
    };

    let mut s = String::new();
    match file.read_to_string(&mut s) {
        Err(why) => panic!("couldn't read {}: {}", display, why),
        Ok(_) => match parser_statements(&s) {
            Err(err) => panic!("{}", err),
            Ok((_, ast)) => {
                let mut typeinfer = TypeInfer::new();
                let ast = typeinfer.typeinfer_statements(&ast)?;
                let eval = Eval::new();
                eval.eval_statements(ast)?;
                Ok(())
            }
        },
    }
}
