use actix_web::{get, post, web, App, HttpResponse, HttpServer, Responder};
use dotenv::dotenv;
use lunalang::{eval, parser, typeinfer, types};
use serde::{Deserialize, Serialize};
use std::env;

#[derive(Debug, Serialize, Deserialize)]
struct Program {
    program: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct ProgramResult {
    result: String,
    error: Option<String>,
    stdout: String,
}

#[post("/")]
async fn index(program: web::Json<Program>) -> impl Responder {
    let result: Result<(String, String), String> = (|| {
        let ast = parser::parser_statements(&program.program).map_err(|err| err.to_string())?;
        let mut typeinfer = typeinfer::TypeInfer::new();
        let ast = typeinfer
            .typeinfer_statements(&ast.1)
            .map_err(|err| err.to_string())?;
        let eval = eval::Eval::new(eval::Mode::Playground);
        eval.eval_statements(ast).map_err(|err| err.to_string())?;
        let result = eval
            .eval_main()
            .map(|value| format!("{}", value))
            .map_err(|err| err.to_string())?;
        let stdout = eval.stdout.borrow().clone();
        Ok((result, stdout))
    })();
    let result_json = match result {
        Ok(result) => ProgramResult {
            result: result.0,
            error: None,
            stdout: result.1,
        },
        Err(err) => ProgramResult {
            result: "".to_string(),
            error: Some(err),
            stdout: "".to_string(),
        },
    };
    HttpResponse::Ok().json(result_json)
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    dotenv().ok();
    let address = env::var("ADDRESS").expect("Address is not set.");
    HttpServer::new(|| App::new().service(index))
        .bind(address)?
        .run()
        .await
}
