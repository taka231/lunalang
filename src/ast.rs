#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Expr {
    EInt(i64),
    EVar(String),
    EFunApp(Box<Expr>, Box<Expr>),
}

pub fn e_int(n: i64) -> Expr {
    Expr::EInt(n)
}

pub fn e_var(str: &str) -> Expr {
    Expr::EVar(str.to_string())
}

pub fn e_fun_app(e1: Expr, e2: Expr) -> Expr {
    Expr::EFunApp(Box::new(e1), Box::new(e2))
}
