#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Expr {
    EInt(i64),
    EBinOp(String, Box<Expr>, Box<Expr>),
    EIf(Box<Expr>, Box<Expr>, Box<Expr>),
    EVar(String),
}

pub fn e_int(n: i64) -> Expr {
    Expr::EInt(n)
}

pub fn e_bin_op(str: &str, e1: Expr, e2: Expr) -> Expr {
    Expr::EBinOp(str.to_string(), Box::new(e1), Box::new(e2))
}

pub fn e_if(cond: Expr, e1: Expr, e2: Expr) -> Expr {
    Expr::EIf(Box::new(cond), Box::new(e1), Box::new(e2))
}

pub fn e_var(str: &str) -> Expr {
    Expr::EVar(str.to_string())
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Statement {
    Assign(String, Expr),
}

pub type Statements = Vec<Statement>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum StatementOrExpr {
    Statement(Statement),
    Expr(Expr),
}
