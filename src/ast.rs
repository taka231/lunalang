#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Expr {
    EInt(i64),
    EBinOp(String, Box<Expr>, Box<Expr>),
    EIf(Box<Expr>, Box<Expr>, Box<Expr>),
    EVar(String),
    EFun(String, Box<Expr>),
    EFunApp(Box<Expr>, Box<Expr>),
    EString(String),
    EUnit,
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

pub fn e_fun(str: &str, e: Expr) -> Expr {
    Expr::EFun(str.to_string(), Box::new(e))
}

pub fn e_fun_app(e1: Expr, e2: Expr) -> Expr {
    Expr::EFunApp(Box::new(e1), Box::new(e2))
}

pub fn e_string(str: &str) -> Expr {
    Expr::EString(str.to_owned())
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
