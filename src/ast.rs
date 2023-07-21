use crate::typeinfer::Type;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Expr {
    EInt(i64),
    EBinOp(String, Box<Expr>, Box<Expr>),
    EUnary(String, Box<Expr>),
    EIf(Box<Expr>, Box<Expr>, Box<Expr>),
    EVar(String),
    EFun(String, Box<Expr>),
    EFunApp(Box<Expr>, Box<Expr>),
    EString(String),
    EUnit,
    EBlockExpr(Vec<StatementOrExpr>),
    EVector(Vec<Expr>),
    EMatch(Box<Expr>, Vec<(Pattern, Expr)>),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Pattern {
    PValue(Expr),
    PConstructor(String, Vec<Pattern>),
    PVar(String),
}

impl Expr {
    pub fn bin_op(op: &str, e1: Expr, e2: Expr) -> Expr {
        Expr::EBinOp(op.to_string(), Box::new(e1), Box::new(e2))
    }

    pub fn e_if(cond: Expr, e1: Expr, e2: Expr) -> Expr {
        Expr::EIf(Box::new(cond), Box::new(e1), Box::new(e2))
    }

    pub fn var(str: &str) -> Expr {
        Expr::EVar(str.to_string())
    }

    pub fn fun(str: &str, e: Expr) -> Expr {
        Expr::EFun(str.to_string(), Box::new(e))
    }

    pub fn fun_app(e1: Expr, e2: Expr) -> Expr {
        Expr::EFunApp(Box::new(e1), Box::new(e2))
    }

    pub fn string(str: &str) -> Expr {
        Expr::EString(str.to_string())
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Statement {
    Assign(String, Expr),
    TypeDef(String, Vec<ConstructorDef>),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ConstructorDef {
    pub name: String,
    pub args: Vec<Type>,
}

pub type Statements = Vec<Statement>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum StatementOrExpr {
    Statement(Statement),
    Expr(Expr),
}
