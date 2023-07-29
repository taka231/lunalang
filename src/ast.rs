use crate::types::Type;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Expr_<Ty, Span> {
    EInt(i64),
    EBinOp(String, Box<Expr<Ty, Span>>, Box<Expr<Ty, Span>>),
    EUnary(String, Box<Expr<Ty, Span>>),
    EIf(
        Box<Expr<Ty, Span>>,
        Box<Expr<Ty, Span>>,
        Box<Expr<Ty, Span>>,
    ),
    EVar(String),
    EFun(String, Box<Expr<Ty, Span>>),
    EFunApp(Box<Expr<Ty, Span>>, Box<Expr<Ty, Span>>),
    EString(String),
    EUnit,
    EBlockExpr(Vec<StatementOrExpr<Ty, Span>>),
    EVector(Vec<Expr<Ty, Span>>),
    EMatch(
        Box<Expr<Ty, Span>>,
        Vec<(Pattern<Ty, Span>, Expr<Ty, Span>)>,
    ),
}

pub type Expr<Ty, Span> = Annot<Ty, Span, Expr_<Ty, Span>>;

pub type UntypedExpr = Expr<(), ()>;

impl UntypedExpr {
    pub fn e_int(i: i64) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EInt(i),
        }
    }
    pub fn e_block_expr(v: Vec<UntypedStatementOrExpr>) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EBlockExpr(v),
        }
    }
    pub fn e_vector(v: Vec<Self>) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EVector(v),
        }
    }
    pub fn bin_op(op: &str, e1: Self, e2: Self) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EBinOp(op.to_string(), Box::new(e1), Box::new(e2)),
        }
    }

    pub fn e_if(cond: Self, e1: Self, e2: Self) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EIf(Box::new(cond), Box::new(e1), Box::new(e2)),
        }
    }

    pub fn e_var(str: &str) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EVar(str.to_string()),
        }
    }

    pub fn e_fun(str: &str, e: Self) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EFun(str.to_string(), Box::new(e)),
        }
    }

    pub fn fun_app(e1: Self, e2: Self) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EFunApp(Box::new(e1), Box::new(e2)),
        }
    }

    pub fn string(str: &str) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EString(str.to_string()),
        }
    }
    pub fn e_unit() -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EUnit,
        }
    }
    pub fn e_match(e: Self, v: Vec<(UntypedPattern, UntypedExpr)>) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EMatch(Box::new(e), v),
        }
    }
    pub fn e_unary(op: &str, e: Self) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Expr_::EUnary(op.to_string(), Box::new(e)),
        }
    }
}

pub type TypedExpr = Expr<Type, ()>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Annot<Ty, Span, Inner> {
    pub ty: Ty,
    pub span: Span,
    pub inner: Inner,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Pattern_<Ty, Span> {
    PValue(Expr<Ty, Span>),
    PConstructor(String, Vec<Pattern<Ty, Span>>),
    PVar(String),
}

pub type Pattern<Ty, Span> = Annot<Ty, Span, Pattern_<Ty, Span>>;

pub type UntypedPattern = Pattern<(), ()>;

impl UntypedPattern {
    pub fn p_value(e: UntypedExpr) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Pattern_::PValue(e),
        }
    }
    pub fn p_constructor(name: &str, v: Vec<Self>) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Pattern_::PConstructor(name.to_string(), v),
        }
    }
    pub fn p_var(name: &str) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Pattern_::PVar(name.to_string()),
        }
    }
}

pub type TypedPattern = Pattern<Type, ()>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Statement_<Ty, Span> {
    Assign(String, Expr<Ty, Span>),
    TypeDef(String, Vec<ConstructorDef>),
}

pub type Statement<Ty, Span> = Annot<(), Span, Statement_<Ty, Span>>;
pub type UntypedStatement = Statement<(), ()>;

impl UntypedStatement {
    pub fn assign(name: &str, e: UntypedExpr) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Statement_::Assign(name.to_string(), e),
        }
    }
    pub fn type_def(name: &str, v: Vec<ConstructorDef>) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: Statement_::TypeDef(name.to_string(), v),
        }
    }
}

pub type TypedStatement = Statement<Type, ()>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ConstructorDef {
    pub name: String,
    pub args: Vec<Type>,
}

pub type Statements<Ty, Span> = Vec<Statement<Ty, Span>>;

pub type UntypedStatements = Statements<(), ()>;
pub type TypedStatements = Statements<Type, ()>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum StatementOrExpr_<Ty, Span> {
    Statement(Statement<Ty, Span>),
    Expr(Expr<Ty, Span>),
}

pub type StatementOrExpr<Ty, Span> = Annot<Ty, Span, StatementOrExpr_<Ty, Span>>;
pub type UntypedStatementOrExpr = StatementOrExpr<(), ()>;

impl UntypedStatementOrExpr {
    pub fn statement(s: UntypedStatement) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: StatementOrExpr_::Statement(s),
        }
    }
    pub fn expr(e: UntypedExpr) -> Self {
        Annot {
            ty: (),
            span: (),
            inner: StatementOrExpr_::Expr(e),
        }
    }
}

pub type TypedStatementOrExpr = StatementOrExpr<Type, ()>;
