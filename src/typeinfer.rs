use crate::ast::{ConstructorDef, Expr, Pattern, Statement, StatementOrExpr, Statements};
use crate::error::TypeInferError;
use std::collections::HashMap;
use std::fmt::write;
use std::{cell::RefCell, fmt::Display, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    TType(String),
    TFun(Box<Type>, Box<Type>),
    TVar(u64, Rc<RefCell<u64>>, Rc<RefCell<Option<Type>>>),
    TQVar(u64),
    TVector(Box<Type>),
    TRef(Box<Type>),
}

impl Type {
    fn ttype(ty: impl Into<String>) -> Type {
        Type::TType(ty.into())
    }
}

fn t_fun(t1: Type, t2: Type) -> Type {
    Type::TFun(Box::new(t1), Box::new(t2))
}

impl Type {
    fn simplify(&self) -> Self {
        match self {
            t @ Type::TVar(n, level, ty) => match &*Rc::clone(ty).borrow() {
                Some(ty) => ty.simplify(),
                None => t.clone(),
            },
            Type::TFun(t1, t2) => t_fun(t1.simplify(), t2.simplify()),
            Type::TQVar(n) => Type::TQVar(*n),
            Type::TVector(ty) => Type::TVector(Box::new(ty.simplify())),
            Type::TRef(ty) => Type::TRef(Box::new(ty.simplify())),
            Type::TType(ty) => Type::TType(ty.to_owned()),
        }
    }

    fn unwrap_all(t: Rc<RefCell<Option<Type>>>) -> Type {
        (*t).borrow().as_ref().unwrap().clone()
    }

    fn separate_to_args_and_resulttype(&self) -> (Vec<Type>, Type) {
        let mut ty = self.simplify();
        let mut args = vec![];
        loop {
            match ty {
                Self::TFun(ty1, ty2) => {
                    args.push(*ty1);
                    ty = *ty2
                }
                _ => break,
            }
        }
        (args, ty)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeEnv {
    env: HashMap<String, Type>,
    outer: Option<Rc<RefCell<TypeEnv>>>,
    builtin: HashMap<String, Type>,
}

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv {
            env: HashMap::new(),
            outer: None,
            builtin: TypeEnv::builtin(),
        }
    }
    pub fn get(&self, name: &str) -> Result<Type, TypeInferError> {
        match self.env.get(name) {
            Some(ty) => Ok(ty.clone()),
            None => match &self.outer {
                None => match self.builtin.get(name) {
                    Some(ty) => Ok(ty.clone()),
                    None => Err(TypeInferError::UndefinedVariable(name.to_owned())),
                },
                Some(env) => env.borrow().get(name),
            },
        }
    }
    pub fn insert(&mut self, name: String, val: Type) {
        self.env.insert(name, val);
    }
    pub fn new_enclosed_env(env: Rc<RefCell<TypeEnv>>) -> Self {
        TypeEnv {
            env: HashMap::new(),
            outer: Some(env),
            builtin: TypeEnv::builtin(),
        }
    }
    fn builtin() -> HashMap<String, Type> {
        let mut builtin = HashMap::new();
        builtin.insert(
            "puts".to_owned(),
            t_fun(Type::ttype("String"), Type::ttype("()")),
        );
        builtin.insert(
            "foreach".to_owned(),
            t_fun(
                t_fun(Type::TQVar(0), Type::ttype("()")),
                t_fun(Type::TVector(Box::new(Type::TQVar(0))), Type::ttype("()")),
            ),
        );
        builtin.insert(
            "int_to_string".to_owned(),
            t_fun(Type::ttype("Int"), Type::ttype("String")),
        );
        builtin.insert(
            "enum_from_until".to_owned(),
            t_fun(
                Type::ttype("Int"),
                t_fun(
                    Type::ttype("Int"),
                    Type::TVector(Box::new(Type::ttype("Int"))),
                ),
            ),
        );
        builtin.insert(
            "enum_from_to".to_owned(),
            t_fun(
                Type::ttype("Int"),
                t_fun(
                    Type::ttype("Int"),
                    Type::TVector(Box::new(Type::ttype("Int"))),
                ),
            ),
        );
        builtin
    }
}

pub struct TypeInfer {
    env: Rc<RefCell<TypeEnv>>,
    unassigned_num: u64,
    level: u64,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.simplify() {
            Type::TVar(n, level, _) => write!(f, "_a{}({})", n, level.borrow()),
            Type::TFun(t1, t2) => write!(f, "({}) -> {}", t1, t2),
            Type::TQVar(n) => write!(f, "a{}", n),
            Type::TVector(ty) => write!(f, "Vector[{}]", ty),
            Type::TRef(ty) => write!(f, "Ref[{}]", ty),
            Type::TType(ty) => write!(f, "{}", ty),
        }
    }
}

impl TypeInfer {
    pub fn new() -> Self {
        TypeInfer {
            env: Rc::new(RefCell::new(TypeEnv::new())),
            unassigned_num: 0,
            level: 0,
        }
    }
    fn from(env: TypeEnv, unassigned_num: u64, level: u64) -> Self {
        TypeInfer {
            env: Rc::new(RefCell::new(env)),
            unassigned_num,
            level,
        }
    }
    pub fn newTVar(&mut self) -> Type {
        let ty = Type::TVar(
            self.unassigned_num,
            Rc::new(RefCell::new(self.level)),
            Rc::new(RefCell::new(None)),
        );
        self.unassigned_num += 1;
        ty
    }
    pub fn typeinfer_expr(&mut self, ast: &Expr) -> Result<Type, TypeInferError> {
        match ast {
            Expr::EInt(_) => Ok(Type::ttype("Int")),
            Expr::EBinOp(op, e1, e2) => match &op as &str {
                "+" | "-" | "*" | "/" | "%" => {
                    unify(&Type::ttype("Int"), &self.typeinfer_expr(e1)?)?;
                    unify(&Type::ttype("Int"), &self.typeinfer_expr(e2)?)?;
                    Ok(Type::ttype("Int"))
                }
                "<" | ">" | "<=" | ">=" | "==" | "!=" => {
                    unify(&Type::ttype("Int"), &self.typeinfer_expr(e1)?)?;
                    unify(&Type::ttype("Int"), &self.typeinfer_expr(e2)?)?;
                    Ok(Type::ttype("Bool"))
                }
                ":=" => {
                    let ty = self.newTVar();
                    unify(&Type::TRef(Box::new(ty.clone())), &self.typeinfer_expr(e1)?)?;
                    unify(&ty, &self.typeinfer_expr(e2)?)?;
                    Ok(Type::ttype("()"))
                }
                _ => Err(TypeInferError::UnimplementedOperatorError(op.clone())),
            },
            Expr::EIf(cond, e1, e2) => {
                unify(&Type::ttype("Bool"), &self.typeinfer_expr(cond)?)?;
                let t = self.typeinfer_expr(e1)?;
                unify(&t, &self.typeinfer_expr(e2)?)?;
                Ok(t)
            }
            Expr::EVar(ident) => {
                let ty = self.env.borrow().get(ident)?;
                Ok(self.instantiate(&ty))
            }
            Expr::EFun(arg, e) => {
                let mut typeinfer = TypeInfer::from(
                    TypeEnv::new_enclosed_env(Rc::clone(&self.env)),
                    self.unassigned_num,
                    self.level,
                );
                let ty = typeinfer.newTVar();
                typeinfer
                    .env
                    .borrow_mut()
                    .insert(arg.to_string(), ty.clone());
                let result_ty = typeinfer.typeinfer_expr(e)?;
                self.unassigned_num = typeinfer.unassigned_num;
                Ok(t_fun(ty, result_ty))
            }
            Expr::EFunApp(e1, e2) => {
                let t1 = self.typeinfer_expr(e1)?;
                let t2 = self.typeinfer_expr(e2)?;
                let t3 = self.newTVar();
                unify(&t1, &t_fun(t2, t3.clone()))?;
                Ok(t3)
            }
            Expr::EString(_) => Ok(Type::ttype("String")),
            Expr::EUnit => Ok(Type::ttype("()")),
            Expr::EBlockExpr(asts) => {
                let mut typeinfer = TypeInfer::from(
                    TypeEnv::new_enclosed_env(Rc::clone(&self.env)),
                    self.unassigned_num,
                    self.level,
                );
                if asts.len() > 1 {
                    for i in 0..(asts.len() - 1) {
                        match &asts[i] {
                            StatementOrExpr::Expr(e) => {
                                typeinfer.typeinfer_expr(&e)?;
                            }
                            StatementOrExpr::Statement(stmt) => {
                                typeinfer.typeinfer_statement(&stmt)?
                            }
                        }
                    }
                }
                let ty = match &asts[asts.len() - 1] {
                    StatementOrExpr::Expr(e) => typeinfer.typeinfer_expr(&e)?,
                    StatementOrExpr::Statement(stmt) => {
                        typeinfer.typeinfer_statement(&stmt)?;
                        Type::ttype("()")
                    }
                };
                self.unassigned_num = typeinfer.unassigned_num;
                Ok(ty)
            }
            Expr::EVector(exprs) => {
                let ty = self.newTVar();
                for expr in exprs {
                    unify(&ty, &self.typeinfer_expr(expr)?)?;
                }
                Ok(Type::TVector(Box::new(ty)))
            }
            Expr::EUnary(op, e) => {
                let ty = self.typeinfer_expr(e)?;
                match &op as &str {
                    "-" => {
                        unify(&Type::ttype("Int"), &ty)?;
                        Ok(Type::ttype("Int"))
                    }
                    "*" => {
                        let newtvar = self.newTVar();

                        unify(&Type::TRef(Box::new(newtvar.clone())), &ty)?;
                        Ok(newtvar)
                    }
                    "&" => {
                        let newtvar = self.newTVar();
                        unify(&newtvar, &ty)?;
                        Ok(Type::TRef(Box::new(newtvar)))
                    }
                    op => Err(TypeInferError::UnimplementedOperatorError(op.to_owned())),
                }
            }
            Expr::EMatch(expr, match_arms) => {
                let ty = self.typeinfer_expr(expr)?;
                if match_arms.len() == 0 {
                    return Ok(ty);
                }
                let result_ty = self.newTVar();
                for (pattern, expr) in match_arms {
                    let mut typeinfer = TypeInfer::from(
                        TypeEnv::new_enclosed_env(Rc::clone(&self.env)),
                        self.unassigned_num,
                        self.level,
                    );
                    typeinfer.typeinfer_pattern(&pattern, &ty)?;
                    unify(&result_ty, &typeinfer.typeinfer_expr(expr)?)?;
                    self.unassigned_num = typeinfer.unassigned_num
                }
                Ok(result_ty)
            }
        }
    }
    fn typeinfer_expr_levelup(&mut self, ast: &Expr) -> Result<Type, TypeInferError> {
        self.level += 1;
        let ty = self.typeinfer_expr(ast)?;
        self.level -= 1;
        Ok(ty)
    }

    fn typeinfer_pattern(&mut self, pattern: &Pattern, ty: &Type) -> Result<(), TypeInferError> {
        match pattern {
            Pattern::PValue(value) => unify(&self.typeinfer_expr(value)?, ty)?,
            Pattern::PConstructor(name, patterns) => {
                let constructor_ty = self.env.borrow().get(&name)?;
                let (args, result) = constructor_ty.separate_to_args_and_resulttype();
                if args.len() != patterns.len() {
                    return Err(TypeInferError::InvalidArgumentPatternError(
                        args.len(),
                        patterns.len(),
                    ));
                }
                for i in 0..args.len() {
                    self.typeinfer_pattern(&patterns[i], &args[i])?;
                }
                unify(&result, ty)?;
            }
            Pattern::PVar(var_name) => {
                let new_type = self.newTVar();
                unify(&new_type, ty)?;
                self.env.borrow_mut().insert(var_name.clone(), new_type)
            }
        };
        Ok(())
    }

    pub fn typeinfer_statement(&mut self, ast: &Statement) -> Result<(), TypeInferError> {
        match ast {
            Statement::Assign(name, e) => {
                let ty = self.newTVar();
                self.env.borrow_mut().insert(name.to_string(), ty.clone());
                let inferred_ty = self.typeinfer_expr_levelup(e)?;
                unify(&ty, &inferred_ty)?;
                self.generalize(&ty);
            }
            Statement::TypeDef(type_name, constructor_def_vec) => {
                for ConstructorDef { name, args } in constructor_def_vec {
                    self.env.borrow_mut().insert(
                        name.to_owned(),
                        args.iter()
                            .rev()
                            .fold(Type::ttype(type_name), |acm, ty| t_fun(ty.clone(), acm)),
                    )
                }
            }
        }
        Ok(())
    }
    pub fn typeinfer_statements(&mut self, asts: &Statements) -> Result<(), TypeInferError> {
        for ast in asts {
            self.typeinfer_statement(ast)?;
        }
        Ok(())
    }

    fn instantiate(&mut self, ty: &Type) -> Type {
        let ty = ty.simplify();
        fn go(ty: Type, map: &mut HashMap<u64, Type>, self_: &mut TypeInfer) -> Type {
            match ty {
                Type::TQVar(n) => match map.get(&n) {
                    Some(t) => t.clone(),
                    None => {
                        let ty = self_.newTVar();
                        map.insert(n, ty.clone());
                        ty
                    }
                },
                Type::TFun(t1, t2) => t_fun(go(*t1, map, self_), go(*t2, map, self_)),
                t @ Type::TVar(_, _, _) => t,
                Type::TVector(ty) => Type::TVector(Box::new(go(*ty, map, self_))),
                Type::TRef(ty) => Type::TRef(Box::new(go(*ty, map, self_))),
                Type::TType(ty) => Type::TType(ty),
            }
        }
        go(ty, &mut HashMap::new(), self)
    }
    fn generalize(&self, ty: &Type) {
        match ty.simplify() {
            Type::TVar(n, level, r) if *level.borrow() > self.level => {
                *(*r).borrow_mut() = Some(Type::TQVar(n))
            }
            Type::TVar(_, _, _) => (),
            Type::TFun(t1, t2) => {
                self.generalize(&*t1);
                self.generalize(&*t2);
            }
            Type::TVector(t1) => self.generalize(&*t1),
            Type::TQVar(_) => (),
            Type::TRef(ty) => self.generalize(&ty),
            Type::TType(_) => (),
        }
    }
}

#[test]
fn typeinfer_expr_test() {
    use crate::parser::parser_expr;
    let mut typeinfer = TypeInfer::new();
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("1+1").unwrap().1),
        Ok(Type::ttype("Int"))
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("3<2").unwrap().1),
        Ok(Type::ttype("Bool"))
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("1%1").unwrap().1),
        Ok(Type::ttype("Int"))
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("if (3>2) 1 else 2").unwrap().1),
        Ok(Type::ttype("Int"))
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("if (3>2) 1 else 3>2").unwrap().1),
        Err(TypeInferError::UnifyError(
            Type::ttype("Int"),
            Type::ttype("Bool")
        ))
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&Expr::EString("hoge".to_owned())),
        Ok(Type::ttype("String"))
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("()").unwrap().1),
        Ok(Type::ttype("()"))
    );
    assert_eq!(
        typeinfer
            .typeinfer_expr(&parser_expr(r#"puts("Hello, world!")"#).unwrap().1)
            .map(|ty| ty.simplify()),
        Ok(Type::ttype("()"))
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("{let x = 1; x == 1;}").unwrap().1),
        Ok(Type::ttype("Bool"))
    );
    assert_eq!(
        typeinfer.typeinfer_expr(&parser_expr("{let x = 1;}").unwrap().1),
        Ok(Type::ttype("()"))
    );
    assert_eq!(
        typeinfer
            .typeinfer_expr(&parser_expr("[1, 2, 3]").unwrap().1)
            .map(|t| t.simplify()),
        Ok(Type::TVector(Box::new(Type::ttype("Int"))))
    );
    assert_eq!(
        typeinfer
            .typeinfer_expr(&parser_expr("-1").unwrap().1)
            .map(|t| t.simplify()),
        Ok(Type::ttype("Int"))
    );
    assert_eq!(
        typeinfer
            .typeinfer_expr(&parser_expr("&3").unwrap().1)
            .map(|t| t.simplify()),
        Ok(Type::TRef(Box::new(Type::ttype("Int"))))
    );
    assert_eq!(
        typeinfer
            .typeinfer_expr(&parser_expr("*(&1)").unwrap().1)
            .map(|t| t.simplify()),
        Ok(Type::ttype("Int"))
    );
    assert_eq!(
        typeinfer
            .typeinfer_expr(&parser_expr("&3:=4").unwrap().1)
            .map(|t| t.simplify()),
        Ok(Type::ttype("()"))
    );
}

fn typeinfer_statements_test_helper(str: &str, name: &str, ty: Result<Type, TypeInferError>) {
    use crate::parser::parser_statements;
    let mut typeinfer = TypeInfer::new();
    typeinfer.typeinfer_statements(&parser_statements(str).unwrap().1);
    assert_eq!(
        Rc::clone(&typeinfer.env)
            .borrow()
            .get(name)
            .map(|t| t.simplify()),
        ty
    )
}

#[test]
fn typeinfer_statements_test() {
    typeinfer_statements_test_helper("let a = 1;", "a", Ok(Type::ttype("Int")));
    typeinfer_statements_test_helper("let a = 1; let b = a + 1;", "b", Ok(Type::ttype("Int")));
}

#[test]
fn typeinfer_if_test() {
    typeinfer_statements_test_helper(
        "let a = 1; let b = if (a == 1) 3 > 2 else 4 < 2;",
        "b",
        Ok(Type::ttype("Bool")),
    );
}

#[test]
fn typeinfer_fun_test() {
    typeinfer_statements_test_helper(
        "let add(a, b) = a + b;",
        "add",
        Ok(t_fun(
            Type::ttype("Int"),
            t_fun(Type::ttype("Int"), Type::ttype("Int")),
        )),
    );
    typeinfer_statements_test_helper(
        "let add(a, b) = a + b; let a = add(2, 3);",
        "a",
        Ok(Type::ttype("Int")),
    );
    typeinfer_statements_test_helper("let id(x) = x; let a = id(2);", "a", Ok(Type::ttype("Int")));
    typeinfer_statements_test_helper(
        "let id(x) = x; let a = id(2);",
        "id",
        Ok(t_fun(Type::TQVar(1), Type::TQVar(1))),
    );
}

#[test]
fn typeinfer_enum_test() {
    typeinfer_statements_test_helper(
        "enum Hoge {Foo(Int)}; let a = Foo;",
        "a",
        Ok(t_fun(Type::ttype("Int"), Type::ttype("Hoge"))),
    )
}

fn unify(t1: &Type, t2: &Type) -> Result<(), TypeInferError> {
    match (t1.simplify(), t2.simplify()) {
        (t1, t2) if t1 == t2 => Ok(()),
        (Type::TVar(n1, level1, _), Type::TVar(n2, level2, _)) if n1 == n2 => Ok(()),
        (Type::TVar(n1, level1, t1), t2) => {
            if occur(n1, &t2) {
                Err(TypeInferError::OccurError(n1, t2))
            } else {
                level_balance(&Type::TVar(n1, level1, Rc::clone(&t1)), &t2);
                *(*t1).borrow_mut() = Some(t2);
                Ok(())
            }
        }
        (t1, Type::TVar(n2, level2, t2)) => {
            if occur(n2, &t1) {
                Err(TypeInferError::OccurError(n2, t1))
            } else {
                level_balance(&t1, &Type::TVar(n2, level2, Rc::clone(&t2)));
                *(*t2).borrow_mut() = Some(t1);
                Ok(())
            }
        }
        (Type::TFun(tyA1, tyA2), Type::TFun(tyB1, tyB2)) => {
            unify(&*tyA1, &*tyB1)?;
            unify(&*tyA2, &*tyB2)
        }
        (Type::TVector(t1), Type::TVector(t2)) => unify(&t1, &t2),
        (Type::TRef(t1), Type::TRef(t2)) => unify(&t1, &t2),
        (t1, t2) => Err(TypeInferError::UnifyError(t1.clone(), t2.clone())),
    }
}

fn occur(n: u64, t: &Type) -> bool {
    match (n, t.simplify()) {
        (_, Type::TType(_)) => false,
        (n, Type::TVar(m, level, _)) if n == m => true,
        (n, Type::TVar(_, level1, t1)) => false,
        (n, Type::TFun(t1, t2)) => occur(n, &t1) || occur(n, &t2),
        (_, Type::TQVar(n)) => false,
        (n, Type::TVector(ty)) => occur(n, &ty),
        (n, Type::TRef(ty)) => occur(n, &ty),
    }
}

fn level_balance(t1: &Type, t2: &Type) {
    match (t1.simplify(), t2.simplify()) {
        (Type::TVar(_, level1, _), Type::TVar(_, level2, _)) => {
            let level1num: u64 = *Rc::clone(&level1).borrow();
            let level2num: u64 = *Rc::clone(&level2).borrow();
            if level1num > level2num {
                *level1.borrow_mut() = level2num;
            } else {
                *level2.borrow_mut() = level1num;
            }
        }
        (_, _) => (),
    }
}
