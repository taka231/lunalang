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
    TRecVar(u64),
    TRec(Box<Type>),
    TVector(Box<Type>),
    TRef(Box<Type>),
    TVariant(Vec<(String, Vec<Type>)>),
}

impl Type {
    fn ttype(ty: impl Into<String>) -> Type {
        Type::TType(ty.into())
    }

    fn variant_to_type(&self, name: &str) -> Result<Vec<Type>, TypeInferError> {
        match self.simplify() {
            Type::TVariant(variants) => variants
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, tys)| tys.clone())
                .ok_or_else(|| {
                    TypeInferError::VariantDoesNotHaveConstructor(self.clone(), name.to_owned())
                }),
            _ => Err(TypeInferError::ExpectedVariatButGot(self.clone())),
        }
    }

    fn unfold(&self, ty: &Type) -> Type {
        fn go(t: &Type, ty: &Type) -> Type {
            match t {
                Type::TType(name) => Type::TType(name.clone()),
                Type::TFun(t1, t2) => t_fun(go(&*t1, ty), go(&*t2, ty)),
                Type::TVar(n, level, r) => Type::TVar(*n, Rc::clone(level), Rc::clone(r)),
                Type::TQVar(n) => Type::TQVar(*n),
                Type::TRecVar(_) => ty.clone(),
                Type::TRec(t) => go(&*t, ty),
                Type::TVector(t) => Type::TVector(Box::new(go(&*t, ty))),
                Type::TRef(t) => Type::TRef(Box::new(go(&*t, ty))),
                Type::TVariant(variants) => Type::TVariant(
                    variants
                        .iter()
                        .map(|(name, tys)| {
                            (name.to_owned(), tys.iter().map(|t| go(&t, ty)).collect())
                        })
                        .collect(),
                ),
            }
        }
        match self.simplify() {
            Type::TRec(t) => go(&t, ty),
            _ => self.clone(),
        }
    }

    fn fold_variant(&self) -> Type {
        match self.simplify() {
            Type::TVariant(variants) => {
                for (_, tys) in &variants {
                    for ty in tys {
                        match ty {
                            Type::TRec(_) => {
                                if self == &ty.unfold(ty) {
                                    return ty.clone();
                                }
                            }

                            _ => {}
                        }
                    }
                }
                return Type::TVariant(variants);
            }
            t => t.clone(),
        }
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
            Type::TVariant(variants) => Type::TVariant(
                variants
                    .iter()
                    .map(|(name, tys)| {
                        (
                            name.to_owned(),
                            tys.iter().map(|ty| ty.simplify()).collect(),
                        )
                    })
                    .collect(),
            ),
            Type::TRecVar(n) => Type::TRecVar(*n),
            Type::TRec(ty) => Type::TRec(Box::new(ty.simplify())),
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeToTypeEnv {
    env: HashMap<String, Type>,
    outer: Option<Rc<RefCell<TypeToTypeEnv>>>,
}

impl TypeToTypeEnv {
    pub fn new() -> Self {
        TypeToTypeEnv {
            env: Self::builtin(),
            outer: None,
        }
    }
    pub fn get(&self, name: &str) -> Result<Type, TypeInferError> {
        match self.env.get(name) {
            Some(ty) => Ok(ty.clone()),
            None => match &self.outer {
                None => Err(TypeInferError::UndefinedType(name.to_owned())),
                Some(env) => env.borrow().get(name),
            },
        }
    }
    pub fn insert(&mut self, name: String, val: Type) -> Result<(), TypeInferError> {
        if self.env.contains_key(&name) {
            Err(TypeInferError::TypeAlreadyDefined(name))
        } else {
            self.env.insert(name, val);
            Ok(())
        }
    }
    pub fn new_enclosed_env(env: Rc<RefCell<TypeToTypeEnv>>) -> Self {
        TypeToTypeEnv {
            env: Self::builtin(),
            outer: Some(env),
        }
    }
    fn builtin() -> HashMap<String, Type> {
        let mut builtin = HashMap::new();
        builtin.insert("Int".to_owned(), Type::ttype("Int"));
        builtin.insert("String".to_owned(), Type::ttype("String"));
        builtin.insert("Bool".to_owned(), Type::ttype("Bool"));
        builtin.insert("()".to_owned(), Type::ttype("()"));
        builtin
    }
}

pub struct TypeInfer {
    env: Rc<RefCell<TypeEnv>>,
    type_to_type_env: Rc<RefCell<TypeToTypeEnv>>,
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
            Type::TVariant(variants) => write!(
                f,
                "<{}>",
                variants
                    .iter()
                    .map(|(name, tys)| {
                        format!(
                            "{}({})",
                            name,
                            tys.iter()
                                .map(|ty| ty.to_string())
                                .collect::<Vec<String>>()
                                .join(", ")
                        )
                    })
                    .collect::<Vec<String>>()
                    .join(" | ")
            ),
            Type::TRecVar(n) => write!(f, "_rec{}", n),
            Type::TRec(ty) => write!(f, "μ({})", ty),
        }
    }
}

impl TypeInfer {
    pub fn new() -> Self {
        TypeInfer {
            env: Rc::new(RefCell::new(TypeEnv::new())),
            type_to_type_env: Rc::new(RefCell::new(TypeToTypeEnv::new())),
            unassigned_num: 0,
            level: 0,
        }
    }
    fn from(
        env: TypeEnv,
        type_to_type_env: TypeToTypeEnv,
        unassigned_num: u64,
        level: u64,
    ) -> Self {
        TypeInfer {
            env: Rc::new(RefCell::new(env)),
            type_to_type_env: Rc::new(RefCell::new(type_to_type_env)),
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
                    TypeToTypeEnv::new_enclosed_env(Rc::clone(&self.type_to_type_env)),
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
                    TypeToTypeEnv::new_enclosed_env(Rc::clone(&self.type_to_type_env)),
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
                    unify(&ty, &self.peak_pattern(pattern)?)?;
                    let mut typeinfer = TypeInfer::from(
                        TypeEnv::new_enclosed_env(Rc::clone(&self.env)),
                        TypeToTypeEnv::new_enclosed_env(Rc::clone(&self.type_to_type_env)),
                        self.unassigned_num,
                        self.level,
                    );
                    typeinfer.typeinfer_pattern(&pattern, &ty.unfold(&ty))?;
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

    fn peak_pattern(&mut self, pattern: &Pattern) -> Result<Type, TypeInferError> {
        match pattern {
            Pattern::PValue(e) => self.typeinfer_expr(e),
            Pattern::PConstructor(name, _) => {
                let (_, ty) = self
                    .env
                    .borrow()
                    .get(name)?
                    .separate_to_args_and_resulttype();
                Ok(ty)
            }
            Pattern::PVar(_) => Ok(self.newTVar()),
        }
    }

    fn typeinfer_pattern(&mut self, pattern: &Pattern, ty: &Type) -> Result<(), TypeInferError> {
        match pattern {
            Pattern::PValue(value) => unify(&self.typeinfer_expr(value)?, &ty)?,
            Pattern::PConstructor(name, patterns) => {
                let args = ty.variant_to_type(name)?;
                if args.len() != patterns.len() {
                    return Err(TypeInferError::InvalidArgumentPatternError(
                        args.len(),
                        patterns.len(),
                    ));
                }
                for i in 0..args.len() {
                    unify(&args[i], &self.peak_pattern(&patterns[i])?)?;
                    self.typeinfer_pattern(&patterns[i], &args[i].unfold(&args[i]))?;
                }
            }
            Pattern::PVar(var_name) => {
                let ty = ty.fold_variant();
                let new_type = self.newTVar();
                unify(&new_type, &ty)?;
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
                let has_recvar = RefCell::new(false);
                let variant_type = Type::TVariant(
                    constructor_def_vec
                        .iter()
                        .map(|ConstructorDef { name, args }| {
                            Ok((
                                name.to_owned(),
                                args.iter()
                                    .map(|t| {
                                        self.replace_type(t, |name| {
                                            if name == &type_name as &str {
                                                *has_recvar.borrow_mut() = true;
                                                Ok(Type::TRecVar(0))
                                            } else {
                                                self.type_to_type_env.borrow().get(&name)
                                            }
                                        })
                                    })
                                    .collect::<Result<_, _>>()?,
                            ))
                        })
                        .collect::<Result<_, _>>()?,
                );
                let variant_type = if *has_recvar.borrow() {
                    Type::TRec(Box::new(variant_type))
                } else {
                    variant_type
                };
                self.type_to_type_env
                    .borrow_mut()
                    .insert(type_name.to_owned(), variant_type.clone())?;
                for ConstructorDef { name, args } in constructor_def_vec {
                    self.env.borrow_mut().insert(
                        name.to_owned(),
                        args.iter()
                            .rev()
                            .try_fold(variant_type.clone(), |acm, ty| {
                                Ok(t_fun(
                                    self.replace_type(ty, |name| {
                                        self.type_to_type_env.borrow().get(&name)
                                    })?,
                                    acm,
                                ))
                            })?,
                    )
                }
            }
        }
        Ok(())
    }

    fn replace_type(
        &self,
        ty: &Type,
        replace_fn: impl Fn(&str) -> Result<Type, TypeInferError> + Clone,
    ) -> Result<Type, TypeInferError> {
        match ty.simplify() {
            Type::TType(name) => replace_fn(&name),
            Type::TFun(t1, t2) => Ok(t_fun(
                self.replace_type(&t1, replace_fn.clone())?,
                self.replace_type(&t2, replace_fn)?,
            )),
            Type::TVar(n, level, r) => Ok(Type::TVar(n, level, r)),
            Type::TQVar(n) => Ok(Type::TQVar(n)),
            Type::TRecVar(n) => Ok(Type::TRecVar(n)),
            Type::TRec(ty) => Ok(Type::TRec(Box::new(self.replace_type(&ty, replace_fn)?))),
            Type::TVector(ty) => Ok(Type::TVector(Box::new(self.replace_type(&ty, replace_fn)?))),
            Type::TRef(ty) => Ok(Type::TRef(Box::new(self.replace_type(&ty, replace_fn)?))),
            Type::TVariant(variants) => Ok(Type::TVariant(
                variants
                    .iter()
                    .map(|(name, args)| {
                        Ok((
                            name.to_owned(),
                            args.iter()
                                .map(|t| self.replace_type(t, replace_fn.clone()))
                                .collect::<Result<_, _>>()?,
                        ))
                    })
                    .collect::<Result<_, _>>()?,
            )),
        }
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
                Type::TVariant(variants) => Type::TVariant(
                    variants
                        .into_iter()
                        .map(|(name, tys)| {
                            (
                                name,
                                tys.into_iter()
                                    .map(|ty| go(ty, map, self_))
                                    .collect::<Vec<_>>(),
                            )
                        })
                        .collect(),
                ),
                Type::TRecVar(n) => Type::TRecVar(n),
                Type::TRec(ty) => Type::TRec(Box::new(go(*ty, map, self_))),
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
            Type::TVariant(variants) => {
                for (_, tys) in variants {
                    for ty in tys {
                        self.generalize(&ty);
                    }
                }
            }
            Type::TRecVar(_) => (),
            Type::TRec(ty) => self.generalize(&*ty),
        }
    }
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
        (Type::TVariant(variants1), Type::TVariant(variants2)) => {
            if variants1.len() != variants2.len() {
                return Err(TypeInferError::UnifyError(t1.clone(), t2.clone()));
            }
            // 代数的データ型でのみVaritant型は使われるかつ、環境に同じ名前のVariantは一つのみなので、順番を考慮する必要は無い
            for ((name1, tys1), (name2, tys2)) in variants1.iter().zip(variants2.iter()) {
                if name1 != name2 {
                    return Err(TypeInferError::UnifyError(t1.clone(), t2.clone()));
                }
                if tys1.len() != tys2.len() {
                    return Err(TypeInferError::UnifyError(t1.clone(), t2.clone()));
                }
                for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                    unify(ty1, ty2)?;
                }
            }
            Ok(())
        }
        (Type::TRecVar(n), Type::TRecVar(m)) if n == m => Ok(()),
        (Type::TRec(ty1), Type::TRec(ty2)) => unify(&ty1, &ty2),
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
        (n, Type::TVariant(variants)) => variants
            .iter()
            .map(|(_, tys)| tys)
            .any(|tys| tys.iter().map(|ty| ty.simplify()).any(|ty| occur(n, &ty))),
        (_, Type::TRecVar(_)) => false,
        (n, Type::TRec(ty)) => occur(n, &ty),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parser_expr;
    use rstest::rstest;

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

    #[rstest]
    #[case("1+1", Ok(Type::ttype("Int")))]
    #[case("3<2", Ok(Type::ttype("Bool")))]
    #[case("1%1", Ok(Type::ttype("Int")))]
    #[case("if (3>2) 1 else 2", Ok(Type::ttype("Int")))]
    #[case(
        "if (3>2) 1 else 3>2",
        Err(TypeInferError::UnifyError(Type::ttype("Int"), Type::ttype("Bool")))
    )]
    #[case("\"hoge\"", Ok(Type::ttype("String")))]
    #[case("()", Ok(Type::ttype("()")))]
    #[case(r#"puts("Hello, world!")"#, Ok(Type::ttype("()")))]
    #[case("{let x = 1; x == 1;}", Ok(Type::ttype("Bool")))]
    #[case(
        "{let x = 1; x == \"hoge\";}",
        Err(TypeInferError::UnifyError(Type::ttype("Int"), Type::ttype("String")))
    )]
    #[case("{let x = 1;}", Ok(Type::ttype("()")))]
    #[case("[1, 2, 3]", Ok(Type::TVector(Box::new(Type::ttype("Int")))))]
    #[case("-1", Ok(Type::ttype("Int")))]
    #[case("&3", Ok(Type::TRef(Box::new(Type::ttype("Int")))))]
    #[case("*(&1)", Ok(Type::ttype("Int")))]
    #[case("&3:=4", Ok(Type::ttype("()")))]
    fn test_typeinfer_expr(#[case] str: &str, #[case] ty: Result<Type, TypeInferError>) {
        let mut typeinfer = TypeInfer::new();
        assert_eq!(
            typeinfer
                .typeinfer_expr(&parser_expr(str).unwrap().1)
                .map(|ty| ty.simplify()),
            ty
        );
    }

    #[rstest]
    #[case("let a = 1;", "a", Ok(Type::ttype("Int")))]
    #[case("let a = 1; let b = a + 1;", "b", Ok(Type::ttype("Int")))]
    fn test_typeinfer_let(
        #[case] str: &str,
        #[case] var: &str,
        #[case] ty: Result<Type, TypeInferError>,
    ) {
        typeinfer_statements_test_helper(str, var, ty);
    }

    #[rstest]
    #[case(
        "let a = 1; let b = if (a == 1) 3 > 2 else 4 < 2;",
        "b",
        Ok(Type::ttype("Bool"))
    )]
    fn test_typeinfer_if(
        #[case] str: &str,
        #[case] var: &str,
        #[case] ty: Result<Type, TypeInferError>,
    ) {
        typeinfer_statements_test_helper(str, var, ty);
    }

    #[rstest]
    #[case(
        "let add(a, b) = a + b;",
        "add",
        Ok(t_fun(Type::ttype("Int"), t_fun(Type::ttype("Int"), Type::ttype("Int"))))
    )]
    #[case(
        "let add(a, b) = a + b; let a = add(2, 3);",
        "a",
        Ok(Type::ttype("Int"))
    )]
    #[case("let id(x) = x; let a = id(2);", "a", Ok(Type::ttype("Int")))]
    #[case(
        "let id(x) = x; let a = id(2);",
        "id",
        Ok(t_fun(Type::TQVar(1), Type::TQVar(1)))
    )]
    fn test_typeinfer_fun(
        #[case] str: &str,
        #[case] var: &str,
        #[case] ty: Result<Type, TypeInferError>,
    ) {
        typeinfer_statements_test_helper(str, var, ty);
    }

    #[test]
    fn test_typeinfer_enum() {
        typeinfer_statements_test_helper(
            "enum Hoge {Foo(Int)};",
            "Foo",
            Ok(t_fun(
                Type::ttype("Int"),
                Type::TVariant(vec![("Foo".to_owned(), vec![Type::ttype("Int")])]),
            )),
        );
        typeinfer_statements_test_helper(
            "enum Hoge {Foo(Int)}; let main = Foo;",
            "main",
            Ok(t_fun(
                Type::ttype("Int"),
                Type::TVariant(vec![("Foo".to_owned(), vec![Type::ttype("Int")])]),
            )),
        );
        {
            use crate::parser::parser_statements;
            let mut typeinfer = TypeInfer::new();
            assert_eq!(
                typeinfer.typeinfer_statements(
                    &parser_statements("enum Hoge {Foo(Int)}; enum Hoge {Bar(Int)}; let main = 1;")
                        .unwrap()
                        .1
                ),
                Err(TypeInferError::TypeAlreadyDefined("Hoge".to_owned()))
            );
        };
        typeinfer_statements_test_helper(
            "enum List {Cons(Int, List), Nil};",
            "Cons",
            Ok(t_fun(
                Type::ttype("Int"),
                t_fun(
                    Type::TRec(Box::new(Type::TVariant(vec![
                        (
                            "Cons".to_owned(),
                            vec![Type::ttype("Int"), Type::TRecVar(0)],
                        ),
                        ("Nil".to_owned(), vec![]),
                    ]))),
                    Type::TRec(Box::new(Type::TVariant(vec![
                        (
                            "Cons".to_owned(),
                            vec![Type::ttype("Int"), Type::TRecVar(0)],
                        ),
                        ("Nil".to_owned(), vec![]),
                    ]))),
                ),
            )),
        );
        typeinfer_statements_test_helper(
            "enum Hoge {Foo(Int)}; enum Huga {Bar(Hoge)};",
            "Bar",
            Ok(t_fun(
                Type::TVariant(vec![("Foo".to_owned(), vec![Type::ttype("Int")])]),
                Type::TVariant(vec![(
                    "Bar".to_owned(),
                    vec![Type::TVariant(vec![(
                        "Foo".to_owned(),
                        vec![Type::ttype("Int")],
                    )])],
                )]),
            )),
        );
        typeinfer_statements_test_helper(
            "enum Hoge {Foo(Int)}; enum Huga {Bar(Hoge -> Int)};",
            "Bar",
            Ok(t_fun(
                t_fun(
                    Type::TVariant(vec![("Foo".to_owned(), vec![Type::ttype("Int")])]),
                    Type::ttype("Int"),
                ),
                Type::TVariant(vec![(
                    "Bar".to_owned(),
                    vec![t_fun(
                        Type::TVariant(vec![("Foo".to_owned(), vec![Type::ttype("Int")])]),
                        Type::ttype("Int"),
                    )],
                )]),
            )),
        )
    }

    #[rstest]
    #[case(
        "enum Option {Some(Int), None}; let main = Some(3) match {
        Some(x) => x,
        None => 0
    };",
        Ok(Type::ttype("Int"))
    )]
    #[case(
        "enum List {Cons(Int, List), Nil}; let main = Cons(3, Nil) match {
            Cons(x, xs) => x,
            Nil => 0
        };",
        Ok(Type::ttype("Int"))
    )]
    #[case(
        "enum List {Cons(Int, List), Nil}; let main = Cons(3, Cons(2, Nil)) match {
            Cons(3, xs) => xs,
            Nil => Nil
        };",
        Ok(Type::TRec(Box::new(Type::TVariant(vec![
            (
                "Cons".to_owned(),
                vec![Type::ttype("Int"), Type::TRecVar(0)],
            ),
            ("Nil".to_owned(), vec![]),
        ]))))
    )]
    #[case(
        "enum List {Cons(Int, List), Nil}; enum Pair {Pair(List, List)};
        let main = Pair(Cons(1, Nil), Cons(2, Nil)) match {
            Pair(Cons(x, xs), Cons(y, ys)) => x + y,
            Pair(x, y) => 0
        };",
        Ok(Type::ttype("Int"))
    )]
    fn typeinfer_match_test(#[case] str: &str, #[case] ty: Result<Type, TypeInferError>) {
        typeinfer_statements_test_helper(str, "main", ty);
    }
}
