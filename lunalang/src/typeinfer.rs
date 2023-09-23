use crate::ast::{
    Annot, ConstructorDef, Expr_, Ident, Path, Pattern_, StatementOrExpr_, Statement_, TypedExpr,
    TypedPattern, TypedStatement, TypedStatements, UntypedExpr, UntypedPattern, UntypedStatement,
    UntypedStatements,
};
use crate::error::TypeInferError;
use crate::types::{HashableType, Type};
use std::collections::HashMap;
use std::{cell::RefCell, rc::Rc};

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
    pub fn get(&self, ident: &Ident) -> Result<Type, TypeInferError> {
        match self.env.get(&ident.name) {
            Some(ty) => Ok(ty.clone()),
            None => match &self.outer {
                None => match self.builtin.get(&ident.name) {
                    Some(ty) => Ok(ty.clone()),
                    None => Err(TypeInferError::UndefinedVariable(ident.name.to_owned())),
                },
                Some(env) => env.borrow().get(ident),
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
            "println".to_owned(),
            Type::fun(Type::ttype("String"), Type::ttype("()")),
        );
        builtin.insert(
            "print".to_owned(),
            Type::fun(Type::ttype("String"), Type::ttype("()")),
        );
        builtin.insert(
            "foreach".to_owned(),
            Type::fun(
                Type::fun(Type::TQVar(0), Type::ttype("()")),
                Type::fun(Type::TVector(Box::new(Type::TQVar(0))), Type::ttype("()")),
            ),
        );
        builtin.insert(
            "int_to_string".to_owned(),
            Type::fun(Type::ttype("Int"), Type::ttype("String")),
        );
        builtin.insert(
            "enum_from_until".to_owned(),
            Type::fun(
                Type::ttype("Int"),
                Type::fun(
                    Type::ttype("Int"),
                    Type::TVector(Box::new(Type::ttype("Int"))),
                ),
            ),
        );
        builtin.insert(
            "enum_from_to".to_owned(),
            Type::fun(
                Type::ttype("Int"),
                Type::fun(
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
        builtin.insert("Char".to_owned(), Type::ttype("Char"));
        builtin
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleEnv {
    module_env: HashMap<Path, Rc<RefCell<TypeEnv>>>,
    type_module_env: HashMap<HashableType, Rc<RefCell<TypeEnv>>>,
    type_to_path: HashMap<HashableType, Path>,
}

impl ModuleEnv {
    pub fn new() -> Self {
        let (module_env, type_module_env, type_to_path) = Self::builtin();
        ModuleEnv {
            module_env,
            type_module_env,
            type_to_path,
        }
    }
    pub fn get(&self, ident: &Ident, default_module: &Path) -> Result<Type, TypeInferError> {
        let path = match ident.path {
            Some(ref path) => path,
            None => default_module,
        };
        // todo: 相対pathの扱いをどうするか
        match self.module_env.get(path) {
            Some(env) => env.borrow().get(&ident),
            None => Err(TypeInferError::UndefinedVariable(ident.name.to_owned())),
        }
    }
    fn get_module(&self, path: &Path) -> Result<Rc<RefCell<TypeEnv>>, TypeInferError> {
        match self.module_env.get(path) {
            Some(env) => Ok(Rc::clone(env)),
            None => Err(TypeInferError::ModuleNotFound(path.clone())),
        }
    }
    // HashMapの要素のタプルの１つ目の要素はTypeModuleの型
    pub fn search_from_current_module_and_type_modules(
        &self,
        ident: &Ident,
        current_module: &Path,
    ) -> Result<HashMap<Path, (Option<Type>, Type)>, TypeInferError> {
        let mut result: HashMap<Path, (Option<Type>, Type)> = HashMap::new();
        match self.get_module(&current_module)?.borrow().get(&ident) {
            Ok(ty) => {
                result.insert(current_module.clone(), (None, ty.clone()));
            }
            Err(_) => (),
        }
        for (hashable_ty, env) in self.type_module_env.iter() {
            match env.borrow().get(&ident) {
                Ok(ty) => {
                    result.insert(
                        self.type_to_path[hashable_ty].clone(),
                        (Some(Type::from(hashable_ty.clone())), ty.clone()),
                    );
                }
                Err(_) => (),
            }
        }
        if result.len() == 0 {
            return Err(TypeInferError::UndefinedVariable(ident.name.to_owned()));
        }
        Ok(result)
    }
    pub fn new_enclosed_env(
        env: Rc<RefCell<ModuleEnv>>,
        current_module: &Path,
    ) -> Result<Self, TypeInferError> {
        let mut new_env = env.borrow().clone();
        match new_env.module_env.get(current_module) {
            Some(env) => {
                new_env.module_env.insert(
                    current_module.clone(),
                    Rc::new(RefCell::new(TypeEnv::new_enclosed_env(Rc::clone(env)))),
                );
            }
            None => {
                return Err(TypeInferError::ModuleNotFound(current_module.clone()));
            }
        }
        Ok(new_env)
    }
    fn builtin() -> (
        HashMap<Path, Rc<RefCell<TypeEnv>>>,
        HashMap<HashableType, Rc<RefCell<TypeEnv>>>,
        HashMap<HashableType, Path>,
    ) {
        let mut builtin_module_env = HashMap::new();
        let mut builtin_type_module_env = HashMap::new();
        let mut builtin_type_to_path = HashMap::new();

        // ::main
        builtin_module_env.insert(
            Path::Module(Box::new(Path::Root), "main".to_owned()),
            Rc::new(RefCell::new(TypeEnv::new())),
        );

        // ::Vector[a]
        let mut vector_env = TypeEnv::new();
        vector_env.insert(
            "at".to_owned(),
            Type::fun(
                Type::ttype("Int"),
                Type::fun(Type::TVector(Box::new(Type::TQVar(0))), Type::TQVar(0)),
            ),
        );
        let vector_env = Rc::new(RefCell::new(vector_env));
        builtin_type_module_env.insert(
            HashableType::TVector(Box::new(HashableType::TQVar(0))),
            Rc::clone(&vector_env),
        );
        builtin_module_env.insert(
            Path::TypeModule(
                Box::new(Path::Root),
                HashableType::TVector(Box::new(HashableType::TQVar(0))),
            ),
            vector_env,
        );
        builtin_type_to_path.insert(
            HashableType::TVector(Box::new(HashableType::TQVar(0))),
            Path::TypeModule(
                Box::new(Path::Root),
                HashableType::TVector(Box::new(HashableType::TQVar(0))),
            ),
        );

        // ::String
        let mut string_env = TypeEnv::new();
        string_env.insert(
            "at".to_owned(),
            Type::fun(
                Type::ttype("Int"),
                Type::fun(Type::ttype("String"), Type::ttype("Char")),
            ),
        );
        let string_env = Rc::new(RefCell::new(string_env));
        builtin_type_module_env.insert(
            HashableType::TType("String".to_owned()),
            Rc::clone(&string_env),
        );
        builtin_module_env.insert(
            Path::TypeModule(
                Box::new(Path::Root),
                HashableType::TType("String".to_owned()),
            ),
            string_env,
        );
        builtin_type_to_path.insert(
            HashableType::TType("String".to_owned()),
            Path::TypeModule(
                Box::new(Path::Root),
                HashableType::TType("String".to_owned()),
            ),
        );
        (
            builtin_module_env,
            builtin_type_module_env,
            builtin_type_to_path,
        )
    }
}

pub struct TypeInfer {
    env: Rc<RefCell<ModuleEnv>>,
    type_to_type_env: Rc<RefCell<TypeToTypeEnv>>,
    unassigned_num: u64,
    level: u64,
    current_module: Path,
}

impl TypeInfer {
    pub fn new() -> Self {
        TypeInfer {
            env: Rc::new(RefCell::new(ModuleEnv::new())),
            type_to_type_env: Rc::new(RefCell::new(TypeToTypeEnv::new())),
            unassigned_num: 0,
            level: 0,
            current_module: Path::Module(Box::new(Path::Root), "main".to_owned()),
        }
    }
    fn from(
        env: ModuleEnv,
        type_to_type_env: TypeToTypeEnv,
        unassigned_num: u64,
        level: u64,
        current_module: Path,
    ) -> Self {
        TypeInfer {
            env: Rc::new(RefCell::new(env)),
            type_to_type_env: Rc::new(RefCell::new(type_to_type_env)),
            unassigned_num,
            level,
            current_module,
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
    pub fn typeinfer_expr(
        &mut self,
        ast: &UntypedExpr,
        type_restriction: Option<Type>,
    ) -> Result<TypedExpr, TypeInferError> {
        match &ast.inner {
            Expr_::EInt(n) => Ok(Annot {
                ty: Type::ttype("Int"),
                span: (),
                inner: Expr_::EInt(*n),
            }),
            Expr_::EBinOp(op, e1, e2) => match &op as &str {
                "+" | "-" | "*" | "/" | "%" => {
                    let e1 = self.typeinfer_expr(&e1, None)?;
                    unify(&Type::ttype("Int"), &e1.ty)?;
                    let e2 = self.typeinfer_expr(&e2, None)?;
                    unify(&Type::ttype("Int"), &e2.ty)?;
                    Ok(Annot {
                        ty: Type::ttype("Int"),
                        span: (),
                        inner: Expr_::EBinOp(op.clone(), Box::new(e1), Box::new(e2)),
                    })
                }
                "<" | ">" | "<=" | ">=" | "==" | "!=" => {
                    let e1 = self.typeinfer_expr(&e1, None)?;
                    unify(&Type::ttype("Int"), &e1.ty)?;
                    let e2 = self.typeinfer_expr(&e2, None)?;
                    unify(&Type::ttype("Int"), &e2.ty)?;
                    Ok(Annot {
                        ty: Type::ttype("Bool"),
                        span: (),
                        inner: Expr_::EBinOp(op.clone(), Box::new(e1), Box::new(e2)),
                    })
                }
                ":=" => {
                    let ty = self.newTVar();
                    let e1 = self.typeinfer_expr(&e1, None)?;
                    unify(&Type::TRef(Box::new(ty.clone())), &e1.ty)?;
                    let e2 = self.typeinfer_expr(&e2, None)?;
                    unify(&ty, &e2.ty)?;
                    Ok(Annot {
                        ty: Type::ttype("()"),
                        span: (),
                        inner: Expr_::EBinOp(op.clone(), Box::new(e1), Box::new(e2)),
                    })
                }
                _ => Err(TypeInferError::UnimplementedOperatorError(op.clone())),
            },
            Expr_::EIf(cond, e1, e2) => {
                let cond = self.typeinfer_expr(&cond, None)?;
                unify(&Type::ttype("Bool"), &cond.ty)?;
                let e1 = self.typeinfer_expr(&e1, None)?;
                let e2 = self.typeinfer_expr(&e2, None)?;
                unify(&e1.ty, &e2.ty)?;
                Ok(Annot {
                    ty: e1.ty.clone(),
                    span: (),
                    inner: Expr_::EIf(Box::new(cond), Box::new(e1), Box::new(e2)),
                })
            }
            Expr_::EVar(ident) => {
                let ty = self.env.borrow().get(&ident, &self.current_module)?;
                Ok(Annot {
                    ty: self.instantiate(&ty),
                    span: (),
                    inner: Expr_::EVar(ident.clone()),
                })
            }
            Expr_::EFun(arg, e) => {
                let mut typeinfer = TypeInfer::from(
                    ModuleEnv::new_enclosed_env(Rc::clone(&self.env), &self.current_module)?,
                    TypeToTypeEnv::new_enclosed_env(Rc::clone(&self.type_to_type_env)),
                    self.unassigned_num,
                    self.level,
                    self.current_module.clone(),
                );
                let ty = typeinfer.newTVar();
                match type_restriction {
                    Some(type_restriction) => unify(
                        &Type::TFun(Box::new(ty.clone()), Box::new(self.newTVar())),
                        &type_restriction,
                    )?,
                    None => (),
                }
                typeinfer
                    .env
                    .borrow()
                    .get_module(&self.current_module)?
                    .borrow_mut()
                    .insert(arg.to_string(), ty.clone());
                let result = typeinfer.typeinfer_expr(&e, None)?;
                self.unassigned_num = typeinfer.unassigned_num;
                Ok(Annot {
                    ty: Type::fun(ty, result.ty.clone()),
                    span: (),
                    inner: Expr_::EFun(arg.clone(), Box::new(result)),
                })
            }
            Expr_::EFunApp(e1, e2) => {
                let e1 = self.typeinfer_expr(&e1, None)?;
                let e2 = self.typeinfer_expr(&e2, None)?;
                let ty = self.newTVar();
                unify(&e1.ty, &Type::fun(e2.ty.clone(), ty.clone()))?;
                Ok(Annot {
                    ty,
                    span: (),
                    inner: Expr_::EFunApp(Box::new(e1), Box::new(e2)),
                })
            }
            Expr_::EString(str) => Ok(Annot {
                ty: Type::ttype("String"),
                span: (),
                inner: Expr_::EString(str.clone()),
            }),
            Expr_::EUnit => Ok(Annot {
                ty: Type::ttype("()"),
                span: (),
                inner: Expr_::EUnit,
            }),
            Expr_::EBlockExpr(asts) => {
                let mut typeinfer = TypeInfer::from(
                    ModuleEnv::new_enclosed_env(Rc::clone(&self.env), &self.current_module)?,
                    TypeToTypeEnv::new_enclosed_env(Rc::clone(&self.type_to_type_env)),
                    self.unassigned_num,
                    self.level,
                    self.current_module.clone(),
                );
                let mut result_asts = Vec::new();
                if asts.len() > 1 {
                    for i in 0..(asts.len() - 1) {
                        match &asts[i].inner {
                            StatementOrExpr_::Expr(e) => {
                                let e = typeinfer.typeinfer_expr(&e, None)?;
                                result_asts.push(Annot {
                                    ty: e.ty.clone(),
                                    span: (),
                                    inner: StatementOrExpr_::Expr(e),
                                });
                            }
                            StatementOrExpr_::Statement(stmt) => result_asts.push(Annot {
                                ty: Type::ttype("()"),
                                span: (),
                                inner: StatementOrExpr_::Statement(
                                    typeinfer.typeinfer_statement(&stmt)?,
                                ),
                            }),
                        }
                    }
                }
                let ty = match &asts[asts.len() - 1].inner {
                    StatementOrExpr_::Expr(e) => {
                        let e = typeinfer.typeinfer_expr(&e, None)?;
                        result_asts.push(Annot {
                            ty: e.ty.clone(),
                            span: (),
                            inner: StatementOrExpr_::Expr(e.clone()),
                        });
                        e.ty
                    }
                    StatementOrExpr_::Statement(stmt) => {
                        result_asts.push(Annot {
                            ty: Type::ttype("()"),
                            span: (),
                            inner: StatementOrExpr_::Statement(
                                typeinfer.typeinfer_statement(&stmt)?,
                            ),
                        });
                        Type::ttype("()")
                    }
                };
                self.unassigned_num = typeinfer.unassigned_num;
                Ok(Annot {
                    ty,
                    span: (),
                    inner: Expr_::EBlockExpr(result_asts),
                })
            }
            Expr_::EVector(exprs) => {
                let ty = self.newTVar();
                let mut result_exprs = Vec::new();
                for expr in exprs {
                    let expr = self.typeinfer_expr(&expr, None)?;
                    unify(&ty, &expr.ty.clone())?;
                    result_exprs.push(expr);
                }
                Ok(Annot {
                    ty: Type::TVector(Box::new(ty)),
                    span: (),
                    inner: Expr_::EVector(result_exprs),
                })
            }
            Expr_::EUnary(op, e) => {
                let e = self.typeinfer_expr(&e, None)?;
                match &op as &str {
                    "-" => {
                        unify(&Type::ttype("Int"), &e.ty)?;
                        Ok(Annot {
                            ty: Type::ttype("Int"),
                            span: (),
                            inner: Expr_::EUnary(op.clone(), Box::new(e)),
                        })
                    }
                    "*" => {
                        let newtvar = self.newTVar();

                        unify(&Type::TRef(Box::new(newtvar.clone())), &e.ty)?;
                        Ok(Annot {
                            ty: newtvar,
                            span: (),
                            inner: Expr_::EUnary(op.clone(), Box::new(e)),
                        })
                    }
                    "&" => {
                        let newtvar = self.newTVar();
                        unify(&newtvar, &e.ty)?;
                        Ok(Annot {
                            ty: Type::TRef(Box::new(newtvar)),
                            span: (),
                            inner: Expr_::EUnary(op.clone(), Box::new(e)),
                        })
                    }
                    op => Err(TypeInferError::UnimplementedOperatorError(op.to_owned())),
                }
            }
            Expr_::EMatch(expr, match_arms) => {
                let match_expr = self.typeinfer_expr(&expr, None)?;
                if match_arms.len() == 0 {
                    return Ok(Annot {
                        ty: match_expr.ty.clone(),
                        span: (),
                        inner: Expr_::EMatch(Box::new(match_expr), Vec::new()),
                    });
                }
                let result_ty = self.newTVar();
                let mut result_match_arms = Vec::new();
                for (pattern, expr) in match_arms {
                    unify(&match_expr.ty, &self.peak_pattern(&pattern)?)?;
                    let mut typeinfer = TypeInfer::from(
                        ModuleEnv::new_enclosed_env(Rc::clone(&self.env), &self.current_module)?,
                        TypeToTypeEnv::new_enclosed_env(Rc::clone(&self.type_to_type_env)),
                        self.unassigned_num,
                        self.level,
                        self.current_module.clone(),
                    );
                    let pattern = typeinfer
                        .typeinfer_pattern(&pattern, &match_expr.ty.unfold(&match_expr.ty))?;
                    let expr = typeinfer.typeinfer_expr(&expr, None)?;
                    unify(&result_ty, &expr.ty.clone())?;
                    result_match_arms.push((pattern, expr));

                    self.unassigned_num = typeinfer.unassigned_num
                }
                Ok(Annot {
                    ty: result_ty,
                    span: (),
                    inner: Expr_::EMatch(Box::new(match_expr), result_match_arms),
                })
            }
            Expr_::EMethod(receiver, ident, args) => {
                let receiver = self.typeinfer_expr(&receiver, None)?;
                let receiver_ty = receiver.ty.simplify();
                let args = args
                    .iter()
                    .map(|arg| self.typeinfer_expr(&arg, None))
                    .collect::<Result<Vec<_>, _>>()?;
                let result_type = self.newTVar();
                let mut ty = Type::fun(receiver.ty.simplify(), result_type.clone());
                for arg in args.iter().rev() {
                    ty = Type::fun(arg.ty.simplify(), ty)
                }
                let saved_ty = ty.simplify();
                let envs = self
                    .env
                    .borrow()
                    .search_from_current_module_and_type_modules(&ident, &self.current_module)?;
                let mut candidate: Vec<(Path, Type)> = Vec::new();
                let mut last_err = None;
                for (path, (opt_ty, fun_type)) in envs {
                    let fun_type = self.instantiate(&fun_type).simplify();
                    let saved_fun_type = fun_type.clone();
                    match unify(&fun_type, &ty) {
                        Ok(_) => match opt_ty {
                            Some(ty) => match unify(&self.instantiate(&ty), &receiver_ty) {
                                Ok(_) => {
                                    candidate.push((path, fun_type.simplify()));
                                }
                                Err(err) => {
                                    last_err = Some(err);
                                }
                            },
                            None => {
                                candidate.push((path, fun_type.simplify()));
                            }
                        },
                        Err(err) => {
                            last_err = Some(err);
                        }
                    }
                    saved_fun_type.reset();
                    saved_ty.reset();
                }
                if candidate.len() == 0 {
                    return Err(last_err.unwrap());
                } else if candidate.len() >= 2 {
                    return Err(TypeInferError::AmbiguousMethodCallError(
                        ident.name.to_owned(),
                        candidate
                            .iter()
                            .map(|(path, _)| path.clone())
                            .collect::<Vec<_>>(),
                    ));
                }
                dbg!(&candidate);
                let fun_type = &candidate[0].1;
                unify(fun_type, &ty)?;
                Ok(Annot {
                    ty: result_type,
                    span: (),
                    inner: Expr_::EMethod(
                        Box::new(receiver),
                        Ident {
                            path: Some(candidate[0].0.clone()),
                            name: ident.name.clone(),
                        },
                        args,
                    ),
                })
            }
        }
    }
    fn typeinfer_expr_levelup(
        &mut self,
        ast: &UntypedExpr,
        type_restrict: Option<Type>,
    ) -> Result<TypedExpr, TypeInferError> {
        self.level += 1;
        let ty = self.typeinfer_expr(ast, type_restrict)?;
        self.level -= 1;
        Ok(ty)
    }

    fn peak_pattern(&mut self, pattern: &UntypedPattern) -> Result<Type, TypeInferError> {
        match &pattern.inner {
            Pattern_::PValue(e) => self.typeinfer_expr(&e, None).map(|e| e.ty),
            Pattern_::PConstructor(name, _) => {
                let (_, ty) = self
                    .env
                    .borrow()
                    .get(&name, &self.current_module)?
                    .separate_to_args_and_resulttype();
                Ok(ty)
            }
            Pattern_::PVar(_) => Ok(self.newTVar()),
        }
    }

    fn typeinfer_pattern(
        &mut self,
        pattern: &UntypedPattern,
        ty: &Type,
    ) -> Result<TypedPattern, TypeInferError> {
        match &pattern.inner {
            Pattern_::PValue(value) => {
                let value = self.typeinfer_expr(&value, None)?;
                unify(&value.ty, &ty)?;
                Ok(Annot {
                    ty: value.ty.clone(),
                    span: (),
                    inner: Pattern_::PValue(value),
                })
            }
            Pattern_::PConstructor(name, patterns) => {
                let args = ty.variant_to_type(&name.name)?;
                if args.len() != patterns.len() {
                    return Err(TypeInferError::InvalidArgumentPatternError(
                        args.len(),
                        patterns.len(),
                    ));
                }
                let mut result_patterns = Vec::new();
                for i in 0..args.len() {
                    unify(&args[i], &self.peak_pattern(&patterns[i])?)?;
                    let pattern =
                        self.typeinfer_pattern(&patterns[i], &args[i].unfold(&args[i]))?;
                    result_patterns.push(pattern);
                }
                Ok(Annot {
                    ty: ty.clone(),
                    span: (),
                    inner: Pattern_::PConstructor(name.clone(), result_patterns),
                })
            }
            Pattern_::PVar(var_name) => {
                let ty = ty.fold_variant();
                let new_type = self.newTVar();
                unify(&new_type, &ty)?;
                self.env.borrow().module_env[&self.current_module]
                    .borrow_mut()
                    .insert(var_name.clone(), new_type.clone());
                Ok(Annot {
                    ty: new_type,
                    span: (),
                    inner: Pattern_::PVar(var_name.clone()),
                })
            }
        }
    }

    pub fn typeinfer_statement(
        &mut self,
        ast: &UntypedStatement,
    ) -> Result<TypedStatement, TypeInferError> {
        match &ast.inner {
            Statement_::Assign(name, opt_ty, e) => {
                let ty = match opt_ty {
                    Some(ty) => ty.clone(),
                    None => self.newTVar(),
                };
                self.env
                    .borrow()
                    .get_module(&self.current_module)?
                    .borrow_mut()
                    .insert(name.to_string(), ty.clone());
                let instanciated_ty = self.instantiate(&ty);
                let e = self.typeinfer_expr_levelup(
                    &e,
                    if opt_ty.is_some() {
                        Some(instanciated_ty)
                    } else {
                        None
                    },
                )?;
                unify(&ty, &e.ty)?;
                self.generalize(&ty);
                Ok(Annot {
                    ty: (),
                    span: (),
                    inner: Statement_::Assign(name.to_string(), opt_ty.clone(), e),
                })
            }
            Statement_::TypeDef(type_name, constructor_def_vec) => {
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
                    self.env
                        .borrow()
                        .get_module(&self.current_module)?
                        .borrow_mut()
                        .insert(
                            name.to_owned(),
                            args.iter()
                                .rev()
                                .try_fold(variant_type.clone(), |acm, ty| {
                                    Ok(Type::fun(
                                        self.replace_type(ty, |name| {
                                            self.type_to_type_env.borrow().get(&name)
                                        })?,
                                        acm,
                                    ))
                                })?,
                        )
                }
                Ok(Annot {
                    ty: (),
                    span: (),
                    inner: Statement_::TypeDef(
                        type_name.to_owned(),
                        constructor_def_vec.to_owned(),
                    ),
                })
            }
        }
    }

    fn replace_type(
        &self,
        ty: &Type,
        replace_fn: impl Fn(&str) -> Result<Type, TypeInferError> + Clone,
    ) -> Result<Type, TypeInferError> {
        match ty.simplify() {
            Type::TType(name) => replace_fn(&name),
            Type::TFun(t1, t2) => Ok(Type::fun(
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

    pub fn typeinfer_statements(
        &mut self,
        asts: &UntypedStatements,
    ) -> Result<TypedStatements, TypeInferError> {
        let mut result_statements = Vec::new();
        for ast in asts {
            result_statements.push(self.typeinfer_statement(ast)?);
        }
        Ok(result_statements)
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
                Type::TFun(t1, t2) => Type::fun(go(*t1, map, self_), go(*t2, map, self_)),
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
                .get(
                    &Ident {
                        path: None,
                        name: name.to_string()
                    },
                    &Path::Module(Box::new(Path::Root), "main".to_string())
                )
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
    #[case(r#"println("Hello, world!")"#, Ok(Type::ttype("()")))]
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
                .typeinfer_expr(&parser_expr(str).unwrap().1, None)
                .map(|ty| ty.ty.simplify()),
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
        Ok(Type::fun(Type::ttype("Int"), Type::fun(Type::ttype("Int"), Type::ttype("Int"))))
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
        Ok(Type::fun(Type::TQVar(1), Type::TQVar(1)))
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
            Ok(Type::fun(
                Type::ttype("Int"),
                Type::TVariant(vec![("Foo".to_owned(), vec![Type::ttype("Int")])]),
            )),
        );
        typeinfer_statements_test_helper(
            "enum Hoge {Foo(Int)}; let main = Foo;",
            "main",
            Ok(Type::fun(
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
            Ok(Type::fun(
                Type::ttype("Int"),
                Type::fun(
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
            Ok(Type::fun(
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
            Ok(Type::fun(
                Type::fun(
                    Type::TVariant(vec![("Foo".to_owned(), vec![Type::ttype("Int")])]),
                    Type::ttype("Int"),
                ),
                Type::TVariant(vec![(
                    "Bar".to_owned(),
                    vec![Type::fun(
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
    fn test_typeinfer_match(#[case] str: &str, #[case] ty: Result<Type, TypeInferError>) {
        typeinfer_statements_test_helper(str, "main", ty);
    }
}
