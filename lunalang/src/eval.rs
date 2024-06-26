use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;

use crate::ast::{
    ConstructorDef, Expr_, Ident, Path, Pattern_, StatementOrExpr_, Statement_, TypedExpr,
    TypedPattern, TypedStatement, TypedStatements,
};
use crate::error::EvalError;
use crate::types::{HashableType, Type};
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum Value {
    VInt(i64),
    VBool(bool),
    VFun(String, TypedExpr, Environment),
    VString(String),
    VUnit,
    VBuiltin(String, BuiltinFn, Vec<Value>, usize),
    VVector(Vec<Value>),
    VConstructor(String, Vec<Value>, usize),
    VRef(Rc<RefCell<Value>>),
    VChar(char),
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::VInt(n) => write!(f, "{}", n),
            Value::VBool(b) => write!(f, "{}", b),
            Value::VFun(name, e, env) => write!(f, "<fun {}: {}>", name, e.ty),
            Value::VString(str) => write!(f, "{}", str),
            Value::VUnit => write!(f, "()"),
            Value::VVector(vec) => {
                write!(f, "[")?;
                for (i, v) in vec.iter().enumerate() {
                    write!(f, "{}", v)?;
                    if i != vec.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")
            }
            Value::VConstructor(name, args, n) => {
                if *n == 0 {
                    return write!(f, "{}", name);
                }
                if *n != args.len() {
                    write!(f, "<constructor {} with args [", name);
                    for (i, v) in args.iter().enumerate() {
                        write!(f, "{}", v)?;
                        if i != args.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, "]>")
                } else {
                    write!(f, "{}(", name)?;
                    for (i, v) in args.iter().enumerate() {
                        write!(f, "{}", v)?;
                        if i != args.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, ")")
                }
            }
            Value::VRef(r) => write!(f, "Ref ( content = {} )", r.borrow()),
            Value::VBuiltin(name, _, args, _) => {
                write!(f, "<builtin {} with args [", name)?;
                for (i, v) in args.iter().enumerate() {
                    write!(f, "{}", v)?;
                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]>")
            }
            Value::VChar(c) => write!(f, "{}", c),
        }
    }
}

type BuiltinFn = fn(Vec<Value>, Eval) -> Result<Value, EvalError>;

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum Mode {
    Repl,
    Playground,
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub struct Environment {
    env: HashMap<String, Value>,
    outer: Option<Rc<RefCell<Environment>>>,
    builtin: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            env: HashMap::new(),
            outer: None,
            builtin: Environment::builtin(),
        }
    }
    pub fn get(&self, ident: &Ident) -> Result<Value, EvalError> {
        match self.env.get(&ident.name) {
            Some(value) => Ok(value.clone()),
            None => match &self.outer {
                None => match self.builtin.get(&ident.name) {
                    Some(value) => Ok(value.clone()),
                    None => Err(EvalError::UndefinedVariable(ident.name.to_owned())),
                },
                Some(env) => env.borrow().get(&ident),
            },
        }
    }
    pub fn insert(&mut self, name: String, val: Value) {
        self.env.insert(name, val);
    }
    pub fn new_enclosed_env(env: Rc<RefCell<Environment>>) -> Self {
        Environment {
            env: HashMap::new(),
            outer: Some(env),
            builtin: Environment::builtin(),
        }
    }
    fn builtin() -> HashMap<String, Value> {
        let mut builtin = HashMap::new();
        builtin.insert(
            "println".to_owned(),
            Value::VBuiltin(
                "println".to_owned(),
                |values, eval| match &values[0] {
                    Value::VString(str) => {
                        if eval.mode == Mode::Repl {
                            println!("{}", str);
                        } else {
                            eval.stdout.borrow_mut().push_str(&(str.to_owned() + "\n"))
                        }
                        Ok(Value::VUnit)
                    }
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                1,
            ),
        );
        builtin.insert(
            "print".to_owned(),
            Value::VBuiltin(
                "print".to_owned(),
                |values, eval| match &values[0] {
                    Value::VString(str) => {
                        if eval.mode == Mode::Repl {
                            print!("{}", str);
                        } else {
                            eval.stdout.borrow_mut().push_str(str)
                        }
                        Ok(Value::VUnit)
                    }
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                1,
            ),
        );
        builtin.insert(
            "foreach".to_owned(),
            Value::VBuiltin(
                "foreach".to_owned(),
                |values, eval| match (&values[0], &values[1]) {
                    (Value::VFun(_, _, _) | Value::VBuiltin(_, _, _, _), Value::VVector(vec)) => {
                        for value in vec {
                            eval.fun_app_helper(values[0].clone(), value.clone())?;
                        }
                        Ok(Value::VUnit)
                    }
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                2,
            ),
        );
        builtin.insert(
            "int_to_string".to_owned(),
            Value::VBuiltin(
                "int_to_string".to_owned(),
                |values, _| match &values[0] {
                    Value::VInt(n) => Ok(Value::VString(n.to_string())),
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                1,
            ),
        );
        builtin.insert(
            "enum_from_until".to_owned(),
            Value::VBuiltin(
                "enum_from_until".to_owned(),
                |values, _| match (&values[0], &values[1]) {
                    (Value::VInt(n1), Value::VInt(n2)) => Ok(Value::VVector(
                        (*n1..=*n2).into_iter().map(|x| Value::VInt(x)).collect(),
                    )),
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                2,
            ),
        );
        builtin.insert(
            "enum_from_to".to_owned(),
            Value::VBuiltin(
                "enum_from_to".to_owned(),
                |values, _| match (&values[0], &values[1]) {
                    (Value::VInt(n1), Value::VInt(n2)) => Ok(Value::VVector(
                        (*n1..*n2).into_iter().map(|x| Value::VInt(x)).collect(),
                    )),
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                2,
            ),
        );
        builtin
    }
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub struct ModuleEnv {
    env: HashMap<Path, Rc<RefCell<Environment>>>,
}

impl ModuleEnv {
    pub fn new() -> Self {
        ModuleEnv {
            env: Self::builtin(),
        }
    }

    fn get(&self, ident: &Ident, current_path: &Path) -> Result<Value, EvalError> {
        let path = match ident.path {
            Some(ref path) => path,
            None => current_path,
        };

        match self.env.get(path) {
            Some(env) => env.borrow().get(&ident),
            None => Err(EvalError::UndefinedVariable(ident.name.to_owned())),
        }
    }

    fn get_module(&self, path: &Path) -> Result<Rc<RefCell<Environment>>, EvalError> {
        match self.env.get(path) {
            Some(env) => Ok(Rc::clone(env)),
            None => Err(EvalError::ModuleNotFound(path.clone())),
        }
    }

    fn new_enclosed_env(
        env: Rc<RefCell<ModuleEnv>>,
        current_path: &Path,
    ) -> Result<Self, EvalError> {
        let mut new_env = env.borrow().clone();
        match new_env.env.get(current_path) {
            Some(env) => {
                new_env.env.insert(
                    current_path.clone(),
                    Rc::new(RefCell::new(Environment::new_enclosed_env(Rc::clone(env)))),
                );
            }
            None => {
                return Err(EvalError::ModuleNotFound(current_path.clone()));
            }
        }
        Ok(new_env)
    }

    fn new_envclosed_env_from_environment(
        env: Rc<RefCell<ModuleEnv>>,
        current_path: &Path,
        environment: Environment,
    ) -> Result<Self, EvalError> {
        let mut new_env = env.borrow().clone();
        new_env
            .env
            .insert(current_path.clone(), Rc::new(RefCell::new(environment)));
        Ok(new_env)
    }

    fn builtin() -> HashMap<Path, Rc<RefCell<Environment>>> {
        let mut builtin: HashMap<Path, Rc<RefCell<Environment>>> = HashMap::new();

        // ::main
        builtin.insert(
            Path::Module(Box::new(Path::Root), "main".to_owned()),
            Rc::new(RefCell::new(Environment::new())),
        );

        // ::Vector[a]
        let mut vector_env = Environment::new();
        vector_env.insert(
            "at".to_owned(),
            Value::VBuiltin(
                "at".to_owned(),
                |values, _| match (&values[0], &values[1]) {
                    (Value::VInt(n), Value::VVector(vec)) => Ok(vec[*n as usize].clone()),
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                2,
            ),
        );
        vector_env.insert(
            "length".to_owned(),
            Value::VBuiltin(
                "length".to_owned(),
                |values, _| match &values[0] {
                    Value::VVector(vec) => Ok(Value::VInt(vec.len() as i64)),
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                1,
            ),
        );
        builtin.insert(
            Path::TypeModule(
                Box::new(Path::Root),
                HashableType::TVector(Box::new(HashableType::TQVar(0))),
            ),
            Rc::new(RefCell::new(vector_env)),
        );

        // ::String
        let mut string_env = Environment::new();
        string_env.insert(
            "at".to_owned(),
            Value::VBuiltin(
                "at".to_owned(),
                |values, _| match (&values[0], &values[1]) {
                    (Value::VInt(n), Value::VString(str)) => {
                        Ok(Value::VChar(str.chars().nth(*n as usize).unwrap()))
                    }
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                2,
            ),
        );
        string_env.insert(
            "length".to_owned(),
            Value::VBuiltin(
                "length".to_owned(),
                |values, _| match &values[0] {
                    Value::VString(str) => Ok(Value::VInt(str.len() as i64)),
                    _ => Err(EvalError::InternalTypeError),
                },
                vec![],
                1,
            ),
        );
        builtin.insert(
            Path::TypeModule(
                Box::new(Path::Root),
                HashableType::TType("String".to_owned()),
            ),
            Rc::new(RefCell::new(string_env)),
        );
        builtin
    }
}

pub struct Eval {
    env: Rc<RefCell<ModuleEnv>>,
    depth: usize,
    mode: Mode,
    pub stdout: Rc<RefCell<String>>,
    current_path: Path,
}

impl Eval {
    pub fn new(mode: Mode) -> Eval {
        let env = ModuleEnv::new();
        Eval {
            env: Rc::new(RefCell::new(env)),
            depth: 0,
            mode,
            stdout: Rc::new(RefCell::new("".to_owned())),
            current_path: Path::Module(Box::new(Path::Root), "main".to_owned()),
        }
    }
    fn from(
        env: ModuleEnv,
        depth: usize,
        mode: Mode,
        stdout: &Rc<RefCell<String>>,
        current_path: Path,
    ) -> Eval {
        Eval {
            env: Rc::new(RefCell::new(env)),
            depth,
            mode,
            stdout: Rc::clone(stdout),
            current_path,
        }
    }
    pub fn eval_expr(&self, ast: TypedExpr) -> Result<Value, EvalError> {
        match ast.inner {
            Expr_::EBinOp(op, e1, e2) => {
                let v1 = self.eval_expr(*e1)?;
                let v2 = self.eval_expr(*e2)?;
                match (v1, v2) {
                    (Value::VInt(n1), Value::VInt(n2)) => match &op as &str {
                        "+" => Ok(Value::VInt(n1 + n2)),
                        "-" => Ok(Value::VInt(n1 - n2)),
                        "*" => Ok(Value::VInt(n1 * n2)),
                        "/" => Ok(Value::VInt(n1 / n2)),
                        "%" => Ok(Value::VInt(n1 % n2)),
                        "<" => Ok(Value::VBool(n1 < n2)),
                        ">" => Ok(Value::VBool(n1 > n2)),
                        "<=" => Ok(Value::VBool(n1 <= n2)),
                        ">=" => Ok(Value::VBool(n1 >= n2)),
                        "==" => Ok(Value::VBool(n1 == n2)),
                        "!=" => Ok(Value::VBool(n1 != n2)),
                        _ => Err(EvalError::UnimplementedOperatorError(op)),
                    },
                    (Value::VRef(v1), v2) => match &op as &str {
                        ":=" => {
                            *v1.borrow_mut() = v2;
                            Ok(Value::VUnit)
                        }
                        _ => Err(EvalError::UnimplementedOperatorError(op)),
                    },
                    (_, _) => Err(EvalError::InternalTypeError),
                }
            }
            Expr_::EInt(n) => Ok(Value::VInt(n)),
            Expr_::EIf(cond, e1, e2) => {
                let cond = self.eval_expr(*cond)?;
                match cond {
                    Value::VBool(true) => self.eval_expr(*e1),
                    Value::VBool(false) => self.eval_expr(*e2),
                    _ => Err(EvalError::InternalTypeError),
                }
            }
            Expr_::EVar(ident) => self.env.borrow().get(&ident, &self.current_path),
            Expr_::EFun(arg, e) => Ok(Value::VFun(
                arg,
                *e,
                Environment::new_enclosed_env(self.env.borrow().get_module(&self.current_path)?),
            )),
            Expr_::EFunApp(e1, e2) => {
                let v1 = self.eval_expr(*e1)?;
                let v2 = self.eval_expr(*e2)?;
                self.fun_app_helper(v1, v2)
            }
            Expr_::EString(str) => Ok(Value::VString(str)),
            Expr_::EUnit => Ok(Value::VUnit),
            Expr_::EBlockExpr(asts) => {
                let eval = Eval::from(
                    ModuleEnv::new_enclosed_env(Rc::clone(&self.env), &self.current_path)?,
                    self.depth,
                    self.mode,
                    &self.stdout,
                    self.current_path.clone(),
                );
                if asts.len() > 1 {
                    for i in 0..(asts.len() - 1) {
                        match &asts[i].inner {
                            StatementOrExpr_::Statement(s) => eval.eval_statement(s.clone())?,
                            StatementOrExpr_::Expr(e) => {
                                eval.eval_expr(e.clone())?;
                            }
                        }
                    }
                }
                match &asts[asts.len() - 1].inner {
                    StatementOrExpr_::Statement(stmt) => {
                        eval.eval_statement(stmt.clone())?;
                        Ok(Value::VUnit)
                    }
                    StatementOrExpr_::Expr(e) => eval.eval_expr(e.clone()),
                }
            }
            Expr_::EVector(exprs) => {
                let mut vvec = vec![];
                for e in exprs {
                    vvec.push(self.eval_expr(e)?)
                }
                Ok(Value::VVector(vvec))
            }
            Expr_::EUnary(op, e) => match &op as &str {
                "-" => {
                    let e = self.eval_expr(*e)?;
                    match e {
                        Value::VInt(n) => Ok(Value::VInt(-n)),
                        _ => Err(EvalError::InternalTypeError),
                    }
                }
                "&" => {
                    let e = self.eval_expr(*e)?;
                    Ok(Value::VRef(Rc::new(RefCell::new(e))))
                }
                "*" => {
                    let e = self.eval_expr(*e)?;
                    match e {
                        Value::VRef(e) => Ok(e.borrow().clone()),
                        _ => Err(EvalError::InternalTypeError),
                    }
                }
                _ => Err(EvalError::UnimplementedOperatorError(op)),
            },
            Expr_::EMatch(expr, match_arms) => {
                let expr = self.eval_expr(*expr)?;
                for (pattern, expr_arm) in match_arms {
                    let eval = Eval::from(
                        ModuleEnv::new_enclosed_env(Rc::clone(&self.env), &self.current_path)?,
                        self.depth,
                        self.mode,
                        &self.stdout,
                        self.current_path.clone(),
                    );
                    if eval.expr_match_pattern(&expr, &pattern)? == true {
                        return eval.eval_expr(expr_arm);
                    }
                }
                Err(EvalError::NotMatchAnyPattern)
            }
            Expr_::EMethod(receiver, ident, args) => {
                let mut result = self.env.borrow().get(&ident, &self.current_path)?;
                for arg in args {
                    result = self.fun_app_helper(result, self.eval_expr(arg)?)?;
                }
                Ok(self.fun_app_helper(result, self.eval_expr(*receiver)?)?)
            }
        }
    }
    fn expr_match_pattern(&self, expr: &Value, pattern: &TypedPattern) -> Result<bool, EvalError> {
        match &pattern.inner {
            Pattern_::PValue(value) => {
                let value = self.eval_expr(value.clone())?;
                Ok(value == *expr)
            }
            Pattern_::PConstructor(name, patterns) => {
                if let Value::VConstructor(constructor_name, args, _) = expr {
                    if constructor_name != &name.name {
                        return Ok(false);
                    } else if patterns.len() != args.len() {
                        return Err(EvalError::InternalTypeError);
                    }
                    let mut result = true;
                    for i in 0..patterns.len() {
                        result = result && self.expr_match_pattern(&args[i], &patterns[i])?;
                    }
                    Ok(result)
                } else {
                    Ok(false)
                }
            }
            Pattern_::PVar(var_name) => {
                self.env
                    .borrow()
                    .get_module(&self.current_path)?
                    .borrow_mut()
                    .insert(var_name.clone(), expr.clone());
                Ok(true)
            }
        }
    }
    pub fn eval_statement(&self, ast: TypedStatement) -> Result<(), EvalError> {
        match ast.inner {
            Statement_::Assign(name, _, e) => {
                let val = self.eval_expr(e)?;
                Ok(self
                    .env
                    .borrow()
                    .get_module(&self.current_path)?
                    .borrow_mut()
                    .insert(name, val))
            }
            Statement_::TypeDef(_, constructor_def_vec) => {
                for ConstructorDef { name, args } in &constructor_def_vec {
                    self.env
                        .borrow()
                        .get_module(&self.current_path)?
                        .borrow_mut()
                        .insert(
                            name.to_owned(),
                            Value::VConstructor(name.to_owned(), vec![], args.len()),
                        )
                }
                Ok(())
            }
        }
    }
    pub fn eval_statements(&self, asts: TypedStatements) -> Result<(), EvalError> {
        for ast in asts {
            self.eval_statement(ast)?;
        }
        Ok(())
    }
    pub fn eval_main(&self) -> Result<Value, EvalError> {
        self.env
            .borrow()
            .get_module(&Path::Module(Box::new(Path::Root), "main".to_owned()))?
            .borrow()
            .get(&Ident {
                path: Some(Path::Module(Box::new(Path::Root), "main".to_owned())),
                name: "main".to_owned(),
            })
    }
    fn fun_app_helper(&self, v1: Value, v2: Value) -> Result<Value, EvalError> {
        match v1 {
            Value::VFun(arg, expr, env) => {
                if self.mode == Mode::Playground && self.depth >= 29 {
                    return Err(EvalError::RecursionLimitExceeded);
                }
                let eval = Eval::from(
                    ModuleEnv::new_envclosed_env_from_environment(
                        Rc::clone(&self.env),
                        &self.current_path,
                        env.clone(),
                    )?,
                    self.depth + 1,
                    self.mode,
                    &self.stdout,
                    self.current_path.clone(),
                );
                eval.env
                    .borrow()
                    .get_module(&self.current_path)?
                    .borrow_mut()
                    .insert(arg, v2);
                let result = eval.eval_expr(expr);
                result
            }
            Value::VBuiltin(name, fun, args, args_num) => {
                let mut args_mut = args;
                args_mut.push(v2);
                if args_mut.len() == args_num {
                    fun(
                        args_mut,
                        Eval {
                            env: Rc::clone(&self.env),
                            depth: self.depth + 1,
                            mode: self.mode,
                            stdout: Rc::clone(&self.stdout),
                            current_path: self.current_path.clone(),
                        },
                    )
                } else {
                    Ok(Value::VBuiltin(name, fun, args_mut, args_num))
                }
            }
            Value::VConstructor(name, args, n) => {
                let mut mut_args = args;
                mut_args.push(v2);
                Ok(Value::VConstructor(name, mut_args, n))
            }
            _ => Err(EvalError::InternalTypeError),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parser_expr;
    use crate::parser::parser_statements;
    use crate::typeinfer::TypeInfer;
    fn test_eval_expr_helper(str: &str, v: Result<Value, EvalError>) {
        let eval = Eval::new(Mode::Repl);
        let mut typeinfer = TypeInfer::new();
        assert_eq!(
            eval.eval_expr(
                typeinfer
                    .typeinfer_expr(&parser_expr(str).unwrap().1, None)
                    .unwrap()
            ),
            v
        )
    }

    #[test]
    fn test_op_expr() {
        test_eval_expr_helper("3*3+4*4", Ok(Value::VInt(25)));
        test_eval_expr_helper("4+(6/3)-2", Ok(Value::VInt(4)));
        test_eval_expr_helper("2+4/2/2", Ok(Value::VInt(3)));
        test_eval_expr_helper("3>2", Ok(Value::VBool(true)));
        test_eval_expr_helper("3<2", Ok(Value::VBool(false)));
        test_eval_expr_helper("2>=2", Ok(Value::VBool(true)));
        test_eval_expr_helper("2<=3", Ok(Value::VBool(true)));
        test_eval_expr_helper("2==3", Ok(Value::VBool(false)));
        test_eval_expr_helper("2!=3", Ok(Value::VBool(true)));
        test_eval_expr_helper("4%3", Ok(Value::VInt(1)));
        test_eval_expr_helper("&3", Ok(Value::VRef(Rc::new(RefCell::new(Value::VInt(3))))));
        test_eval_expr_helper("*(&3)", Ok(Value::VInt(3)));
    }

    #[test]
    fn test_if_expr() {
        test_eval_expr_helper("if (3>2) 1 else 2", Ok(Value::VInt(1)));
        test_eval_expr_helper("if (3<2) 1 else 2", Ok(Value::VInt(2)));
        test_eval_expr_helper("if (3<2) 1 else if (4==4) 2 else 3", Ok(Value::VInt(2)));
    }

    #[test]
    fn test_string_expr() {
        test_eval_expr_helper(
            r#""Hello, world!""#,
            Ok(Value::VString("Hello, world!".to_owned())),
        )
    }

    #[test]
    fn test_unit_expr() {
        test_eval_expr_helper("()", Ok(Value::VUnit))
    }

    #[test]
    fn test_block_expr() {
        test_eval_expr_helper("{let x = 1; x + 3;}", Ok(Value::VInt(4)));
        test_eval_expr_helper("{let x = 1;}", Ok(Value::VUnit));
    }

    fn test_eval_statements_helper(str: &str, v: Result<Value, EvalError>) {
        let mut eval = Eval::new(Mode::Repl);
        let mut typeinfer = TypeInfer::new();
        eval.eval_statements(
            typeinfer
                .typeinfer_statements(&parser_statements(str).unwrap().1)
                .unwrap(),
        )
        .unwrap();
        assert_eq!(eval.eval_main(), v)
    }

    #[test]
    fn test_eval_statements() {
        test_eval_statements_helper("let main = 4;", Ok(Value::VInt(4)));
        test_eval_statements_helper(
            "let a = 3; let b = 4; let main = a + b;",
            Ok(Value::VInt(7)),
        );
        test_eval_statements_helper(
            "let add(a, b) = a + b; let main = add(2, 3);",
            Ok(Value::VInt(5)),
        );
    }

    #[test]
    fn test_high_order_function() {
        test_eval_statements_helper(
            "let double(f, x) = f(f(x)); let succ(n) = n + 1; let main = double(succ, 3);",
            Ok(Value::VInt(5)),
        );
    }

    #[test]
    fn test_recursive_function() {
        test_eval_statements_helper(
            "let fact(n) = if (n==1) 1 else n * fact(n-1); let main = fact(3);",
            Ok(Value::VInt(6)),
        );
        test_eval_statements_helper(
        "let fib(n) = if (n==1) 1 else if (n==2) 1 else fib(n-1) + fib(n-2); let main = fib(5);",
        Ok(Value::VInt(5)),
    );
    }

    #[test]
    fn test_vector() {
        test_eval_expr_helper(
            "[1, 2]",
            Ok(Value::VVector(vec![Value::VInt(1), Value::VInt(2)])),
        )
    }

    #[test]
    fn test_ref() {
        test_eval_statements_helper(
            "let sum(vec) = {
  let sum = &0;
  for (v in vec) {
    sum := *sum + v;
  };
  *sum;
};
let main = sum([1..=100]);",
            Ok(Value::VInt(5050)),
        )
    }

    #[test]
    fn test_enum() {
        test_eval_statements_helper(
            "enum Hoge{Foo(Int)}; let main = Foo(3);",
            Ok(Value::VConstructor(
                "Foo".to_owned(),
                vec![Value::VInt(3)],
                1,
            )),
        )
    }

    #[test]
    fn test_match_expr() {
        test_eval_statements_helper(
            "
enum OptionInt {
    Some(Int),
    None
};
let main = Some(3) match {
    Some(x) => x,
    None => 0
};
        ",
            Ok(Value::VInt(3)),
        )
    }
}
