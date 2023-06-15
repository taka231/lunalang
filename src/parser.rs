use crate::ast::{
    self, e_bin_op, e_fun, e_fun_app, e_if, e_int, e_string, e_var, Expr, Statement,
    StatementOrExpr, Statements,
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::{
        complete::{
            alphanumeric0, digit1, multispace0, multispace1, none_of, one_of, satisfy, space0,
        },
        is_alphanumeric,
    },
    combinator::{eof, fail, map_res, opt, value},
    error::ParseError,
    multi::{many0, many1, separated_list0},
    sequence::delimited,
    IResult,
};
use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet};

/// A combinator that takes a parser `inner` and produces a parser that also consumes both leading and
/// trailing whitespace, returning the output of `inner`.
fn ws<'a, F: 'a, O, E: ParseError<&'a str>>(
    inner: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O, E>,
{
    delimited(multispace0, inner, multispace0)
}

/// ## Example
/// ```
/// use lunalang::parser::int;
/// assert_eq!(int("123"), Ok(("", 123)));
/// assert_eq!(int(" 123 "), Ok(("", 123)));
/// ```
pub fn int(input: &str) -> IResult<&str, i64> {
    map_res(ws(digit1), str::parse)(input)
}

pub fn expr_int(input: &str) -> IResult<&str, Expr> {
    let (input, n) = int(input)?;
    Ok((input, Expr::EInt(n)))
}

pub fn symbol<'a>(s: &'a str) -> impl FnMut(&'a str) -> IResult<&'a str, &str> {
    ws(tag(s))
}

pub fn keyword<'a>(s: &'a str) -> impl FnMut(&'a str) -> IResult<&'a str, &str> {
    delimited(multispace0, tag(s), multispace1)
}

/// ## Example
/// ```
/// use lunalang::parser::op;
/// assert_eq!(op("++"), Ok(("", "++".to_string())));
/// assert_eq!(op("<="), Ok(("", "<=".to_string())));
/// ```
pub fn op(input: &str) -> IResult<&str, String> {
    ws(|input| many1(one_of("|$%&=~-^+:*/<>"))(input))(input)
        .map(|(s, vec)| (s, vec.iter().collect::<String>()))
}

pub fn term(input: &str) -> IResult<&str, Expr> {
    alt((expr_if, for_in_expr, lambda_fn, dot_expr, simple_term))(input)
}

pub fn simple_term(input: &str) -> IResult<&str, Expr> {
    alt((
        expr_int,
        |input| {
            let (input, _) = symbol("(")(input)?;
            let (input, _) = symbol(")")(input)?;
            Ok((input, Expr::EUnit))
        },
        block_term,
        enum_vec_expr,
        expr_vector,
        delimited(symbol("("), parser_expr, symbol(")")),
        |input| {
            let (input, ident) = identifier(input)?;
            Ok((input, Expr::EVar(ident)))
        },
        expr_string,
    ))(input)
}

pub fn block_term(input: &str) -> IResult<&str, Expr> {
    alt((lambda_block_fn, parse_block_expr))(input)
}

pub fn unary(input: &str) -> IResult<&str, Expr> {
    let (input, op) = opt(alt((symbol("-"), symbol("&"), symbol("*"))))(input)?;
    let (input, e) = term(input)?;
    match op {
        Some(op) => Ok((input, Expr::EUnary(op.to_owned(), Box::new(e)))),
        None => Ok((input, e)),
    }
}

#[test]
fn unary_test() {
    assert_eq!(
        parser_expr("-3"),
        Ok(("", Expr::EUnary("-".to_owned(), Box::new(Expr::EInt(3)))))
    );
    assert_eq!(
        parser_expr("*3"),
        Ok(("", Expr::EUnary("*".to_owned(), Box::new(Expr::EInt(3)))))
    );
    assert_eq!(
        parser_expr("&3"),
        Ok(("", Expr::EUnary("&".to_owned(), Box::new(Expr::EInt(3)))))
    );
    assert_eq!(
        parser_expr("-3+3"),
        Ok((
            "",
            e_bin_op(
                "+",
                Expr::EUnary("-".to_owned(), Box::new(Expr::EInt(3))),
                Expr::EInt(3)
            )
        ))
    );
}

pub fn expr_op_7l(input: &str) -> IResult<&str, Expr> {
    let (input, e1) = unary(input)?;
    let (input, e2) = many0(|input| {
        let (input, op) = alt((symbol("*"), symbol("/"), symbol("%")))(input)?;
        let (input, ex) = unary(input)?;
        Ok((input, (op, ex)))
    })(input)?;
    Ok((
        input,
        e2.iter()
            .fold(e1, |acc, (op, ex)| e_bin_op(&op, acc, ex.clone())),
    ))
}

pub fn expr_op_6l(input: &str) -> IResult<&str, Expr> {
    let (input, e1) = expr_op_7l(input)?;
    let (input, e2) = many0(|input| {
        let (input, op) = alt((symbol("+"), symbol("-")))(input)?;
        let (input, ex) = expr_op_7l(input)?;
        Ok((input, (op, ex)))
    })(input)?;
    Ok((
        input,
        e2.iter()
            .fold(e1, |acc, (op, ex)| e_bin_op(&op, acc, ex.clone())),
    ))
}

pub fn expr_op_4n(input: &str) -> IResult<&str, Expr> {
    let (input, e1) = expr_op_6l(input)?;
    let (input, optional) = opt(|input| {
        let (input, op) = alt((
            tag("=="),
            tag("!="),
            tag("<="),
            tag("<"),
            tag(">="),
            tag(">"),
        ))(input)?;
        let (input, e2) = expr_op_6l(input)?;
        Ok((input, (op, e2)))
    })(input)?;
    match optional {
        Some((op, e2)) => Ok((input, e_bin_op(op, e1, e2))),
        None => Ok((input, e1)),
    }
}

pub fn expr_op_0n(input: &str) -> IResult<&str, Expr> {
    let (input, e1) = expr_op_4n(input)?;
    let (input, optional) = opt(|input| {
        let (input, op) = alt((tag(":="),))(input)?;
        let (input, e2) = expr_op_4n(input)?;
        Ok((input, (op, e2)))
    })(input)?;
    match optional {
        Some((op, e2)) => Ok((input, e_bin_op(op, e1, e2))),
        None => Ok((input, e1)),
    }
}

#[test]
fn test_expr_op() {
    assert_eq!(
        parser_expr("1 + 1"),
        Ok(("", e_bin_op("+", e_int(1), e_int(1))))
    );
    assert_eq!(
        parser_expr("1 + 1 * 1"),
        Ok((
            "",
            e_bin_op("+", e_int(1), e_bin_op("*", e_int(1), e_int(1)))
        ))
    );
    assert_eq!(
        parser_expr("1 + (2 * 3)"),
        Ok((
            "",
            e_bin_op("+", e_int(1), e_bin_op("*", e_int(2), e_int(3)))
        ))
    );
    assert_eq!(
        parser_expr("1<2"),
        Ok(("", e_bin_op("<", e_int(1), e_int(2))))
    );
    assert_eq!(
        parser_expr("1%2"),
        Ok(("", e_bin_op("%", e_int(1), e_int(2))))
    );
    assert_eq!(
        parser_expr("1<1+1"),
        Ok((
            "",
            e_bin_op("<", e_int(1), e_bin_op("+", e_int(1), e_int(1)))
        ))
    );
    assert_eq!(
        parser_expr("a:=3"),
        Ok(("", e_bin_op(":=", e_var("a"), e_int(3))))
    );
    assert_eq!(
        parser_expr("a+b"),
        Ok(("", e_bin_op("+", e_var("a"), e_var("b"))))
    );
    assert_eq!(
        parser_expr("a + b"),
        Ok(("", e_bin_op("+", e_var("a"), e_var("b"))))
    );
    assert_eq!(
        parser_expr("add(2, 3)").unwrap().1,
        e_fun_app(e_fun_app(e_var("add"), e_int(2)), e_int(3)),
    )
}

#[test]
fn test_expr_string() {
    assert_eq!(
        parser_expr(r#""Hello, world!""#),
        Ok(("", e_string("Hello, world!")))
    );
    assert_eq!(parser_expr(r#""""#), Ok(("", e_string(""))));
}

#[test]
fn test_unit() {
    assert_eq!(parser_expr("()"), Ok(("", Expr::EUnit)))
}

#[test]
fn test_expr_if() {
    assert_eq!(
        parser_expr("if (1<2) 1 else 2"),
        Ok((
            "",
            e_if(e_bin_op("<", e_int(1), e_int(2)), e_int(1), e_int(2))
        ))
    );
}

#[test]
fn test_fun_app() {
    assert_eq!(
        parser_expr("add(2, 3)").unwrap().1,
        e_fun_app(e_fun_app(e_var("add"), e_int(2)), e_int(3)),
    )
}

pub fn expr_if(input: &str) -> IResult<&str, Expr> {
    let (input, _) = symbol("if")(input)?;
    let (input, cond) = delimited(symbol("("), parser_expr, symbol(")"))(input)?;
    let (input, e1) = parser_expr(input)?;
    let (input, _) = symbol("else")(input)?;
    let (input, e2) = parser_expr(input)?;
    Ok((input, e_if(cond, e1, e2)))
}

pub fn fun_app(input: &str) -> IResult<&str, Expr> {
    let (input, e) = simple_term(input)?;
    let (input, args) = opt(alt((|input| {
        let (input, _) = symbol("(")(input)?;
        let (input, args) = separated_list0(symbol(","), parser_expr)(input)?;
        let (input, _) = symbol(")")(input)?;
        Ok((input, args))
    },)))(input)?;
    match args {
        None => Ok((input, e)),
        Some(args) => Ok((
            input,
            args.iter()
                .fold(e, |acc, expr| e_fun_app(acc, expr.clone())),
        )),
    }
}

#[test]
fn fun_app_test() {
    assert_eq!(
        dot_expr("add(2, 3)").unwrap().1,
        e_fun_app(e_fun_app(e_var("add"), e_int(2)), e_int(3)),
    );
    assert_eq!(
        dot_expr("{add;}(2, 3)").unwrap().1,
        e_fun_app(
            e_fun_app(
                Expr::EBlockExpr(vec![StatementOrExpr::Expr(e_var("add"))]),
                e_int(2)
            ),
            e_int(3)
        ),
    );
    assert_eq!(
        dot_expr("add(2) {3;}").unwrap().1,
        e_fun_app(
            e_fun_app(e_var("add"), e_int(2)),
            Expr::EBlockExpr(vec![StatementOrExpr::Expr(e_int(3))])
        ),
    );
}

pub fn expr_string(input: &str) -> IResult<&str, Expr> {
    let (input, _) = space0(input)?;
    let (input, _) = tag("\"")(input)?;
    let (input, str) = many0(none_of("\""))(input)?;
    let (input, _) = symbol("\"")(input)?;
    Ok((input, Expr::EString(str.iter().collect())))
}

#[test]
fn expr_string_test() {
    assert_eq!(
        expr_string(r#""Hello, world!""#),
        Ok(("", e_string("Hello, world!")))
    );
    assert_eq!(expr_string(r#""""#), Ok(("", e_string(""))));
    assert_eq!(expr_string(r#"" ""#), Ok(("", e_string(" "))));
}

fn parse_block_expr(input: &str) -> IResult<&str, Expr> {
    let (input, _) = symbol("{")(input)?;
    let (input, statement_or_expr_vec) = many1(parser_statement_or_expr)(input)?;
    let (input, _) = symbol("}")(input)?;
    Ok((input, Expr::EBlockExpr(statement_or_expr_vec)))
}

#[test]
fn parse_block_expr_test() {
    assert_eq!(
        parse_block_expr(
            "{
        let x = 1;
        x + 1;
    }"
        ),
        Ok((
            "",
            Expr::EBlockExpr(vec![
                StatementOrExpr::Statement(Statement::Assign("x".to_owned(), Expr::EInt(1))),
                StatementOrExpr::Expr(e_bin_op("+", e_var("x"), e_int(1)))
            ])
        ))
    );
    assert_eq!(
        parser_expr(
            "{
        let x = 1;
        x + 1;
    }"
        ),
        Ok((
            "",
            Expr::EBlockExpr(vec![
                StatementOrExpr::Statement(Statement::Assign("x".to_owned(), Expr::EInt(1))),
                StatementOrExpr::Expr(e_bin_op("+", e_var("x"), e_int(1)))
            ])
        ))
    )
}

pub fn statement_assign(input: &str) -> IResult<&str, Statement> {
    let (input, _) = keyword("let")(input)?;
    let (input, id) = identifier(input)?;
    let (input, _) = symbol("=")(input)?;
    let (input, e) = parser_expr(input)?;
    let (input, _) = symbol(";")(input)?;
    Ok((input, Statement::Assign(id, e)))
}

#[test]
fn statement_assign_test() {
    assert_eq!(
        statement_assign("let a = 1;").unwrap().1,
        Statement::Assign("a".to_string(), e_int(1))
    );
}

pub fn fun_def(input: &str) -> IResult<&str, Statement> {
    let (input, _) = keyword("let")(input)?;
    let (input, id) = identifier(input)?;
    let (input, _) = symbol("(")(input)?;
    let (input, args) = separated_list0(symbol(","), identifier)(input)?;
    let (input, _) = symbol(")")(input)?;
    let (input, _) = symbol("=")(input)?;
    let (input, expr) = parser_expr(input)?;
    let (input, _) = symbol(";")(input)?;
    let mut result = expr;
    for i in (0..args.len()).rev() {
        result = Expr::EFun(args[i].clone(), Box::new(result))
    }
    Ok((input, Statement::Assign(id, result)))
}

#[test]
pub fn fun_def_test() {
    assert_eq!(
        fun_def("let add(a, b) = a + b;").unwrap().1,
        Statement::Assign(
            "add".to_string(),
            e_fun("a", e_fun("b", e_bin_op("+", e_var("a"), e_var("b"))))
        )
    )
}

fn identifier(input: &str) -> IResult<&str, String> {
    let (input, _) = multispace0(input)?;
    let (input, first_char) = one_of("abcdefghijklmnopqrstuvwxyz_")(input)?;
    let (input, mut chars) = many0(satisfy(|c| is_alphanumeric(c as u8) || c == '_'))(input)?;
    let (input, _) = multispace0(input)?;
    let is_keyword = |x: &&str| vec!["if", "else", "let", "fn", "for", "in", "do"].contains(x);
    chars.insert(0, first_char);
    let ident: String = chars.iter().collect();
    if is_keyword(&(&ident as &str)) {
        return Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        )));
    }
    Ok((input, ident))
}

#[test]
fn identifier_test() {
    assert_eq!(identifier("aA3B").unwrap().1, "aA3B".to_string());
    assert!(identifier("PA3B").is_err());
    assert_eq!(identifier("a3Bse").unwrap().1, "a3Bse".to_string());
    assert_eq!(
        identifier("int_to_string").unwrap().1,
        "int_to_string".to_string()
    );
}

pub fn parser_statement(input: &str) -> IResult<&str, Statement> {
    let (input, statement) = alt((fun_def, statement_assign))(input)?;
    Ok((input, statement))
}

#[test]
pub fn parser_statement_test() {
    assert_eq!(
        parser_statement("let main = 1;").unwrap().1,
        Statement::Assign("main".to_string(), e_int(1)),
    );
    assert_eq!(
        parser_statement("let add(a, b) = a + b;").unwrap().1,
        Statement::Assign(
            "add".to_string(),
            e_fun("a", e_fun("b", e_bin_op("+", e_var("a"), e_var("b"))))
        )
    );
}

pub fn parser_statements(input: &str) -> IResult<&str, Statements> {
    let (input, statements) = many1(parser_statement)(input)?;
    let (input, _) = eof(input)?;
    Ok((input, statements))
}

#[test]
fn parser_statements_test() {
    assert_eq!(
        parser_statements("let main = 1;").unwrap().1,
        vec![Statement::Assign("main".to_string(), e_int(1)),]
    );
    assert_eq!(
        parser_statements("let main = a + b;").unwrap().1,
        vec![Statement::Assign(
            "main".to_string(),
            e_bin_op("+", e_var("a"), e_var("b"))
        ),]
    );
    assert_eq!(
        parser_statements("let a = 1; let b = 2;").unwrap().1,
        vec![
            Statement::Assign("a".to_string(), e_int(1)),
            Statement::Assign("b".to_string(), e_int(2))
        ]
    );
    assert_eq!(
        parser_statements("let a = 1; let b = 2; let main = a + b;")
            .unwrap()
            .1,
        vec![
            Statement::Assign("a".to_string(), e_int(1)),
            Statement::Assign("b".to_string(), e_int(2)),
            Statement::Assign("main".to_string(), e_bin_op("+", e_var("a"), e_var("b")))
        ]
    )
}

pub fn parser_expr<'a>(input: &'a str) -> IResult<&'a str, Expr> {
    let (input, expr) = expr_op_0n(input)?;
    Ok((input, expr))
}

pub fn parser_statement_or_expr(input: &str) -> IResult<&str, StatementOrExpr> {
    match parser_statement(input) {
        Ok((input, stmt)) => Ok((input, StatementOrExpr::Statement(stmt))),
        Err(_) => {
            let (input, e) = parser_expr(input)?;
            let (input, _) = symbol(";")(input)?;
            Ok((input, StatementOrExpr::Expr(e)))
        }
    }
}

pub fn parser_statement_or_expr_for_repl(input: &str) -> IResult<&str, StatementOrExpr> {
    match parser_statement(input) {
        Ok((input, stmt)) => Ok((input, StatementOrExpr::Statement(stmt))),
        Err(_) => {
            let (input, e) = parser_expr(input)?;
            Ok((input, StatementOrExpr::Expr(e)))
        }
    }
}

pub fn parser_for_repl(input: &str) -> IResult<&str, StatementOrExpr> {
    let (input, stmt) = parser_statement_or_expr_for_repl(input)?;
    let (input, _) = eof(input)?;
    Ok((input, stmt))
}

pub fn dot_expr(input: &str) -> IResult<&str, Expr> {
    let (input, mut expr) = fun_app(input)?;
    let (input, mut temp_exprs) = many0(|input| {
        let (input, _) = symbol(".")(input)?;
        let (input, ident) = identifier(input)?;
        let (input, args) = opt(|input| {
            let (input, _) = symbol("(")(input)?;
            let (input, args) = separated_list0(symbol(","), parser_expr)(input)?;
            let (input, _) = symbol(")")(input)?;
            Ok((input, args))
        })(input)?;
        let args = args.unwrap_or(vec![]);
        let mut temp_expr = Expr::EVar(ident);
        for arg in args {
            temp_expr = e_fun_app(temp_expr, arg);
        }
        Ok((input, temp_expr))
    })(input)?;
    let (input, opt_expr) = opt(block_term)(input)?;
    match opt_expr {
        None => (),
        Some(e) => {
            if temp_exprs.len() == 0 {
                return Ok((input, e_fun_app(expr, e)));
            }
            let len = temp_exprs.len();
            temp_exprs[len - 1] = e_fun_app(temp_exprs[len - 1].clone(), e)
        }
    }
    for temp_expr in temp_exprs {
        expr = e_fun_app(temp_expr, expr)
    }
    Ok((input, expr))
}

#[test]
fn test_dot_expr() {
    assert_eq!(
        dot_expr("3.inc"),
        Ok(("", e_fun_app(e_var("inc"), Expr::EInt(3))))
    );
    assert_eq!(
        dot_expr("3.inc()"),
        Ok(("", e_fun_app(e_var("inc"), Expr::EInt(3))))
    );
    assert_eq!(
        dot_expr("3.add(2)"),
        Ok((
            "",
            e_fun_app(e_fun_app(e_var("add"), Expr::EInt(2)), Expr::EInt(3))
        ))
    );
    assert_eq!(
        dot_expr("add(2, 3).inc"),
        Ok((
            "",
            e_fun_app(
                e_var("inc"),
                e_fun_app(e_fun_app(e_var("add"), Expr::EInt(2)), Expr::EInt(3))
            )
        ))
    );
    assert_eq!(
        dot_expr("3.add(2).add(4)"),
        Ok((
            "",
            e_fun_app(
                e_fun_app(e_var("add"), Expr::EInt(4)),
                e_fun_app(e_fun_app(e_var("add"), Expr::EInt(2)), Expr::EInt(3))
            )
        ))
    );
    assert_eq!(
        dot_expr("3.add {2;}"),
        Ok((
            "",
            e_fun_app(
                e_fun_app(
                    e_var("add"),
                    Expr::EBlockExpr(vec![StatementOrExpr::Expr(Expr::EInt(2))])
                ),
                Expr::EInt(3)
            )
        ))
    );
    assert_eq!(
        dot_expr("3.add() {2;}"),
        Ok((
            "",
            e_fun_app(
                e_fun_app(
                    e_var("add"),
                    Expr::EBlockExpr(vec![StatementOrExpr::Expr(Expr::EInt(2))])
                ),
                Expr::EInt(3)
            )
        ))
    );
}

pub fn lambda_fn(input: &str) -> IResult<&str, Expr> {
    let (input, _) = symbol("fn")(input)?;
    let (input, args) = separated_list0(symbol(","), identifier)(input)?;
    let (input, _) = symbol("->")(input)?;
    let (input, mut e) = parser_expr(input)?;
    for i in 0..args.len() {
        let index = args.len() - i - 1;
        e = Expr::EFun(args[index].to_owned(), Box::new(e))
    }
    Ok((input, e))
}

#[test]
fn test_lambda_fn() {
    assert_eq!(lambda_fn("fn x -> x"), Ok(("", e_fun("x", e_var("x")))));
}

pub fn lambda_block_fn(input: &str) -> IResult<&str, Expr> {
    let (input, _) = symbol("{")(input)?;
    let (input, _) = symbol("fn")(input)?;
    let (input, args) = separated_list0(symbol(","), identifier)(input)?;
    let (input, _) = symbol("->")(input)?;
    let (input, statement_or_expr_vec) = many1(parser_statement_or_expr)(input)?;
    let (input, _) = symbol("}")(input)?;
    let mut expr = Expr::EBlockExpr(statement_or_expr_vec);
    for i in 0..args.len() {
        let index = args.len() - i - 1;
        expr = Expr::EFun(args[index].to_owned(), Box::new(expr))
    }
    Ok((input, expr))
}

#[test]
fn test_lambda_block() {
    assert_eq!(
        lambda_block_fn("{fn x -> x; x;}"),
        Ok((
            "",
            e_fun(
                "x",
                Expr::EBlockExpr(vec![
                    StatementOrExpr::Expr(e_var("x")),
                    StatementOrExpr::Expr(e_var("x"))
                ])
            )
        ))
    );
    assert_eq!(
        parser_expr("hoge {fn x -> x; x;}"),
        Ok((
            "",
            e_fun_app(
                e_var("hoge"),
                e_fun(
                    "x",
                    Expr::EBlockExpr(vec![
                        StatementOrExpr::Expr(e_var("x")),
                        StatementOrExpr::Expr(e_var("x"))
                    ])
                )
            )
        ))
    );
}

pub fn expr_vector(input: &str) -> IResult<&str, Expr> {
    let (input, vec) = delimited(
        symbol("["),
        separated_list0(symbol(","), parser_expr),
        symbol("]"),
    )(input)?;
    Ok((input, Expr::EVector(vec)))
}

#[test]
fn test_expr_vector() {
    assert_eq!(
        expr_vector("[1, 2, 3]"),
        Ok((
            "",
            Expr::EVector(vec![Expr::EInt(1), Expr::EInt(2), Expr::EInt(3)])
        ))
    );
}

pub fn for_in_expr(input: &str) -> IResult<&str, Expr> {
    let (input, _) = symbol("for")(input)?;
    let (input, _) = symbol("(")(input)?;
    let (input, ident) = identifier(input)?;
    let (input, _) = symbol("in")(input)?;
    let (input, vec) = parser_expr(input)?;
    let (input, _) = symbol(")")(input)?;
    let (input, expr) = parser_expr(input)?;
    Ok((
        input,
        e_fun_app(
            e_fun_app(e_var("foreach"), Expr::EFun(ident, Box::new(expr))),
            vec,
        ),
    ))
}

pub fn enum_vec_expr(input: &str) -> IResult<&str, Expr> {
    let (input, _) = symbol("[")(input)?;
    let (input, e1) = parser_expr(input)?;
    let (input, op) = alt((symbol("..="), symbol("..")))(input)?;
    let (input, e2) = parser_expr(input)?;
    let (input, _) = symbol("]")(input)?;
    match op {
        "..=" => Ok((
            input,
            e_fun_app(e_fun_app(e_var("enum_from_until"), e1), e2),
        )),
        ".." => Ok((input, e_fun_app(e_fun_app(e_var("enum_from_to"), e1), e2))),
        _ => panic!("internal error"),
    }
}
