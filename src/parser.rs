use crate::ast::{
    self, e_bin_op, e_if, e_int, e_var, Expr, Statement, StatementOrExpr, Statements,
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric0, digit1, multispace0, multispace1, one_of, satisfy},
    combinator::{fail, map_res, opt, value},
    error::ParseError,
    multi::{many0, many1},
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
    alt((
        expr_int,
        delimited(symbol("("), expr_op_4n, symbol(")")),
        expr_if,
        |input| {
            let (input, ident) = identifier(input)?;
            Ok((input, Expr::EVar(ident)))
        },
    ))(input)
}

pub fn expr_op_7l(input: &str) -> IResult<&str, Expr> {
    let (input, e1) = term(input)?;
    let (input, e2) = many0(|input| {
        let (input, op) = alt((tag("*"), tag("/")))(input)?;
        let (input, ex) = term(input)?;
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
        let (input, op) = alt((tag("+"), tag("-")))(input)?;
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
        parser_expr("1<1+1"),
        Ok((
            "",
            e_bin_op("<", e_int(1), e_bin_op("+", e_int(1), e_int(1)))
        ))
    );
    assert_eq!(
        parser_expr("if (1<2) 1 else 2"),
        Ok((
            "",
            e_if(e_bin_op("<", e_int(1), e_int(2)), e_int(1), e_int(2))
        ))
    );
    assert_eq!(
        parser_expr("a+b"),
        Ok(("", e_bin_op("+", e_var("a"), e_var("b"))))
    );
    assert_eq!(
        parser_expr("a + b"),
        Ok(("", e_bin_op("+", e_var("a"), e_var("b"))))
    );
}

pub fn expr_if(input: &str) -> IResult<&str, Expr> {
    let (input, _) = symbol("if")(input)?;
    let (input, cond) = delimited(symbol("("), parser_expr, symbol(")"))(input)?;
    let (input, e1) = parser_expr(input)?;
    let (input, _) = symbol("else")(input)?;
    let (input, e2) = parser_expr(input)?;
    Ok((input, e_if(cond, e1, e2)))
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

fn identifier(input: &str) -> IResult<&str, String> {
    let (input, _) = multispace0(input)?;
    let (input, first_char) = one_of("abcdefghijklmnopqrstuvwxyz")(input)?;
    let (input, chars) = alphanumeric0(input)?;
    let (input, _) = multispace0(input)?;
    Ok((input, (first_char.to_string() + chars)))
}

#[test]
fn identifier_test() {
    assert_eq!(identifier("aA3B").unwrap().1, "aA3B".to_string());
    assert!(identifier("PA3B").is_err());
    assert_eq!(identifier("a3Bse").unwrap().1, "a3Bse".to_string());
}

pub fn parser_statements(input: &str) -> IResult<&str, Statements> {
    let (input, statements) = many1(statement_assign)(input)?;
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
    let (input, expr) = expr_op_4n(input)?;
    Ok((input, expr))
}

pub fn parser_statement_or_expr(input: &str) -> IResult<&str, StatementOrExpr> {
    match statement_assign(input) {
        Ok((input, stmt)) => Ok((input, StatementOrExpr::Statement(stmt))),
        Err(_) => parser_expr(input).map(|(input, e)| (input, StatementOrExpr::Expr(e))),
    }
}

pub fn parser_for_repl(input: &str) -> IResult<&str, StatementOrExpr> {
    let (input, stmt) = parser_statement_or_expr(input)?;
    let (input, _) = eof(input)?;
    Ok((input, stmt))
}
