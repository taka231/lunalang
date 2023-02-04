use std::collections::{HashMap, HashSet};

use crate::ast::{self, e_bin_op, e_int, Expr};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{digit1, multispace0, one_of, satisfy},
    combinator::{map_res, value},
    error::ParseError,
    multi::{many0, many1},
    sequence::delimited,
    IResult,
};

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

fn symbol<'a>(s: &'a str) -> impl FnMut(&'a str) -> IResult<&'a str, &str> {
    ws(tag(s))
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
    alt((expr_int, delimited(symbol("("), expr_op, symbol(")"))))(input)
}

pub fn expr_op(input: &str) -> IResult<&str, Expr> {
    let (input, e1) = term(input)?;
    let (input, e2) = many0(|input| {
        let (input, op) = op(input)?;
        let (input, ex) = term(input)?;
        Ok((input, (op, ex)))
    })(input)?;
    Ok((
        input,
        e2.iter()
            .fold(e1, |acc, (op, ex)| e_bin_op(&op, acc, ex.clone())),
    ))
}

#[test]
fn test_expr_op() {
    assert_eq!(
        expr_op("1 + 1"),
        Ok(("", e_bin_op("+", e_int(1), e_int(1))))
    );
    assert_eq!(
        expr_op("1 + 1 * 1"),
        Ok((
            "",
            e_bin_op("*", e_bin_op("+", e_int(1), e_int(1)), e_int(1))
        ))
    );
    assert_eq!(
        expr_op("1 + (2 * 3)"),
        Ok((
            "",
            e_bin_op("+", e_int(1), e_bin_op("*", e_int(2), e_int(3)))
        ))
    )
}

pub fn fixity_resolution(ast: Expr, map: &HashMap<String, i64>) -> Expr {
    match ast {
        Expr::EBinOp(op1, e1, e2) => match *e1 {
            Expr::EBinOp(op2, e3, e4) => {
                let pri1 = map[&op1];
                let pri2 = map[&op2];
                if pri1 <= pri2 {
                    e_bin_op(
                        &op1,
                        fixity_resolution(e_bin_op(&op2, *e3, *e4), map),
                        fixity_resolution(*e2, map),
                    )
                } else {
                    e_bin_op(
                        &op2,
                        fixity_resolution(*e3, map),
                        fixity_resolution(e_bin_op(&op1, *e4, *e2), map),
                    )
                }
            }
            e => {
                let e_ = fixity_resolution(e, map);
                let e2_ = fixity_resolution(*e2, map);
                e_bin_op(&op1, e_, e2_)
            }
        },
        Expr::EInt(n) => e_int(n),
    }
}

#[test]
fn test_fixity_resolution() {
    let map: HashMap<_, _> = vec![
        ("+".to_string(), 6),
        ("-".to_string(), 6),
        ("*".to_string(), 7),
        ("/".to_string(), 7),
    ]
    .iter()
    .map(|x| x.clone())
    .collect();
    let test1 = e_bin_op("*", e_bin_op("+", e_int(1), e_int(2)), e_int(3));
    assert_eq!(
        fixity_resolution(test1, &map),
        e_bin_op("+", e_int(1), e_bin_op("*", e_int(2), e_int(3)))
    );
    assert_eq!(
        fixity_resolution(expr_op("3*1+4/2").unwrap().1, &map),
        e_bin_op(
            "+",
            e_bin_op("*", e_int(3), e_int(1)),
            e_bin_op("/", e_int(4), e_int(2))
        )
    );
    assert_eq!(
        fixity_resolution(expr_op("3+4-2").unwrap().1, &map),
        e_bin_op("-", e_bin_op("+", e_int(3), e_int(4)), e_int(2))
    );
    assert_eq!(
        fixity_resolution(expr_op("3 * (1 + 4) / 2").unwrap().1, &map),
        e_bin_op(
            "/",
            e_bin_op("*", e_int(3), e_bin_op("+", e_int(1), e_int(4))),
            e_int(2)
        )
    )
}
