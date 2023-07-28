use crate::{
    ast::{
        ConstructorDef, Pattern, Statement, StatementOrExpr, UntypedExpr, UntypedPattern,
        UntypedStatement, UntypedStatementOrExpr, UntypedStatements,
    },
    types::Type,
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::{
        complete::{digit1, multispace0, multispace1, none_of, one_of, satisfy, space0},
        is_alphanumeric,
    },
    combinator::{eof, map_res, opt},
    error::ParseError,
    multi::{many0, many1, separated_list0},
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

pub fn expr_int(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, n) = int(input)?;
    Ok((input, UntypedExpr::e_int(n)))
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

pub fn term(input: &str) -> IResult<&str, UntypedExpr> {
    alt((expr_if, for_in_expr, lambda_fn, dot_expr, simple_term))(input)
}

pub fn simple_term(input: &str) -> IResult<&str, UntypedExpr> {
    alt((
        expr_int,
        parser_unit,
        block_term,
        enum_vec_expr,
        expr_vector,
        delimited(symbol("("), parser_expr, symbol(")")),
        |input| {
            let (input, ident) = alt((identifier, identifier_start_with_capital))(input)?;
            Ok((input, UntypedExpr::e_var(&ident)))
        },
        expr_string,
    ))(input)
}

pub fn parser_unit(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, _) = symbol("(")(input)?;
    let (input, _) = symbol(")")(input)?;
    Ok((input, UntypedExpr::e_unit()))
}

pub fn block_term(input: &str) -> IResult<&str, UntypedExpr> {
    alt((lambda_block_fn, parse_block_expr))(input)
}

pub fn unary(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, op) = opt(alt((symbol("-"), symbol("&"), symbol("*"))))(input)?;
    let (input, e) = term(input)?;
    match op {
        Some(op) => Ok((input, UntypedExpr::e_unary(op, e))),
        None => Ok((input, e)),
    }
}

pub fn expr_op_7l(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, e1) = unary(input)?;
    let (input, e2) = many0(|input| {
        let (input, op) = alt((symbol("*"), symbol("/"), symbol("%")))(input)?;
        let (input, ex) = unary(input)?;
        Ok((input, (op, ex)))
    })(input)?;
    Ok((
        input,
        e2.iter().fold(e1, |acc, (op, ex)| {
            UntypedExpr::bin_op(&op, acc, ex.clone())
        }),
    ))
}

pub fn expr_op_6l(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, e1) = expr_op_7l(input)?;
    let (input, e2) = many0(|input| {
        let (input, op) = alt((symbol("+"), symbol("-")))(input)?;
        let (input, ex) = expr_op_7l(input)?;
        Ok((input, (op, ex)))
    })(input)?;
    Ok((
        input,
        e2.iter().fold(e1, |acc, (op, ex)| {
            UntypedExpr::bin_op(&op, acc, ex.clone())
        }),
    ))
}

pub fn expr_op_4n(input: &str) -> IResult<&str, UntypedExpr> {
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
        Some((op, e2)) => Ok((input, UntypedExpr::bin_op(op, e1, e2))),
        None => Ok((input, e1)),
    }
}

pub fn expr_op_0n(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, e1) = expr_op_4n(input)?;
    let (input, optional) = opt(|input| {
        let (input, op) = alt((tag(":="),))(input)?;
        let (input, e2) = expr_op_4n(input)?;
        Ok((input, (op, e2)))
    })(input)?;
    match optional {
        Some((op, e2)) => Ok((input, UntypedExpr::bin_op(op, e1, e2))),
        None => Ok((input, e1)),
    }
}

pub fn parser_match_expr(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, e1) = expr_op_0n(input)?;
    let (input, match_arms) = opt(|input| {
        let (input, _) = keyword("match")(input)?;
        let (input, _) = symbol("{")(input)?;
        let (input, match_arms) = separated_list0(symbol(","), |input| {
            let (input, pattern) = parser_pattern(input)?;
            let (input, _) = symbol("=>")(input)?;
            let (input, expr) = parser_expr(input)?;
            Ok((input, (pattern, expr)))
        })(input)?;
        let (input, _) = symbol("}")(input)?;
        Ok((input, match_arms))
    })(input)?;
    match match_arms {
        Some(match_arms) => Ok((input, UntypedExpr::e_match(e1, match_arms))),
        None => Ok((input, e1)),
    }
}

pub fn expr_if(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, _) = symbol("if")(input)?;
    let (input, cond) = delimited(symbol("("), parser_expr, symbol(")"))(input)?;
    let (input, e1) = parser_expr(input)?;
    let (input, _) = symbol("else")(input)?;
    let (input, e2) = parser_expr(input)?;
    Ok((input, UntypedExpr::e_if(cond, e1, e2)))
}

pub fn fun_app(input: &str) -> IResult<&str, UntypedExpr> {
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
                .fold(e, |acc, expr| UntypedExpr::fun_app(acc, expr.clone())),
        )),
    }
}

pub fn expr_string(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, _) = space0(input)?;
    let (input, _) = tag("\"")(input)?;
    let (input, str) = many0(none_of("\""))(input)?;
    let (input, _) = symbol("\"")(input)?;
    Ok((input, UntypedExpr::string(&str.iter().collect::<String>())))
}

fn parse_block_expr(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, _) = symbol("{")(input)?;
    let (input, statement_or_expr_vec) = many1(parser_statement_or_expr)(input)?;
    let (input, _) = symbol("}")(input)?;
    Ok((input, UntypedExpr::e_block_expr(statement_or_expr_vec)))
}

pub fn statement_assign(input: &str) -> IResult<&str, UntypedStatement> {
    let (input, _) = keyword("let")(input)?;
    let (input, id) = identifier(input)?;
    let (input, _) = symbol("=")(input)?;
    let (input, e) = parser_expr(input)?;
    let (input, _) = symbol(";")(input)?;
    Ok((input, UntypedStatement::assign(&id, e)))
}

pub fn statement_typedef(input: &str) -> IResult<&str, UntypedStatement> {
    let (input, _) = keyword("enum")(input)?;
    let (input, id) = identifier_start_with_capital(input)?;
    let (input, _) = symbol("{")(input)?;
    let (input, constructors) = separated_list0(symbol(","), |input| {
        let (input, name) = identifier_start_with_capital(input)?;
        let (input, args) = opt(|input| {
            let (input, _) = symbol("(")(input)?;
            let (input, args) = separated_list0(symbol(","), parser_type_init)(input)?;
            let (input, _) = symbol(")")(input)?;
            Ok((input, args))
        })(input)?;
        match args {
            Some(args) => Ok((input, ConstructorDef { name, args })),
            None => Ok((input, ConstructorDef { name, args: vec![] })),
        }
    })(input)?;
    let (input, _) = symbol("}")(input)?;
    let (input, _) = symbol(";")(input)?;
    Ok((input, UntypedStatement::type_def(&id, constructors)))
}

pub fn parser_type_init(input: &str) -> IResult<&str, Type> {
    parser_fun_type(input)
}

pub fn parser_fun_type(input: &str) -> IResult<&str, Type> {
    let (input, t1) = parser_type(input)?;
    let (input, t2) = opt(|input| {
        let (input, _) = symbol("->")(input)?;
        let (input, t2) = parser_fun_type(input)?;
        Ok((input, t2))
    })(input)?;
    match t2 {
        Some(t2) => Ok((input, Type::TFun(Box::new(t1), Box::new(t2)))),
        None => Ok((input, t1)),
    }
}

pub fn parser_type(input: &str) -> IResult<&str, Type> {
    alt((
        delimited(symbol("("), parser_type_init, symbol(")")),
        parser_ref_type,
        parser_vector_type,
        parser_simple_type,
        parser_unit_type,
    ))(input)
}

pub fn parser_simple_type(input: &str) -> IResult<&str, Type> {
    let (input, id) = identifier_start_with_capital(input)?;
    Ok((input, Type::TType(id)))
}

pub fn parser_unit_type(input: &str) -> IResult<&str, Type> {
    let (input, _) = symbol("()")(input)?;
    Ok((input, Type::TType("()".to_owned())))
}

pub fn parser_ref_type(input: &str) -> IResult<&str, Type> {
    let (input, _) = symbol("Ref")(input)?;
    let (input, _) = symbol("[")(input)?;
    let (input, ty) = parser_type_init(input)?;
    let (input, _) = symbol("]")(input)?;
    Ok((input, Type::TRef(Box::new(ty))))
}

pub fn parser_vector_type(input: &str) -> IResult<&str, Type> {
    let (input, _) = symbol("Vector")(input)?;
    let (input, _) = symbol("[")(input)?;
    let (input, ty) = parser_type_init(input)?;
    let (input, _) = symbol("]")(input)?;
    Ok((input, Type::TVector(Box::new(ty))))
}

pub fn fun_def(input: &str) -> IResult<&str, UntypedStatement> {
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
        result = UntypedExpr::e_fun(&args[i], result)
    }
    Ok((input, UntypedStatement::assign(&id, result)))
}

fn identifier(input: &str) -> IResult<&str, String> {
    let (input, _) = multispace0(input)?;
    let (input, first_char) = one_of("abcdefghijklmnopqrstuvwxyz_")(input)?;
    let (input, mut chars) = many0(satisfy(|c| is_alphanumeric(c as u8) || c == '_'))(input)?;
    let (input, _) = multispace0(input)?;
    let is_keyword = |x: &&str| {
        vec![
            "if", "else", "let", "fn", "for", "in", "do", "enum", "match",
        ]
        .contains(x)
    };
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

pub fn identifier_start_with_capital(input: &str) -> IResult<&str, String> {
    let (input, _) = multispace0(input)?;
    let (input, first_char) = one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ")(input)?;
    let (input, mut chars) = many0(satisfy(|c| is_alphanumeric(c as u8) || c == '_'))(input)?;
    let (input, _) = multispace0(input)?;
    chars.insert(0, first_char);
    let ident: String = chars.iter().collect();
    Ok((input, ident))
}

pub fn parser_statement(input: &str) -> IResult<&str, UntypedStatement> {
    let (input, statement) = alt((fun_def, statement_assign, statement_typedef))(input)?;
    Ok((input, statement))
}

pub fn parser_statements(input: &str) -> IResult<&str, UntypedStatements> {
    let (input, statements) = many1(parser_statement)(input)?;
    let (input, _) = eof(input)?;
    Ok((input, statements))
}

pub fn parser_expr<'a>(input: &'a str) -> IResult<&'a str, UntypedExpr> {
    let (input, expr) = parser_match_expr(input)?;
    Ok((input, expr))
}

pub fn parser_statement_or_expr(input: &str) -> IResult<&str, UntypedStatementOrExpr> {
    match parser_statement(input) {
        Ok((input, stmt)) => Ok((input, UntypedStatementOrExpr::statement(stmt))),
        Err(_) => {
            let (input, e) = parser_expr(input)?;
            let (input, _) = symbol(";")(input)?;
            Ok((input, UntypedStatementOrExpr::expr(e)))
        }
    }
}

pub fn parser_statement_or_expr_for_repl(input: &str) -> IResult<&str, UntypedStatementOrExpr> {
    match parser_statement(input) {
        Ok((input, stmt)) => Ok((input, UntypedStatementOrExpr::statement(stmt))),
        Err(_) => {
            let (input, e) = parser_expr(input)?;
            Ok((input, UntypedStatementOrExpr::expr(e)))
        }
    }
}

pub fn parser_for_repl(input: &str) -> IResult<&str, UntypedStatementOrExpr> {
    let (input, stmt) = parser_statement_or_expr_for_repl(input)?;
    let (input, _) = eof(input)?;
    Ok((input, stmt))
}

pub fn dot_expr(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, mut expr) = fun_app(input)?;
    let (input, mut temp_exprs) = many0(|input| {
        let (input, _) = symbol(".")(input)?;
        let (input, ident) = alt((identifier, identifier_start_with_capital))(input)?;
        let (input, args) = opt(|input| {
            let (input, _) = symbol("(")(input)?;
            let (input, args) = separated_list0(symbol(","), parser_expr)(input)?;
            let (input, _) = symbol(")")(input)?;
            Ok((input, args))
        })(input)?;
        let args = args.unwrap_or(vec![]);
        let mut temp_expr = UntypedExpr::e_var(&ident);
        for arg in args {
            temp_expr = UntypedExpr::fun_app(temp_expr, arg);
        }
        Ok((input, temp_expr))
    })(input)?;
    let (input, opt_expr) = opt(block_term)(input)?;
    match opt_expr {
        None => (),
        Some(e) => {
            if temp_exprs.len() == 0 {
                return Ok((input, UntypedExpr::fun_app(expr, e)));
            }
            let len = temp_exprs.len();
            temp_exprs[len - 1] = UntypedExpr::fun_app(temp_exprs[len - 1].clone(), e)
        }
    }
    for temp_expr in temp_exprs {
        expr = UntypedExpr::fun_app(temp_expr, expr)
    }
    Ok((input, expr))
}

pub fn lambda_fn(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, _) = symbol("fn")(input)?;
    let (input, args) = separated_list0(symbol(","), identifier)(input)?;
    let (input, _) = symbol("->")(input)?;
    let (input, mut e) = parser_expr(input)?;
    for i in 0..args.len() {
        let index = args.len() - i - 1;
        e = UntypedExpr::e_fun(&args[index], e)
    }
    Ok((input, e))
}

pub fn lambda_block_fn(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, _) = symbol("{")(input)?;
    let (input, _) = symbol("fn")(input)?;
    let (input, args) = separated_list0(symbol(","), identifier)(input)?;
    let (input, _) = symbol("->")(input)?;
    let (input, statement_or_expr_vec) = many1(parser_statement_or_expr)(input)?;
    let (input, _) = symbol("}")(input)?;
    let mut expr = UntypedExpr::e_block_expr(statement_or_expr_vec);
    for i in 0..args.len() {
        let index = args.len() - i - 1;
        expr = UntypedExpr::e_fun(&args[index], expr)
    }
    Ok((input, expr))
}

pub fn expr_vector(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, vec) = delimited(
        symbol("["),
        separated_list0(symbol(","), parser_expr),
        symbol("]"),
    )(input)?;
    Ok((input, UntypedExpr::e_vector(vec)))
}

pub fn for_in_expr(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, _) = symbol("for")(input)?;
    let (input, _) = symbol("(")(input)?;
    let (input, ident) = identifier(input)?;
    let (input, _) = symbol("in")(input)?;
    let (input, vec) = parser_expr(input)?;
    let (input, _) = symbol(")")(input)?;
    let (input, expr) = parser_expr(input)?;
    Ok((
        input,
        UntypedExpr::fun_app(
            UntypedExpr::fun_app(
                UntypedExpr::e_var("foreach"),
                UntypedExpr::e_fun(&ident, expr),
            ),
            vec,
        ),
    ))
}

pub fn enum_vec_expr(input: &str) -> IResult<&str, UntypedExpr> {
    let (input, _) = symbol("[")(input)?;
    let (input, e1) = parser_expr(input)?;
    let (input, op) = alt((symbol("..="), symbol("..")))(input)?;
    let (input, e2) = parser_expr(input)?;
    let (input, _) = symbol("]")(input)?;
    match op {
        "..=" => Ok((
            input,
            UntypedExpr::fun_app(
                UntypedExpr::fun_app(UntypedExpr::e_var("enum_from_until"), e1),
                e2,
            ),
        )),
        ".." => Ok((
            input,
            UntypedExpr::fun_app(
                UntypedExpr::fun_app(UntypedExpr::e_var("enum_from_to"), e1),
                e2,
            ),
        )),
        _ => panic!("internal error"),
    }
}

pub fn parser_pattern(input: &str) -> IResult<&str, UntypedPattern> {
    alt((
        parser_constructor_pattern,
        parser_variable_pattern,
        parser_value_pattern,
    ))(input)
}

pub fn parser_variable_pattern(input: &str) -> IResult<&str, UntypedPattern> {
    let (input, var) = identifier(input)?;
    Ok((input, UntypedPattern::p_var(&var)))
}

pub fn parser_value_pattern(input: &str) -> IResult<&str, UntypedPattern> {
    let (input, expr) = alt((expr_int, parser_unit))(input)?;
    Ok((input, UntypedPattern::p_value(expr)))
}

pub fn parser_constructor_pattern(input: &str) -> IResult<&str, UntypedPattern> {
    let (input, name) = identifier_start_with_capital(input)?;
    let (input, args) = opt(|input| {
        delimited(
            symbol("("),
            separated_list0(symbol(","), parser_pattern),
            symbol(")"),
        )(input)
    })(input)?;
    match args {
        Some(args) => Ok((input, UntypedPattern::p_constructor(&name, args))),
        None => Ok((input, UntypedPattern::p_constructor(&name, vec![]))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_unary_expr() {
        assert_eq!(
            parser_expr("-3"),
            Ok(("", UntypedExpr::e_unary("-", UntypedExpr::e_int(3))))
        );
        assert_eq!(
            parser_expr("*3"),
            Ok(("", UntypedExpr::e_unary("*", UntypedExpr::e_int(3))))
        );
        assert_eq!(
            parser_expr("&3"),
            Ok(("", UntypedExpr::e_unary("&", UntypedExpr::e_int(3))))
        );
        assert_eq!(
            parser_expr("-3+3"),
            Ok((
                "",
                UntypedExpr::bin_op(
                    "+",
                    UntypedExpr::e_unary("-", UntypedExpr::e_int(3)),
                    UntypedExpr::e_int(3)
                )
            ))
        );
    }

    #[test]
    fn test_op_expr() {
        assert_eq!(
            parser_expr("1 + 1"),
            Ok((
                "",
                UntypedExpr::bin_op("+", UntypedExpr::e_int(1), UntypedExpr::e_int(1))
            ))
        );
        assert_eq!(
            parser_expr("1 + 1 * 1"),
            Ok((
                "",
                UntypedExpr::bin_op(
                    "+",
                    UntypedExpr::e_int(1),
                    UntypedExpr::bin_op("*", UntypedExpr::e_int(1), UntypedExpr::e_int(1))
                )
            ))
        );
        assert_eq!(
            parser_expr("1 + (2 * 3)"),
            Ok((
                "",
                UntypedExpr::bin_op(
                    "+",
                    UntypedExpr::e_int(1),
                    UntypedExpr::bin_op("*", UntypedExpr::e_int(2), UntypedExpr::e_int(3))
                )
            ))
        );
        assert_eq!(
            parser_expr("1<2"),
            Ok((
                "",
                UntypedExpr::bin_op("<", UntypedExpr::e_int(1), UntypedExpr::e_int(2))
            ))
        );
        assert_eq!(
            parser_expr("1%2"),
            Ok((
                "",
                UntypedExpr::bin_op("%", UntypedExpr::e_int(1), UntypedExpr::e_int(2))
            ))
        );
        assert_eq!(
            parser_expr("1<1+1"),
            Ok((
                "",
                UntypedExpr::bin_op(
                    "<",
                    UntypedExpr::e_int(1),
                    UntypedExpr::bin_op("+", UntypedExpr::e_int(1), UntypedExpr::e_int(1))
                )
            ))
        );
        assert_eq!(
            parser_expr("a:=3"),
            Ok((
                "",
                UntypedExpr::bin_op(":=", UntypedExpr::e_var("a"), UntypedExpr::e_int(3))
            ))
        );
        assert_eq!(
            parser_expr("a+b"),
            Ok((
                "",
                UntypedExpr::bin_op("+", UntypedExpr::e_var("a"), UntypedExpr::e_var("b"))
            ))
        );
        assert_eq!(
            parser_expr("a + b"),
            Ok((
                "",
                UntypedExpr::bin_op("+", UntypedExpr::e_var("a"), UntypedExpr::e_var("b"))
            ))
        );
        assert_eq!(
            parser_expr("add(2, 3)"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::fun_app(UntypedExpr::e_var("add"), UntypedExpr::e_int(2)),
                    UntypedExpr::e_int(3)
                )
            )),
        )
    }

    #[test]
    fn test_string_expr() {
        assert_eq!(
            parser_expr(r#""Hello, world!""#),
            Ok(("", UntypedExpr::string("Hello, world!")))
        );
        assert_eq!(parser_expr(r#""""#), Ok(("", UntypedExpr::string(""))));
        assert_eq!(expr_string(r#"" ""#), Ok(("", UntypedExpr::string(" "))));
    }

    #[test]
    fn test_unit_expr() {
        assert_eq!(parser_expr("()"), Ok(("", UntypedExpr::e_unit())))
    }

    #[test]
    fn test_if_expr() {
        assert_eq!(
            parser_expr("if (1<2) 1 else 2"),
            Ok((
                "",
                UntypedExpr::e_if(
                    UntypedExpr::bin_op("<", UntypedExpr::e_int(1), UntypedExpr::e_int(2)),
                    UntypedExpr::e_int(1),
                    UntypedExpr::e_int(2)
                )
            ))
        );
    }

    #[test]
    fn test_fun_app() {
        assert_eq!(
            parser_expr("add(2, 3)"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::fun_app(UntypedExpr::e_var("add"), UntypedExpr::e_int(2)),
                    UntypedExpr::e_int(3)
                )
            )),
        );
        assert_eq!(
            dot_expr("{add;}(2, 3)"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::fun_app(
                        UntypedExpr::e_block_expr(vec![UntypedStatementOrExpr::expr(
                            UntypedExpr::e_var("add")
                        )]),
                        UntypedExpr::e_int(2)
                    ),
                    UntypedExpr::e_int(3)
                )
            )),
        );
        assert_eq!(
            dot_expr("add(2) {3;}"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::fun_app(UntypedExpr::e_var("add"), UntypedExpr::e_int(2)),
                    UntypedExpr::e_block_expr(vec![UntypedStatementOrExpr::expr(
                        UntypedExpr::e_int(3)
                    )])
                )
            )),
        );
    }

    #[test]
    fn test_match_expr() {
        assert_eq!(
            parser_expr(
                "hoge match {
            Some(n) => n,
            None => 0
        }"
            ),
            Ok((
                "",
                UntypedExpr::e_match(
                    UntypedExpr::e_var("hoge"),
                    vec![
                        (
                            UntypedPattern::p_constructor("Some", vec![UntypedPattern::p_var("n")]),
                            UntypedExpr::e_var("n")
                        ),
                        (
                            UntypedPattern::p_constructor("None", vec![]),
                            UntypedExpr::e_int(0)
                        )
                    ]
                )
            ))
        )
    }

    #[test]
    fn test_parse_block_expr() {
        assert_eq!(
            parse_block_expr(
                "{
        let x = 1;
        x + 1;
    }"
            ),
            Ok((
                "",
                UntypedExpr::e_block_expr(vec![
                    UntypedStatementOrExpr::statement(UntypedStatement::assign(
                        "x",
                        UntypedExpr::e_int(1)
                    )),
                    UntypedStatementOrExpr::expr(UntypedExpr::bin_op(
                        "+",
                        UntypedExpr::e_var("x"),
                        UntypedExpr::e_int(1)
                    ))
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
                UntypedExpr::e_block_expr(vec![
                    UntypedStatementOrExpr::statement(UntypedStatement::assign(
                        "x",
                        UntypedExpr::e_int(1)
                    )),
                    UntypedStatementOrExpr::expr(UntypedExpr::bin_op(
                        "+",
                        UntypedExpr::e_var("x"),
                        UntypedExpr::e_int(1)
                    ))
                ])
            ))
        )
    }

    #[test]
    fn test_assign_statement() {
        assert_eq!(
            statement_assign("let a = 1;"),
            Ok(("", UntypedStatement::assign("a", UntypedExpr::e_int(1))))
        );
    }

    #[test]
    fn test_typedef_statement() {
        assert_eq!(
            statement_typedef("enum Hoge {Foo(Bar, Huga), Huge};"),
            Ok((
                "",
                UntypedStatement::type_def(
                    "Hoge",
                    vec![
                        ConstructorDef {
                            name: "Foo".to_owned(),
                            args: vec![
                                Type::TType("Bar".to_owned()),
                                Type::TType("Huga".to_owned())
                            ]
                        },
                        ConstructorDef {
                            name: "Huge".to_owned(),
                            args: vec![]
                        }
                    ]
                )
            ))
        )
    }

    #[test]
    fn test_parser_type() {
        assert_eq!(
            parser_type_init("Int"),
            Ok(("", Type::TType("Int".to_owned())))
        );
        assert_eq!(
            parser_type_init("Int -> Int"),
            Ok((
                "",
                Type::TFun(
                    Box::new(Type::TType("Int".to_owned())),
                    Box::new(Type::TType("Int".to_owned())),
                )
            ))
        );
        assert_eq!(
            parser_type_init("Int -> Bool -> Int"),
            Ok((
                "",
                Type::TFun(
                    Box::new(Type::TType("Int".to_owned())),
                    Box::new(Type::TFun(
                        Box::new(Type::TType("Bool".to_owned())),
                        Box::new(Type::TType("Int".to_owned()))
                    )),
                )
            ))
        );
        assert_eq!(
            parser_type_init("()"),
            Ok(("", Type::TType("()".to_owned())))
        );
        assert_eq!(
            parser_type_init("Ref[Int]"),
            Ok(("", Type::TRef(Box::new(Type::TType("Int".to_owned())))))
        );
        assert_eq!(
            parser_type_init("Vector[Bool]"),
            Ok(("", Type::TVector(Box::new(Type::TType("Bool".to_owned())))))
        );
        assert_eq!(
            parser_type_init("(Int -> Int)"),
            Ok((
                "",
                Type::TFun(
                    Box::new(Type::TType("Int".to_owned())),
                    Box::new(Type::TType("Int".to_owned())),
                )
            ))
        );
    }

    #[test]
    pub fn test_fun_def() {
        assert_eq!(
            fun_def("let add(a, b) = a + b;"),
            Ok((
                "",
                UntypedStatement::assign(
                    "add",
                    UntypedExpr::e_fun(
                        "a",
                        UntypedExpr::e_fun(
                            "b",
                            UntypedExpr::bin_op(
                                "+",
                                UntypedExpr::e_var("a"),
                                UntypedExpr::e_var("b")
                            )
                        )
                    )
                )
            ))
        )
    }

    #[test]
    fn test_identifier() {
        assert_eq!(identifier("aA3B").unwrap().1, "aA3B".to_string());
        assert!(identifier("PA3B").is_err());
        assert_eq!(identifier("a3Bse").unwrap().1, "a3Bse".to_string());
        assert_eq!(
            identifier("int_to_string").unwrap().1,
            "int_to_string".to_string()
        );
    }

    #[test]
    pub fn test_parser_statement() {
        assert_eq!(
            parser_statement("let main = 1;"),
            Ok(("", UntypedStatement::assign("main", UntypedExpr::e_int(1)))),
        );
        assert_eq!(
            parser_statement("let add(a, b) = a + b;"),
            Ok((
                "",
                UntypedStatement::assign(
                    "add",
                    UntypedExpr::e_fun(
                        "a",
                        UntypedExpr::e_fun(
                            "b",
                            UntypedExpr::bin_op(
                                "+",
                                UntypedExpr::e_var("a"),
                                UntypedExpr::e_var("b")
                            )
                        )
                    )
                )
            ))
        );
    }

    #[test]
    fn test_parser_statements() {
        assert_eq!(
            parser_statements("let main = 1;"),
            Ok((
                "",
                vec![UntypedStatement::assign("main", UntypedExpr::e_int(1))]
            ))
        );
        assert_eq!(
            parser_statements("let main = a + b;"),
            Ok((
                "",
                vec![UntypedStatement::assign(
                    "main",
                    UntypedExpr::bin_op("+", UntypedExpr::e_var("a"), UntypedExpr::e_var("b"))
                ),]
            ))
        );
        assert_eq!(
            parser_statements("let a = 1; let b = 2;"),
            Ok((
                "",
                vec![
                    UntypedStatement::assign("a", UntypedExpr::e_int(1)),
                    UntypedStatement::assign("b", UntypedExpr::e_int(2))
                ]
            ))
        );
        assert_eq!(
            parser_statements("let a = 1; let b = 2; let main = a + b;"),
            Ok((
                "",
                vec![
                    UntypedStatement::assign("a", UntypedExpr::e_int(1)),
                    UntypedStatement::assign("b", UntypedExpr::e_int(2)),
                    UntypedStatement::assign(
                        "main",
                        UntypedExpr::bin_op("+", UntypedExpr::e_var("a"), UntypedExpr::e_var("b"))
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_dot_expr() {
        assert_eq!(
            dot_expr("3.inc"),
            Ok((
                "",
                UntypedExpr::fun_app(UntypedExpr::e_var("inc"), UntypedExpr::e_int(3))
            ))
        );
        assert_eq!(
            dot_expr("3.inc()"),
            Ok((
                "",
                UntypedExpr::fun_app(UntypedExpr::e_var("inc"), UntypedExpr::e_int(3))
            ))
        );
        assert_eq!(
            dot_expr("3.add(2)"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::fun_app(UntypedExpr::e_var("add"), UntypedExpr::e_int(2)),
                    UntypedExpr::e_int(3)
                )
            ))
        );
        assert_eq!(
            dot_expr("add(2, 3).inc"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::e_var("inc"),
                    UntypedExpr::fun_app(
                        UntypedExpr::fun_app(UntypedExpr::e_var("add"), UntypedExpr::e_int(2)),
                        UntypedExpr::e_int(3)
                    )
                )
            ))
        );
        assert_eq!(
            dot_expr("3.add(2).add(4)"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::fun_app(UntypedExpr::e_var("add"), UntypedExpr::e_int(4)),
                    UntypedExpr::fun_app(
                        UntypedExpr::fun_app(UntypedExpr::e_var("add"), UntypedExpr::e_int(2)),
                        UntypedExpr::e_int(3)
                    )
                )
            ))
        );
        assert_eq!(
            dot_expr("3.add {2;}"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::fun_app(
                        UntypedExpr::e_var("add"),
                        UntypedExpr::e_block_expr(vec![UntypedStatementOrExpr::expr(
                            UntypedExpr::e_int(2)
                        )])
                    ),
                    UntypedExpr::e_int(3)
                )
            ))
        );
        assert_eq!(
            dot_expr("3.add() {2;}"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::fun_app(
                        UntypedExpr::e_var("add"),
                        UntypedExpr::e_block_expr(vec![UntypedStatementOrExpr::expr(
                            UntypedExpr::e_int(2)
                        )])
                    ),
                    UntypedExpr::e_int(3)
                )
            ))
        );
    }

    #[test]
    fn test_lambda_fn() {
        assert_eq!(
            lambda_fn("fn x -> x"),
            Ok(("", UntypedExpr::e_fun("x", UntypedExpr::e_var("x"))))
        );
    }

    #[test]
    fn test_lambda_block() {
        assert_eq!(
            lambda_block_fn("{fn x -> x; x;}"),
            Ok((
                "",
                UntypedExpr::e_fun(
                    "x",
                    UntypedExpr::e_block_expr(vec![
                        UntypedStatementOrExpr::expr(UntypedExpr::e_var("x")),
                        UntypedStatementOrExpr::expr(UntypedExpr::e_var("x"))
                    ])
                )
            ))
        );
        assert_eq!(
            parser_expr("hoge {fn x -> x; x;}"),
            Ok((
                "",
                UntypedExpr::fun_app(
                    UntypedExpr::e_var("hoge"),
                    UntypedExpr::e_fun(
                        "x",
                        UntypedExpr::e_block_expr(vec![
                            UntypedStatementOrExpr::expr(UntypedExpr::e_var("x")),
                            UntypedStatementOrExpr::expr(UntypedExpr::e_var("x"))
                        ])
                    )
                )
            ))
        );
    }

    #[test]
    fn test_vector_expr() {
        assert_eq!(
            expr_vector("[1, 2, 3]"),
            Ok((
                "",
                UntypedExpr::e_vector(vec![
                    UntypedExpr::e_int(1),
                    UntypedExpr::e_int(2),
                    UntypedExpr::e_int(3)
                ])
            ))
        );
    }

    #[test]
    fn test_parser_pattern() {
        assert_eq!(
            parser_pattern("3"),
            Ok(("", UntypedPattern::p_value(UntypedExpr::e_int(3))))
        );
        assert_eq!(
            parser_pattern("()"),
            Ok(("", UntypedPattern::p_value(UntypedExpr::e_unit())))
        );
        assert_eq!(parser_pattern("n"), Ok(("", UntypedPattern::p_var("n"))));
        assert_eq!(
            parser_pattern("Foo(3)"),
            Ok((
                "",
                UntypedPattern::p_constructor(
                    "Foo",
                    vec![UntypedPattern::p_value(UntypedExpr::e_int(3))]
                )
            ))
        );
        assert_eq!(
            parser_pattern("Foo(x)"),
            Ok((
                "",
                UntypedPattern::p_constructor("Foo", vec![UntypedPattern::p_var("x")])
            ))
        );
        assert_eq!(
            parser_pattern("Foo(3, x)"),
            Ok((
                "",
                UntypedPattern::p_constructor(
                    "Foo",
                    vec![
                        UntypedPattern::p_value(UntypedExpr::e_int(3)),
                        UntypedPattern::p_var("x")
                    ]
                )
            ))
        );
    }
}
