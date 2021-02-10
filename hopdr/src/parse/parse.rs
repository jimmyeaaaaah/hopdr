use super::hes::{Clause, Expr, Fixpoint, NuHFLzValidityChecking, Problem};
use crate::formula::{OpKind, PredKind};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_while},
    character::complete::{alpha1, char, digit1, one_of},
    combinator::{map, map_res},
    error::ParseError,
    multi::{fold_many0, separated_list},
    sequence::{pair, preceded},
    IResult,
};
use std::str::FromStr;

fn sp<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    let chars = " \t\r\n";
    take_while(move |c| chars.contains(c))(input)
}

fn sp1<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, char, E> {
    one_of(" \t\r\n")(input)
}

fn ident<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    alpha1(input)
}

fn parse_var<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, ident) = preceded(sp, ident)(input)?;
    Ok((input, Expr::mk_var(String::from(ident))))
}

fn parse_par<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, _) = preceded(sp, char('('))(input)?;
    let (input, expr) = parse_expr(input)?;
    let (input, _) = preceded(sp, char(')'))(input)?;
    Ok((input, expr))
}

fn parse_bool<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    alt((
        map(tag("true"), |_| Expr::mk_true()),
        map(tag("false"), |_| Expr::mk_false()),
    ))(input)
}

// 負の数
fn parse_num<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, num) = map_res(preceded(sp, digit1), FromStr::from_str)(input)?;
    Ok((input, Expr::mk_num(num)))
}

fn pred<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, PredKind, E> {
    alt((
        map(tag(">"), |_| PredKind::Gt),
        map(tag("<="), |_| PredKind::Leq),
        map(tag("="), |_| PredKind::Eq),
        map(tag("!="), |_| PredKind::Neq),
    ))(input)
}

fn op1<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, OpKind, E> {
    alt((
        map(tag("+"), |_| OpKind::Add),
        map(tag("-"), |_| OpKind::Sub),
    ))(input)
}

fn op2<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, OpKind, E> {
    let (i, _) = char('*')(input)?;
    Ok((i, OpKind::Mul))
}

fn parse_atom<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    alt((parse_var, parse_par, parse_num, parse_bool))(input)
}

fn parse_arith2<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, e1) = preceded(sp, parse_atom)(input)?;
    fold_many0(
        pair(preceded(sp, op2), preceded(sp, parse_atom)),
        e1,
        |e1, (op, e2)| Expr::mk_op(op, e1, e2),
    )(input)
}

fn parse_arith<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, e1) = preceded(sp, parse_arith2)(input)?;
    fold_many0(
        pair(preceded(sp, op1), preceded(sp, parse_arith2)),
        e1,
        |e1, (op, e2)| Expr::mk_op(op, e1, e2),
    )(input)
}

fn parse_pred<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, e1) = preceded(sp, parse_arith)(input)?;
    fold_many0(
        pair(preceded(sp, pred), preceded(sp, parse_arith)),
        e1,
        |e1, (pred, e2)| Expr::mk_pred(pred, e1, e2),
    )(input)
}

fn parse_app<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, e1) = preceded(sp, parse_pred)(input)?;
    fold_many0(pair(sp1, preceded(sp, parse_pred)), e1, |e1, (_, e2)| {
        Expr::mk_app(e1, e2)
    })(input)
}

fn parse_and<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, e1) = preceded(sp, parse_app)(input)?;
    fold_many0(
        pair(preceded(sp, char('&')), preceded(sp, parse_app)),
        e1,
        |e1, (_, e2)| Expr::mk_and(e1, e2),
    )(input)
}

fn parse_or<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, e1) = preceded(sp, parse_and)(input)?;
    fold_many0(
        pair(preceded(sp, char('|')), preceded(sp, parse_and)),
        e1,
        |e1, (_, e2)| Expr::mk_or(e1, e2),
    )(input)
}

fn parse_expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    alt((parse_or, parse_var))(input)
}

fn parse_hes<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Clause, E> {
    let (input, id) = preceded(sp, map(ident, String::from))(input)?;
    let (input, args) = separated_list(sp1, preceded(sp, map(ident, String::from)))(input)?;
    let (input, _) = preceded(sp, char('='))(input)?;
    let (input, expr) = preceded(sp, parse_expr)(input)?;
    let (input, _) = preceded(sp, char(';'))(input)?;
    let fixpoint = Fixpoint::Greatest;
    Ok((
        input,
        Clause {
            fixpoint,
            id,
            args,
            expr,
        },
    ))
}

pub fn parse<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Problem, E> {
    let v = Vec::new();
    let (input, mut formulas) = fold_many0(parse_hes, v, |mut v, hes| {
        v.push(hes);
        v
    })(input)?;
    // tentative
    let toplevel = formulas.pop().unwrap().expr;

    Ok((
        input,
        Problem::NuHFLZValidityChecking(NuHFLzValidityChecking { formulas, toplevel }),
    ))
}
