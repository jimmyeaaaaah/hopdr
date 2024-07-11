use super::hes::{Clause, Expr, Fixpoint, NuHFLzValidityChecking, Problem};
use crate::formula::{OpKind, PredKind};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_while},
    character::complete::{alpha1, alphanumeric1, char, digit1, one_of},
    combinator::{map, map_res, opt},
    error::ParseError,
    multi::{fold_many0, many0, separated_list},
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

fn ident<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, String, E> {
    let (input, (i1, i2)) = pair(
        alt((alpha1, tag("_"))),
        many0(alt((alphanumeric1, tag("_"), tag("!")))),
    )(input)?;
    let mut s = i1.to_string();
    for s2 in i2 {
        s += s2;
    }
    Ok((input, s))
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

fn parse_num<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    // handle negative number
    let (input, sign) = opt(preceded(sp, char('-')))(input)?;
    let (input, num): (_, i64) = map_res(preceded(sp, digit1), FromStr::from_str)(input)?;
    let num = if sign.is_some() { -num } else { num };
    Ok((input, Expr::mk_num(num)))
}

fn pred<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, PredKind, E> {
    alt((
        map(tag("<="), |_| PredKind::Leq),
        map(tag(">="), |_| PredKind::Geq),
        map(tag("!="), |_| PredKind::Neq),
        map(tag("<>"), |_| PredKind::Neq),
        map(tag(">"), |_| PredKind::Gt),
        map(tag("="), |_| PredKind::Eq),
        map(tag("<"), |_| PredKind::Lt),
    ))(input)
}

fn op1<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, OpKind, E> {
    alt((
        map(tag("+"), |_| OpKind::Add),
        map(tag("-"), |_| OpKind::Sub),
    ))(input)
}

fn op2<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, OpKind, E> {
    alt((
        map(tag("*"), |_| OpKind::Mul),
        map(tag("/"), |_| OpKind::Div),
        map(tag("%"), |_| OpKind::Mod),
    ))(input)
}
fn parse_neg<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, _) = preceded(sp, char('-'))(input)?;
    let (input, e) = parse_atom(input)?;
    Ok((input, Expr::mk_op(OpKind::Sub, Expr::mk_num(0), e)))
}

fn parse_atom<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    alt((parse_par, parse_num, parse_neg, parse_bool, parse_var))(input)
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
        pair(
            preceded(sp, alt((tag("&&"), tag("&"), tag("/\\")))),
            preceded(sp, parse_app),
        ),
        e1,
        |e1, (_, e2)| Expr::mk_and(e1, e2),
    )(input)
}

fn parse_or<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, e1) = preceded(sp, parse_and)(input)?;
    fold_many0(
        pair(
            preceded(sp, alt((tag("||"), tag("|"), tag("\\/")))),
            preceded(sp, parse_and),
        ),
        e1,
        |e1, (_, e2)| Expr::mk_or(e1, e2),
    )(input)
}

fn parse_lambda<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, _) = preceded(sp, alt((char('\\'), char('λ'))))(input)?;
    let (input, id) = preceded(sp, map(ident, String::from))(input)?;
    let (input, _) = preceded(sp, char('.'))(input)?;
    let (input, e) = preceded(sp, parse_expr)(input)?;
    Ok((input, Expr::mk_abs(id, e)))
}

fn parse_forall<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, _) = preceded(sp, char('∀'))(input)?;
    let (input, id) = preceded(sp, map(ident, String::from))(input)?;
    let (input, _) = preceded(sp, char('.'))(input)?;
    let (input, e) = preceded(sp, parse_expr)(input)?;
    Ok((input, Expr::mk_univ(id, e)))
}

pub fn parse_expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    alt((parse_lambda, parse_forall, parse_or, parse_var))(input)
}

pub fn parse_hes<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Clause, E> {
    let (input, id) = preceded(sp, map(ident, String::from))(input)?;
    let (input, args) = separated_list(sp1, preceded(sp, map(ident, String::from)))(input)?;
    let (input, _) = preceded(sp, tag("=v"))(input)?;
    let (input, expr) = preceded(sp, parse_expr)(input)?;
    let (input, _) = preceded(sp, char('.'))(input)?;
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

#[test]
fn test_parse_hes_1() {
    use nom::error::VerboseError;
    let s = "S n k =v (n > 0 || k 0) && (n <= 0 || S (n - 1) (\\r. k (r + n))).";
    let (s, c) = parse_hes::<VerboseError<&str>>(s).unwrap();
    assert_eq!(s, "");
    assert_eq!(c.args.len(), 2);
    assert_eq!(c.fixpoint, Fixpoint::Greatest);
}
#[test]
fn test_parse_hes_2() {
    use nom::error::VerboseError;
    let s = "M =v ∀ x. S x (\\r. r >= x).";
    let (s, c) = parse_hes::<VerboseError<&str>>(s).unwrap();
    assert_eq!(s, "");
    assert_eq!(c.args.len(), 0);
    assert_eq!(c.fixpoint, Fixpoint::Greatest);
}
#[test]
fn test_parse_expr() {
    use nom::error::VerboseError;
    let table = vec![
        ("∀x.true", Expr::mk_univ("x".to_string(), Expr::mk_true())),
        ("\\x.true", Expr::mk_abs("x".to_string(), Expr::mk_true())),
        (
            "true || false && false",
            Expr::mk_or(
                Expr::mk_true(),
                Expr::mk_and(Expr::mk_false(), Expr::mk_false()),
            ),
        ),
        (
            "(-2*x_397 + 2*x_398) <= 0",
            Expr::mk_pred(
                PredKind::Leq,
                Expr::mk_op(
                    OpKind::Add,
                    Expr::mk_op(
                        OpKind::Mul,
                        Expr::mk_num(-2),
                        Expr::mk_var("x_397".to_string()),
                    ),
                    Expr::mk_op(
                        OpKind::Mul,
                        Expr::mk_num(2),
                        Expr::mk_var("x_398".to_string()),
                    ),
                ),
                Expr::mk_num(0),
            ),
        ),
    ];
    for (s, r) in table.into_iter() {
        let (s, c) = parse_expr::<VerboseError<&str>>(s).unwrap();
        assert_eq!(s, "");
        assert_eq!(r, c);
    }
}

pub fn parse<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Problem, E> {
    let (input, _) = preceded(sp, tag("%HES"))(input)?;
    let (input, toplevel) = parse_hes(input)?;

    let (input, formulas) = fold_many0(parse_hes, Vec::new(), |mut v, hes| {
        v.push(hes);
        v
    })(input)?;
    let toplevel = toplevel.expr;

    Ok((
        input,
        Problem::NuHFLZValidityChecking(NuHFLzValidityChecking { formulas, toplevel }),
    ))
}
#[test]
fn test_parse() {
    use nom::error::VerboseError;
    let (_, f) = parse::<VerboseError<&str>>(
        "
        %HES
        M =v ∀ x. S x (K x).
        S n k =v (n > 0 || k 0) && (n <= 0 || S (n - 1) (L n k)).
        K m n =v m <= n.
        L n k m =v k (n + m).
         ",
    )
    .unwrap();
    match f {
        Problem::NuHFLZValidityChecking(vc) => {
            assert_eq!(vc.formulas.len(), 3);
            let toplevel = Expr::mk_univ(
                "x".to_string(),
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_var("S".to_string()), Expr::mk_var("x".to_string())),
                    Expr::mk_app(Expr::mk_var("K".to_string()), Expr::mk_var("x".to_string())),
                ),
            );
            assert_eq!(toplevel, vc.toplevel);
        }
    }
}

#[test]
fn test_edge_case() {
    let s = "
    %HES
    Sentry =v RF 1 (-1) 0 (-1) 0.
    RF x r =v r <> -x + 2.
    ";
    use nom::error::VerboseError;
    let (_, f) = parse::<VerboseError<&str>>(s).unwrap();
    let Problem::NuHFLZValidityChecking(vc) = f;

    assert_eq!(vc.formulas.len(), 1);

    let rf = &vc.formulas[0];
    let rf_body = Expr::mk_pred(
        PredKind::Neq,
        Expr::mk_var("r".to_string()),
        Expr::mk_op(
            OpKind::Add,
            Expr::mk_op(OpKind::Sub, Expr::mk_num(0), Expr::mk_var("x".to_string())),
            Expr::mk_num(2),
        ),
    );
    println!("{}", rf_body);
    println!("{}", rf.expr);
    assert_eq!(rf.expr, rf_body);
}
