
use std::collections::VecDeque;
use std::fmt;

use logos::Logos;

use codespan_reporting::diagnostic::{Label, Diagnostic};

use crate::lib::names::fv;

#[derive(Logos, Debug, PartialEq, Clone)]
enum Token {
    // Tokens can be literal strings, of any length.
    #[token("λ")]
    Lambda,
    #[token(".")]
    Dot,

    #[token("->")]
    Arrow,

    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,
    #[token(":=")]
    Walrus,

    #[regex("Type", |_lex| Some(0))]
    #[regex("Type [0-9][1-9]*", |lex| { let slice = lex.slice(); slice[5..slice.len()].parse() })]
    Type(u32),

    #[regex("let")]
    Let,

    #[regex("true")]
    True,
    #[regex("false")]
    False,
    #[regex("if")]
    If,
    #[regex("then")]
    Then,
    #[regex("else")]
    Else,
    #[regex("bool")]
    Bool,

    #[regex("[a-zA-Z][_a-zA-Z]*", |lex| lex.slice().parse())]
    Identifier(String),

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error,
}
impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Lambda => write!(f, "λ"),
            Token::Dot => write!(f, "."),
            Token::Identifier(x) => write!(f, "{}", x),
            Token::Error => write!(f, "ERROR"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::Colon => write!(f, ":"),
            Token::Arrow => write!(f, "->"),
            Token::Type(0) => write!(f, "Type"),
            Token::Type(n) => write!(f, "Type {}", n),
            Token::Walrus => write!(f, ":="),
            Token::Let => write!(f, "let"),
            Token::Semicolon => write!(f, ";"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::If => write!(f, "if"),
            Token::Then => write!(f, "then"),
            Token::Else => write!(f, "else"),
            Token::Bool => write!(f, "bool"),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum EPreterm {
    Lambda(String, Option<Box<Preterm>>, Box<Preterm>),
    App(Box<Preterm>, Box<Preterm>),
    Var(String),

    Unit,
    Type(u32),
    Kind,

    Let(String, Option<Box<Preterm>>, Box<Preterm>, Box<Preterm>),

    True,
    False,
    If(Box<Preterm>, Box<Preterm>, Box<Preterm>),
    Bool,

    // typed hole; index into arena which contains the constraints
    Ex(String, usize),

    TAnnot(Box<Preterm>, Box<Preterm>)
}
#[derive(Clone, PartialEq, Debug)]
pub struct Preterm(pub EPreterm, pub Option<logos::Span>);

macro_rules! rc {
    ( $id0 : expr, $id1 : expr ) => { std::cmp::min($id0.start, $id1.start)..std::cmp::max($id0.end, $id1.end) }
}

impl fmt::Display for Preterm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.0 {
            EPreterm::Type(0) => write!(f, "Type"),
            EPreterm::Type(n) => write!(f, "Type {}", n),
            EPreterm::Kind => write!(f, "Kind"),
            EPreterm::True => write!(f, "true"),
            EPreterm::False => write!(f, "false"),
            EPreterm::Bool => write!(f, "bool"),
            EPreterm::If(a,b,c) => write!(f, "if {} then {} else {}", a, b, c),
            EPreterm::Var(x) => write!(f, "{}", x),
            EPreterm::App(a,b) => {
                match (&(*a).0,&(*b).0) {
                    (EPreterm::Var(_),EPreterm::Var(_)) => write!(f, "{} {}", a, b),
                    (EPreterm::Var(_),_) => write!(f, "{} ({})", a, b),
                    (EPreterm::Lambda(_,_,_),_) => write!(f, "({}) {}", a, b),
                    (_,EPreterm::App(_,_)) => write!(f, "{} ({})", a, b),
                    (_,_) => write!(f, "({} {})", a, b),
                }
            },
            EPreterm::Ex(x, es) => write!(f, "{}{{{}}}", x, es),
            EPreterm::Let(x, ot, a, b) =>
                if let Some(t) = ot {
                    write!(f, "let {} : {} = {}; {}", x, t, a, b)
                }
                else {
                    write!(f, "let {} = {}; {}", x, a, b)
                }

            EPreterm::Lambda(x,t,b) =>
                if t.is_none() {
                    write!(f, "λ{}. {}", x, b)
                }
                else {
                    let containsbinder = fv(&(*b).0).contains(x);
                    if x != "_" && containsbinder {
                        write!(f, "λ{} : {}. {}", x, t.clone().unwrap(), b)
                    }
                    else {
                        let ut = (&*t).clone().unwrap().0;
                        match (&ut, &(*b).0) {
                            (EPreterm::Lambda(_,_,_), EPreterm::Lambda(_,_,_)) =>
                                write!(f, "({}) -> {}", t.clone().unwrap(), b),
                            (EPreterm::Lambda(_,_,_), EPreterm::Unit) =>
                                write!(f, "({}) -> {}", t.clone().unwrap(), b),
                            (EPreterm::Lambda(_,_,_), _) =>
                                write!(f, "({}) -> ({})", t.clone().unwrap(), b),
                            (EPreterm::Unit | EPreterm::Kind | EPreterm::Type(_),EPreterm::Lambda(_,_,_)) =>
                                write!(f, "{} -> {}", t.clone().unwrap(), b),
                            (EPreterm::Var(_),EPreterm::Lambda(_,_,_)) =>
                                write!(f, "{} -> {}", t.clone().unwrap(), b),
                            (_,EPreterm::Lambda(_,_,_)) =>
                                write!(f, "({}) -> {}", t.clone().unwrap(), b),
                            (_,_) =>
                                write!(f, "{} -> {}", t.clone().unwrap(), b),
                        }
                    }
                }
            EPreterm::Unit => write!(f, "()"),
            EPreterm::TAnnot(a,b) => write!(f, "{} : {}", a, b)
        }
    }
}

fn expect(dat : &mut VecDeque<(Token, logos::Span)>, what : Token) -> Result<(Token, logos::Span), Diagnostic<()>> {
    match dat.front().cloned() {
        Some((x, loc)) => {
            dat.pop_front();
            if x == what {
                Ok((x, loc))
            }
            else {
                Err(Diagnostic::error()
                    .with_code("P-EXP")
                    .with_message("unexpected token")
                    .with_labels(vec![Label::primary((), loc).with_message(format!(
                        "Expected {} but got {}!",
                        what, x))
                    ]))
            }
        },
        None => Err(Diagnostic::error()
                    .with_code("P-EOF")
                    .with_message("unexpected end of file")
                    .with_labels(vec![Label::primary((), 0..0).with_message(format!(
                        "Expected {} but reached end of input!",
                        what))
                    ]))
    }
}
fn accept(dat : &mut VecDeque<(Token, logos::Span)>, what : Token) -> bool {
    match dat.front().cloned() {
        Some((x,_)) => {
            if x == what {
                dat.pop_front();
                true
            }
            else {
                false
            }
        },
        None => false
    }
}

fn eatid(data : &mut VecDeque<(Token, logos::Span)>) -> Result<(String, logos::Span), Diagnostic<()>> {
    match data.front().cloned() {
        Some((Token::Identifier(x), y)) => { data.pop_front(); Ok((x.clone(), y)) },
        None => Err(Diagnostic::error()
                    .with_code("P-EOF")
                    .with_message("unexpected end of file")
                    .with_labels(vec![Label::primary((), 0..0).with_message(format!(
                        "Expected an identifier but reached end of input!"))
                    ])),
        Some((x, y)) => Err(Diagnostic::error()
                    .with_code("P-EXP")
                    .with_message("unexpected token")
                    .with_labels(vec![Label::primary((), y).with_message(format!(
                        "Expected an identifier, but got {}!", x))
                    ]))
    }
}

fn eat(dat : &mut VecDeque<(Token, logos::Span)>) -> Result<(Token, logos::Span), Diagnostic<()>> {
    match dat.front().cloned() {
        Some(x) => { dat.pop_front(); Ok(x) },
        None => Err(Diagnostic::error()
                    .with_code("P-EOF")
                    .with_message("unexpected end of file")
                    .with_labels(vec![Label::primary((), 0..0).with_message(format!(
                        "Unexpectedly reached the end of input!"))
                    ])),
    }
}

fn delimiting(dat : &mut VecDeque<(Token, logos::Span)>) -> bool {
    match dat.front().cloned() {
        Some((Token::RParen, _)) | Some((Token::Dot, _)) | Some((Token::Walrus, _)) | Some((Token::Semicolon, _)) |
        Some((Token::Then, _)) | Some((Token::Else, _)) => true,
        None => true,
        _ => false,
    }
}

fn parse_prefix(dat : &mut VecDeque<(Token, logos::Span)>) -> Result<Preterm, Diagnostic<()>> {
    let (tok,loc) = eat(dat)?;
    match tok {
        Token::True => Ok(Preterm(EPreterm::True, Some(loc))),
        Token::False => Ok(Preterm(EPreterm::False, Some(loc))),
        Token::Bool => Ok(Preterm(EPreterm::Bool, Some(loc))),
        Token::Type(lv) => Ok(Preterm(EPreterm::Type(lv), Some(loc))),
        Token::Identifier(x) => {
            if x == "Type" {
                Ok(Preterm(EPreterm::Type(0), Some(loc)))
            }
            else {
                Ok(Preterm(EPreterm::Var(x), Some(loc)))
            }
        },
        Token::Lambda => parse_lambda(dat),
        Token::Let => parse_let(dat),
        Token::If => parse_if(dat),
        Token::LParen => {
            if accept(dat, Token::RParen) {
                Ok(Preterm(EPreterm::Unit, Some(loc)))
            }
            else {
                let result = parse_expr(dat)?;
                expect(dat, Token::RParen)?;
                let pos = result.1.unwrap();
                Ok(Preterm(result.0, Some(rc!(pos, loc))))
            }
        }
        _ => Err(Diagnostic::error()
                    .with_code("P-PREF")
                    .with_message("prefix expression opener expected")
                    .with_labels(vec![Label::primary((), loc).with_message(format!(
                        "This is not the beginning of an expression."))
                    ])),
    }
}

fn parse_expr(dat : &mut VecDeque<(Token, logos::Span)>) -> Result<Preterm, Diagnostic<()>> {
    let mut pref = parse_prefix(dat)?;

    while !dat.is_empty() && !delimiting(dat) {
        let prefpos = pref.1.clone().unwrap();
        if accept(dat, Token::Colon) {
            let typ = parse_expr(dat)?;
            let typpos = typ.1.clone().unwrap();
            pref = Preterm(EPreterm::TAnnot(Box::new(pref), Box::new(typ)), Some(rc!(prefpos, typpos)));
        }
        else if accept(dat, Token::Arrow) {
            let typ = parse_expr(dat)?;
            let typpos = typ.1.clone().unwrap();
            pref = Preterm(EPreterm::Lambda("_".to_string(), Some(Box::new(pref)), Box::new(typ)), Some(rc!(prefpos, typpos)));
        }
        else {
            let other = parse_prefix(dat)?;
            let otherpos = other.1.clone().unwrap();
            pref = Preterm(EPreterm::App(Box::new(pref), Box::new(other)), Some(rc!(prefpos, otherpos)));
        }
    }
    Ok(pref)
}

fn parse_if(dat : &mut VecDeque<(Token, logos::Span)>) -> Result<Preterm, Diagnostic<()>> {
    let cond = parse_expr(dat)?;
    expect(dat, Token::Then)?;
    let cons = parse_expr(dat)?;
    expect(dat, Token::Else)?;
    let alte = parse_expr(dat)?;

    let condpos = cond.1.clone().unwrap();
    let altepos = alte.1.clone().unwrap();

    Ok(Preterm(EPreterm::If(Box::new(cond), Box::new(cons), Box::new(alte)), Some(rc!(condpos, altepos))))
}

fn parse_let(dat : &mut VecDeque<(Token, logos::Span)>) -> Result<Preterm, Diagnostic<()>> {
    let eaten = eatid(dat)?;
    let (id,_) = eaten;

    let mut typ : Option<Box<Preterm>> = None;
    if accept(dat, Token::Colon) {
        let pref = parse_expr(dat)?;
        typ = Some(Box::new(pref));
    }
    expect(dat, Token::Walrus)?;
    let def = parse_expr(dat)?;
    expect(dat, Token::Semicolon)?;

    let bdy = parse_expr(dat)?;
    let bdypos = bdy.1.clone().unwrap();
    Ok(Preterm(EPreterm::Let(id, typ, Box::new(def), Box::new(bdy)), Some(rc!(eaten.1, bdypos))))
}

fn parse_lambda(dat : &mut VecDeque<(Token, logos::Span)>) -> Result<Preterm, Diagnostic<()>> {
    let eaten = eatid(dat)?;
    let (id,_) = eaten;

    let mut typ : Option<Box<Preterm>> = None;
    if accept(dat, Token::Colon) {
        let pref = parse_expr(dat)?;
        typ = Some(Box::new(pref));
    }
    expect(dat, Token::Dot)?;
    let bdy = parse_expr(dat)?;

    let bdypos = bdy.1.clone().unwrap();
    Ok(Preterm(EPreterm::Lambda(id, typ, Box::new(bdy)), Some(rc!(eaten.1, bdypos))))
}

pub fn parse(text : String) -> Result<Preterm, Diagnostic<()>> {
    let lex = Token::lexer(text.as_str());
    let mut deque : VecDeque<_> = lex.spanned().collect();
    parse_expr(&mut deque)
}
