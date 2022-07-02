
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

    #[regex("Type", |_lex| Some(0))]
    #[regex("Type [0-9][1-9]*", |lex| { let slice = lex.slice(); slice[5..slice.len()].parse() })]
    Type(u32),

    #[regex("[_a-zA-Z]+", |lex| lex.slice().parse())]
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
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Preterm {
    Lambda(String, Option<Box<Preterm>>, Box<Preterm>),
    App(Box<Preterm>, Box<Preterm>),
    Var(String),

    Unit,
    Type(u32),
    Kind,
    TAnnot(Box<Preterm>, Box<Preterm>)
}
impl fmt::Display for Preterm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Preterm::Type(0) => write!(f, "Type"),
            Preterm::Type(n) => write!(f, "Type {}", n),
            Preterm::Kind => write!(f, "Kind"),
            Preterm::Var(x) => write!(f, "{}", x),
            Preterm::App(a,b) => {
                match ((**a).clone(), (**b).clone()) {
                    (Preterm::Var(_),Preterm::Var(_)) => write!(f, "{} {}", a, b),
                    (Preterm::Var(_),_) => write!(f, "{} ({})", a, b),
                    (Preterm::Lambda(_,_,_),_) => write!(f, "({}) {}", a, b),
                    (_,_) => write!(f, "({} {})", a, b),
                }
            },
            Preterm::Lambda(x,t,b) =>
                if t.is_none() {
                    write!(f, "λ{}. {}", x, b)
                }
                else {
                    let containsbinder = fv(&*b).contains(x);
                    if x != "_" && containsbinder {
                        write!(f, "λ{} : {}. {}", x, t.clone().unwrap(), b)
                    }
                    else {
                        let ut = t.clone().unwrap();
                        match (*ut, (**b).clone()) {
                            (Preterm::Lambda(_,_,_), Preterm::Lambda(_,_,_)) =>
                                write!(f, "({}) -> ({})", t.clone().unwrap(), b),
                            (Preterm::Lambda(_,_,_), Preterm::Unit) =>
                                write!(f, "({}) -> {}", t.clone().unwrap(), b),
                            (Preterm::Lambda(_,_,_), _) =>
                                write!(f, "({}) -> ({})", t.clone().unwrap(), b),
                            (Preterm::Unit | Preterm::Type(_),Preterm::Lambda(_,_,_)) =>
                                write!(f, "{} -> {}", t.clone().unwrap(), b),
                            (_,Preterm::Lambda(_,_,_)) =>
                                write!(f, "({}) -> {}", t.clone().unwrap(), b),
                            (_,_) =>
                                write!(f, "{} -> {}", t.clone().unwrap(), b),
                        }
                    }
                }
            Preterm::Unit => write!(f, "()"),
            Preterm::TAnnot(a,b) => write!(f, "{} : {}", a, b)
        }
    }
}

fn expect(dat : &mut VecDeque<Token>, what : Token) -> Result<Token, Diagnostic<()>> {
    match dat.front().cloned() {
        Some(x) => {
            dat.pop_front();
            if x == what {
                Ok(x)
            }
            else {
                Err(Diagnostic::error()
                    .with_code("P-EXP")
                    .with_message("unexpected token")
                    .with_labels(vec![Label::primary((), 1..1).with_message(format!(
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
fn accept(dat : &mut VecDeque<Token>, what : Token) -> bool {
    match dat.front().cloned() {
        Some(x) => {
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

fn eatid(data : &mut VecDeque<Token>) -> Result<String, Diagnostic<()>> {
    match data.front().cloned() {
        Some(Token::Identifier(x)) => { data.pop_front(); Ok(x.clone()) },
        None => Err(Diagnostic::error()
                    .with_code("P-EOF")
                    .with_message("unexpected end of file")
                    .with_labels(vec![Label::primary((), 0..0).with_message(format!(
                        "Expected an identifier but reached end of input!"))
                    ])),
        Some(x) => Err(Diagnostic::error()
                    .with_code("P-EXP")
                    .with_message("unexpected token")
                    .with_labels(vec![Label::primary((), 1..1).with_message(format!(
                        "Expected an identifier, but got {}!", x))
                    ]))
    }
}

fn eat(dat : &mut VecDeque<Token>) -> Result<Token, Diagnostic<()>> {
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

fn delimiting(dat : &mut VecDeque<Token>) -> bool {
    match dat.front().cloned() {
        Some(Token::RParen) | Some(Token::Dot) => true,
        None => true,
        _ => false,
    }
}

fn parse_prefix(dat : &mut VecDeque<Token>) -> Result<Preterm, Diagnostic<()>> {
    match eat(dat)? {
        Token::Type(lv) => Ok(Preterm::Type(lv)),
        Token::Identifier(x) => Ok(Preterm::Var(x)),
        Token::Lambda => parse_lambda(dat),
        Token::LParen => {
            if accept(dat, Token::RParen) {
                Ok(Preterm::Unit)
            }
            else {
                let result = parse_expr(dat)?;
                expect(dat, Token::RParen)?;
                Ok(result)
            }
        }
        _ => Err(Diagnostic::error()
                    .with_code("P-EOF")
                    .with_message("unexpected end of file")
                    .with_labels(vec![Label::primary((), 0..0).with_message(format!(
                        "Unexpectedly reached the end of input!"))
                    ])),
    }
}

fn parse_expr(dat : &mut VecDeque<Token>) -> Result<Preterm, Diagnostic<()>> {
    let mut pref = parse_prefix(dat)?;

    while !dat.is_empty() && !delimiting(dat) {
        if accept(dat, Token::Colon) {
            let typ = parse_expr(dat)?;
            pref = Preterm::TAnnot(Box::new(pref), Box::new(typ));
        }
        else if accept(dat, Token::Arrow) {
            let typ = parse_expr(dat)?;
            pref = Preterm::Lambda("_".to_string(), Some(Box::new(pref)), Box::new(typ))
        }
        else {
            let other = parse_prefix(dat)?;
            pref = Preterm::App(Box::new(pref), Box::new(other));
        }
    }
    Ok(pref)
}

fn parse_lambda(dat : &mut VecDeque<Token>) -> Result<Preterm, Diagnostic<()>> {
    let id = eatid(dat)?;

    let mut typ : Option<Box<Preterm>> = None;
    if accept(dat, Token::Colon) {
        let pref = parse_expr(dat)?;
        typ = Some(Box::new(pref));
    }

    expect(dat, Token::Dot)?;
    let bdy = parse_expr(dat)?;

    Ok(Preterm::Lambda(id, typ, Box::new(bdy)))
}

pub fn parse(text : String) -> Result<Preterm, Diagnostic<()>> {
    let lex = Token::lexer(text.as_str());
    let mut deque : VecDeque<_> = lex.collect();
    parse_expr(&mut deque)
}
