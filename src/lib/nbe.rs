
use std::fmt;

mod domain {
use crate::lib::debruijn::LTerm;

pub type Env = Vec<Value>;
#[derive(Clone,Debug)]
pub struct Closure {
    pub term : LTerm,
    pub env : Env
}
#[derive(Clone,Debug)]
pub struct NeutralV {
    pub typ : Value,
    pub term : Neutral,
}
#[derive(Clone,Debug)]
pub enum Value {
    Unit,
    Type(u32),
    Kind,

    Lambda(Option<Box<Value>>, Closure),
    Neutral(Box<NeutralV>)
}
#[derive(Clone,Debug)]
pub enum Neutral {
    Var(usize),
    App(Box<Neutral>, Normal),
}
#[derive(Clone,Debug)]
pub struct Normal {
    pub typ : Value,
    pub term : Value,
}
}

use crate::lib::debruijn::LTerm;
fn handle_closure(c : domain::Closure, a : domain::Value) -> domain::Value {
    let mut ctx = c.env;
    ctx.push(a);
    eval(c.term, &ctx)
}
fn handle_app(f : domain::Value, a : domain::Value) -> domain::Value {
    match f {
        domain::Value::Lambda(_,c) => handle_closure(c, a),
        domain::Value::Neutral(n) => {
            match n.typ {
                domain::Value::Lambda(Some(src), dst) => {
                    let dst = handle_closure(dst, a.clone());
                    domain::Value::Neutral(Box::new(domain::NeutralV {
                       typ: dst,
                       term: domain::Neutral::App(
                           Box::new(n.term),
                           domain::Normal {
                               typ : *src,
                               term : a,
                           }
                       ),
                    }))
                },
                _ => panic!("Cannot app a non-function thing! Got type: {:?}", n.typ)
            }
        },
        _ => panic!("Cannot app a non-function thing! Got f: {:?}", f)
    }
}
fn eval(t : LTerm, env : &domain::Env) -> domain::Value {
    match t {
        LTerm::Var(i) => env.get(i as usize).unwrap().clone(),
        LTerm::Unit => domain::Value::Unit,
        LTerm::Type(u) => domain::Value::Type(u),
        LTerm::Kind => domain::Value::Kind,
        LTerm::Lambda(_,None,b) => domain::Value::Lambda(None, domain::Closure {
            term : *b,
            env : env.clone()
        }),
        LTerm::Lambda(_,Some(at),b) => domain::Value::Lambda(
            Some(Box::new(eval(*at, env))),
            domain::Closure {
                term : *b,
                env : env.clone()
            }),
        LTerm::App(a,b) => handle_app(eval(*a, env), eval(*b, env))
    }
}

fn mk_var(typ : domain::Value, level : usize) -> domain::Value {
    domain::Value::Neutral(Box::new(domain::NeutralV {
        typ : typ,
        term : domain::Neutral::Var(level),
    }))
}

fn from_normal(level : usize, n : domain::Normal) -> LTerm {
    match n.typ {
        domain::Value::Lambda(Some(src), dst) => {
            let arg = mk_var(*src, level);
            let nprime = domain::Normal {
                typ : handle_closure(dst, arg.clone()),
                term : handle_app(n.term, arg)
            };
            LTerm::Lambda((), None, Box::new(from_normal(level + 1, nprime)))
        },
        domain::Value::Kind => {
            match n.term {
                domain::Value::Type(l) => LTerm::Type(l),
                _ => panic!()
            }
        },
        domain::Value::Type(l) => {
            match n.term {
                domain::Value::Type(lp) if lp < l => LTerm::Type(lp),
                domain::Value::Lambda(Some(src), dst) => {
                    let var = mk_var((*src).clone(), level);
                    LTerm::Lambda((), Some(Box::new(from_normal(
                        level,
                        domain::Normal {
                            typ : domain::Value::Type(l),
                            term : *src,
                        }
                    ))),
                        Box::new(from_normal(level + 1,
                        domain::Normal {
                            typ : domain::Value::Type(l),
                            term : handle_closure(dst, var),
                        }))
                    )
                },
                domain::Value::Neutral(x) => from_neutral(level, (*x).term),
                _ => panic!()
            }
        },
        domain::Value::Neutral(_) => {
            match n.term {
                domain::Value::Neutral(x) => from_neutral(level, (*x).term),
                _ => panic!(),
            }
        },
        _ => panic!("{:?}", n.typ)
    }
}

fn from_neutral(level : usize, n : domain::Neutral) -> LTerm {
    match n {
        domain::Neutral::Var(u) => {
            LTerm::Var((level - (u + 1)) as i32)
        },
        domain::Neutral::App(a, b) => {
            LTerm::App(Box::new(from_neutral(level, *a)), Box::new(from_normal(level, b)))
        },
    }
}

pub fn normalize(term : LTerm, typ : LTerm) -> LTerm {
    let ctx : domain::Env = vec![]; // FIXME: this should be a parameter
    let term = eval(term, &ctx);
    let typ = eval(typ, &ctx);

    from_normal(ctx.len(), domain::Normal { typ: typ, term: term })
}
