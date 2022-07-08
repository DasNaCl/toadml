use std::collections::HashMap;
use std::vec::Vec;
use std::fmt;

use codespan_reporting::diagnostic::{Label, Diagnostic};

use crate::lib::parse::{Preterm, EPreterm};
use crate::lib::names::lcontains;

// string is just for debug info
#[derive(Clone,PartialEq,Debug)]
pub struct Binder(pub Option<String>);
pub fn noname() -> Binder {
    Binder(None)
}
fn name(str:&String) -> Binder {
    Binder(Some(str.clone()))
}

// Uses DeBruijn indices
#[derive(Clone,PartialEq,Debug)]
pub enum ELTerm {
    Lambda(Binder, Option<Box<LTerm>>, Box<LTerm>),
    App(Box<LTerm>, Box<LTerm>),
    Var(i32),

    Unit,
    Type(u32),
    Kind,

    Let(Binder, Option<Box<LTerm>>, Box<LTerm>, Box<LTerm>),

    True,
    False,
    If(Box<LTerm>, Box<LTerm>, Box<LTerm>),
    Bool,

    Ex(String, usize),

    TAnnot(Box<LTerm>, Box<LTerm>)
}
#[derive(Clone, PartialEq, Debug)]
pub struct LTerm(pub ELTerm, pub Option<logos::Span>);

pub fn map(f : impl Fn(LTerm) -> LTerm, x : LTerm) -> LTerm {
    match x.0 {
        ELTerm::Lambda(b,t,bdy) => {
            LTerm(ELTerm::Lambda(b,
                                 if t.is_none() { None }
                                 else { Some(Box::new(f(*t.unwrap()))) },
                                 Box::new(f(*bdy))), x.1)
        },
        ELTerm::Let(bind,t,def,bdy) => {
            LTerm(ELTerm::Let(bind,
                              if t.is_none() { None }
                              else { Some(Box::new(f(*t.unwrap()))) },
                              Box::new(f(*def)),
                              Box::new(f(*bdy))), x.1)
        },
        ELTerm::App(a,b) => LTerm(ELTerm::App(Box::new(f(*a)), Box::new(f(*b))), x.1),
        ELTerm::Var(v) => LTerm(ELTerm::Var(v), x.1),
        ELTerm::Unit => LTerm(ELTerm::Unit, x.1),
        ELTerm::Type(v) => LTerm(ELTerm::Type(v), x.1),
        ELTerm::Kind => LTerm(ELTerm::Kind, x.1),
        ELTerm::Ex(v,u) => LTerm(ELTerm::Ex(v,u), x.1),
        ELTerm::True => LTerm(ELTerm::True, x.1),
        ELTerm::False => LTerm(ELTerm::False, x.1),
        ELTerm::Bool => LTerm(ELTerm::Bool, x.1),
        ELTerm::If(a,b,c) => LTerm(ELTerm::If(Box::new(f(*a)),
                                              Box::new(f(*b)),
                                              Box::new(f(*c))), x.1),
        ELTerm::TAnnot(a,b) => LTerm(ELTerm::TAnnot(Box::new(f(*a)), Box::new(f(*b))), x.1),
    }
}

impl fmt::Display for LTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = vec![];
        write!(f, "{}", self.to_string(&mut buf))
    }
}

impl LTerm {
    pub fn to_string(&self, ctx : &mut Vec<String>) -> String {
        let lookup = |x| {
            match ctx.iter().nth(x) {
                Some(s) => format!("{}", s),
                None => format!("{}", x),
            }
        };
        match &self.0 {
            ELTerm::Type(0) => format!("Type"),
            ELTerm::Type(n) => format!("Type {}", n),
            ELTerm::Kind => format!("Kind"),
            ELTerm::True => format!("true"),
            ELTerm::False => format!("false"),
            ELTerm::Bool => format!("bool"),
            ELTerm::If(a,b,c) => {
                let a = (**a).to_string(ctx);
                let b = (**b).to_string(ctx);
                let c = (**c).to_string(ctx);
                format!("if {} then {} else {}", a, b, c)
            }
            ELTerm::Var(x) => lookup(*x as usize),
            ELTerm::App(a,b) => {
                match ((*a).0.clone(), (*b).0.clone()) {
                    (ELTerm::Var(x),ELTerm::Var(y)) => format!("{} {}", lookup(x as usize), lookup(y as usize)),
                    (ELTerm::Var(x),bb) => {
                        let a = lookup(x as usize);
                        let b = LTerm(bb, None).to_string(ctx);
                        format!("{} ({})", a, b)
                    },
                    (ELTerm::Lambda(u,v,w),bb) => {
                        let a = LTerm(ELTerm::Lambda(u,v,w),None).to_string(ctx);
                        let b = LTerm(bb, None).to_string(ctx);
                        format!("({}) {}", a, b)
                    },
                    (u,ELTerm::App(v,w)) => {
                        let u = LTerm(u,None).to_string(ctx);
                        let v = LTerm(ELTerm::App(v,w),None).to_string(ctx);
                        format!("{} ({})", u, v)
                    },
                    (u,v) => {
                        let u = LTerm(u,None).to_string(ctx);
                        let v = LTerm(v,None).to_string(ctx);
                        format!("({} {})", u, v)
                    },
                }
            },
            ELTerm::Let(x,t,a,b) => {
                let ts = match t {
                    Some(tt) => { let st = (**tt).to_string(ctx); format!("{}", st) },
                    None => format!(""),
                };
                let aas = (**a).to_string(ctx);
                let name = match x.0.clone() {
                    Some(n) => { ctx.push(n.clone()); n },
                    None => { ctx.push(format!("_")); format!("_") },
                };
                let bs = (**b).to_string(ctx);
                ctx.pop();
                if t.is_none() {
                    format!("let {} := {}; {}", name, aas, bs)
                }
                else {
                    format!("let {} : {} := {}; {}", name, ts, aas, bs)
                }
            },
            ELTerm::Lambda(x,t,b) => {
                let ts = match t {
                    Some(tt) => { let st = (**tt).to_string(ctx); format!("{}", st) },
                    None => format!(""),
                };
                let name = match x.0.clone() {
                    Some(n) => { ctx.push(n.clone()); n },
                    None => { ctx.push(format!("_")); format!("_") },
                };
                let bs = (**b).to_string(ctx);
                ctx.pop();
                if t.is_none() {
                    format!("λ{}. {}", name, bs)
                }
                else {
                    if lcontains(&(*b).0, ctx.len() as i32) {
                        format!("λ{} : {}. {}", name, ts, bs)
                    }
                    else {
                        match ((*t).clone().unwrap().0, (**b).clone().0) {
                            (ELTerm::Lambda(_,_,_), ELTerm::Lambda(_,_,_)) =>
                                format!("({}) -> {}", ts, bs),
                            (ELTerm::Lambda(_,_,_), ELTerm::Unit) =>
                                format!("({}) -> {}", ts, bs),
                            (ELTerm::Lambda(_,_,_), _) =>
                                format!("({}) -> ({})", ts, bs),
                            (ELTerm::Unit | ELTerm::Type(_) | ELTerm::Kind, ELTerm::Lambda(_,_,_)) =>
                                format!("{} -> {}", ts, bs),
                            (ELTerm::Var(_), ELTerm::Lambda(_,_,_)) =>
                                format!("{} -> {}", ts, bs),
                            (_,ELTerm::Lambda(_,_,_)) =>
                                format!("({}) -> {}", ts, bs),
                            (_,_) => format!("{} -> {}", ts, bs),
                        }
                    }
                }
            },
            ELTerm::Unit => format!("()"),
            ELTerm::Ex(x,u) => format!("{}{{{}}}", x, u),
            ELTerm::TAnnot(a,b) => {
                let a = (**a).to_string(ctx);
                let b = (**b).to_string(ctx);
                format!("({}) : ({})", a, b)
            },
        }
    }
}

// We need Vec<HashMap<_, _>> for shadowing
fn lookup_detail(scope : &mut Vec<HashMap<String, i32>>, what : &String, pos : usize) -> Option<i32> {
    match scope.get(pos) {
        Some(map) => {
            match map.get(what) {
                Some(lv) => Some(*lv),
                None => lookup_detail(scope, what, pos - 1)
            }
        },
        None => None
    }
}
fn lookup(scope : &mut Vec<HashMap<String, i32>>, what : &String) -> Option<i32> {
    lookup_detail(scope, what, (scope.len() - 1) as usize)
}

fn from_preterm_detail(t : &Preterm, map : &mut Vec<HashMap<String, i32>>, lv : i32) -> Result<LTerm, Diagnostic<()>> {
    match &t.0 {
        EPreterm::Lambda(binder, ty, bdy) => {
            map.push(HashMap::from([((*binder).clone(), lv+1)]));
            let lterm = from_preterm_detail(&bdy, map, lv+1)?;
            map.pop();
            let typ = match ty {
                None => None,
                Some(t) => Some(Box::new(from_preterm_detail(&t, map, lv)?)),
            };
            Ok(LTerm(ELTerm::Lambda(name(binder), typ, Box::new(lterm)), t.1.clone()))
        },
        EPreterm::Let(binder, ty, def, bdy) => {
            let typ = match ty {
                None => None,
                Some(t) => Some(Box::new(from_preterm_detail(&t, map, lv)?)),
            };
            let ldef = from_preterm_detail(def, map, lv)?;
            map.push(HashMap::from([((*binder).clone(), lv+1)]));
            let lbdy = from_preterm_detail(bdy, map, lv+1)?;
            //map.pop(); NO POP HERE: The def needs to stay in the ctx!
            Ok(LTerm(ELTerm::Let(name(binder), typ, Box::new(ldef), Box::new(lbdy)), t.1.clone()))
        },
        EPreterm::Var(x) => {
            match lookup(map, x) {
                Some(l) => Ok(LTerm(ELTerm::Var(lv - l), t.1.clone())),
                None => {
                    match t.1.clone() {
                        Some(loc) => Err(Diagnostic::error()
                                        .with_code("B-FREE")
                                        .with_message("free variable found")
                                        .with_labels(vec![Label::primary((), loc).with_message(format!(
                                            "This variable occurs free."))
                                        ])),
                        None =>  Err(Diagnostic::error()
                                        .with_code("B-FREE")
                                        .with_message("free variable found")
                                        .with_notes(vec![format!("Variable {} occurs free.", x)])),
                    }
                }
            }
        },
        EPreterm::App(a, b) => {
            Ok(LTerm(ELTerm::App(Box::new(from_preterm_detail(&(*a), map, lv)?),
                                 Box::new(from_preterm_detail(&(*b), map, lv)?)), t.1.clone()))
        },
        EPreterm::Unit => Ok(LTerm(ELTerm::Unit, t.1.clone())),
        EPreterm::Kind => Ok(LTerm(ELTerm::Kind, t.1.clone())),
        EPreterm::Type(ulv) => Ok(LTerm(ELTerm::Type(ulv.clone()), t.1.clone())),
        EPreterm::TAnnot(e, t) => Ok(LTerm(ELTerm::TAnnot(Box::new(from_preterm_detail(&(*e), map, lv)?),
                                                          Box::new(from_preterm_detail(&(*t), map, lv)?)), t.1.clone())),
        EPreterm::Ex(x,y) => Ok(LTerm(ELTerm::Ex(x.clone(),y.clone()), t.1.clone())),
        EPreterm::True => Ok(LTerm(ELTerm::True, t.1.clone())),
        EPreterm::False => Ok(LTerm(ELTerm::False, t.1.clone())),
        EPreterm::Bool => Ok(LTerm(ELTerm::Bool, t.1.clone())),
        EPreterm::If(a,b,c) => Ok(LTerm(ELTerm::If(Box::new(from_preterm_detail(&(*a), map, lv)?),
                                                   Box::new(from_preterm_detail(&(*b), map, lv)?),
                                                   Box::new(from_preterm_detail(&(*c), map, lv)?)), t.1.clone())),
    }
}

pub fn from_preterm(t : &Preterm) -> Result<LTerm, Diagnostic<()>> {
    let mut str_to_lv = vec![HashMap::new()];
    from_preterm_detail(&t, &mut str_to_lv, 0)
}

fn to_from_indices_detail(lv: i32, e : LTerm) -> LTerm {
    match e.0 {
        ELTerm::Var(u) => LTerm(ELTerm::Var(lv - u - 1), e.1),
        ELTerm::Lambda(a,b,c) =>
            LTerm(ELTerm::Lambda(a,
                                 if b.is_none() { None }
                                 else { Some(Box::new(to_from_indices_detail(lv, *b.unwrap()))) },
                                 Box::new(to_from_indices_detail(lv+1, *c))), e.1),
        ELTerm::Let(a,b,c,d) =>
            LTerm(ELTerm::Let(a,
                              if b.is_none() { None }
                              else { Some(Box::new(to_from_indices_detail(lv, *b.unwrap())))  },
                              Box::new(to_from_indices_detail(lv, *c)),
                              Box::new(to_from_indices_detail(lv+1, *d))), e.1),
        _ => map(|o| to_from_indices_detail(lv, o), e)
    }
}
/// Convert level to indices, e.g. [λx y.x(λz.z)y] aka λλ0(λ2)1 becomes λλ1(λ0)0
pub fn to_indices(e : LTerm) -> LTerm {
    to_from_indices_detail(0, e)
}

/// Convert indices to level, e.g. [λx y.x(λz.z)y] aka λλ1(λ0)0 becomes λλ0(λ2)1
pub fn to_level(e : LTerm) -> LTerm {
    to_from_indices_detail(0, e)
}
