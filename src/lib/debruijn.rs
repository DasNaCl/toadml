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
}
#[derive(Clone, PartialEq, Debug)]
pub struct LTerm {
    pub tm : ELTerm,
    pub ty : Option<Box<LTerm>>,
    pub pos : Option<logos::Span>,
}
pub fn mk_ltermt(tm : ELTerm, ty : LTerm, pos : Option<logos::Span>) -> LTerm {
    LTerm {
        tm : tm,
        ty : Some(Box::new(ty)),
        pos : pos,
    }
}
pub fn mk_ltermu(tm : ELTerm, pos : Option<logos::Span>) -> LTerm {
    LTerm {
        tm : tm,
        ty : None,
        pos : pos,
    }
}

pub fn map(f : impl Fn(LTerm) -> LTerm, x : LTerm) -> LTerm {
    let thething = match x.tm {
        ELTerm::Lambda(b,t,bdy) => {
            ELTerm::Lambda(b,
                           if t.is_none() { None }
                           else { Some(Box::new(f(*t.unwrap()))) },
                           Box::new(f(*bdy)))
        },
        ELTerm::Let(bind,t,def,bdy) => {
            ELTerm::Let(bind,
                        if t.is_none() { None }
                        else { Some(Box::new(f(*t.unwrap()))) },
                        Box::new(f(*def)),
                        Box::new(f(*bdy)))
        },
        ELTerm::App(a,b) => ELTerm::App(Box::new(f(*a)), Box::new(f(*b))),
        ELTerm::Var(v) => ELTerm::Var(v),
        ELTerm::Unit => ELTerm::Unit,
        ELTerm::Type(v) => ELTerm::Type(v),
        ELTerm::Kind => ELTerm::Kind,
        ELTerm::Ex(v,u) => ELTerm::Ex(v,u),
        ELTerm::True => ELTerm::True,
        ELTerm::False => ELTerm::False,
        ELTerm::Bool => ELTerm::Bool,
        ELTerm::If(a,b,c) => ELTerm::If(Box::new(f(*a)),
                                              Box::new(f(*b)),
                                              Box::new(f(*c))),
    };
    if let Some(ty) = x.ty {
        mk_ltermt(thething, *ty, x.pos)
    }
    else {
        mk_ltermu(thething, x.pos)
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
                Some(s) => format!("{}[{}]", s, x),
                None => format!("{}", x),
            }
        };
        let s = match &self.tm {
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
                match ((*a).tm.clone(), (*b).tm.clone()) {
                    (ELTerm::Var(x),ELTerm::Var(y)) => format!("{} {}", lookup(x as usize), lookup(y as usize)),
                    (ELTerm::Var(x),_bb) => {
                        let a = lookup(x as usize);
                        let b = (**b).to_string(ctx);
                        format!("{} ({})", a, b)
                    },
                    (ELTerm::Lambda(u,v,w),_bb) => {
                        let a = mk_ltermu(ELTerm::Lambda(u,v,w),None).to_string(ctx);
                        let b = (**b).to_string(ctx);
                        format!("({}) {}", a, b)
                    },
                    (u,ELTerm::App(v,w)) => {
                        let u = (**a).to_string(ctx);
                        let v = mk_ltermu(ELTerm::App(v,w),None).to_string(ctx);
                        format!("{} ({})", u, v)
                    },
                    (u,v) => {
                        let u = (**a).to_string(ctx);
                        let v = (**b).to_string(ctx);
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
                    if lcontains(&(**b).tm, ctx.len() as i32) {
                        format!("λ{} : {}. {}", name, ts, bs)
                    }
                    else {
                        match ((*t).clone().unwrap().tm, (**b).clone().tm) {
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
        };
        if let Some(t) = self.ty.clone() {
            let ts = (*t).to_string(ctx);
            format!("{} : {}", s, ts)
        }
        else {
            s
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
            Ok(mk_ltermu(ELTerm::Lambda(name(binder), typ, Box::new(lterm)), t.1.clone()))
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
            Ok(mk_ltermu(ELTerm::Let(name(binder), typ, Box::new(ldef), Box::new(lbdy)), t.1.clone()))
        },
        EPreterm::Var(x) => {
            match lookup(map, x) {
                Some(l) => Ok(mk_ltermu(ELTerm::Var(lv - l), t.1.clone())),
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
            Ok(mk_ltermu(ELTerm::App(Box::new(from_preterm_detail(&(*a), map, lv)?),
                                     Box::new(from_preterm_detail(&(*b), map, lv)?)), t.1.clone()))
        },
        EPreterm::Unit => Ok(mk_ltermu(ELTerm::Unit, t.1.clone())),
        EPreterm::Kind => Ok(mk_ltermu(ELTerm::Kind, t.1.clone())),
        EPreterm::Type(ulv) => Ok(mk_ltermu(ELTerm::Type(ulv.clone()), t.1.clone())),
        EPreterm::TAnnot(e, t) => Ok(mk_ltermt(from_preterm_detail(&(*e), map, lv)?.tm,
                                               from_preterm_detail(&(*t), map, lv)?,
                                               t.1.clone())),
        EPreterm::Ex(x,y) => Ok(mk_ltermu(ELTerm::Ex(x.clone(),y.clone()), t.1.clone())),
        EPreterm::True => Ok(mk_ltermu(ELTerm::True, t.1.clone())),
        EPreterm::False => Ok(mk_ltermu(ELTerm::False, t.1.clone())),
        EPreterm::Bool => Ok(mk_ltermu(ELTerm::Bool, t.1.clone())),
        EPreterm::If(a,b,c) => Ok(mk_ltermu(ELTerm::If(Box::new(from_preterm_detail(&(*a), map, lv)?),
                                                   Box::new(from_preterm_detail(&(*b), map, lv)?),
                                                   Box::new(from_preterm_detail(&(*c), map, lv)?)), t.1.clone())),
    }
}

pub fn from_preterm(t : &Preterm) -> Result<LTerm, Diagnostic<()>> {
    let mut str_to_lv = vec![HashMap::new()];
    from_preterm_detail(&t, &mut str_to_lv, 0)
}

fn to_from_indices_detail(lv: i32, e : LTerm) -> LTerm {
    let ty = e.ty.clone();
    let tm = match e.tm {
        ELTerm::Var(u) => mk_ltermu(ELTerm::Var(lv - u - 1), e.pos),
        ELTerm::Lambda(a,b,c) =>
            mk_ltermu(ELTerm::Lambda(a,
                                     if b.is_none() { None }
                                     else { Some(Box::new(to_from_indices_detail(lv, *b.unwrap()))) },
                                     Box::new(to_from_indices_detail(lv+1, *c))), e.pos),
        ELTerm::Let(a,b,c,d) =>
            mk_ltermu(ELTerm::Let(a,
                              if b.is_none() { None }
                              else { Some(Box::new(to_from_indices_detail(lv, *b.unwrap())))  },
                              Box::new(to_from_indices_detail(lv, *c)),
                              Box::new(to_from_indices_detail(lv+1, *d))), e.pos),
        _ => map(|o| to_from_indices_detail(lv, o), e)
    };
    if let Some(ty) = ty {
        let ty = to_from_indices_detail(lv, *ty);
        mk_ltermt(tm.tm, ty, tm.pos)
    }
    else {
        mk_ltermu(tm.tm, tm.pos)
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
