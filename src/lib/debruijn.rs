use std::collections::HashMap;
use std::vec::Vec;
use std::fmt;

use crate::lib::parse::Preterm;

type Binder = ();

// Uses DeBruijn indices
#[derive(Clone,Debug)]
pub enum LTerm {
    Lambda(Binder, Option<Box<LTerm>>, Box<LTerm>),
    App(Box<LTerm>, Box<LTerm>),
    Var(i32),

    Unit,
    Type(u32),
    Kind,
}
impl fmt::Display for LTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LTerm::Type(0) => write!(f, "Type"),
            LTerm::Type(n) => write!(f, "Type {}", n),
            LTerm::Kind => write!(f, "Kind"),
            LTerm::Var(x) => write!(f, "{}", x),
            LTerm::App(a,b) => {
                match ((**a).clone(), (**b).clone()) {
                    (LTerm::Var(_),LTerm::Var(_)) => write!(f, "{} {}", a, b),
                    (LTerm::Var(_),_) => write!(f, "{} ({})", a, b),
                    (LTerm::Lambda(_,_,_),_) => write!(f, "({}) {}", a, b),
                    (_,_) => write!(f, "({} {})", a, b),
                }
            },
            LTerm::Lambda(_,_t,b) => {
                write!(f, "λ {}", b)
            }
            LTerm::Unit => write!(f, "()"),
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

fn from_preterm_detail(t : &Preterm, map : &mut Vec<HashMap<String, i32>>, lv : i32) -> LTerm {
    match t {
        Preterm::Lambda(binder, t, bdy) => {
            map.push(HashMap::from([((*binder).clone(), lv+1)]));
            let lterm = from_preterm_detail(bdy, map, lv+1);
            map.pop();
            let typ = match t {
                None => None,
                Some(t) => Some(Box::new(from_preterm_detail(t, map, lv))),
            };
            LTerm::Lambda((), typ, Box::new(lterm))
        }
        Preterm::Var(x) => {
            match lookup(map, x) {
                Some(l) => LTerm::Var(lv - l),
                None => todo!("Terms with free variables are not supported")
            }
        },
        Preterm::App(a, b) => {
            LTerm::App(Box::new(from_preterm_detail(&*a, map, lv)),
                       Box::new(from_preterm_detail(&*b, map, lv)))
        },
        Preterm::Unit => LTerm::Unit,
        Preterm::Kind => LTerm::Kind,
        Preterm::Type(ulv) => LTerm::Type(ulv.clone()),
        Preterm::TAnnot(t, _) => from_preterm_detail(&*t, map, lv), //TODO: add TAnnot to LTerm?
    }
}

pub fn from_preterm(t : &Preterm) -> LTerm {
    let mut str_to_lv = vec![HashMap::new()];
    from_preterm_detail(t, &mut str_to_lv, 0)
}
