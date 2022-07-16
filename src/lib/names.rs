
use std::collections::HashSet;

use crate::lib::parse::EPreterm;
use crate::lib::debruijn::{ELTerm, LTerm, map};

fn fv_detail(bound : &mut HashSet<String>, e : &EPreterm) -> HashSet<String> {
    match e {
        EPreterm::True | EPreterm::False | EPreterm::Unit | EPreterm::Type(_) | EPreterm::Kind |
        EPreterm::Ex(_,_) | EPreterm::Bool => HashSet::new(),
        EPreterm::If(a, b, c) => {
            let mut set = fv_detail(bound, &(*a).0);
            set.extend(fv_detail(bound, &(*b).0));
            set.extend(fv_detail(bound, &(*c).0));
            set
        },
        EPreterm::TAnnot(a, b) => {
            let mut set = fv_detail(bound, &(*a).0);
            set.extend(fv_detail(bound, &(*b).0));
            set
        },
        EPreterm::Var(x) => {
            if bound.contains(x) {
                HashSet::new()
            }
            else {
                [x.clone()].iter().cloned().collect()
            }
        },
        EPreterm::App(a, b) => {
            let mut set = fv_detail(bound, &(*a).0);
            set.extend(fv_detail(bound, &(*b).0));
            set
        }
        EPreterm::Lambda(x, ot, b) => {
            let mut fvot = HashSet::new();
            match ot {
                None => (),
                Some(t) => { fvot = fv_detail(bound, &(*t).0); () },
            }
            bound.insert(x.clone());
            fvot.extend(fv_detail(bound, &(*b).0));
            bound.remove(x);
            fvot
        }
        EPreterm::Let(x, ot, def, bdy) => {
            let mut fvot = HashSet::new();
            match ot {
                None => (),
                Some(t) => { fvot = fv_detail(bound, &(*t).0); () },
            }
            fvot.extend(fv_detail(bound, &(*def).0));
            bound.insert(x.clone());
            fvot.extend(fv_detail(bound, &(*bdy).0));
            bound.remove(x);
            fvot
        }
    }
}

pub fn fv(e : &EPreterm) -> HashSet<String> {
    let mut bound : HashSet<String> = HashSet::new();
    fv_detail(&mut bound, e)
}

fn lontains_detail(lv : i32, e : &ELTerm, what : i32) -> bool {
    match e {
        ELTerm::True | ELTerm::False | ELTerm::Unit | ELTerm::Type(_) | ELTerm::Kind |
        ELTerm::Ex(_,_) | ELTerm::Bool => false,
        ELTerm::If(a, b, c) => {
            lontains_detail(lv, &(**a).tm, what) ||
                lontains_detail(lv, &(**b).tm, what) ||
                lontains_detail(lv, &(**c).tm, what)
        }
        ELTerm::Var(x) => {
            // this only works for levels, not indices.
            *x == what
        },
        ELTerm::App(a, b) => {
            if lontains_detail(lv, &(*a).tm, what) {
                return true;
            }
            lontains_detail(lv, &(*b).tm, what)
        }
        ELTerm::Lambda(_x, ot, b) => {
            match ot {
                Some(t) => {
                    if lontains_detail(lv, &(*t).tm, what) {
                        return true;
                    }
                },
                None => (),
            }
            lontains_detail(lv + 1, &(*b).tm, what)
        }
        ELTerm::Let(_x, ot, def, bdy) => {
            match ot {
                Some(t) => {
                    if lontains_detail(lv, &(*t).tm, what) {
                        return true;
                    }
                },
                None => (),
            }
            lontains_detail(lv, &(*def).tm, what) && lontains_detail(lv + 1, &(*bdy).tm, what)
        }
    }
}

/// expects debruijn levels
pub fn lcontains(e : &ELTerm, x : i32) -> bool {
    lontains_detail(0, e, x)
}
