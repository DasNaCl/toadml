
use std::collections::HashSet;

use crate::lib::parse::EPreterm;
use crate::lib::debruijn::{ELTerm, LTerm, map};

fn fv_detail(bound : &mut HashSet<String>, e : &EPreterm) -> HashSet<String> {
    match e {
        EPreterm::Unit | EPreterm::Type(_) | EPreterm::Kind | EPreterm::Ex(_,_) => HashSet::new(),
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
    }
}

pub fn fv(e : &EPreterm) -> HashSet<String> {
    let mut bound : HashSet<String> = HashSet::new();
    fv_detail(&mut bound, e)
}

fn lontains_detail(lv : i32, e : &ELTerm, what : i32) -> bool {
    match e {
        ELTerm::Unit | ELTerm::Type(_) | ELTerm::Kind | ELTerm::Ex(_,_) => false,
        ELTerm::TAnnot(a, b) => {
            if lontains_detail(lv, &(*a).0, what) {
                return true;
            }
            lontains_detail(lv, &(*b).0, what)
        },
        ELTerm::Var(x) => {
            // this only works for levels, not indices.
            *x == what
        },
        ELTerm::App(a, b) => {
            if lontains_detail(lv, &(*a).0, what) {
                return true;
            }
            lontains_detail(lv, &(*b).0, what)
        }
        ELTerm::Lambda(_x, ot, b) => {
            match ot {
                Some(t) => {
                    if lontains_detail(lv, &(*t).0, what) {
                        return true;
                    }
                },
                None => (),
            }
            lontains_detail(lv + 1, &(*b).0, what)
        }
    }
}

/// expects debruijn levels
pub fn lcontains(e : &ELTerm, x : i32) -> bool {
    lontains_detail(0, e, x)
}
