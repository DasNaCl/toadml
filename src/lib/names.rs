
use std::collections::HashSet;

use crate::lib::parse::EPreterm;

fn fv_detail(bound : &mut HashSet<String>, e : &EPreterm) -> HashSet<String> {
    match e {
        EPreterm::Unit | EPreterm::Type(_) | EPreterm::Kind => HashSet::new(),
        EPreterm::TAnnot(a, b) => {
            let mut set = fv_detail(bound, &a.0);
            set.extend(fv_detail(bound, &b.0));
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
            let mut set = fv_detail(bound, &a.0);
            set.extend(fv_detail(bound, &b.0));
            set
        }
        EPreterm::Lambda(x, ot, b) => {
            let mut fvot = HashSet::new();
            match ot {
                None => (),
                Some(t) => { fvot = fv_detail(bound, &t.0); () },
            }
            bound.insert(x.clone());
            fvot.extend(fv_detail(bound, &b.0));
            bound.remove(x);
            fvot
        }
    }
}

pub fn fv(e : &EPreterm) -> HashSet<String> {
    let mut bound : HashSet<String> = HashSet::new();
    fv_detail(&mut bound, e)
}
