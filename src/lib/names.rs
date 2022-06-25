
use std::collections::HashSet;

use crate::lib::parse::Preterm;

fn fv_detail(bound : &mut HashSet<String>, e : &Preterm) -> HashSet<String> {
    match e {
        Preterm::Unit | Preterm::Type(_) | Preterm::Kind => HashSet::new(),
        Preterm::TAnnot(a, b) => {
            let mut set = fv_detail(bound, a);
            set.extend(fv_detail(bound, b));
            set
        },
        Preterm::Var(x) => {
            if bound.contains(x) {
                HashSet::new()
            }
            else {
                [x.clone()].iter().cloned().collect()
            }
        },
        Preterm::App(a, b) => {
            let mut set = fv_detail(bound, a);
            set.extend(fv_detail(bound, b));
            set
        }
        Preterm::Lambda(x, ot, b) => {
            let mut fvot = HashSet::new();
            match ot {
                None => (),
                Some(t) => { fvot = fv_detail(bound, t); () },
            }
            bound.insert(x.clone());
            fvot.extend(fv_detail(bound, b));
            bound.remove(x);
            fvot
        }
    }
}

pub fn fv(e : &Preterm) -> HashSet<String> {
    let mut bound : HashSet<String> = HashSet::new();
    fv_detail(&mut bound, e)
}
