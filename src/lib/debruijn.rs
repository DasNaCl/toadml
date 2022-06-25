use std::collections::{Vec, HashMap};

// Plan:
//  transform to debruijn indices
//  implement NbE

type Binder = ();

// Uses DeBruijn levels. Better for NbE
// Levels  = lambdas counted from outside in
// Indices = lambdas counted from inside out
pub enum LTerm {
    Lambda(Binder, Option<Box<LTerm>>, Box<LTerm>),
    App(Box<LTerm>, Box<LTerm>),
    Var(i32),

    Unit,
    Type(u32),
}

fn lookup_detail(scope : &mut Vec<HashMap<String, i32>>, what : &String, pos : i32) -> Option<i32> {
    if pos < 0 {
        return None;
    }
    match scope.get(pos) {
        Some(map) => {
            match map.get(what) {
                Some(lv) => Some(lv),
                None => lookup_detail(scope, what, pos - 1)
            }
        },
        None => None
    }
}
fn lookup(scope : &mut Vec<HashMap<String, i32>>, what : &String) -> Option<i32> {
    lookup_detail(scope, what, scope.len() - 1)
}

fn from_preterm_detail(t : &Preterm, map : &mut Vec<HashMap<String, i32>>, lv : u32) -> LTerm {
    match t {
        Preterm::Lambda(binder, _t, bdy) => {
            let el = HashMap::from([(binder, lv+1)]);
            map.push(el);
            let lterm = from_preterm_detail(bdy, map, lv+1);
            map.pop();
            lterm
        }
        Preterm::Var(x) => {
            match lookup(x) {
                Some(l) => LTerm::Var(le),
                None => todo!("Terms with free variables are not supported")
            }
        },
        Preterm::App(a, b) => {
            LTerm::App(from_preterm_detail(&*a, map, lv), from_preterm_detail(&*b, map, lv))
        },
        Preterm::Unit => LTerm::Unit,
        Preterm::Type(ulv) => LTerm::Type(ulv),
        Preterm::TAnnot(t, _) => from_preterm_detail(&*t, map, lv), //TODO: add TAnnot to LTerm?
    }
}

// TODO: implement. count lambdas from outside in, not inside out!
pub fn from_preterm(t : &Preterm) -> LTerm {
    let mut str_to_lv = vec![HashMap::new()];
    from_preterm_detail(t, &mut str_to_lv, 0)
}
