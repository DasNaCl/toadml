
use crate::lib::parse::Preterm;

fn equal(term : Preterm, typ : Preterm) -> bool {
    term == typ
}

fn wf(typ : &Preterm) -> bool {
    match typ {
        Preterm::Unit => true,
        Preterm::Lambda(_,Some(t0),t1) => wf(&*t0) && wf(&*t1),
        _ => false,
    }
}

pub enum CtxElem {
    C(String, Preterm)
}

pub type Ctx = Vec<CtxElem>;

pub fn check(gamma : &mut Ctx, term : Preterm, typ : Preterm) -> bool {
    if !wf(&typ) {
        return false;
    }
    let inferrd = infer(gamma, term);

    if inferrd.is_none() {
        return false;
    }
    equal(typ, inferrd.unwrap())
}

pub fn infer(gamma : &mut Ctx, term : Preterm) -> Option<Preterm> {
    match term {
        Preterm::Unit => Some(Preterm::Unit),

        Preterm::TAnnot(a, t) => {
            if check(gamma, *a, (*t).clone()) {
                Some(*t)
            }
            else {
                None
            }
        },

        Preterm::Var(x) => {
            let CtxElem::C(_y,t) = gamma.into_iter()
                                        .find(|CtxElem::C(y,_t)| x == y.clone())?;
            Some((*t).clone())
        },

        Preterm::Lambda(x, ot, bdy) => {
            match ot {
                Some(t) => {
                    if !wf(&*t) {
                        return None;
                    }
                    if x != "_" {
                        gamma.push(CtxElem::C(x.clone(), (*t).clone()));
                    }
                    let r = infer(gamma, *bdy);
                    if x != "_" {
                        gamma.pop();
                    }
                    // no dependent types ...yet
                    match r {
                        Some(rt) => Some(Preterm::Lambda(String::from("_"), Some(Box::new(*t)), Box::new(rt))),
                        None => None,
                    }
                },
                None => {
                    None
                }
            }
        },

        Preterm::App(a,b) => {
            let fnt = infer(gamma, *a)?;
            let argt = infer(gamma, *b)?;

            match fnt {
                Preterm::Lambda(_, Some(t0), t1) => {
                    // t0 -> t1
                    if equal(*t0, argt) {
                        Some(*t1)
                    }
                    else {
                        None
                    }
                },
                _ => None,
            }
        }
    }
}
