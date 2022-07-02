
use crate::lib::parse::Preterm;
use crate::lib::names::fv;

#[derive(Debug, Clone)]
pub enum CtxElem {
    Ex(String, Vec<CtxElem>),
    C(String, Preterm)
}

pub type Ctx = Vec<CtxElem>;

fn lessequal(term : &Preterm, typ : &Preterm) -> bool {
    match (term, typ) {
        (Preterm::Type(_), Preterm::Kind) => true,
        (_, _) => *term == *typ,
    }
}

// checks if a given thing `typ` is actually a type
fn wf(gamma : &mut Ctx, typ : &Preterm) -> bool {
    match typ {
        Preterm::Kind => true,
        Preterm::Type(_i) => true,
        Preterm::Unit => true,
        Preterm::Var(x) => {
            let el = gamma.into_iter()
                          .find(|el| match el {
                              CtxElem::C(y,_t) => x == y,
                              CtxElem::Ex(y, _v) => x == y,
                          });
            if el.is_none() {
                return false;
            }
            match el.unwrap().clone() {
                CtxElem::C(_y, t) => wf(gamma, &t),
                CtxElem::Ex(_y, _v) => true,
            }
        },
        Preterm::Lambda(_,Some(t0),t1) => wf(gamma, &*t0) && wf(gamma, &*t1),

        Preterm::TAnnot(a,t) => wf(gamma, &*a) && check(gamma, &*t, &Preterm::Kind),
        _ => { println!("{} with ctx {gamma:?}", typ); false },
    }
}

pub fn check(gamma : &mut Ctx, term : &Preterm, typ : &Preterm) -> bool {
    if !wf(gamma, &typ) {
        return false;
    }
    let inferrd = infer(gamma, term);

    if inferrd.is_err() {
        return false;
    }
    lessequal(&inferrd.unwrap(), typ)
}

// TODO: return CTXElem?
pub fn infer(gamma : &mut Ctx, term : &Preterm) -> Result<Preterm, String> {
    match term {
        Preterm::Kind => Err(format!("Cannot infer the type of a Kind")),
        Preterm::Type(lv) => Ok(Preterm::Type(lv + 1)),
        Preterm::Unit => Ok(Preterm::Unit),

        Preterm::TAnnot(a, t) => {
            if check(gamma, &*a, &*t) {
                Ok(*t.clone())
            }
            else {
                Err(format!("{}", "Ill-formed type-annotation."))
            }
        },

        Preterm::Var(x) => {
            let el = gamma.into_iter()
                          .find(|el| match el {
                              CtxElem::C(y,_t) => x == y,
                              CtxElem::Ex(y,_v) => x == y,
                          });
            match el {
                Some(CtxElem::C(_y,t)) => Ok((*t).clone()),
                Some(CtxElem::Ex(_y,v)) => Err(format!("aeurnadu")),
                None => Err(format!("Variable {} not in context", x))
            }
        },

        Preterm::Lambda(x, ot, bdy) => {
            match ot {
                Some(t) => {
                    if !wf(gamma, &*t) {
                        return Err(format!("Ill-formed type annotation for binder {}.", x));
                    }
                    let containsbinder = x != "_" && fv(bdy).contains(x);
                    if containsbinder {
                        gamma.push(CtxElem::C(x.clone(), *t.clone()));
                    }
                    let r = infer(gamma, &*bdy);
                    if containsbinder {
                        gamma.pop();
                    }
                    match r {
                        Ok(rt) => Ok(Preterm::Lambda(
                            if !containsbinder { String::from("_") } else { x.clone() },
                            Some(Box::new(*t.clone())), Box::new(rt))),
                        Err(msg) => Err(msg),
                    }
                },
                None => {
                    let containsbinder = x != "_" && fv(bdy).contains(x);
                    if !containsbinder {
                        return match infer(gamma, &*bdy) {
                            Ok(tbdy) => Ok(Preterm::Lambda(format!("_"), Some(Box::new(Preterm::Unit)), Box::new(tbdy))),
                            Err(msg) => Err(msg),
                        }
                    }
                    Err(format!("Type inference not implemented properly."))
                }
            }
        },

        Preterm::App(a,b) => {
            let fnt = infer(gamma, &*a)?;
            let argt = infer(gamma, &*b)?;

            match fnt {
                Preterm::Lambda(_, Some(t0), t1) => {
                    // t0 -> t1
                    if lessequal(&argt, &*t0) {
                        Ok(*t1)
                    }
                    else {
                        Err(format!("Function argument and function parameter are incompatible."))
                    }
                },
                _ => Err(format!("Cannot call non-function.")),
            }
        }
    }
}
