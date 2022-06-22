
use crate::lib::parse::Preterm;
use crate::lib::names::fv;

#[derive(Debug, Clone)]
pub enum CtxElem {
    C(String, Preterm)
}

pub type Ctx = Vec<CtxElem>;

fn equal(term : &Preterm, typ : &Preterm) -> bool {
    *term == *typ
}


fn wf(gamma : &mut Ctx, typ : &Preterm) -> bool {
    match typ {
        Preterm::Type => true,
        Preterm::Unit => true,
        Preterm::Var(x) => {
            let el = gamma.into_iter()
                          .find(|CtxElem::C(y,_t)| x == y);
            if el.is_none() {
                return false;
            }
            let CtxElem::C(_y, t) = el.unwrap().clone();
            wf(gamma, &t)
        },
        Preterm::Lambda(_,Some(t0),t1) => wf(gamma, &*t0) && wf(gamma, &*t1),
        Preterm::TAnnot(a,t) => wf(gamma, &*a) && check(gamma, &*t, &Preterm::Type),
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
    equal(typ, &inferrd.unwrap())
}

pub fn infer(gamma : &mut Ctx, term : &Preterm) -> Result<Preterm, String> {
    match term {
        Preterm::Type => Ok(Preterm::Type),

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
                          .find(|CtxElem::C(y,_t)| x == y);
            match el {
                Some(CtxElem::C(_y,t)) => Ok((*t).clone()),
                None => Err(format!("Variable {} not in context", x))
            }
        },

        Preterm::Lambda(x, ot, bdy) => {
            match ot {
                Some(t) => {
                    if !wf(gamma, &*t) {
                        return Err(format!("Ill-formed type annotation for binder {}.", x));
                    }
                    let notignore = x != "_";
                    if notignore {
                        gamma.push(CtxElem::C(x.clone(), *t.clone()));
                    }
                    let r = infer(gamma, &*bdy);
                    if notignore {
                        gamma.pop();
                    }
                    let containsbinder = fv(bdy).contains(x);
                    match r {
                        Ok(rt) => Ok(Preterm::Lambda(
                            if !notignore || !containsbinder { String::from("_") } else { x.clone() },
                            Some(Box::new(*t.clone())), Box::new(rt))),
                        Err(msg) => Err(msg),
                    }
                },
                None => {
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
                    if equal(&*t0, &argt) {
                        Ok(*t1)
                    }
                    else {
                        Err(format!("Function arguments not unifying."))
                    }
                },
                _ => Err(format!("Cannot call non-function.")),
            }
        }
    }
}
