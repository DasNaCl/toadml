
use std::fmt;

use crate::lib::parse::Preterm;
use crate::lib::names::fv;

use codespan_reporting::diagnostic::{Label, Diagnostic};

#[derive(Debug, Clone)]
pub enum CtxElem {
    Ex(String, Ctx),
    C(String, Preterm)
}

impl fmt::Display for CtxElem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CtxElem::Ex(name, els) => {
                write!(f, "α{{{}}} : {}", name, els)
            },
            CtxElem::C(name, p) => write!(f, "{} : {}", name, p),
        }
    }
}

pub type InformativeBool = Result<(), Diagnostic<()>>;

#[derive(Debug, Clone)]
pub struct Ctx(pub Vec<CtxElem>);

impl fmt::Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;

        let mut cnt = 0;
        for x in &self.0 {
            write!(f, "{}", x)?;
            if cnt > 0 && cnt < self.0.len() - 1 {
                write!(f, ", ")?;
            }
            cnt += 1;
        }
        write!(f, "]")
    }
}

fn lessequal(term : &Preterm, typ : &Preterm) -> InformativeBool {
    match (term, typ) {
        (Preterm::Type(_), Preterm::Kind) => Ok(()),
        (_, _) => {
            if *term == *typ {
                Ok(())
            } else {
                return Err(Diagnostic::error()
                            .with_code("T-COMP")
                            .with_message("types are incompatible")
                            .with_notes(vec![format!(
                                "Expected {} and {} to be equal.",
                                *term, *typ)
                            ]));
            }
        },
    }
}

// checks if a given thing `typ` is actually a type
// Return type models
fn wf(gamma : &mut Ctx, typ : &Preterm) -> InformativeBool {
    match typ {
        Preterm::Kind => Ok(()),
        Preterm::Type(_i) => Ok(()),
        Preterm::Unit => Ok(()),
        Preterm::Var(x) => {
            let el = (&gamma.0).into_iter()
                          .find(|el| match el {
                              CtxElem::C(y,_t) => x == y,
                              CtxElem::Ex(y, _v) => x == y,
                          });
            if el.is_none() {
                return Err(Diagnostic::error()
                            .with_code("T-TVAR")
                            .with_message("type variable not found in context")
                            .with_notes(vec![format!(
                                "The type variable {} does not appear in the context:\n{}",
                                x, gamma)
                            ]));
            }
            match el.unwrap().clone() {
                CtxElem::C(_y, t) => wf(gamma, &t),
                CtxElem::Ex(_y, _v) => Ok(()),
            }
        },
        Preterm::Lambda(_,Some(t0),t1) => { let _ = wf(gamma, &*t0)?; wf(gamma, &*t1) },

        Preterm::TAnnot(a,t) => { let _ = wf(gamma, &*a)?; check(gamma, &*t, &Preterm::Kind) },
        _ => Err(Diagnostic::error()
                 .with_code("T-WF")
                 .with_message("expected well-formed type")
                 .with_notes(vec![format!(
                     "{} does not appear to be well-formed!",
                     typ)
                 ]))
    }
}

// the return type is supposed to model a boolean value, where "false" has a bit info about the error
pub fn check(gamma : &mut Ctx, term : &Preterm, typ : &Preterm) -> InformativeBool {
    let _ = wf(gamma, &typ)?;
    let inferrd = infer(gamma, term)?;

    lessequal(&inferrd, typ)
}

// TODO: return CTXElem?
pub fn infer(gamma : &mut Ctx, term : &Preterm) -> Result<Preterm, Diagnostic<()>> {
    match term {
        Preterm::Kind => Err(Diagnostic::error()
                             .with_code("T-INFK")
                             .with_message("Kinds don't have a type")),
        Preterm::Type(lv) => Ok(Preterm::Type(lv + 1)),
        Preterm::Unit => Ok(Preterm::Unit),

        Preterm::TAnnot(a, t) => {
            check(gamma, &*a, &*t)
                .and_then(|_| Ok(*t.clone()))
                .map_err(|e| e.with_notes(vec![format!("Ill-formed type annotation.")]))
        },

        Preterm::Var(x) => {
            let el = (&gamma.0).into_iter()
                          .find(|el| match el {
                              CtxElem::C(y,_t) => x == y,
                              CtxElem::Ex(y,_v) => x == y,
                          });
            match el {
                Some(CtxElem::C(_y,t)) => Ok(t.clone()),
                Some(CtxElem::Ex(y,v)) => Err(Diagnostic::error()
                                               .with_code("TODO")),
                None => Err(Diagnostic::error()
                            .with_code("T-VAR")
                            .with_message("variable not found in context")
                            .with_notes(vec![format!(
                                "The variable {} does not appear in the context:\n{}",
                                x, gamma)
                            ]))
            }
        },

        Preterm::Lambda(x, ot, bdy) => {
            match ot {
                Some(t) => {
                    let _ = wf(gamma, &*t)
                        .map_err(|e| e.with_notes(vec![format!("Ill-formed type annotation for binder {}.", x)]))?;
                    let containsbinder = x != "_" && fv(bdy).contains(x);
                    if containsbinder {
                        gamma.0.push(CtxElem::C(x.clone(), *t.clone()));
                    }
                    let r = infer(gamma, &*bdy)?;
                    if containsbinder {
                        gamma.0.pop();
                    }
                    Ok(Preterm::Lambda(
                       if !containsbinder { String::from("_") } else { x.clone() },
                       Some(Box::new(*t.clone())), Box::new(r)))
                },
                None => {
                    let containsbinder = x != "_" && fv(bdy).contains(x);
                    if !containsbinder {
                        return infer(gamma, &*bdy)
                            .and_then(|tbdy| Ok(Preterm::Lambda(format!("_"),
                                                                Some(Box::new(Preterm::Unit)),
                                                                Box::new(tbdy)
                            )));
                    }
                    todo!()
                }
            }
        },

        Preterm::App(a,b) => {
            let fnt = infer(gamma, &*a)?;
            let argt = infer(gamma, &*b)?;

            match fnt {
                Preterm::Lambda(_, Some(t0), t1) => {
                    // t0 -> t1
                    lessequal(&argt, &*t0)
                        .and_then(|_| Ok(*t1))
                        .map_err(|msg| msg.with_notes(vec![format!(
                            "Function argument {} and function parameter {} are incompatible.",
                            argt, *t0
                        )]))
                },
                _ => Err(Diagnostic::error()
                            .with_code("T-FUN")
                            .with_message("function type expected")
                            .with_notes(vec![format!(
                                "The type {} is not callable.",
                                fnt)
                            ]))
            }
        }
    }
}
