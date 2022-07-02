
use std::fmt;

use crate::lib::parse::{EPreterm, Preterm};
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
    match (&term.0, &typ.0) {
        (EPreterm::Type(_), EPreterm::Kind) => Ok(()),
        (_, _) => {
            if *term == *typ {
                Ok(())
            } else {
                if term.1.is_none() || typ.1.is_none() {
                    return Err(Diagnostic::error()
                                .with_code("T-COMP")
                                .with_message("types are incompatible")
                                .with_notes(vec![format!("The types {} and {} are expected to be equal!",
                                                         term, typ)]));
                }
                else {
                    return Err(Diagnostic::error()
                                .with_code("T-COMP")
                                .with_message("types are incompatible")
                                .with_labels(vec![Label::primary((), term.1.clone().unwrap())
                                                .with_message(format!("This is the first type.")),
                                                Label::primary((), typ.1.clone().unwrap())
                                                .with_message(format!("This is the second type."))])
                                .with_notes(vec![format!("They are expected to be equal")]));
                }
            }
        },
    }
}

// checks if a given thing `typ` is actually a type
// Return type models
fn wf(gamma : &mut Ctx, typ : &Preterm) -> InformativeBool {
    match &typ.0 {
        EPreterm::Kind => Ok(()),
        EPreterm::Type(_i) => Ok(()),
        EPreterm::Unit => Ok(()),
        EPreterm::Var(x) => {
            let el = (&gamma.0).into_iter()
                          .find(|el| match el {
                              CtxElem::C(y,_t) => x == y,
                              CtxElem::Ex(y, _v) => x == y,
                          });
            if el.is_none() {
                if typ.1.is_none() {
                    return Err(Diagnostic::error()
                                .with_code("T-TVAR")
                                .with_message("type variable not found in context")
                                .with_notes(vec![format!("The variable that was expected is {}.", x)])
                                .with_notes(vec![format!(
                                    "This is the context:\n{}",
                                    gamma)
                                ]));
                }
                else {
                    return Err(Diagnostic::error()
                                .with_code("T-TVAR")
                                .with_message("type variable not found in context")
                                .with_labels(vec![Label::primary((), typ.1.clone().unwrap())
                                                .with_message(format!("This is the variable."))])
                                .with_notes(vec![format!(
                                    "This is the context:\n{}",
                                    gamma)
                                ]));
                }
            }
            match el.unwrap().clone() {
                CtxElem::C(_y, t) => wf(gamma, &t),
                CtxElem::Ex(_y, _v) => Ok(()),
            }
        },
        EPreterm::Lambda(_,Some(t0),t1) => { let _ = wf(gamma, &*t0)?; wf(gamma, &*t1) },

        EPreterm::TAnnot(a,t) => { let _ = wf(gamma, &*a)?; check(gamma, &*t, &Preterm(EPreterm::Kind, None)) },
        _ => {
            if typ.1.is_none() {
                Err(Diagnostic::error()
                    .with_code("T-WF")
                    .with_message("expected well-formed type")
                    .with_notes(vec![format!("{} doesn't appear to be well-formed!", typ)]))
            }
            else {
                Err(Diagnostic::error()
                    .with_code("T-WF")
                    .with_message("expected well-formed type")
                    .with_labels(vec![Label::primary((), typ.1.clone().unwrap())
                                    .with_message(format!("This doesn't appear to be well-formed!"))]))
            }
        }
    }
}

// the return type is supposed to model a boolean value, where "false" has a bit info about the error
pub fn check(gamma : &mut Ctx, term : &Preterm, typ : &Preterm) -> InformativeBool {
    let _ = wf(gamma, &typ)?;
    let inferrd = infer(gamma, term)?;

    lessequal(&Preterm(inferrd, None), typ)
}

// TODO: return CTXElem?
pub fn infer(gamma : &mut Ctx, term : &Preterm) -> Result<EPreterm, Diagnostic<()>> {
    match &term.0 {
        EPreterm::Kind => Err(Diagnostic::error()
                             .with_code("T-INFK")
                             .with_message("Kinds don't have a type")),
        EPreterm::Type(lv) => Ok(EPreterm::Type(lv + 1)),
        EPreterm::Unit => Ok(EPreterm::Unit),

        EPreterm::TAnnot(a, t) => {
            check(gamma, &*a, &*t)
                .and_then(|_| Ok((*t).0.clone()))
                .map_err(|e| e.with_labels(vec![Label::primary((), term.1.clone().unwrap()) // an annotation must be present in the source file...!
                                           .with_message(format!("This is the annotation in question."))])
                              .with_notes(vec![format!("Ill-formed type annotation.")]))
        },

        EPreterm::Var(x) => {
            let el = (&gamma.0).into_iter()
                          .find(|el| match el {
                              CtxElem::C(y,_t) => x == y,
                              CtxElem::Ex(y,_v) => x == y,
                          });
            match el {
                Some(CtxElem::C(_y,t)) => Ok(t.0.clone()),
                Some(CtxElem::Ex(y,v)) => Err(Diagnostic::error()
                                               .with_code("TODO")),
                None => {
                    if term.1.is_none() {
                        Err(Diagnostic::error()
                            .with_code("T-VAR")
                            .with_message("variable not found in context")
                            .with_notes(vec![format!("{} is the expected variable.", term),
                                             format!("The context:\n{}", gamma)]))
                    }
                    else {
                        Err(Diagnostic::error()
                            .with_code("T-VAR")
                            .with_message("variable not found in context")
                            .with_labels(vec![Label::primary((), term.1.clone().unwrap())
                                              .with_message(format!("This is the variable."))])
                            .with_notes(vec![format!("The context:\n{}", gamma)]))
                    }
                }
            }
        },

        EPreterm::Lambda(x, ot, bdy) => {
            match ot {
                Some(t) => {
                    let _ = wf(gamma, &*t)?;
                    let containsbinder = x != "_" && fv(&(*bdy).0).contains(x);
                    if containsbinder {
                        gamma.0.push(CtxElem::C(x.clone(), *t.clone()));
                    }
                    let r = infer(gamma, &*bdy)?;
                    if containsbinder {
                        gamma.0.pop();
                    }
                    Ok(EPreterm::Lambda(
                       if !containsbinder { String::from("_") } else { x.clone() },
                       Some(Box::new(*t.clone())), Box::new(Preterm(r, None))))
                },
                None => {
                    let containsbinder = x != "_" && fv(&(*bdy).0).contains(x);
                    if !containsbinder {
                        return infer(gamma, &*bdy)
                            .and_then(|tbdy| Ok(EPreterm::Lambda(format!("_"),
                                                                Some(Box::new(Preterm(EPreterm::Unit, None))),
                                                                Box::new(Preterm(tbdy, None))
                            )));
                    }
                    todo!()
                }
            }
        },

        EPreterm::App(a,b) => {
            let fnt = infer(gamma, &*a)?;
            let argt = infer(gamma, &*b)?;
            let argT = Preterm(argt, None);

            match fnt {
                EPreterm::Lambda(_, Some(t0), t1) => {
                    // t0 -> t1
                    lessequal(&argT, &*t0)
                        .and_then(|_| Ok((*t1).0))
                        .map_err(|msg| {
                            if (*a).1.is_none() || (*b).1.is_none() {
                                msg
                            }
                            else {
                                msg.with_labels(vec![Label::primary((), (*a).1.clone().unwrap().start..(*b).1.clone().unwrap().end)
                                                                .with_message(format!("Function does not accept the type of this argument.")),

                                                                Label::secondary((), (*a).1.clone().unwrap().clone())
                                                                .with_message(format!("Parameter type is {}", t0)),

                                                                Label::secondary((), (*b).1.clone().unwrap().clone())
                                                                .with_message(format!("Argument type is {}", argT))])
                            }
                            .with_notes(vec![format!("Parameter and argument type need to be compatible.")])
                        })
                },
                _ => {
                    if (*a).1.is_none() {
                        Err(Diagnostic::error()
                                .with_code("T-FUN")
                                .with_message("function type expected")
                                .with_notes(vec![format!("Type {} is not a function type.", argT)]))
                    }
                    else {
                        Err(Diagnostic::error()
                                .with_code("T-FUN")
                                .with_message("function type expected")
                                .with_labels(vec![Label::primary((), (*a).1.clone().unwrap())
                                                .with_message(format!("This has type {} which is not a function type.",
                                                                        Preterm(fnt, None)))]))
                    }
                }
            }
        }
    }
}
