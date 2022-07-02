
use std::fmt;
use std::sync::Mutex;

use crate::lib::parse::{EPreterm, Preterm, Constraints};
use crate::lib::names::fv;

use lazy_static::lazy_static;
use itertools::Itertools;
use codespan_reporting::diagnostic::{Label, Diagnostic};

fn C(p : EPreterm) -> Preterm { Preterm(p, None) }
fn Ex() -> Preterm {
    lazy_static! {
        static ref COUNTER : Mutex<Box<u32>> = Mutex::new(Box::new(0));
    }
    let c = **COUNTER.lock().unwrap();
    **COUNTER.lock().unwrap() = c + 1;

    C(EPreterm::Ex(format!("α{}", c), Constraints(vec![])))
}
#[derive(Debug, Clone)]
pub struct Ctx(pub Vec<(String,Preterm)>);

impl fmt::Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;

        let mut cnt = 0;
        for (n,x) in &self.0 {
            write!(f, "{} : {}", n, x)?;
            if cnt > 0 && cnt < self.0.len() - 1 {
                write!(f, ", ")?;
            }
            cnt += 1;
        }
        write!(f, "]")
    }
}

pub type InformativeBool = Result<(), Diagnostic<()>>;

fn lessequal(typa : &mut Preterm, typb : &mut Preterm) -> InformativeBool {
    match (&mut typa.0, &mut typb.0) {
        (EPreterm::Ex(x,_), EPreterm::Ex(y, _)) => {
            if x == y { Ok(()) } else { Err(Diagnostic::error()) }
        },
        (_t, EPreterm::Ex(_, es)) => { (*es).0.push(typa.clone()); Ok(()) },
        (EPreterm::Ex(_, es), _t) => { (*es).0.push(typb.clone()); Ok(()) },
        (EPreterm::Type(_), EPreterm::Kind) => Ok(()),
        (t0, t1) => {
            if t0 == t1 {
                Ok(())
            } else {
                if typa.1.is_none() || typb.1.is_none() {
                    return Err(Diagnostic::error()
                                .with_code("T-COMP")
                                .with_message("types are incompatible")
                                .with_notes(vec![format!("The types {} and {} are expected to be equal!",
                                                        typa, typb)]));
                }
                else {
                    return Err(Diagnostic::error()
                                .with_code("T-COMP")
                                .with_message("types are incompatible")
                                .with_labels(vec![Label::primary((), typa.1.clone().unwrap())
                                                .with_message(format!("This is the first type.")),
                                                Label::primary((), typb.1.clone().unwrap())
                                                .with_message(format!("This is the second type."))])
                                .with_notes(vec![format!("They are expected to be equal")]));
                }
            }
        },
    }
}

// checks if a given thing `typ` is actually a type
// Return type models
fn wf(gamma : &mut Ctx, typ : &mut Preterm) -> InformativeBool {
    match &mut typ.0 {
        EPreterm::Kind => Ok(()),
        EPreterm::Type(_i) => Ok(()),
        EPreterm::Unit => Ok(()),
        EPreterm::Ex(_,_) => todo!(),
        EPreterm::Var(x) => {
            let el = (&gamma.0).into_iter()
                               .find(|(el,_)| x == el).clone();
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
            match el.clone() {
                Some((_,Preterm(EPreterm::Ex(_y, _v),_))) => Ok(()),
                Some((_,t)) => wf(gamma, &mut t.clone()),
                _ => panic!()
            }
        },
        EPreterm::Lambda(_,Some(t0),t1) => { let _ = wf(gamma, &mut *t0)?; wf(gamma, &mut *t1) },

        EPreterm::TAnnot(a,t) => { let _ = wf(gamma, &mut *a)?; check(gamma, &mut *t, &mut C(EPreterm::Kind)) },
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

fn concretize(c : &mut Preterm) -> Result<Preterm, Diagnostic<()>> {
    match &mut c.0 {
        EPreterm::Ex(_,es) => {
            if (*es).0.len() == 1 {
                let mut t = (*es).0.first().unwrap().clone();
                concretize(&mut t)
            }
            else {
                let mut t = (*es).0.first().unwrap().clone();

                for x in (*es).0.iter_mut() {
                    let mut mx = x;
                    if let Err(e) = lessequal(&mut t, &mut mx) {
                        return Err(e);
                    }
                }
                concretize(&mut t)
            }
        },
        t => Ok(C((*t).clone()))
    }
}

// the return type is supposed to model a boolean value, where "false" has a bit info about the error
pub fn check(gamma : &mut Ctx, term : &mut Preterm, typ : &mut Preterm) -> InformativeBool {
    let _ = wf(gamma, typ)?;
    let mut inferrd = infer(gamma, term)?;

    lessequal(&mut inferrd, typ)
}

pub fn infer(gamma : &mut Ctx, term : &mut Preterm) -> Result<Preterm, Diagnostic<()>> {
    match &mut term.0 {
        EPreterm::Kind => Err(Diagnostic::error()
                             .with_code("T-INFK")
                             .with_message("Kinds don't have a type")),
        EPreterm::Type(lv) => Ok(C(EPreterm::Type(*lv + 1))),
        EPreterm::Unit => Ok(C(EPreterm::Unit)),
        EPreterm::Ex(_,_) => Err(Diagnostic::error().with_code("FIXME?")),

        EPreterm::TAnnot(a, t) => {
            check(gamma, &mut *a, &mut *t)
                .and_then(|_| Ok((**t).clone()))
                .map_err(|e| e.with_labels(vec![Label::primary((), term.1.clone().unwrap()) // an annotation must be present in the source file...!
                                           .with_message(format!("This is the annotation in question."))])
                              .with_notes(vec![format!("Ill-formed type annotation.")]))
        },

        EPreterm::Var(x) => {
            let el = (&gamma.0).into_iter()
                               .find(|(el,_)| x == el);
            match el {
                Some((_,Preterm(EPreterm::Ex(y,v), _))) => Err(Diagnostic::error()
                                               .with_code("TODO")),
                Some((_,t)) => Ok(t.clone()),
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
                    let _ = wf(gamma, &mut *t)?;
                    let containsbinder = x != "_" && fv(&(*bdy).0).contains(x);
                    if containsbinder {
                        gamma.0.push((x.clone(), *t.clone()));
                    }
                    let mut r = infer(gamma, &mut *bdy)?;
                    if containsbinder {
                        gamma.0.pop();
                    }
                    let cr = concretize(&mut r)?;
                    Ok(C(EPreterm::Lambda(
                        if !containsbinder { String::from("_") } else { x.clone() },
                        Some(Box::new(*t.clone())), Box::new(cr))))
                },
                None => {
                    let containsbinder = x != "_" && fv(&(*bdy).0).contains(x);
                    if !containsbinder {
                        return infer(gamma, &mut *bdy)
                            .and_then(|tbdy| {
                                let mut mtbdy = tbdy;
                                let ctbdy = concretize(&mut mtbdy)?;
                                Ok(C(EPreterm::Lambda(format!("_"),
                                                      Some(Box::new(Preterm(EPreterm::Unit, None))),
                                                      Box::new(ctbdy))))
                            });
                    }
                    todo!()
                }
            }
        },

        EPreterm::App(a,b) => {
            let mut fnt = infer(gamma, &mut *a)?;
            let mut argt = infer(gamma, &mut *b)?;

            match &mut fnt.0 {
                EPreterm::Ex(_,fntes) => {
                    //let ex1 = Ex();
                    //let ex2 = Ex();

                    // (*fntes).0.push(C(EPreterm::Lambda("_", ex1, ex2)));
                    todo!("add constraint to this existential that it should be a function")
                }
                EPreterm::Lambda(_, Some(t0), t1) => {
                    // t0 -> t1
                    lessequal(&mut argt, &mut *t0)
                        .and_then(|_| Ok((**t1).clone()))
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
                                                                .with_message(format!("Argument type is {}", argt.clone()))])
                            }
                            .with_notes(vec![format!("Parameter and argument type need to be compatible.")])
                        })
                },
                _ => {
                    if (*a).1.is_none() {
                        Err(Diagnostic::error()
                                .with_code("T-FUN")
                                .with_message("function type expected")
                                .with_notes(vec![format!("Type {} is not a function type.", argt.clone())]))
                    }
                    else {
                        Err(Diagnostic::error()
                                .with_code("T-FUN")
                                .with_message("function type expected")
                                .with_labels(vec![Label::primary((), (*a).1.clone().unwrap())
                                                .with_message(format!("This has type {} which is not a function type.", fnt))]))
                    }
                },
            }
        }
    }
}
