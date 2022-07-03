use std::fmt;
use std::sync::Mutex;

use crate::lib::names::fv;
use crate::lib::parse::{EPreterm, Preterm};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use lazy_static::lazy_static;
use typed_arena::Arena;

fn cc(p: EPreterm) -> Preterm {
    Preterm(p, None)
}
fn cex(ctx : &mut Ctx) -> Preterm {
    lazy_static! {
        static ref COUNTER: Mutex<Box<u32>> = Mutex::new(Box::new(0));
    }
    let c = **COUNTER.lock().unwrap();
    **COUNTER.lock().unwrap() = c + 1;

    ctx.1.alloc(vec![]);
    cc(EPreterm::Ex(format!("α{}", c), ctx.1.len()-1))
}
pub struct Ctx(pub Vec<(String, Preterm)>, pub Arena<Vec<Preterm>>);

impl fmt::Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;

        let mut cnt = 0;
        for (n, x) in &self.0 {
            if cnt > 0 {
                write!(f, ", ");
            }
            write!(f, "{} : {}", n, x)?;
            cnt += 1;
        }
        write!(f, "]")
    }
}

pub type InformativeBool = Result<(), Diagnostic<()>>;

fn lessequal(gamma: &mut Ctx, typa: &mut Preterm, typb: &mut Preterm) -> InformativeBool {
    match (&mut typa.0, &mut typb.0) {
        (EPreterm::Ex(x, _), EPreterm::Ex(y, _)) => {
            if x == y {
                Ok(())
            } else {
                Err(Diagnostic::error())
            }
        }
        (_t, EPreterm::Ex(_, es)) => {
            gamma.1.iter_mut().nth(*es).and_then(|v| Some(v.push((*typa).clone())));
            Ok(())
        }
        (EPreterm::Ex(_, es), _t) => {
            gamma.1.iter_mut().nth(*es).and_then(|v| Some(v.push((*typb).clone())));
            Ok(())
        }
        (EPreterm::Kind, EPreterm::Kind) => Ok(()),
        (EPreterm::Kind, _) => Err(Diagnostic::error().with_code("T-KIND").with_message("kind expected to be less than something else which is not a kind")),
        (EPreterm::Type(_), EPreterm::Kind) => Ok(()),
        (EPreterm::Lambda(x,Some(a), b), EPreterm::Kind) => {
            let r = lessequal(gamma, &mut *a, &mut cc(EPreterm::Kind));

            gamma.0.push((x.clone(), (**a).clone()));
            let r = r.and(lessequal(gamma, &mut *b, &mut cc(EPreterm::Kind)));
            gamma.0.pop();
            r
        }
        (EPreterm::Var(x), EPreterm::Kind) => {
            let (mut _ign, mut el) = (&gamma.0).into_iter().find(|(el, _)| x == el).cloned().unwrap();
            lessequal(gamma, &mut el, &mut cc(EPreterm::Kind))
        },
        (EPreterm::Lambda(x0, Some(a0), b0), EPreterm::Lambda(x1, Some(a1), b1)) => {
            let ra = lessequal(gamma, &mut *a0, &mut *a1);

            gamma.0.push((x0.clone(), (**a0).clone()));
            gamma.0.push((x1.clone(), (**a1).clone()));
            let rb = ra.and(lessequal(gamma, &mut *b0, &mut *b1));
            gamma.0.pop();
            gamma.0.pop();
            rb
        },
        (t0, t1) => {
            if t0 == t1 {
                Ok(())
            } else {
                if typa.1.is_none() || typb.1.is_none() {
                    return Err(Diagnostic::error()
                        .with_code("T-COMP")
                        .with_message("types are incompatible")
                        .with_notes(vec![format!(
                            "The types {} and {} are expected to be equal!",
                            typa, typb
                        )]));
                } else {
                    return Err(Diagnostic::error()
                        .with_code("T-COMP")
                        .with_message("types are incompatible")
                        .with_labels(vec![
                            Label::primary((), typa.1.clone().unwrap())
                                .with_message(format!("This is the first type.")),
                            Label::primary((), typb.1.clone().unwrap())
                                .with_message(format!("This is the second type.")),
                        ])
                        .with_notes(vec![format!("They are expected to be equal")]));
                }
            }
        }
    }
}

// checks if a given thing `typ` is actually a type
// Return type models
fn wf(gamma: &mut Ctx, typ: &mut Preterm) -> InformativeBool {
    match &mut typ.0 {
        EPreterm::Kind => Ok(()),
        EPreterm::Type(_i) => Ok(()),
        EPreterm::Unit => Ok(()),
        EPreterm::Ex(_, _) => todo!(),
        EPreterm::Var(x) => {
            let el = (&gamma.0).into_iter().find(|(el, _)| x == el).clone();
            if el.is_none() {
                if typ.1.is_none() {
                    return Err(Diagnostic::error()
                        .with_code("T-TVAR")
                        .with_message("type variable not found in context")
                        .with_notes(vec![format!("The variable that was expected is {}.", x)])
                        .with_notes(vec![format!("This is the context:\n{}", gamma)]));
                } else {
                    return Err(Diagnostic::error()
                        .with_code("T-TVAR")
                        .with_message("type variable not found in context")
                        .with_labels(vec![Label::primary((), typ.1.clone().unwrap())
                            .with_message(format!("This is the variable."))])
                        .with_notes(vec![format!("This is the context:\n{}", gamma)]));
                }
            }
            match el.clone() {
                Some((_, Preterm(EPreterm::Ex(_y, _v), _))) => Ok(()),
                Some((_, t)) => wf(gamma, &mut t.clone()),
                _ => panic!(),
            }
        }
        EPreterm::Lambda(x, Some(t0), t1) => {
            let _ = wf(gamma, &mut *t0)?;

            gamma.0.push((x.clone(), *t0.clone()));
            let r = wf(gamma, &mut *t1);
            gamma.0.pop();

            r
        }

        EPreterm::TAnnot(a, t) => {
            let _ = wf(gamma, &mut *a)?;
            check(gamma, &mut *t, &mut cc(EPreterm::Kind))
        }
        _ => {
            if typ.1.is_none() {
                Err(Diagnostic::error()
                    .with_code("T-WF")
                    .with_message("expected well-formed type")
                    .with_notes(vec![format!("{} doesn't appear to be well-formed!", typ)]))
            } else {
                Err(Diagnostic::error()
                    .with_code("T-WF")
                    .with_message("expected well-formed type")
                    .with_labels(vec![Label::primary((), typ.1.clone().unwrap())
                        .with_message(format!("This doesn't appear to be well-formed!"))]))
            }
        }
    }
}

fn concretize(gamma: &mut Ctx, c: &mut Preterm) -> Result<Preterm, Diagnostic<()>> {
    match &mut c.0 {
        EPreterm::Ex(_, esidx) => {
            let eslen = gamma.1.iter_mut().nth(*esidx).unwrap().len();
            if eslen == 0 {
                Err(Diagnostic::error()
                    .with_code("T-EX")
                    .with_message("no constraints for typed hole"))
            } else if eslen == 1 {
                let mut t = gamma.1.iter_mut().nth(*esidx).unwrap().first().unwrap().clone();
                concretize(gamma, &mut t)
            } else {
                let mut t = gamma.1.iter_mut().nth(*esidx).unwrap().first().unwrap().clone();

                for mx in gamma.1.iter_mut().nth(*esidx).unwrap().iter().next().cloned() {
                    let mut mx = mx;
                    if let Err(e) = lessequal(gamma, &mut t, &mut mx) {
                        return Err(e);
                    }
                }
                concretize(gamma, &mut t)
            }
        }
        t => Ok(cc((*t).clone())),
    }
}
pub fn deep_concretize(gamma: &mut Ctx, c: &mut Preterm) -> Result<Preterm, Diagnostic<()>> {
    match &mut c.0 {
        EPreterm::Type(_) | EPreterm::Var(_) | EPreterm::Unit | EPreterm::Kind => Ok(c.clone()),
        EPreterm::App(a,b) => {
            let a = deep_concretize(gamma, &mut *a)?;
            let b = deep_concretize(gamma, &mut *b)?;
            Ok(Preterm(EPreterm::App(Box::new(a), Box::new(b)), c.1.clone()))
        },
        EPreterm::Lambda(x,ot,b) => {
            let b = deep_concretize(gamma, b)?;
            match ot {
                None => Ok(Preterm(EPreterm::Lambda(x.clone(), None, Box::new(b)), c.1.clone())),
                Some(t) => {
                    let t = deep_concretize(gamma, t)?;
                    Ok(Preterm(EPreterm::Lambda(x.clone(), Some(Box::new(t)), Box::new(b)), c.1.clone()))
                }
            }
        },
        EPreterm::TAnnot(a,b) => {
            let a = deep_concretize(gamma, &mut *a)?;
            let b = deep_concretize(gamma, &mut *b)?;
            Ok(Preterm(EPreterm::TAnnot(Box::new(a), Box::new(b)), c.1.clone()))
        },
        EPreterm::Ex(_,_) => concretize(gamma, c),
    }
}

// the return type is supposed to model a boolean value, where "false" has a bit info about the error
pub fn check(gamma: &mut Ctx, term: &mut Preterm, typ: &mut Preterm) -> InformativeBool {
    let _ = wf(gamma, typ)?;
    let mut inferrd = infer(gamma, term)?;

    lessequal(gamma, &mut inferrd, typ)
}

pub fn infer(gamma: &mut Ctx, term: &mut Preterm) -> Result<Preterm, Diagnostic<()>> {
    match &mut term.0 {
        EPreterm::Kind => Err(Diagnostic::error()
            .with_code("T-INFK")
            .with_message("Kinds don't have a type")),
        EPreterm::Type(lv) => Ok(cc(EPreterm::Type(*lv + 1))),
        EPreterm::Unit => Ok(cc(EPreterm::Unit)),
        EPreterm::Ex(_, _) => Err(Diagnostic::error().with_code("FIXME?")),

        EPreterm::TAnnot(a, t) => {
            let location = term.1.clone().unwrap();
            let _ =
                check(gamma, &mut *t, &mut cc(EPreterm::Kind))
                    .and_then(|_| Ok(()))
                    .map_err(|e| {
                        e
                            .with_labels(
                                vec![
                                    Label::primary((), location) // an annotation must be present in the source file...!
                                        .with_message(format!(
                                            "This is the annotation in question."
                                        )),
                                ],
                            )
                            .with_notes(vec![format!("Ill-formed type annotation.")])
                    })?;
            check(gamma, &mut *a, &mut *t).and_then(|_| Ok((**t).clone()))
        }

        EPreterm::Var(x) => {
            let el = (&gamma.0).into_iter().find(|(el, _)| x == el);
            match el {
                Some((_, Preterm(EPreterm::Ex(y, v), l))) => {
                    Ok(Preterm(EPreterm::Ex((*y).clone(), (*v).clone()), (*l).clone()))
                }
                Some((_, t)) => Ok(t.clone()),
                None => {
                    if term.1.is_none() {
                        Err(Diagnostic::error()
                            .with_code("T-VAR")
                            .with_message("variable not found in context")
                            .with_notes(vec![
                                format!("{} is the expected variable.", term),
                                format!("The context:\n{}", gamma),
                            ]))
                    } else {
                        Err(Diagnostic::error()
                            .with_code("T-VAR")
                            .with_message("variable not found in context")
                            .with_labels(vec![Label::primary((), term.1.clone().unwrap())
                                .with_message(format!("This is the variable."))])
                            .with_notes(vec![format!("The context:\n{}", gamma)]))
                    }
                }
            }
        }

        EPreterm::Lambda(x, ot, bdy) => {
            match ot {
                Some(t) => {
                    let _ = wf(gamma, &mut *t)?;
                    let containsbinder = x != "_" && fv(&(*bdy).0).contains(x);
                    if containsbinder {
                        gamma.0.push((x.clone(), *t.clone()));
                    }
                    let r = infer(gamma, &mut *bdy)?;
                    if containsbinder {
                        gamma.0.pop();
                    }
                    Ok(cc(EPreterm::Lambda(
                        if !containsbinder {
                            String::from("_")
                        } else {
                            x.clone()
                        },
                        Some(Box::new(*t.clone())),
                        Box::new(r),
                    )))
                }
                None => {
                    let containsbinder = x != "_" && fv(&(*bdy).0).contains(x);
                    let ex = cex(gamma);
                    let r = {
                        if containsbinder {
                            gamma.0.push((x.clone(), ex.clone()));
                            let r = infer(gamma, &mut *bdy)?;
                            gamma.0.pop();
                            Ok(r)
                        }
                        else {
                            infer(gamma, &mut *bdy)
                        }
                    }?;

                    Ok(cc(EPreterm::Lambda(
                        x.clone(),
                        Some(Box::new(ex)),
                        Box::new(r),
                    )))
                }
            }
        }

        EPreterm::App(a, b) => {
            let mut fnt = infer(gamma, &mut *a)?;
            let mut argt = infer(gamma, &mut *b)?;

            match &mut fnt.0 {
                EPreterm::Ex(_, fntes) => {
                    let ex1 = cex(gamma);
                    let ex2 = cex(gamma);

                    let ty = cc(EPreterm::Lambda(
                        format!("_"),
                        Some(Box::new(ex1)),
                        Box::new(ex2),
                    ));
                    gamma.1.iter_mut().nth(*fntes).unwrap().push(ty.clone());

                    Ok(ty)
                }
                EPreterm::Lambda(_, Some(t0), t1) => {
                    // t0 -> t1
                    lessequal(gamma, &mut argt, &mut *t0)
                        .and_then(|_| Ok((**t1).clone()))
                        .map_err(|msg| {
                            if (*a).1.is_none() || (*b).1.is_none() {
                                msg
                            } else {
                                msg.with_labels(vec![
                                    Label::primary(
                                        (),
                                        (*a).1.clone().unwrap().start..(*b).1.clone().unwrap().end,
                                    )
                                    .with_message(format!(
                                        "Function does not accept the type of this argument."
                                    )),
                                    Label::secondary((), (*a).1.clone().unwrap().clone())
                                        .with_message(format!("Parameter type is {}", t0)),
                                    Label::secondary((), (*b).1.clone().unwrap().clone())
                                        .with_message(format!("Argument type is {}", argt.clone())),
                                ])
                            }
                            .with_notes(vec![format!(
                                "Parameter and argument type need to be compatible."
                            )])
                        })
                }
                _ => {
                    if (*a).1.is_none() {
                        Err(Diagnostic::error()
                            .with_code("T-FUN")
                            .with_message("function type expected")
                            .with_notes(vec![format!(
                                "Type {} is not a function type.",
                                argt.clone()
                            )]))
                    } else {
                        Err(Diagnostic::error()
                            .with_code("T-FUN")
                            .with_message("function type expected")
                            .with_labels(vec![Label::primary((), (*a).1.clone().unwrap())
                                .with_message(format!(
                                    "This has type {} which is not a function type.",
                                    fnt
                                ))]))
                    }
                }
            }
        }
    }
}
