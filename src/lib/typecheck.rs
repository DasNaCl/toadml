use std::fmt;
use std::sync::Mutex;

use crate::lib::debruijn::{LTerm, ELTerm, noname};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use lazy_static::lazy_static;
use typed_arena::Arena;

fn cc(p: ELTerm) -> LTerm {
    LTerm(p, None)
}
fn cex(ctx : &mut Ctx, loc : logos::Span) -> LTerm {
    lazy_static! {
        static ref COUNTER: Mutex<Box<u32>> = Mutex::new(Box::new(0));
    }
    let c = **COUNTER.lock().unwrap();
    **COUNTER.lock().unwrap() = c + 1;

    ctx.1.alloc(vec![]);
    LTerm(ELTerm::Ex(format!("α{}", c), ctx.1.len()-1), Some(loc))
}
// index into ctx is variable idx/name
pub struct Ctx(pub Vec<LTerm>, pub Arena<Vec<LTerm>>, pub Vec<String>);


impl fmt::Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;

        let mut cnt = 0;
        for x in &self.0 {
            if cnt > 0 {
                write!(f, ", ");
            }
            let (slice, _) = self.2.split_at(cnt);
            let mut ctx = slice.iter().cloned().collect();
            let xstr = x.to_string(&mut ctx);
            let cntctr = (&self.2).into_iter().nth(cnt).unwrap();
            write!(f, "{} : {}", cntctr, xstr)?;
            cnt += 1;
        }
        write!(f, "]")
    }
}

pub type InformativeBool = Result<(), Diagnostic<()>>;

fn lessequal(gamma: &mut Ctx, typa: &LTerm, typb: &LTerm) -> InformativeBool {
    match (&typa.0, &typb.0) {
        (ELTerm::Ex(x, _), ELTerm::Ex(y, _)) => {
            if x == y {
                return Ok(())
            }
            let ra = concretize(gamma, &typa.clone());
            let rb = concretize(gamma, &typb.clone());
            match (ra, rb) {
                (Ok(a), Ok(b)) => lessequal(gamma, &a, &b),
                (Err(_),Ok(b)) => lessequal(gamma, &typa.clone(), &b),
                (Ok(a),Err(_)) => lessequal(gamma, &a, &typb.clone()),
                (Err(_),Err(_)) => {
                    Err(Diagnostic::error()
                        .with_code("T-EX").with_message("")
                        .with_message("type annotation needed")
                        .with_labels(vec![Label::primary((), typa.1.clone().unwrap()).with_message(format!("May need annotation.")),
                                          Label::primary((), typb.1.clone().unwrap()).with_message(format!("May need annotation."))]))
                }
            }
        }
        (_t, ELTerm::Ex(_, es)) => {
            gamma.1.iter_mut().nth(*es).and_then(|v| Some(v.push((*typa).clone())));
            Ok(())
        }
        (ELTerm::Ex(_, es), _t) => {
            gamma.1.iter_mut().nth(*es).and_then(|v| Some(v.push((*typb).clone())));
            Ok(())
        }
        (ELTerm::Kind, ELTerm::Kind) => Ok(()),
        (ELTerm::Kind, _) => Err(Diagnostic::error().with_code("T-KIND").with_message("kind expected to be less than something else which is not a kind")),
        (ELTerm::Type(_), ELTerm::Kind) => Ok(()),
        (ELTerm::Lambda(x,Some(a), b), ELTerm::Kind) => {
            let r = lessequal(gamma, &*a, &cc(ELTerm::Kind));

            gamma.0.push((**a).clone());
            gamma.2.push(if let Some(x) = x.0.clone() { x } else { format!("_") });
            let r = r.and(lessequal(gamma, &*b, &cc(ELTerm::Kind)));
            gamma.0.pop();
            gamma.2.pop();
            r
        }
        (ELTerm::Var(x), ELTerm::Kind) => {
            let el = (&gamma.0).into_iter().nth(*x as usize).cloned().unwrap();
            lessequal(gamma, &el, &cc(ELTerm::Kind))
        },
        (ELTerm::Lambda(x0, Some(a0), b0), ELTerm::Lambda(_x1, Some(a1), b1)) => {
            let ra = lessequal(gamma, &*a0, &*a1);

            gamma.0.push((**a0).clone());
            gamma.2.push(if let Some(x0) = x0.0.clone() { x0 } else { format!("_") });
            let rb = ra.and(lessequal(gamma, &*b0, &*b1));
            gamma.0.pop();
            gamma.2.pop();
            rb
        },
        (ELTerm::App(a0,b0), ELTerm::App(a1,b1)) => lessequal(gamma, &a0, &a1)
                                                        .and(lessequal(gamma, &b0, &b1)),
        (ELTerm::Var(x), ELTerm::Var(y)) => {
            match ((&gamma.0).into_iter().nth(*x as usize), (&gamma.0).into_iter().nth(*y as usize)) {
                (Some(a), Some(b)) => if a == b { Ok(()) } else {
                    let sx = (&gamma.2).into_iter().nth(*x as usize);
                    let sy = (&gamma.2).into_iter().nth(*y as usize);
                    if typa.1.is_none() || typb.1.is_none() {
                        if let (Some(sx), Some(sy)) = (sx, sy) {
                            Err(Diagnostic::error()
                                .with_code("T-COMP")
                                .with_message("types are incompatible")
                                .with_notes(vec![format!("{} and {} are not the same.", sx, sy)])
                            )
                        }
                        else {
                            Err(Diagnostic::error()
                                .with_code("T-COMP")
                                .with_message("types are incompatible"))
                        }
                    }
                    else {
                        Err(Diagnostic::error()
                            .with_code("T-COMP")
                            .with_message("types are incompatible")
                            .with_labels(vec![
                                Label::primary((), typa.1.clone().unwrap()),
                                Label::primary((), typb.1.clone().unwrap())
                            ])
                            .with_notes(vec![
                                if let (Some(sx), Some(sy)) = (sx, sy) {
                                    format!("{} and {} are not the same.", sx, sy)
                                }
                                else {
                                    format!("They are expected to be equal")
                                }]))
                    }
                },
                (_, _) => Err(Diagnostic::error()),
            }
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
                            Label::primary((), typa.1.clone().unwrap()),
                            Label::primary((), typb.1.clone().unwrap())
                        ])
                        .with_notes(vec![format!("They are expected to be equal")]));
                }
            }
        }
    }
}

// checks if a given thing `typ` is actually a type
// Return type models
fn wf(gamma: &mut Ctx, typ: &LTerm) -> InformativeBool {
    match &typ.0 {
        ELTerm::Kind => Ok(()),
        ELTerm::Type(_i) => Ok(()),
        ELTerm::Unit => Ok(()),
        ELTerm::Ex(_, _) => todo!(),
        ELTerm::Var(x) => {
            if let Some(el) = (&gamma.0).into_iter().nth(*x as usize) {
                match el.clone() {
                    LTerm(ELTerm::Ex(_y, _v), _) => Ok(()),
                    t => wf(gamma, &t.clone()),
                }
            }
            else {
                if typ.1.is_none() {
                    let name = (&gamma.2).into_iter().nth(*x as usize).unwrap();
                    return Err(Diagnostic::error()
                        .with_code("T-TVAR")
                        .with_message("type variable not found in context")
                        .with_notes(vec![format!("The variable that was expected is {}.", name)])
                        .with_notes(vec![format!("This is the context: {}", gamma)]));
                } else {
                    return Err(Diagnostic::error()
                        .with_code("T-TVAR")
                        .with_message("type variable not found in context")
                        .with_labels(vec![Label::primary((), typ.1.clone().unwrap())
                            .with_message(format!("This is the variable."))])
                        .with_notes(vec![format!("This is the context: {}", gamma)]));
                }
            }
        }
        ELTerm::Lambda(x, Some(t0), t1) => {
            let _ = wf(gamma, &*t0)?;

            gamma.0.push(*t0.clone());
            gamma.2.push(if let Some(x) = x.0.clone() { x } else { format!("_") });
            let r = wf(gamma, &*t1);
            gamma.0.pop();
            gamma.2.pop();

            r
        }
        ELTerm::App(a, b) => {
            let _ = wf(gamma, &*a)?;
            wf(gamma, &*b)
        }

        ELTerm::TAnnot(a, t) => {
            let _ = wf(gamma, &*a)?;
            check(gamma, &*t, &cc(ELTerm::Kind))
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

fn concretize(gamma: &mut Ctx, c: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    match &c.0 {
        ELTerm::Ex(_, esidx) => {
            let eslen = gamma.1.iter_mut().nth(*esidx).unwrap().len();
            if eslen == 0 {
                Err(Diagnostic::error()
                    .with_code("T-EX")
                    .with_message("type annotation needed")
                    .with_labels(vec![Label::primary((), c.1.clone().unwrap()).with_message(format!("This is the unknown."))]))
            } else if eslen == 1 {
                let t = gamma.1.iter_mut().nth(*esidx).unwrap().first().unwrap().clone();
                deep_concretize(gamma, &t)
            } else {
                let t = gamma.1.iter_mut().nth(*esidx).unwrap().first().unwrap().clone();
                let t = deep_concretize(gamma, &t)?;

                for mx in gamma.1.iter_mut().nth(*esidx).unwrap().iter().next().cloned() {
                    let mx = mx;
                    if let Err(e) = lessequal(gamma, &t, &mx) {
                        return Err(e);
                    }
                }
                Ok(t)
            }
        }
        t => deep_concretize(gamma, &cc((*t).clone())),
    }
}
pub fn deep_concretize(gamma: &mut Ctx, c: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    match &c.0 {
        ELTerm::Type(_) | ELTerm::Var(_) | ELTerm::Unit | ELTerm::Kind => Ok(c.clone()),
        ELTerm::App(a,b) => {
            let a = deep_concretize(gamma, &*a)?;
            let b = deep_concretize(gamma, &*b)?;
            Ok(LTerm(ELTerm::App(Box::new(a), Box::new(b)), c.1.clone()))
        },
        ELTerm::Lambda(x,ot,b) => {
            let b = deep_concretize(gamma, b)?;
            match ot {
                None => Ok(LTerm(ELTerm::Lambda(x.clone(), None, Box::new(b)), c.1.clone())),
                Some(t) => {
                    let t = deep_concretize(gamma, t)?;
                    Ok(LTerm(ELTerm::Lambda(x.clone(), Some(Box::new(t)), Box::new(b)), c.1.clone()))
                }
            }
        },
        ELTerm::TAnnot(a,b) => {
            let a = deep_concretize(gamma, &*a)?;
            let b = deep_concretize(gamma, &*b)?;
            Ok(LTerm(ELTerm::TAnnot(Box::new(a), Box::new(b)), c.1.clone()))
        },
        ELTerm::Ex(_,_) => concretize(gamma, c),
    }
}

// the return type is supposed to model a boolean value, where "false" has a bit info about the error
pub fn check(gamma: &mut Ctx, term: &LTerm, typ: &LTerm) -> InformativeBool {
    let _ = wf(gamma, typ)?;

    match (&term.0, &typ.0) {
        (ELTerm::Lambda(x,None,b), ELTerm::Lambda(_y,Some(t0),t1)) => {
            gamma.0.push((**t0).clone());
            gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
            // FIXME: bound on same level?
            let r = check(gamma, &*b, &*t1)?;
            gamma.0.pop();
            gamma.2.pop();
            Ok(r)
        },
        (ELTerm::Lambda(x,Some(t),b), ELTerm::Lambda(_y,Some(t0),t1)) => {
            let _ = lessequal(gamma, t, t0);

            gamma.0.push((**t).clone());
            gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
            // FIXME: bound on same level?
            let r = check(gamma, &*b, &*t1)?;
            gamma.0.pop();
            gamma.2.pop();
            Ok(r)
        },
        _ => {
            let inferrd = infer(gamma, term)?;

            match deep_concretize(gamma, &inferrd) {
                Ok(iinferrd) => {
                    let inferrd = iinferrd;
                    lessequal(gamma, &inferrd, typ)
                },
                Err(_) => lessequal(gamma, &inferrd, typ) // try instantiating existentials
            }
        }
    }
}

pub fn infer(gamma: &mut Ctx, term: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    match &term.0 {
        ELTerm::Kind => Err(Diagnostic::error()
            .with_code("T-INFK")
            .with_message("Kinds don't have a type")),
        ELTerm::Type(lv) => Ok(cc(ELTerm::Type(*lv + 1))),
        ELTerm::Unit => Ok(cc(ELTerm::Unit)),
        ELTerm::Ex(_, _) => Err(Diagnostic::error().with_code("FIXME?")),

        ELTerm::TAnnot(a, t) => {
            let location = term.1.clone().unwrap();
            let _ =
                check(gamma, &*t, &cc(ELTerm::Kind))
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
            check(gamma, &*a, &*t).and_then(|_| Ok((**t).clone()))
        }

        ELTerm::Var(x) => {
            match (&gamma.0).into_iter().nth(*x as usize) {
                Some(LTerm(ELTerm::Ex(y, v), l)) => {
                    Ok(LTerm(ELTerm::Ex((*y).clone(), (*v).clone()), (*l).clone()))
                }
                Some(t) => Ok(t.clone()),
                None => {
                    if term.1.is_none() {
                        let name = (&gamma.2).into_iter().nth(*x as usize).unwrap();
                        Err(Diagnostic::error()
                            .with_code("T-VAR")
                            .with_message("variable not found in context")
                            .with_notes(vec![
                                format!("{} is the expected variable.", name),
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

        ELTerm::Lambda(x, ot, bdy) => {
            match ot {
                Some(t) => {
                    let _ = wf(gamma, &*t)?;

                    gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
                    gamma.0.push(*t.clone());
                    let r = infer(gamma, &*bdy)?;
                    gamma.0.pop();
                    gamma.2.pop();
                    Ok(cc(ELTerm::Lambda(x.clone(),
                        Some(Box::new(*t.clone())),
                        Box::new(r),
                    )))
                }
                None => {
                    let ex = cex(gamma, term.1.clone().unwrap().start..(*bdy).1.clone().unwrap().start-1);

                    let r = {
                        gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
                        gamma.0.push(ex.clone());
                        let r = infer(gamma, &*bdy)?;
                        gamma.0.pop();
                        gamma.2.pop();
                        Ok(r)
                    }?;

                    Ok(cc(ELTerm::Lambda(
                        x.clone(),
                        Some(Box::new(ex)),
                        Box::new(r),
                    )))
                }
            }
        }

        ELTerm::App(a, b) => {
            let fnt = infer(gamma, &*a)?;
            let argt = infer(gamma, &*b)?;

            match &fnt.0 {
                ELTerm::Ex(_, fntes) => {
                    let ex1 = cex(gamma, (*a).1.clone().unwrap());
                    let ex2 = cex(gamma, (*a).1.clone().unwrap());

                    let ty = cc(ELTerm::Lambda(
                        noname(),
                        Some(Box::new(ex1.clone())),
                        Box::new(ex2.clone()),
                    ));
                    gamma.1.iter_mut().nth(*fntes).unwrap().push(ty.clone());
                    lessequal(gamma, &ex1, &argt)
                        .and_then(|_| Ok(ex2))
                }
                ELTerm::Lambda(_, Some(t0), t1) => {
                    // t0 -> t1
                    lessequal(gamma, &argt, &*t0)
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
