use std::fmt;
use std::sync::Mutex;

use crate::lib::debruijn::{LTerm, ELTerm, noname, mk_ltermt, mk_ltermu};
use crate::lib::{nbe, debruijn};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use lazy_static::lazy_static;
use typed_arena::Arena;

fn cc(p: ELTerm) -> LTerm {
    mk_ltermu(p, None)
}
fn cex(ctx : &mut Ctx, loc : logos::Span) -> LTerm {
    lazy_static! {
        static ref COUNTER: Mutex<Box<u32>> = Mutex::new(Box::new(0));
    }
    let c = **COUNTER.lock().unwrap();
    **COUNTER.lock().unwrap() = c + 1;

    ctx.1.alloc(vec![]);
    mk_ltermu(ELTerm::Ex(format!("α{}", c), ctx.1.len()-1), Some(loc))
}
// index into ctx is variable idx/name
pub struct Ctx(pub Vec<LTerm>, pub Arena<Vec<LTerm>>, pub Vec<String>, pub Vec<LTerm>, pub bool);
            // types           // unification vars    // names         // defs      // print infer/check

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

fn lub(typa: LTerm, typb: LTerm) -> Result<LTerm, Diagnostic<()>> {
    let (a,b) = (typa.tm.clone(), typb.tm.clone());
    match (a,b) {
        (ELTerm::Kind, ELTerm::Type(_)) => Ok(typa),
        (ELTerm::Type(_), ELTerm::Kind) => Ok(typb),
        (ELTerm::Type(i), ELTerm::Type(j)) => {
            if i < j {
                Ok(typb)
            }
            else {
                Ok(typa)
            }
        },
        (ELTerm::Unit, ELTerm::Bool) => Ok(cc(ELTerm::Type(0))),
        (ELTerm::Unit, ELTerm::Type(_)) => Ok(typb),
        (ELTerm::Type(_), ELTerm::Unit) => Ok(typa),
        _ => Err(Diagnostic::error()
                 .with_code("T-NLUB")
                 .with_message("no least upper bound"))
    }
}

fn lessequal(gamma: &mut Ctx, typa: &LTerm, typb: &LTerm) -> InformativeBool {
    match (&typa.tm, &typb.tm) {
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
                        .with_labels(vec![Label::primary((), typa.pos.clone().unwrap()).with_message(format!("May need annotation.")),
                                          Label::primary((), typb.pos.clone().unwrap()).with_message(format!("May need annotation."))]))
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
        (ELTerm::Unit, ELTerm::Unit) => Ok(()),
        (ELTerm::Unit, ELTerm::Type(_)) => Ok(()),
        (ELTerm::Unit, ELTerm::Kind) => Ok(()),
        (ELTerm::True, ELTerm::True) => Ok(()),
        (ELTerm::False, ELTerm::False) => Ok(()),
        (ELTerm::Bool, ELTerm::Bool) => Ok(()),
        (ELTerm::If(_a0,b0,c0), ELTerm::If(_a1,b1,c1)) => {
            //lessequal(gamma, &*a0, &*a1)
                lessequal(gamma, &*b0, &*b1)
                .and(lessequal(gamma, &*c0, &*c1))
        },
        (ELTerm::Kind, ELTerm::Kind) => Ok(()),
        (ELTerm::Kind, _) => Err(Diagnostic::error().with_code("T-KIND").with_message("kind expected to be less than something else which is not a kind")),
        (ELTerm::Type(_), ELTerm::Kind) => Ok(()),
        (ELTerm::Lambda(x,Some(a), b), ELTerm::Kind) => {
            let r = lessequal(gamma, &*a, &cc(ELTerm::Kind));

            gamma.0.push((**a).clone());
            gamma.2.push(if let Some(x) = x.0.clone() { x } else { format!("_") });
            gamma.3.push(cc(ELTerm::Var((gamma.0.len() - 1) as i32)));
            let r = r.and(lessequal(gamma, &*b, &cc(ELTerm::Kind)));
            gamma.3.pop();
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
            gamma.3.push(cc(ELTerm::Var((gamma.0.len() - 1) as i32)));
            let rb = ra.and(lessequal(gamma, &*b0, &*b1));
            gamma.3.pop();
            gamma.2.pop();
            gamma.0.pop();
            rb
        },
        (ELTerm::App(a0,b0), ELTerm::App(a1,b1)) => lessequal(gamma, &a0, &a1)
                                                        .and(lessequal(gamma, &b0, &b1)),
        (ELTerm::Var(x), ELTerm::Var(y)) => {
            match ((&gamma.0).into_iter().nth(*x as usize), (&gamma.0).into_iter().nth(*y as usize)) {
                (Some(a), Some(b)) => if a == b { Ok(()) } else {
                    let sx = typa.to_string(&mut gamma.2);
                    let sy = typb.to_string(&mut gamma.2);
                    if typa.pos.is_none() || typb.pos.is_none() {
                        Err(Diagnostic::error()
                            .with_code("T-COMP")
                            .with_message("types are incompatible")
                            .with_notes(vec![format!("{} and {} are not the same.", sx, sy)])
                        )
                    }
                    else {
                        Err(Diagnostic::error()
                            .with_code("T-COMP")
                            .with_message("types are incompatible")
                            .with_labels(vec![
                                Label::primary((), typa.pos.clone().unwrap()),
                                Label::primary((), typb.pos.clone().unwrap())
                            ])
                            .with_notes(vec![
                                    format!("{} and {} are not the same.", sx, sy)
                                ]))
                    }
                },
                (_, _) => Err(Diagnostic::error()),
            }
        },
        (t0, t1) => {
            if t0 == t1 {
                Ok(())
            } else {
                if typa.pos.is_none() || typb.pos.is_none() {
                    return Err(Diagnostic::error()
                        .with_code("T-COMP")
                        .with_message("types are incompatible")
                        .with_notes(vec![format!(
                            "The types \"{}\" and \"{}\" are expected to be equal!",
                            typa.to_string(&mut gamma.2), typb.to_string(&mut gamma.2)
                        )]));
                } else {
                    return Err(Diagnostic::error()
                        .with_code("T-COMP")
                        .with_message("types are incompatible")
                        .with_labels(vec![
                            Label::primary((), typa.pos.clone().unwrap()),
                            Label::primary((), typb.pos.clone().unwrap())
                        ])
                        .with_notes(vec![format!("They are expected to be equal")]));
                }
            }
        }
    }
}

fn concretize(gamma: &mut Ctx, c: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    match &c.tm {
        ELTerm::Ex(_, esidx) => {
            let eslen = gamma.1.iter_mut().nth(*esidx).unwrap().len();
            if eslen == 0 {
                Err(Diagnostic::error()
                    .with_code("T-EX")
                    .with_message("type annotation needed")
                    .with_labels(vec![Label::primary((), c.pos.clone().unwrap()).with_message(format!("This is the unknown."))]))
            } else if eslen == 1 {
                let t = gamma.1.iter_mut().nth(*esidx).unwrap().first().unwrap().clone();
                deep_concretize(gamma, &t)
            } else {
                let t = gamma.1.iter_mut().nth(*esidx).unwrap().first().unwrap().clone();
                let t = deep_concretize(gamma, &t)?;
                let nt = nbe::normalize(t, gamma);

                for mx in gamma.1.iter_mut().nth(*esidx).unwrap().iter().next().cloned() {
                    let nmx = nbe::normalize(mx, gamma);
                    if let Err(e) = lessequal(gamma, &nt, &nmx) {
                        return Err(e);
                    }
                }
                Ok(nt)
            }
        }
        t => deep_concretize(gamma, &cc((*t).clone())),
    }
}
pub fn deep_concretize(gamma: &mut Ctx, c: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    match &c.tm {
        ELTerm::Type(_) | ELTerm::Var(_) | ELTerm::Unit | ELTerm::Kind |
        ELTerm::True | ELTerm::False | ELTerm::Bool => Ok(c.clone()),
        ELTerm::If(a,b,c) => {
            let a = deep_concretize(gamma, &*a)?;
            let b = deep_concretize(gamma, &*b)?;
            let cc = deep_concretize(gamma, &*c)?;
            Ok(mk_ltermu(ELTerm::If(Box::new(a), Box::new(b), Box::new(cc)), c.pos.clone()))
        },
        ELTerm::App(a,b) => {
            let a = deep_concretize(gamma, &*a)?;
            let b = deep_concretize(gamma, &*b)?;
            Ok(mk_ltermu(ELTerm::App(Box::new(a), Box::new(b)), c.pos.clone()))
        },
        ELTerm::Lambda(x,ot,b) => {
            let b = deep_concretize(gamma, &*b)?;
            match ot {
                None => Ok(mk_ltermu(ELTerm::Lambda(x.clone(), None, Box::new(b)), c.pos.clone())),
                Some(t) => {
                    let t = deep_concretize(gamma, &*t)?;
                    Ok(mk_ltermu(ELTerm::Lambda(x.clone(), Some(Box::new(t)), Box::new(b)), c.pos.clone()))
                }
            }
        },
        ELTerm::Let(x,a,b,d) => {
            let b = deep_concretize(gamma, &*b)?;
            let d = deep_concretize(gamma, &*d)?;
            match a {
                None => Ok(mk_ltermu(ELTerm::Let(x.clone(), None, Box::new(b), Box::new(d)), c.pos.clone())),
                Some(t) => {
                    let t = deep_concretize(gamma, &*t)?;
                    Ok(mk_ltermu(ELTerm::Let(x.clone(), Some(Box::new(t)), Box::new(b), Box::new(d)), c.pos.clone()))
                }
            }
        },
        ELTerm::Ex(_,_) => concretize(gamma, c),
    }
}

fn wf(gamma: &mut Ctx, term: &LTerm) -> InformativeBool {
    let typ = infer(gamma, &cc(term.tm.clone()))?;
    if typ.tm == ELTerm::Kind {
        return Ok(());
    }
    if let ELTerm::Type(_) = typ.tm {
        return Ok(());
    }
    check(gamma, &mk_ltermt(typ.tm.clone(), cc(ELTerm::Kind), typ.pos.clone()))
        .and_then(|_| Ok(()))
}

// Returns the type-annotated term if check was successful
pub fn check(gamma: &mut Ctx, term: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    if gamma.4 {
        let ts = cc(term.tm.clone()).to_string(&mut gamma.2);
        let typs = (*term.ty.clone().unwrap()).to_string(&mut gamma.2);
        println!("{} |- {} <=== {}", gamma, ts, typs);
    }
    check2(gamma, term)
}
pub fn check2(gamma: &mut Ctx, term: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    let typ = *term.ty.clone().unwrap();
    let _ = wf(gamma, &typ)?;

    match (&term.tm, &typ.tm) {
        (ELTerm::Lambda(x,None,b), ELTerm::Lambda(_y,Some(t0),t1)) => {
            gamma.0.push((**t0).clone());
            gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
            gamma.3.push(cc(ELTerm::Var((gamma.0.len() - 1) as i32)));
            // FIXME: bound on same level?
            let r = check(gamma, &mk_ltermt((*b).tm.clone(), (**t1).clone(), (*b).pos.clone()))?;
            gamma.3.pop();
            gamma.2.pop();
            gamma.0.pop();
            Ok(r)
        },
        (ELTerm::Lambda(x,Some(t),b), ELTerm::Lambda(_y,Some(t0),t1)) => {
            let nt = nbe::normalize(*t.clone(), gamma);
            let nt0 = nbe::normalize(*t0.clone(), gamma);
            let _ = lessequal(gamma, &nt, &nt0);

            gamma.0.push((**t).clone());
            gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
            gamma.3.push(cc(ELTerm::Var((gamma.0.len() - 1) as i32)));
            // FIXME: bound on same level?
            let r = check(gamma, &mk_ltermt((*b).tm.clone(), (**t1).clone(), (*b).pos.clone()))?;
            gamma.3.pop();
            gamma.2.pop();
            gamma.0.pop();
            Ok(r)
        },
        (ELTerm::If(a, b, c), _) => {
            let at = infer(gamma, &(*a))?;
            let nat = nbe::normalize(at, gamma);

            lessequal(gamma, &nat, &(cc(ELTerm::Bool)))?;
            match (*a).tm {
                ELTerm::Var(x) => {
                    let typb = mk_ltermu(nbe::subst(x, &ELTerm::True, typ.tm.clone()), typ.pos.clone());
                    let typc = mk_ltermu(nbe::subst(x, &ELTerm::False, typ.tm.clone()), typ.pos.clone());
                    let ntypb = nbe::normalize(typb.clone(), gamma);
                    let ntypc = nbe::normalize(typc.clone(), gamma);
                    let _ = check(gamma, &mk_ltermt((*b).tm.clone(), ntypb.clone(), (*b).pos.clone()))?;
                    let _ = check(gamma, &mk_ltermt((*c).tm.clone(), ntypc.clone(), (*c).pos.clone()))?;
                    //Ok(mk_ltermt(ELTerm::If((*a).clone(), (*b).clone(), (*c).clone()), lub(ntypb, ntypc)?, term.pos.clone()))
                    lub(ntypb, ntypc)
                },
                _ => {
                    let _ = check(gamma, &mk_ltermt((*b).tm.clone(), typ.clone(), (*b).pos.clone()))?;
                    let _ = check(gamma, &mk_ltermt((*c).tm.clone(), typ.clone(), (*c).pos.clone()))?;
                    Ok(mk_ltermt(ELTerm::If((*a).clone(), (*b).clone(), (*c).clone()), typ, term.pos.clone()))
                }
            }
        }
        _ => {
            let inferrd = infer(gamma, &cc(term.tm.clone()))?;

            match deep_concretize(gamma, &inferrd) {
                Ok(iinferrd) => {
                    let inferrd = iinferrd;
                    let ninferrd = nbe::normalize(inferrd, gamma);
                    let ntyp = nbe::normalize(typ.clone(), gamma);
                    lessequal(gamma, &ninferrd, &ntyp)
                        .and_then(|_| Ok(mk_ltermt(term.tm.clone(), ntyp, term.pos.clone())))
                },
                Err(_) => {
                    let ninferrd = nbe::normalize(inferrd, gamma);
                    let ntyp = nbe::normalize(typ.clone(), gamma);
                    lessequal(gamma, &ninferrd, &ntyp)
                        .and_then(|_| Ok(mk_ltermt(term.tm.clone(), ntyp, term.pos.clone())))
                }
            }
        }
    }
}

fn shift(at : i32, gammalen : usize, term : LTerm) -> LTerm {
    let offset = gammalen as i32 - at;
    match &(term.tm) {
        ELTerm::Var(x) => {
            if *x < at {
                term
            }
            else {
                if term.ty.is_none() {
                    mk_ltermu(ELTerm::Var(*x + offset), term.pos)
                }
                else {
                    mk_ltermt(ELTerm::Var(*x + offset), *term.ty.unwrap(), term.pos)
                }
            }
        }
        _ => debruijn::map(|e| shift(at, gammalen, e), term),
    }
}

// FIXME: we need to return the actual term and simply annotate it with the type.
//        however, this changes all call-sites of infer and we need to take care to look at inferrd.ty instead of inferrd.tm
pub fn infer(gamma: &mut Ctx, term: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    if gamma.4 {
        let ts = term.clone().to_string(&mut gamma.2);
        println!("{} |- {} ===> ??", gamma, ts);
        let r = infer2(gamma, term)?;
        let rs = r.clone().to_string(&mut gamma.2);
        println!("{} |- {} ===> {}", gamma, ts, rs);
        Ok(r)
    }
    else {
        infer2(gamma, term)
    }
}
pub fn infer2(gamma: &mut Ctx, term: &LTerm) -> Result<LTerm, Diagnostic<()>> {
    if let Some(t) = term.ty.clone() {
        let location = term.ty.clone().unwrap().pos;
        let _ =
            check(gamma, &mk_ltermt((*t).tm.clone(), cc(ELTerm::Kind), (*t).pos.clone()))
                .and_then(|_| Ok(()))
                .map_err(|e| {
                    if let Some(location) = location {
                        e
                        .with_labels(
                            vec![
                                Label::primary((), location) // an annotation must be present in the source file...!
                                    .with_message(format!(
                                        "This is the annotation in question."
                                    )),
                            ],
                        )
                    }
                    else {
                        e
                    }
                        .with_notes(vec![format!("Ill-formed type annotation.")])
                })?;
        let ts = (*t).to_string(&mut gamma.2);
        let x = check(gamma, &mk_ltermt(term.tm.clone(), (*t).clone(), term.pos.clone()))?;
        return Ok(*t);
    }
    match &term.tm {
        ELTerm::Kind => Ok(cc(ELTerm::Kind)),
        ELTerm::Type(lv) => Ok(cc(ELTerm::Type(*lv + 1))),
        ELTerm::Unit => Ok(cc(ELTerm::Unit)),
        ELTerm::Ex(_, _) => Err(Diagnostic::error().with_code("FIXME?")),
        ELTerm::Bool => Ok(cc(ELTerm::Type(1))),
        ELTerm::True | ELTerm::False => Ok(cc(ELTerm::Bool)),
        ELTerm::If(a,b,c) => {
            let a = infer(gamma, &(*a))?;
            let na = nbe::normalize(a, gamma);
            lessequal(gamma, &na, &(cc(ELTerm::Bool)))?;

            let b = infer(gamma, &(*b))?;
            let c = infer(gamma, &(*c))?;
            let nb = nbe::normalize(b.clone(), gamma);
            let nc = nbe::normalize(c.clone(), gamma);
            lessequal(gamma, &nb, &nc)?;
            lub(nb, nc)
        }

        ELTerm::Var(x) => {
            match (&gamma.0).into_iter().nth(*x as usize) {
                Some(LTerm { tm: ELTerm::Ex(y, v), ty: _, pos: l}) => {
                    Ok(mk_ltermu(ELTerm::Ex((*y).clone(), (*v).clone()), (*l).clone()))
                }
                Some(t) => Ok(shift(*x, gamma.0.len(), t.clone())),
                None => {
                    if term.pos.is_none() {
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
                            .with_labels(vec![Label::primary((), term.pos.clone().unwrap())
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
                    gamma.3.push(cc(ELTerm::Var((gamma.0.len() - 1) as i32)));
                    let r = infer(gamma, &*bdy)?;
                    gamma.0.pop();
                    gamma.2.pop();
                    gamma.3.pop();
                    Ok(cc(ELTerm::Lambda(x.clone(),
                        Some(Box::new(*t.clone())),
                        Box::new(r),
                    )))
                }
                None => {
                    let ex = cex(gamma, term.pos.clone().unwrap().start..(*bdy).pos.clone().unwrap().start-1);

                    let r = {
                        gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
                        gamma.0.push(ex.clone());
                        gamma.3.push(cc(ELTerm::Var((gamma.0.len() - 1) as i32)));
                        let r = infer(gamma, &*bdy)?;
                        gamma.3.pop();
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

        ELTerm::Let(x, ot, def, bdy) => {
            match ot {
                Some(t) => {
                    let _ = wf(gamma, &*t)?;

                    let _ = check(gamma, &mk_ltermt((*def).tm.clone(), (**t).clone(), (*def).pos.clone()))?;
                    gamma.3.push((**def).clone());
                    gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
                    gamma.0.push(*t.clone());
                    let r = infer(gamma, &*bdy)?;
                    gamma.0.pop();
                    gamma.2.pop();
                    gamma.3.pop();
                    Ok(r)
                },
                None => {
                    let t = infer(gamma, &*def)?;

                    gamma.3.push((**def).clone());
                    gamma.2.push(if let Some(x0) = x.0.clone() { x0 } else { format!("_") });
                    gamma.0.push(t);
                    let r = infer(gamma, &*bdy)?;
                    gamma.0.pop();
                    gamma.2.pop();
                    gamma.3.pop();
                    Ok(r)
                }
            }
        }

        ELTerm::App(a, b) => {
            let fnt = infer(gamma, &*a)?;
            let argt = infer(gamma, &*b)?;

            match &fnt.tm {
                ELTerm::Ex(_, fntes) => {
                    let ex1 = cex(gamma, (*a).pos.clone().unwrap());
                    let ex2 = cex(gamma, (*a).pos.clone().unwrap());

                    let ty = cc(ELTerm::Lambda(
                        noname(),
                        Some(Box::new(ex1.clone())),
                        Box::new(ex2.clone()),
                    ));
                    gamma.1.iter_mut().nth(*fntes).unwrap().push(ty.clone());
                    let nargt = nbe::normalize(argt, gamma);
                    lessequal(gamma, &ex1, &nargt)
                        .and_then(|_| Ok(ex2))
                }
                ELTerm::Lambda(_, Some(t0), _t1) => {
                    // t0 -> t1
                    let nargt = nbe::normalize(argt.clone(), gamma);
                    let nt0 = nbe::normalize(*t0.clone(), gamma);
                    lessequal(gamma, &nargt, &nt0)
                        .and_then(|_| Ok(nbe::normalize(mk_ltermu(ELTerm::App(Box::new(fnt.clone()),
                                                                              Box::new((**b).clone())), None), gamma)))
                        .map_err(|msg| {
                            if (*a).pos.is_none() || (*b).pos.is_none() {
                                msg
                            } else {
                                msg.with_labels(vec![
                                    Label::primary(
                                        (),
                                        (*a).pos.clone().unwrap().start..(*b).pos.clone().unwrap().end,
                                    )
                                    .with_message(format!(
                                        "Function does not accept the type of this argument."
                                    )),
                                    Label::secondary((), (*a).pos.clone().unwrap().clone())
                                        .with_message(format!("Parameter type is {}", t0)),
                                    Label::secondary((), (*b).pos.clone().unwrap().clone())
                                        .with_message(format!("Argument type is {}", argt.clone())),
                                ])
                            }
                            .with_notes(vec![format!(
                                "Parameter and argument type need to be compatible."
                            )])
                        })
                }
                _ => {
                    if (*a).pos.is_none() {
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
                            .with_labels(vec![Label::primary((), (*a).pos.clone().unwrap())
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
