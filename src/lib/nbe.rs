
use crate::lib::{debruijn, typecheck};
use crate::lib::debruijn::{LTerm, ELTerm, mk_ltermt, mk_ltermu};

type Env = Vec<NbEDomain>;

#[derive(Clone,Debug)]
struct Closure {
    term : LTerm,
    env : Env,
}
#[derive(Clone,Debug)]
enum ENbEDomain {
    Lam(debruijn::Binder, Box<NbEDomain>, Closure),

    Unit,
    Bool,
    Type(u32),
    Kind,

    True,
    False,

    Quote(Stuck, Box<NbEDomain>),

    Ex(String, usize), // TODO: do we need to concretize, so that this doesn't appear here?
}
#[derive(Clone,Debug)]
enum Stuck { // <- these are "neutral" terms. I've found the terminology confusing, so I use "stuck"
    Var(i32),
    App(Box<Stuck>, Box<NbEDomain>),
    If(Box<Stuck>, Box<NbEDomain>, Box<NbEDomain>),
    Let(debruijn::Binder, Box<Stuck>, Closure),
}
#[derive(Clone,Debug)]
pub struct NbEDomain {
    tm : ENbEDomain,
    ty : Option<ENbEDomain>,
    pos : Option<logos::Span>,
}
fn mk_nbet(what_tm: ENbEDomain, what_ty: ENbEDomain, what_pos: Option<logos::Span>) -> NbEDomain {
    NbEDomain {
        tm : what_tm,
        ty : Some(what_ty),
        pos : what_pos
    }
}
fn mk_nbeu(what_tm: ENbEDomain, what_pos: Option<logos::Span>) -> NbEDomain {
    NbEDomain {
        tm : what_tm,
        ty : None,
        pos : what_pos
    }
}
fn mk_quot(what_tm : Stuck, what_ty : NbEDomain, what_pos: Option<logos::Span>) -> NbEDomain {
    NbEDomain {
        tm : ENbEDomain::Quote(what_tm, Box::new(what_ty)),
        ty : None,
        pos : what_pos,
    }
}

fn do_if(c : NbEDomain, a : LTerm, b : LTerm, env : &Env, pos : Option<logos::Span>) -> NbEDomain {
    match c.tm {
        ENbEDomain::True => eval(a, env),
        ENbEDomain::False => eval(b, env),
        ENbEDomain::Quote(s,t) => {
            match (*t).tm {
                ENbEDomain::Bool => {
                    // TODO: eval with s=true, s=false
                    let a = eval(a, env);
                    let b = eval(b, env);
                    mk_quot(Stuck::If(Box::new(s),
                                      Box::new(a.clone()), Box::new(b)),
                            a, pos) // FIXME:!! how to get the type? !!
                },
                _ => panic!("should have been a bool"),
            }
        },
        _ => panic!("unreachable")
    }
}

fn do_lam(bi : debruijn::Binder, t : NbEDomain, b : LTerm, env : &Env, pos : Option<logos::Span>) -> NbEDomain {
    mk_nbeu(ENbEDomain::Lam(bi,
                            Box::new(t),
                            Closure {
                                term : b,
                                env : env.clone(),
                            }), pos)
}

fn do_clos(cls : Closure, a : NbEDomain) -> NbEDomain {
    let mut env : Env = cls.env;
    env.push(a);
    eval(cls.term, &env)
}

fn do_app(f : NbEDomain, a : NbEDomain, pos : Option<logos::Span>) -> NbEDomain {
    match f.tm {
        ENbEDomain::Lam(_bi, _src, cls) => do_clos(cls, a),
        ENbEDomain::Quote(s,t) => {
            match (*t).tm {
                ENbEDomain::Lam(_bi, src, cls) => {
                    let a = match a.ty {
                        None => mk_nbet(a.tm, (*src).tm, a.pos),
                        Some(t) => mk_nbet(a.tm, t, a.pos),
                    };
                    let dst = do_clos(cls, a.clone());
                    mk_quot(Stuck::App(Box::new(s),
                                       Box::new(a)),
                            dst, pos)
                },
                _ => panic!("should have been a lambda, but is {:?}", (*t).tm)
            }
        }
        _ => panic!("unreachable")
    }
}

fn do_let(bi : debruijn::Binder, a : NbEDomain, b : LTerm, pos : Option<logos::Span>, env : &Env) -> NbEDomain {
    match a.tm {
        ENbEDomain::Quote(s,_t) => {
            mk_quot(Stuck::Let(bi,
                               Box::new(s),
                                Closure {
                                    term : b.clone(),
                                    env : env.clone(),
                                }),
                    eval(b, env), // FIXME: this should use (eval(b.ty, env))
                    pos)
        },
        _ => {
            let mut env = env.clone();
            env.push(a);
            eval(b, &env)
        }
    }
}

fn reify(lv : i32, term : NbEDomain) -> LTerm {
    let matching = term.clone();
    match (matching.tm.clone(), matching.ty.clone()) {
        (_, Some(ENbEDomain::Lam(bi,src,dst))) => {
            let arg = mk_quot(Stuck::Var(lv), (*src).clone(), None);
            let nf = mk_nbet(do_app(term, arg.clone(), None).tm,
                             do_clos(dst, arg).tm, None);
            mk_ltermu(ELTerm::Lambda(bi, Some(Box::new(reify(lv, *src))),
                                     Box::new(reify(lv + 1, nf))),
                      matching.pos)
        },

        (_, Some(ENbEDomain::Unit)) => mk_ltermt(ELTerm::Unit, mk_ltermu(ELTerm::Unit, None), term.pos),

        (ENbEDomain::True, Some(ENbEDomain::Bool)) => mk_ltermt(ELTerm::True, mk_ltermu(ELTerm::Bool, None), term.pos),
        (ENbEDomain::False, Some(ENbEDomain::Bool)) => mk_ltermt(ELTerm::False, mk_ltermu(ELTerm::Bool, None), term.pos),
        (ENbEDomain::Quote(s,_), Some(ENbEDomain::Bool)) => reify_neutral(lv, s, term.pos),

        (ENbEDomain::Kind, Some(ENbEDomain::Kind)) => mk_ltermt(ELTerm::Kind, mk_ltermu(ELTerm::Kind, None), term.pos),
        (ENbEDomain::Type(i), Some(ENbEDomain::Type(j))) => {
            if i+1 == j {
                mk_ltermt(ELTerm::Type(i), mk_ltermu(ELTerm::Type(j), None), term.pos)
            }
            else {
                panic!()
            }
        },
        (ENbEDomain::Type(i), Some(ENbEDomain::Kind)) => mk_ltermt(ELTerm::Type(i), mk_ltermu(ELTerm::Type(i+1), None), term.pos),
        (ENbEDomain::Unit, Some(ENbEDomain::Type(_))) => mk_ltermt(ELTerm::Unit, mk_ltermu(ELTerm::Type(0), None), term.pos),
        (ENbEDomain::Bool, Some(ENbEDomain::Type(_))) => mk_ltermt(ELTerm::Bool, mk_ltermu(ELTerm::Type(0), None), term.pos),

        (ENbEDomain::Ex(s,u), _) => mk_ltermu(ELTerm::Ex(s,u), None),
        (ENbEDomain::Quote(s,_a), _) => reify_neutral(lv, s, term.pos),

        (_,_) => panic!("{:?} : {:?}", matching.tm, matching.ty)
    }
}
fn reify_neutral(lv : i32, term : Stuck, pos : Option<logos::Span>) -> LTerm {
    match term {
        Stuck::Var(i) => mk_ltermu(ELTerm::Var(i), pos),
        Stuck::App(s,b) => mk_ltermu(ELTerm::App(Box::new(reify_neutral(lv, *s, None)),
                                                 Box::new(reify(lv, *b))), pos),
        Stuck::If(s,a,b) => mk_ltermu(ELTerm::If(Box::new(reify_neutral(lv, *s, None)),
                                                 Box::new(reify(lv, *a)),
                                                 Box::new(reify(lv, *b))), pos),
        Stuck::Let(_bi,_s,_b) => {
            todo!("whatever")
        }
    }
}

fn eval(term : LTerm, env : &Env) -> NbEDomain {
    if let Some(t) = term.ty {
        let a = eval(mk_ltermu(term.tm, term.pos.clone()), env);
        let b = eval(*t, env);
        return mk_nbet(a.tm, b.tm, term.pos);
    }
    match term.tm {
        ELTerm::Unit => mk_nbet(ENbEDomain::Unit, ENbEDomain::Unit, term.pos),
        ELTerm::True => mk_nbet(ENbEDomain::True, ENbEDomain::Bool, term.pos),
        ELTerm::False => mk_nbet(ENbEDomain::False, ENbEDomain::Bool, term.pos),

        ELTerm::Bool => mk_nbet(ENbEDomain::Bool, ENbEDomain::Type(0), term.pos),
        ELTerm::Type(u) => mk_nbet(ENbEDomain::Type(u), ENbEDomain::Type(u+1), term.pos),
        ELTerm::Kind => mk_nbet(ENbEDomain::Kind, ENbEDomain::Kind, term.pos),

        ELTerm::Var(i) => {
            let lookdup = (&env).iter().nth(i as usize).unwrap().clone();
            lookdup
        },
        ELTerm::Ex(s,u) => mk_nbeu(ENbEDomain::Ex(s,u), term.pos),

        ELTerm::If(c, a, b) => {
            let c = eval(*c, env);
            do_if(c, *a, *b, env, term.pos)
        },

        ELTerm::Lambda(bi, Some(t), b) => {
            let t = eval(*t, env);
            let cls = do_lam(bi, t, *b, env, term.pos);
            match cls.ty {
                None => cls,
                Some(t) => mk_nbet(cls.tm, t, cls.pos),
            }
        },
        ELTerm::Lambda(_, None, _) => panic!("lams must not be free of annotation!"),

        ELTerm::App(a, b) => {
            let a = eval(*a, env);
            let b = eval(*b, env);
            do_app(a, b, term.pos)
        }

        ELTerm::Let(bi, ot, a, b) => {
            let ot = ot.map(|t| eval(*t, env));
            let a = eval(*a, env);
            let a = match ot {
                None => a,
                Some(t) => mk_nbet(a.tm, t.tm, a.pos),
            };
            do_let(bi, a, *b, term.pos, env)
        }
    }
}
fn mk_env(envv : &typecheck::Ctx) -> Env {
    let mut env = vec![];
    for lterm in envv.3.iter() {
        let lterm : LTerm = lterm.clone();

        env.push(match lterm.tm {
            ELTerm::Var(i) => {
                let typ = (&envv.0).iter().nth(i as usize).unwrap().clone();

                let (slice, _) = env.split_at(i as usize);
                let ctx = slice.iter().cloned().collect();
                let typ = eval(typ, &ctx);
                mk_quot(Stuck::Var(i), typ, None)
            },
            _ => eval(lterm, &env),
        });
    }
    env
}

pub fn normalize(term : LTerm, tenv : &mut typecheck::Ctx) -> LTerm {
    if tenv.4 {
        println!("normlizing {}", term.to_string(&mut tenv.2));
    }
    let env = mk_env(tenv);
    let termm = eval(term, &env);
    reify(env.len() as i32, termm)
}

pub fn subst(var : i32, forr : &ELTerm, inn : ELTerm) -> ELTerm {
    match inn {
        ELTerm::Var(v) => {
            if v == var {
                forr.clone()
            }
            else {
                inn
            }
        },
        _ => debruijn::map(|e| mk_ltermu(subst(var, forr, e.tm), None), mk_ltermu(inn, None)).tm
    }
}
