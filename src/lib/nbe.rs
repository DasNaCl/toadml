
use crate::lib::{debruijn, typecheck};
use crate::lib::debruijn::{LTerm, ELTerm};

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
                _ => panic!("should have been a lambda")
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
            LTerm(ELTerm::Lambda(bi, Some(Box::new(reify(lv, *src))),
                                 Box::new(reify(lv + 1, nf))),
                  matching.pos)
        },

        (_, Some(ENbEDomain::Unit)) => LTerm(ELTerm::Unit, term.pos),

        (ENbEDomain::True, Some(ENbEDomain::Bool)) => LTerm(ELTerm::True, term.pos),
        (ENbEDomain::False, Some(ENbEDomain::Bool)) => LTerm(ELTerm::False, term.pos),
        (ENbEDomain::Quote(s,_), Some(ENbEDomain::Bool)) => reify_neutral(lv, s, term.pos),

        (ENbEDomain::Kind, Some(ENbEDomain::Kind)) => LTerm(ELTerm::Kind, term.pos),
        (ENbEDomain::Type(i), Some(ENbEDomain::Type(j))) => {
            if i+1 == j {
                LTerm(ELTerm::Type(i), term.pos)
            }
            else {
                panic!()
            }
        },
        (ENbEDomain::Type(i), Some(ENbEDomain::Kind)) => LTerm(ELTerm::Type(i), term.pos),
        (ENbEDomain::Unit, Some(ENbEDomain::Type(_))) => LTerm(ELTerm::Unit, term.pos),
        (ENbEDomain::Bool, Some(ENbEDomain::Type(_))) => LTerm(ELTerm::Bool, term.pos),

        (ENbEDomain::Ex(s,u), _) => LTerm(ELTerm::Ex(s,u), None),
        (ENbEDomain::Quote(s,_a), _) => reify_neutral(lv, s, term.pos),

        (_,_) => panic!("{:?} : {:?}", matching.tm, matching.ty)
    }
}
fn reify_neutral(lv : i32, term : Stuck, pos : Option<logos::Span>) -> LTerm {
    match term {
        Stuck::Var(i) => LTerm(ELTerm::Var(i), pos),
        Stuck::App(s,b) => LTerm(ELTerm::App(Box::new(reify_neutral(lv, *s, None)),
                                             Box::new(reify(lv, *b))), pos),
        Stuck::If(s,a,b) => LTerm(ELTerm::If(Box::new(reify_neutral(lv, *s, None)),
                                             Box::new(reify(lv, *a)),
                                             Box::new(reify(lv, *b))), pos),
        Stuck::Let(bi,s,b) => {
            todo!("whatever")
        }
    }
}

fn eval(term : LTerm, env : &Env) -> NbEDomain {
    match term.0 {
        ELTerm::Unit => mk_nbet(ENbEDomain::Unit, ENbEDomain::Unit, term.1),
        ELTerm::True => mk_nbet(ENbEDomain::True, ENbEDomain::Bool, term.1),
        ELTerm::False => mk_nbet(ENbEDomain::False, ENbEDomain::Bool, term.1),

        ELTerm::Bool => mk_nbet(ENbEDomain::Bool, ENbEDomain::Type(0), term.1),
        ELTerm::Type(u) => mk_nbet(ENbEDomain::Type(u), ENbEDomain::Type(u+1), term.1),
        ELTerm::Kind => mk_nbet(ENbEDomain::Kind, ENbEDomain::Kind, term.1),

        ELTerm::TAnnot(a,b) => {
            let a = eval(*a, env);
            let b = eval(*b, env);
            mk_nbet(a.tm, b.tm, term.1)
        }

        ELTerm::Var(i) => {
            let lookdup = (&env).iter().nth(i as usize).unwrap().clone();
            lookdup
        },
        ELTerm::Ex(s,u) => mk_nbeu(ENbEDomain::Ex(s,u), term.1),

        ELTerm::If(c, a, b) => {
            let c = eval(*c, env);
            do_if(c, *a, *b, env, term.1)
        },

        ELTerm::Lambda(bi, Some(t), b) => {
            let t = eval(*t, env);
            let cls = do_lam(bi, t, *b, env, term.1);
            match cls.ty {
                None => cls,
                Some(t) => mk_nbet(cls.tm, t, cls.pos),
            }
        },
        ELTerm::Lambda(_, None, _) => panic!("lams must not be free of annotation!"),

        ELTerm::App(a, b) => {
            let a = eval(*a, env);
            let b = eval(*b, env);
            do_app(a, b, term.1)
        }

        ELTerm::Let(bi, ot, a, b) => {
            let ot = ot.map(|t| eval(*t, env));
            let a = eval(*a, env);
            let a = match ot {
                None => a,
                Some(t) => mk_nbet(a.tm, t.tm, a.pos),
            };
            do_let(bi, a, *b, term.1, env)
        }
    }
}
fn mk_env(envv : &typecheck::Ctx) -> Env {
    let mut env = vec![];
    for lterm in envv.3.iter() {
        let lterm : LTerm = lterm.clone();

        env.push(eval(lterm, &env));
    }
    env
}

pub fn normalize(term : LTerm, tenv : &mut typecheck::Ctx) -> LTerm {
    let ts = term.to_string(&mut tenv.2);
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
        _ => debruijn::map(|e| LTerm(subst(var, forr, e.0), None), LTerm(inn, None)).0
    }
}
