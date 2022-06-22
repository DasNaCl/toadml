
mod lib;

use lib::parse::parse;
use lib::typecheck::infer;

fn main() {
    let parsed = parse("λT : Type 1. λA : T. λx : A. x".to_string()).unwrap();

    let mut ctx = vec![];
    let t = infer(&mut ctx, &parsed);

    match t {
        Err(msg) => {
            println!("{}", parsed);
            println!("Typechecking failed: {}", msg);
        },
        Ok(x) => {
            println!("({}) : {}", parsed, x);
        }
    }
}
