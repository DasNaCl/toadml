
mod lib;

use lib::parse::parse;
use lib::typecheck::infer;
use lib::names::fv;

fn main() {
    let parsed = parse("λA : Type. λx : A. x".to_string()).unwrap();
    println!("{}", parsed);

    let mut ctx = vec![];
    let t = infer(&mut ctx, &parsed);

    match t {
        Err(msg) => println!("Typechecking failed: {}", msg),
        Ok(x) => {
            println!("{}", x);
        }
    }
}
