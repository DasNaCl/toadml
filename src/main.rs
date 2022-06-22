
mod lib;

use lib::parse::{parse, Preterm};
use lib::typecheck::infer;

fn main() {
    let parsed = parse("λf : (() -> ()) -> (). f (λ _ : (). ())".to_string()).unwrap();
    println!("{}", parsed);

    let mut ctx = vec![];
    let t = infer(&mut ctx, parsed);

    match t {
        None => println!("Typechecking failed."),
        Some(x) => println!("{}", x),
    }
}
