
mod lib;

use lib::parse::parse;
use lib::typecheck::infer;
use lib::debruijn;

use rustyline::error::ReadlineError;
use colored::Colorize;
use home::home_dir;


fn repl() {
    let mut rl = rustyline::Editor::<()>::new();
    println!(r#"
        ,,
      ,/ .\-,     _____               ____  ___ _        ,------------,
      .-(Oo /    |_   _|             | |  \/  || |       | Welcome to |
    /_  __\        | | ___   __ _  __| | .  . || |       |  Tadpole,  |
   |  )/  /        | |/ _ \ / _` |/ _` | |\/| || |       | the ToadML |
    }} /|__/        | | (_) | (_| | (_| | |  | || |____   |    REPL    |
    '--'  '        \_/\___/ \__,_|\__,_\_|  |_/\_____/   '------------'
  =======================================================================
"#);

    let history_path_detail = home_dir().unwrap().as_path().join(".toadml_history");
    let history_path = history_path_detail.as_os_str().to_str().unwrap();
    rl.load_history(history_path).unwrap_or(());
    loop {
        let readline = rl.readline("~~o ");
        match readline {
            Ok(line) => {
                if line.is_empty() {
                    continue;
                }
                rl.add_history_entry(line.as_str());
                eval(line);
            },
            Err(ReadlineError::Interrupted) => {
                println!("Quit");
                break
            },
            Err(ReadlineError::Eof) => {
                println!("Quit");
                break
            },
            Err(err) => {
                println!("Error: {:?}", err);
                break
            }
        }
    }
    rl.save_history(history_path).unwrap_or(());
}

fn eval(text : String) {
    let parsed = parse(text).unwrap();

    let mut ctx = vec![];
    let t = infer(&mut ctx, &parsed);

    match t {
        Err(msg) => {
            println!("Typechecking {}: {}", "failed".red().bold(), msg);
        },
        Ok(x) => {
            println!("• {} {} {} {}", "⊢".bold(), format!("{}", parsed).bright_black(), ":".bold(), x);
        }
    }
    let lterm = debruijn::from_preterm(&parsed);
    println!("DeBruijn: {}", lterm)
}


fn main() {
    repl();
}
