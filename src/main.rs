
mod lib;

use lib::parse::parse;
use lib::typecheck::{infer, deep_concretize};
use lib::{debruijn, nbe};

use rustyline::error::ReadlineError;
use typed_arena::Arena;
use colored::Colorize;
use home::home_dir;

use codespan_reporting::files::SimpleFile;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

struct REPL {
    editor : rustyline::Editor::<()>,
    writer : StandardStream,
    config : codespan_reporting::term::Config,
}

fn mk_repl() -> REPL {
    REPL {
        editor : rustyline::Editor::<()>::new(),
        writer : StandardStream::stderr(ColorChoice::Always),
        config : codespan_reporting::term::Config::default(),
    }
}

impl REPL {
    fn run(&mut self) {
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
        self.editor.load_history(history_path).unwrap_or(());
        loop {
            let readline = self.editor.readline("~~o ");
            match readline {
                Ok(line) => {
                    if line.is_empty() {
                        continue;
                    }
                    self.editor.add_history_entry(line.as_str());
                    self.eval(line);
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
        self.editor.save_history(history_path).unwrap_or(());
    }

    fn eval(&mut self, text : String) {
        let file = SimpleFile::new("<repl>", text.clone());

        match parse(text) {
            Ok(parsed) => {
                let mut ctx = lib::typecheck::Ctx(vec![], Arena::new(), vec![]);
                match debruijn::from_preterm(&parsed) {
                    Ok(lterm) => {
                        let lterm = debruijn::to_level(lterm);
                        println!("DeBruijn: {}", lterm);
                        match infer(&mut ctx, &lterm).and_then(|v| deep_concretize(&mut ctx, &v)) {
                            Ok(x) => {
                                println!("• {} {} {} {}", "⊢".bold(), format!("{}", parsed).bright_black(), ":".bold(), x);

                                //let norm = nbe::normalize(lterm.clone(), debruijn::from_preterm(&x));
                                //println!("NF: {}", norm);
                            },
                            Err(msg) => term::emit(&mut self.writer.lock(), &self.config, &file, &msg).unwrap(),
                        }
                    },
                    Err(msg) => term::emit(&mut self.writer.lock(), &self.config, &file, &msg).unwrap(),
                }
            },
            Err(msg) => term::emit(&mut self.writer.lock(), &self.config, &file, &msg).unwrap(),
        }
    }

}

fn main() {
    let mut repl = mk_repl();
    repl.run();
}
