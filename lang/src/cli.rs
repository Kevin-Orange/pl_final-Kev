use clap::{Parser, Subcommand};
use std::fs;

use crate::lexer::Lexer;
use crate::parser::Parser as LangParser;

// parser returns mtree::MTree, NOT semantic::MTree
use crate::mtree::MTree as ParseTree;

// semantic analysis outputs semantic::MTree
use crate::semantic::{MTree as SemanticTree, from_parse_tree};

#[derive(Parser)]
#[command(name = "lang", version)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Clone, Subcommand)]
pub enum Command {
    Print {
        filepath: String,
        #[arg(short, long)]
        numbered: bool,
    },
    Tokenize {
        filepath: String,
    },
    Parse {
        filepath: String,
    },
}

pub fn handle(cli: Cli) -> SemanticTree {
    match cli.command {
        Command::Print { filepath, numbered } => {
            print_file(filepath, numbered);

            // return empty semantic tree 
            SemanticTree::START { funcs: vec![] }
        }

        Command::Tokenize { filepath } => {
            tokenize(filepath);

            // return empty semantic tree
            SemanticTree::START { funcs: vec![] }
        }

        Command::Parse { filepath } => {
            parse_and_convert(filepath)
        }
    }
}

fn print_file(path: String, numbered: bool) {
    let contents = fs::read_to_string(path).unwrap();
    if numbered {
        let width = contents.lines().count().to_string().len();
        for (i, line) in contents.lines().enumerate() {
            println!("{:>width$} | {}", i + 1, line, width = width);
        }
    } else {
        println!("{}", contents);
    }
}

fn tokenize(path: String) {
    let contents = fs::read_to_string(path).unwrap();
    let mut lexer = Lexer::new(contents);
    lexer.print_tokens();
}

fn parse_and_convert(path: String) -> SemanticTree {
    let contents = fs::read_to_string(path).unwrap();

    // correct: parser produces mtree::MTree
    let lexer = Lexer::new(contents);
    let mut parser = LangParser::new(lexer);

    let parse_tree: ParseTree = parser.analyze();

    println!("\n=== Parse Tree ===");
    parse_tree.print();

    // Convert parse tree to semantic tree
    match from_parse_tree(&parse_tree) {
        Ok(ast) => {
            println!("\n=== Semantic AST ===\n{:#?}", ast);
            ast
        }
        Err(e) => {
            panic!("Semantic conversion failed: {}", e);
        }
    }
}






