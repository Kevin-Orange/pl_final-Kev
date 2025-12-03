mod cli;
mod lexer;
mod parser;
mod pratt_parser;
mod semantic;
mod token;
mod mtree;

use clap::Parser;

fn main() {
    // Parse CLI arguments
    let args: cli::Cli = cli::Cli::parse();
    
    // Handle CLI and get the semantic tree
    let tree = cli::handle(args);
    
    // Create a new symbol table
    let mut sym_table = semantic::SymbolTable::new();
    
    // Run semantic analysis
    match semantic::analyze(&tree, &mut sym_table) {
        Ok(_) => println!("\n✓ Semantic analysis completed successfully!"),
        Err(errors) => {
            println!("\n✗ Semantic analysis failed with {} error(s):", errors.len());
            for (i, error) in errors.iter().enumerate() {
                println!("  {}. {}", i + 1, error);
            }
        }
    }
}






