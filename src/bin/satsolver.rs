#![allow(non_snake_case)]

use ramsey_solver::graph::*;
use ramsey_solver::sat::*;

use clap::Parser;
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    // input file path
    #[arg(short, long)]
    input: String,

    // number of vertices to add in vertex extension, x
    #[arg(short, long, default_value_t = 0)]
    x: usize,

    // outdirectory for output files
    #[arg(short, long, default_value_t = String::from("."))]
    outdir: String,
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    // Parse command line arguments
    let args = Args::parse();
    println!("Running SAT solver on input file: {}", args.input);
    run_satsolver(args.x, &args.input)?;

    Ok(())
}


