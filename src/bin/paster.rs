#![allow(non_snake_case)]

use ramsey_solver::graph::*;
use ramsey_solver::pasting::*;

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

    // outdirectory for output files
    #[arg(short, long, default_value_t = String::from("."))]
    outdir: String,
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    // Parse command line arguments
    let args = Args::parse();
    println!("Running pasting on input file: {}, pasted graphs will be written to {}", args.input, args.outdir);
    run_pasting(&args.input, &args.outdir)?;
    Ok(())
}


