#![allow(non_snake_case)]

mod graph;
mod sat;
mod pasting;
use crate::graph::*;
use crate::sat::*;
use crate::pasting::*;

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

    // do pasting instead of gluing/vertex extension
    #[arg(short, long, default_value_t = false)]
    pasting: bool,

    // outdirectory for output files
    #[arg(short, long, default_value_t = String::from("."))]
    outdir: String,
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    // Parse command line arguments
    let args = Args::parse();
    if args.pasting {
        println!("Running pasting on input file: {}, pasted graphs will be written to {}", args.input, args.outdir);
        run_pasting(&args.input, &args.outdir)?;
    }
    else {
        println!("Running SAT solver on input file: {}", args.input);
        run_satsolver(args.x, &args.input)?;
    }

    Ok(())
}


