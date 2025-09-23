#![allow(non_snake_case)]

use ramsey_solver::graph::*;

use clap::Parser;
use mimalloc::MiMalloc;
use std::{collections::HashMap, hash::Hash};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    // input file path
    #[arg(short, long)]
    input: String,

}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    // Parse command line arguments
    let args = Args::parse();
    println!("Running degree counter on input file: {}", args.input);

    let graphs = read_graphs_from_file(&args.input);

    println!("Read {} graphs from {}", graphs.len(), args.input);

    let max_degree = graphs.iter().map(|g| g.vertices().into_iter().map(|v| g.degree(v)).max().unwrap()).max().unwrap();
    let min_degree = graphs.iter().map(|g| g.vertices().into_iter().map(|v| g.degree(v)).min().unwrap()).min().unwrap();

    let mut min_counts= HashMap::<usize, u32>::new();
    let mut max_counts= HashMap::<usize, u32>::new();

    for graph in graphs {
        let mut at_least_degree_count = vec![0; max_degree + 1];
        for v in graph.vertices() {
            let degree = graph.degree(v);
            (0..=degree).for_each(|d| at_least_degree_count[d] += 1)
        }
        for d in min_degree..=max_degree {
            let count = at_least_degree_count[d];
            let _ = *max_counts.entry(d).and_modify(|c| *c = (*c).max(count)).or_insert(count);
        }
    }
    println!("Maximum number of vertices with degree at least d over all graphs:");
    for d in min_degree..=max_degree {
        let count = max_counts.get(&d).unwrap_or(&0);
        println!("Degree {}: {}", d, count);
    }

    Ok(())
}


