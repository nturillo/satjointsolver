#![allow(non_snake_case)]

mod graph;
mod sat;
use crate::graph::*;
use crate::sat::*;

use cadical::Solver;
use clap::Parser;
use itertools::{Itertools, iproduct};
use mimalloc::MiMalloc;
use rayon::prelude::*;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::process::{Command, Stdio};
use std::collections::HashMap;

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
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    // Parse command line arguments
    let args = Args::parse();
    let mut x = args.x;
    let infile_str = args.input;

    let path = Path::new(&infile_str);
    let file = File::open(&path)?;
    let reader = io::BufReader::new(file);
    let mut lines: Vec<String> = reader.lines().collect::<Result<_, _>>()?;

    #[cfg(feature = "regular")]
    {
        println!("Running SAT graph gluer in regular mode");
    }
    #[cfg(feature = "complement")]
    {
        println!("Running SAT graph gluer in complement mode");
    }

    let num_graphs = lines.len();
    println!("Read: {} graphs from {}", num_graphs, infile_str);

    let graph0 = Graph::from_graph6(&lines[0]);
    let deg = graph0.neighbor_set(0).count_ones() as usize;
    let K_size = (graph0.neighbor_set(0) & graph0.neighbor_set(1)).count_ones() as usize;

    println!("Graph degree: {}", deg);
    println!("K size: {}", K_size);

    // Convert each line from graph6 format to a Graph object, create the SAT problem, and solve it
    let mut start = std::time::Instant::now();
    while let Some((i, glued_graph)) = get_glued_graph(&lines, x) {
        println!(
            "Found glued graph with {} vertices, including {} extension vertices",
            glued_graph.num_vertices(),
            x
        );
        println!("Time taken: {:?}", start.elapsed());
        println!(
            "Glued graph in graph6 format: {}",
            graph_to_g6(&glued_graph)
        );
        if glued_graph.num_vertices() == 31 {
            return Ok(());
        }
        // don't research on graphs already searched for lower x
        lines.drain(0..i);
        println!("Eliminated {} graphs, {} graphs remaining", i, lines.len());
        x = x + 1;
        start = std::time::Instant::now();
        println!("Continuing with x = {}", x);
    }
    println!("No glued graph found with {} extension vertices", x);
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    Ok(())
}

fn get_glued_graph(lines: &[String], x: usize) -> Option<(usize, Graph)> {
    //
    // This function takes a slice of graph6 strings and an integer x,
    // and tries to find a gluing of a graph from the input lines which
    // contains x many extension vertices. As soon as one such graph is found,
    // it returns it as a `Graph` object.
    //
    let graph0 = Graph::from_graph6(&lines[0]);
    let deg = graph0.neighbor_set(0).count_ones() as usize;
    let K_size = (graph0.neighbor_set(0) & graph0.neighbor_set(1)).count_ones() as usize;

    let sat_precursor = get_sat_precursor(deg, K_size, x);
    lines
        .par_iter()
        .enumerate()
        .by_exponential_blocks()
        .find_map_first(|(i, line)| {
            let graph = Graph::from_graph6(line);
            #[cfg(debug_assertions)]
            {
                let g_deg = graph.neighbor_set(0).count_ones() as usize;
                let g_K_size =
                    (graph.neighbor_set(0) & graph.neighbor_set(1)).count_ones() as usize;
                assert!(g_deg == deg, "Graph degree does not match expected degree");
                assert!(
                    g_K_size == K_size,
                    "Graph K size does not match expected K size"
                );
            }
            let ext_graph = graph.extend(x);
            let sat_problem = create_sat_problem(&ext_graph, &sat_precursor);
            let mut sat_solver: Solver = Default::default();
            sat_problem.clauses.iter().for_each(|clause| {
                sat_solver.add_clause(clause.clone());
            });
            sat_solver.solve().expect("Failed to solve SAT problem");
            let res = Graph::from_sat_sol(&ext_graph, &sat_problem, &sat_solver);
            if res.is_some() {
                return Some((i, res.unwrap()));
            }
            return None;
        })
}






// tests
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edge_to_var() {
        let deg = 14;
        let K_size = 7;
        let x = 0;
        let sat_precursor = get_sat_precursor(deg, K_size, x);
        println!("edge_to_var: {:?}", sat_precursor.edge_to_var);
    }
    fn clause_edge_good(edge: &Edge, deg: usize, K_size: usize) -> bool {
        // checks if the edge is really a clause edge
        // i.e. that either
        // - one of its vertices is an extension vertex (> n)
        // - one vertex is from A and the other from B
        let n = 2 * deg - K_size;
        if edge.0 >= n || edge.1 >= n {
            return true; // extension vertex
        }
        let A_size = deg - K_size - 1;
        let A = 2..(2 + A_size);
        let B = (2 + A_size)..(2 + 2 * A_size);
        (A.contains(&edge.0) && B.contains(&edge.1)) || (A.contains(&edge.1) && B.contains(&edge.0))
    }
    #[test]
    fn test_sat_precursor() {
        let deg = 14;
        let K_size = 7;
        let x = 0;
        let sat_precursor = get_sat_precursor(deg, K_size, x);
        for (check_edges, clause_edges) in &sat_precursor.edge_sets {
            assert!(
                check_edges.len() + clause_edges.len() == 10,
                "check_edges and clause_edges should sum to 10"
            );
            assert!(!clause_edges.is_empty(), "clause_edges should not be empty");
            assert!(
                check_edges
                    .iter()
                    .all(|edge| !clause_edge_good(edge, deg, K_size)),
                "check edges should not be clause edges"
            );
            assert!(
                clause_edges
                    .iter()
                    .all(|edge| clause_edge_good(edge, deg, K_size)),
                "clause edges should be valid clause edges"
            );
        }
        // println!("edge sets: {:?}", sat_precursor.edge_sets);
    }
    #[test]
    fn test_SAT_solution() {
        let graph = Graph::from_graph6(&String::from("TiXAIa?_C@O?_@_C]UVhguebKKfBAUUUb~~?"));
        let sat_precursor = get_sat_precursor(14, 7, 0);
        let sat_problem = create_sat_problem(&graph, &sat_precursor);
        let mut sat_solver: Solver = Default::default();
        let solution = vec![
            -24, -33, 34, -25, -4, -10, 19, 36, -6, 27, -28, -13, 22, 9, 11, 15, 5, 2, -7, -17, 30,
            31, 20, -35, 1, 18, -14, 8, -32, -3, -23, -26, 29, -12, 16, -21,
        ];
        assert!(
            sat_precursor.edge_to_var.len() == solution.len(),
            "Edge to variable mapping size does not match solution size"
        );
        sat_problem.clauses.iter().for_each(|clause| {
            sat_solver.add_clause(clause.clone());
        });
        sat_solver
            .solve_with(solution)
            .expect("Failed to solve SAT problem with given solution");
        assert!(
            sat_solver.status().expect("Failed to get solver status"),
            "SAT solver did not find a solution"
        );
    }
    fn _print_x_vecs(n: usize, x: usize, solver: &Solver, edge_to_var: &HashMap<Edge, i32>) {
        for i in 2..n + x {
            for j in n..n + x {
                let var = edge_to_var
                    .get(&Edge::new(i, j))
                    .expect("Edge not found in edge_to_var");
                let value = solver.value(*var).expect("Failed to get variable value");
                print!("{} ", if value { 1 } else { 0 });
            }
            println!();
        }
    }
    #[test]
    fn test_symm_clauses() {
        let SatPrecursor = get_sat_precursor(10, 4, 4);
        let symm_clauses = SatPrecursor.symmetry_clauses;
        println!("Symmetry clauses: {:?}", symm_clauses);
    }
    #[test]
    fn test_symm_clauses2() {
        let x = 2;
        let deg = 15;
        let K_size = 6;
        let SatPrecursor = get_sat_precursor(deg, K_size, x);
        let n = 2 * deg - K_size;
        let symm_clauses = SatPrecursor.symmetry_clauses;
        let mut solver: Solver = Solver::default();
        for clause in symm_clauses.clone() {
            solver.add_clause(clause);
        }
        let edge_to_var = SatPrecursor.edge_to_var;
        solver.add_clause(vec![edge_to_var[&Edge::new(2, n)]]);
        solver.add_clause(vec![-edge_to_var[&Edge::new(2, n + 1)]]);
        let _result = solver.solve().expect("Failed to solve SAT problem");
        assert!(
            !solver.status().unwrap(),
            "There should be no solution due to lexicographic ordering"
        );
        solver = Solver::default();
        for clause in symm_clauses.clone() {
            solver.add_clause(clause);
        }
        solver.add_clause(vec![-edge_to_var[&Edge::new(2, n)]]);
        solver.add_clause(vec![edge_to_var[&Edge::new(2, n + 1)]]);
        let result = solver.solve().expect("Failed to solve SAT problem");
        assert!(
            result,
            "There should be a solution with the lexicographic ordering"
        );
    }
}
