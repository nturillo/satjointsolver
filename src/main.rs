#![allow(non_snake_case)]
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use mimalloc::MiMalloc;
use itertools::{iproduct, Itertools};
use std::collections::HashMap;
use cadical::Solver;
use rayon::prelude::*;
use clap::Parser;

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
    let x = args.x;
    let infile_str = args.input;

    let path = Path::new(&infile_str);
    let file = File::open(&path)?;
    let reader = io::BufReader::new(file);
    let lines: Vec<String> = reader.lines().collect::<Result<_, _>>()?;

    let num_graphs = lines.len();
    println!("Read: {} graphs from {}", num_graphs, infile_str);

    let graph0 = Graph::from_graph6(&lines[0]);
    let deg = graph0.neighbor_set(0).count_ones() as usize;
    let K_size = (graph0.neighbor_set(0) & graph0.neighbor_set(1)).count_ones() as usize;

    println!("Graph degree: {}", deg);
    println!("K size: {}", K_size);

    // Convert each line from graph6 format to a Graph object, create the SAT problem, and solve it
    let start = std::time::Instant::now();
    let edge_to_var = get_edge_to_var(deg, K_size, x);
    let glued_graphs: Vec<Graph> = lines.into_par_iter().filter_map(|line| {
        let graph = Graph::from_graph6(&line);
        let ext_graph = graph.extend(x);
        let sat_problem = create_sat_problem(&ext_graph, &edge_to_var);
        let mut sat_solver: Solver = Default::default();
        sat_problem.clauses.iter().for_each(|clause| {
            sat_solver.add_clause(clause.clone());
        });
        sat_solver.solve().expect("Failed to solve SAT problem");
        Graph::from_sat_sol(&graph, &sat_problem, &sat_solver)
    }).collect();

    println!("Number of glued graphs found: {}", glued_graphs.len());

    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    Ok(())
}

#[derive(Debug, Clone)]
struct Graph {
    num_vertices: usize,
    // The adjacency matrix is represented as a vector of BitSet, where each BitSet represents
    // the neighbors of a vertex. The i-th BitSet has a bit set for each vertex j such that there is an edge from i to j.
    adjacency_matrix: Vec<BitSet>,
}
impl Graph {
    fn new(adjacency_matrix: Vec<BitSet>) -> Self {
        let num_vertices = adjacency_matrix.len();
        Graph { num_vertices, adjacency_matrix}
    }
    fn has_edge(&self, u: usize, v: usize) -> bool {
        self.adjacency_matrix[u] & self.get_bit(v) != 0
    }
    fn add_edge(&mut self, u: usize, v: usize) {
        self.adjacency_matrix[u] |= self.get_bit(v);
        self.adjacency_matrix[v] |= self.get_bit(u);
    }
    fn neighbor_set(&self, u: usize) -> BitSet {
        self.adjacency_matrix[u]
    }
    fn num_vertices(&self) -> usize {
        self.num_vertices
    }
    fn get_bit(&self, i: usize) -> BitSet {
        1 << (self.num_vertices() - i - 1) as BitSet
    }
    fn extend(&self, x: usize) -> Graph {
        // Add x new vertices, which are not connected to any existing vertices
        let mut new_adjacency_matrix = self.adjacency_matrix.clone();
        for set in &mut new_adjacency_matrix {
            *set <<= x as BitSet; // Shift existing bits to make space for new vertices
        }
        for _ in 0..x {
            new_adjacency_matrix.push(0);
        }
        Graph::new(new_adjacency_matrix)
    }
    fn from_graph6(g6_str: &String) -> Self {
        Graph::new(decode_g6(g6_str))
    }
    fn from_sat_sol(unglued_graph: &Graph, sat_problem: &SatProblem, solver: &Solver) -> Option<Graph> {
        if !solver.status().expect("Failed to get solver status"){
            return None;
        }

        let mut glued_graph = unglued_graph.clone();
        let edge_to_var = sat_problem.edge_to_var;
        // iterate over the edges in the SAT problem
        for ((u, v), var_index) in edge_to_var {
            if solver.value(
                i32::try_from(*var_index)
                .expect("Failed to convert var_index")
            ).expect("Failed to get variable value") 
            {
                glued_graph.add_edge(*u, *v);
            }
        }

        Some(glued_graph)
    }
}
type BitSet = u32;

#[derive(Debug, Clone)]
pub struct SatProblem<'a> {
    pub clauses: Vec<Vec<i32>>,
    pub edge_to_var: &'a HashMap<(usize, usize), u32>,
}
fn create_sat_problem<'a>(graph: &Graph, edge_to_var: &'a HashMap<(usize, usize), u32>) -> SatProblem<'a> {
    let clauses = get_clauses(graph, &edge_to_var);
    SatProblem { clauses, edge_to_var }
}

fn get_edge_to_var(deg: usize, K_size: usize, x: usize) -> HashMap<(usize, usize), u32> {
    let mut edge_to_var = HashMap::new();
    let A_size = deg - K_size - 1;
    let A = 2..(2 + A_size);
    let B = (2 + A_size)..(2 + 2 * A_size);
    let X = (2 + 2 * A_size + K_size)..(2 + 2 * A_size + K_size + x);
    let ABK = 2..(2 + 2 * A_size + K_size);

    let edges = iproduct!(A.clone(), B.clone())
        .chain(iproduct!(X.clone(), ABK))
        .chain(X.clone().combinations(2).map(|v| (v[0], v[1])));

    edge_to_var.extend(edges
        .enumerate()
        .map(|(i, (a, b))| {
        let var_index = i as u32 + 1; // Start variable indices from 1
        ((a, b), var_index)
    }));
 
    edge_to_var
}

fn get_clauses(graph: &Graph, edge_to_var: &HashMap<(usize, usize), u32>) -> Vec<Vec<i32>> {
    let mut clauses: Vec<Vec<i32>> = Vec::new();

    let num_vertices = graph.num_vertices();

    let five_sets = (0..num_vertices)
        .combinations(5);
        /*
        .filter(|set| {
            // check that either:
            // 1. at least one vertex is in X
            // 2. at least one vertex is in A and at least one vertex is in B
            let bit_set = set.iter()
                .map(|i| graph.get_bit(*i))
                .fold(BitSet::default(), |acc, bit| acc | bit);
            (bit_set & graph.structure.X_bits != 0) ||
            (bit_set & graph.structure.A_bits != 0 && bit_set & graph.structure.B_bits != 0)
        });
        */

    for five_set in five_sets {
        let edges = five_set.iter().combinations(2).map(|v| (*v[0], *v[1]));

        let mut check_edges = vec![];
        let mut clause_edges = vec![];

        for edge in edges {
            if edge_to_var.contains_key(&edge) {
                clause_edges.push(edge); // edges to consider for gluing
            } else {
                check_edges.push(edge); // edges already determined in the graph
            }
        }

        if clause_edges.len() == 0 {
            continue; // skip if there are no edges to consider
        }

        let num_missing_edges = check_edges.iter()
            .filter(|&&(i, j)| !graph.has_edge(i, j))
            .count();

        // clauses for independent sets of size 5
        if num_missing_edges == check_edges.len() { // 10 = 5 choose 2
            let k5bar_clause: Vec<i32> = clause_edges
                .iter()
                .map(|&(i, j)| i32::try_from(edge_to_var[&(i, j)]).expect("Failed to convert index to i32 in k5bar_clause"))
                .collect();
            clauses.push(k5bar_clause);
        }
        // clauses for cliques of size 5
        else if num_missing_edges <= 1 {
            let k5_clause: Vec<i32> = clause_edges
                .iter()
                .map(|&(i, j)| -i32::try_from(edge_to_var[&(i, j)]).expect("Failed to convert index to i32 in k5_clause"))
                .collect();
            clauses.push(k5_clause);
        }
        // clauses for cliques of size 5 minus an edge
        if num_missing_edges == 0 {
            // we want to create a clause for each edge 
            for (i,j) in &clause_edges {
                let j5_clause: Vec<i32> = clause_edges
                    .iter()
                    .filter(|&&(x, y)| x != *i || y != *j)
                    .map(|&(x, y)| -i32::try_from(edge_to_var[&(x, y)]).expect("Failed to convert index to i32 in j5_clause"))
                    .collect();
                clauses.push(j5_clause);
            }
        }
    }
    clauses
}

fn decode_g6(line: &String) -> Vec<u32> {
    let line_vec = line.as_bytes();
    let num_vertices = line_vec[0] - 63;
    let size = u16::from(num_vertices) * (u16::from(num_vertices) - 1) / 2;
    let mut bit_vect: Vec<u8> = vec![0; (size + 6).into()];
    
    let mut i = 0;
    let mut fixed_letter;
    for letter in line_vec[1..].iter() {
        fixed_letter = letter - 63;
        for bit_place in (0..6).rev() {
            bit_vect[i] = (fixed_letter & (1 << bit_place)) >> bit_place;
            i += 1;
        }
    }

    let mut graph: Vec<u32> = vec![0; num_vertices.into()];
    i = 0;
    for column in 1..num_vertices {
        for row in 0..column {
            graph[usize::from(row)] |= u32::from(bit_vect[i]) << (num_vertices - column - 1);
            graph[usize::from(column)] |= u32::from(bit_vect[i]) << (num_vertices - row - 1);
            i += 1;
        }
    }
    graph
}

fn _graph_to_g6(graph: &Graph) -> String {
    let num_vertices = u8::try_from(graph.num_vertices()).expect("num_vertices exceeds u8 limit");
    let size = u16::from(num_vertices) * (u16::from(num_vertices) - 1) / 2;
    let mut bit_vect: Vec<u8> = vec![0; size.into()];

    let mut i = 0;
    for column in 1..num_vertices {
        for row in 0..column {
            let bit = graph.has_edge(row as usize, column as usize);
            bit_vect[i] = bit as u8;
            i += 1;
        }
    }

    let mut g6_str = String::new();
    g6_str.push((num_vertices + 63) as char);
    for chunk in bit_vect.chunks(6) {
        let mut fixed_letter = 0;
        for (j, &bit) in chunk.iter().enumerate() {
            fixed_letter |= bit << (5 - j);
        }
        g6_str.push((fixed_letter + 63) as char);
    }
    g6_str
}