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
    let mut x = args.x;
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
    let mut start = std::time::Instant::now();
    while let Some(glued_graph) = get_glued_graph(&lines, x) {
        println!("Found glued graph with {} vertices, including {} extension vertices", glued_graph.num_vertices(), x);
        println!("Time taken: {:?}", start.elapsed());
        println!("Glued graph in graph6 format: {}", graph_to_g6(&glued_graph));
        x = x+1;
        if x > 1 {
            todo!("x > 1 is not implemented yet, please implement the logic to handle x > 1");
        }
        start = std::time::Instant::now();
        println!("Continuing with x = {}", x);
    }
    println!("No glued graph found with {} extension vertices", x);
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    Ok(())
}

fn get_glued_graph(lines: &[String], x: usize) -> Option<Graph> {
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
    lines.par_iter().find_map_any(|line| {
        let graph = Graph::from_graph6(line);
        let ext_graph = graph.extend(x);
        let sat_problem = create_sat_problem(&ext_graph, &sat_precursor);
        let mut sat_solver: Solver = Default::default();
        sat_problem.clauses.iter().for_each(|clause| {
            sat_solver.add_clause(clause.clone());
        });
        sat_solver.solve().expect("Failed to solve SAT problem");
        Graph::from_sat_sol(&ext_graph, &sat_problem, &sat_solver)
    })
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
    fn has_edge(&self, edge: Edge) -> bool {
        self.adjacency_matrix[edge.0] & self.get_bit(edge.1) != 0
    }
    fn add_edge(&mut self, edge: Edge) {
        self.adjacency_matrix[edge.0] |= self.get_bit(edge.1);
        self.adjacency_matrix[edge.1] |= self.get_bit(edge.0);
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
        for (edge, var_index) in edge_to_var {
            if solver.value(
                i32::try_from(*var_index)
                .expect("Failed to convert var_index")
            ).expect("Failed to get variable value") 
            {
                glued_graph.add_edge(*edge);
            }
        }

        Some(glued_graph)
    }
}
type BitSet = u32;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Edge(usize, usize);

impl Edge {
    fn new(a: usize, b: usize) -> Self {
        if a <= b {
            Edge(a, b)
        } else {
            Edge(b, a)
        }
    }
}

#[derive(Debug, Clone)]
pub struct SatProblem<'a> {
    pub clauses: Vec<Vec<i32>>,
    pub edge_to_var: &'a HashMap<Edge, i32>,
}
fn create_sat_problem<'a>(graph: &Graph, sat_precursor: &'a SatPrecursor) -> SatProblem<'a> {
    let clauses = get_clauses(graph, sat_precursor);
    SatProblem { clauses, edge_to_var: &sat_precursor.edge_to_var }
}
pub struct SatPrecursor {
    pub edge_to_var: HashMap<Edge, i32>,
        // This is a mapping from edges to variable indices, which is used to create the SAT clauses
    pub edge_sets: Vec<
        (Vec<Edge>, Vec<Edge>)
        >,
        // This is a vector of tuples (check_edges, clause_edges)
        // check_edges are edges that are already determined in the graph
        // clause_edges are considered edges for gluing
}

fn get_sat_precursor(deg: usize, K_size: usize, x: usize) -> SatPrecursor {
    //
    // This function creates some data needed for the SAT problem but only 
    // dependent on the parameters deg, K_size, and x. Hence, it does not
    // need to be computed for each graph. The data are:
    // - a mapping from edges to variable indices, which is used to create the SAT clauses
    // - a vec of tuples (check_edges, clause_edges)
    // - check_edges are edges that are already determined in the graph
    // - clause_edges are considered edges for gluing
    // 
    let mut edge_to_var = HashMap::new();
    let A_size = deg - K_size - 1;
    let A = 2..(2 + A_size);
    let B = (2 + A_size)..(2 + 2 * A_size);
    let X = (2 + 2 * A_size + K_size)..(2 + 2 * A_size + K_size + x);
    let ABK = 2..(2 + 2 * A_size + K_size);

    let edges = iproduct!(A.clone(), B.clone())
        .chain(iproduct!(X.clone(), ABK))
        .chain(X.clone().combinations(2).map(|v| (v[0], v[1])))
        .map(|(a, b)| Edge::new(a, b));

    edge_to_var.extend(edges
        .enumerate()
        .map(|(i, edge)| {
            let var_index = i32::try_from(i).expect("Failed to convert index to i32") + 1; // Start variable indices from 1
            (edge, var_index)
        }));
    let n = 2 + 2 * A_size + K_size + x;
    let edge_sets = (0..n)
        .combinations(5)
        .par_bridge()
        .filter_map(|set| {
            let edges = set
                .iter()
                .combinations(2)
                .map(|v| Edge::new(*v[0], *v[1]));
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
                return None; // No edges to consider for gluing
            }
            Some((check_edges, clause_edges))
        })
        .collect::<Vec<_>>();
    SatPrecursor {
        edge_to_var,
        edge_sets,
    }
}

fn get_clauses(graph: &Graph, sat_precursor: &SatPrecursor) -> Vec<Vec<i32>> {
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let edge_to_var = &sat_precursor.edge_to_var;

    for (check_edges, clause_edges) in &sat_precursor.edge_sets {

        let num_missing_edges = check_edges.iter()
            .filter(|&&edge| !graph.has_edge(edge))
            .count();

        // clauses for independent sets of size 5
        if num_missing_edges == check_edges.len() { // all edges are missing
            let k5bar_clause: Vec<i32> = clause_edges
                .iter()
                .map(|edge| edge_to_var[edge])
                .collect();
            clauses.push(k5bar_clause);
        }
        // clauses for cliques of size 5
        else if num_missing_edges <= 1 {
            let k5_clause: Vec<i32> = clause_edges
                .iter()
                .map(|edge| -edge_to_var[edge])
                .collect();
            clauses.push(k5_clause);
        }
        // clauses for cliques of size 5 minus an edge
        if num_missing_edges == 0 {
            // we want to create a clause for each edge 
            for edge in clause_edges {
                let j5_clause: Vec<i32> = clause_edges
                    .iter()
                    .filter(|&edge2| edge2 != edge)
                    .map(|edge| -edge_to_var[edge])
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

fn graph_to_g6(graph: &Graph) -> String {
    let num_vertices = u8::try_from(graph.num_vertices()).expect("num_vertices exceeds u8 limit");
    let size = u16::from(num_vertices) * (u16::from(num_vertices) - 1) / 2;
    let mut bit_vect: Vec<u8> = vec![0; size.into()];

    let mut i = 0;
    for column in 1..num_vertices {
        for row in 0..column {
            let bit = graph.has_edge(Edge::new(usize::from(row), usize::from(column))) as u8;
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

// tests
#[cfg(test)]
mod tests {
    use std::{collections::HashSet};

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
        (A.contains(&edge.0) && B.contains(&edge.1)) ||
           (A.contains(&edge.1) && B.contains(&edge.0))
    }
    #[test]
    fn test_sat_precursor() {
        let deg = 14;
        let K_size = 7;
        let x = 0;
        let sat_precursor = get_sat_precursor(deg, K_size, x);
        for (check_edges, clause_edges) in &sat_precursor.edge_sets {
            assert!(check_edges.len() + clause_edges.len() == 10, 
                "check_edges and clause_edges should sum to 10"
            );
            assert!(!clause_edges.is_empty(), "clause_edges should not be empty");
            assert!(check_edges.iter().all(|edge| !clause_edge_good(edge, deg, K_size)),
                "check edges should not be clause edges"
            );
            assert!(clause_edges.iter().all(|edge| clause_edge_good(edge, deg, K_size)),
                "clause edges should be valid clause edges"
            );
        }
        // println!("edge sets: {:?}", sat_precursor.edge_sets);
    }
    #[test]
    fn test_clauses() {
        let graph = Graph::from_graph6(&String::from("TiXAIa?_C@O?_@_C]UVhguebKKfBAUUUb~~?"));
        let sat_precursor = get_sat_precursor(14, 7, 0);
        let sat_problem = create_sat_problem(&graph, &sat_precursor);
        let true_clause: Vec<Vec<i32>> = vec![
vec![-1, -3], vec![-2, -6], vec![-4, -5], vec![-7, -9], vec![-8, -12], vec![-10, -11], vec![-13, -15], vec![-14, -18], vec![-16, -17], vec![-19, -21],
vec![-20, -24], vec![-22, -23], vec![-25, -27], vec![-26, -30], vec![-28, -29], vec![-31, -33], vec![-32, -36], vec![-34, -35], vec![-1, -13], vec![-2, -14],
vec![-3, -15], vec![-4, -16], vec![-5, -17], vec![-6, -18], vec![-7, -31], vec![-8, -32], vec![-9, -33], vec![-10, -34], vec![-11, -35], vec![-12, -36],
vec![-19, -25], vec![-20, -26], vec![-21, -27], vec![-22, -28], vec![-23, -29], vec![-24, -30], vec![1, 2, 7, 8, 19, 20], vec![1, 4, 7, 10, 19, 22], vec![1, 5, 7, 11, 19, 23], vec![1, 6, 7, 12, 19, 24],
vec![1, 7, 19], vec![2, 3, 8, 9, 20, 21], vec![2, 4, 8, 10, 20, 22], vec![2, 5, 8, 11, 20, 23], vec![2, 8, 20], vec![3, 4, 9, 10, 21, 22], vec![3, 5, 9, 11, 21, 23], vec![3, 6, 9, 12, 21, 24], vec![4, 6, 10, 12, 22, 24], vec![4, 10, 22],
vec![5, 6, 11, 12, 23, 24], vec![1, 2, 7, 8, 25, 26], vec![1, 4, 7, 10, 25, 28], vec![1, 5, 7, 11, 25, 29], vec![1, 6, 7, 12, 25, 30], vec![1, 7, 25], vec![2, 3, 8, 9, 26, 27], vec![2, 4, 8, 10, 26, 28], vec![2, 5, 8, 11, 26, 29], vec![2, 8, 26],
vec![3, 4, 9, 10, 27, 28], vec![3, 5, 9, 11, 27, 29], vec![3, 6, 9, 12, 27, 30], vec![4, 6, 10, 12, 28, 30], vec![5, 6, 11, 12, 29, 30], vec![5, 11, 29], vec![6, 12, 30], vec![1, 2, 4, 7, 8, 10], vec![1, 2, 5, 7, 8, 11], vec![1, 2, 7, 8],
vec![1, 2, 7, 8], vec![-1, -3, -7, -9], vec![1, 4, 6, 7, 10, 12], vec![1, 4, 7, 10], vec![1, 5, 6, 7, 11, 12], vec![1, 5, 7, 11], vec![1, 6, 7, 12], vec![1, 7], vec![2, 3, 4, 8, 9, 10], vec![2, 3, 5, 8, 9, 11],
vec![2, 4, 8, 10], vec![2, 5, 8, 11], vec![-2, -6, -8, -12], vec![2, 8], vec![3, 4, 6, 9, 10, 12], vec![3, 5, 6, 9, 11, 12], vec![-4, -5, -10, -11], vec![5, 6, 11, 12], vec![-1, -2, -13, -14], vec![-1, -3, -13, -15],
vec![-3, -13, -15], vec![-1, -13, -15], vec![-1, -3, -15], vec![-1, -3, -13], vec![-1, -4, -13, -16], vec![-1, -5, -13, -17], vec![-1, -6, -13, -18], vec![-2, -3, -14, -15], vec![-2, -4, -14, -16], vec![-2, -5, -14, -17],
vec![-2, -6, -14, -18], vec![-6, -14, -18], vec![-2, -14, -18], vec![-2, -6, -18], vec![-2, -6, -14], vec![-3, -4, -15, -16], vec![-3, -5, -15, -17], vec![-3, -6, -15, -18], vec![-4, -5, -16, -17], vec![-5, -16, -17],
vec![-4, -16, -17], vec![-4, -5, -17], vec![-4, -5, -16], vec![-4, -6, -16, -18], vec![-5, -6, -17, -18], vec![1, 2, 19, 20, 31, 32], vec![1, 4, 19, 22, 31, 34], vec![1, 5, 19, 23, 31, 35], vec![1, 6, 19, 24, 31, 36], vec![1, 19, 31],
vec![2, 3, 20, 21, 32, 33], vec![2, 4, 20, 22, 32, 34], vec![2, 5, 20, 23, 32, 35], vec![3, 4, 21, 22, 33, 34], vec![3, 5, 21, 23, 33, 35], vec![3, 6, 21, 24, 33, 36], vec![4, 6, 22, 24, 34, 36], vec![4, 22, 34], vec![5, 6, 23, 24, 35, 36], vec![6, 24, 36],
vec![1, 2, 4, 19, 20, 22], vec![1, 2, 5, 19, 20, 23], vec![1, 2, 19, 20], vec![-1, -3, -19, -21], vec![1, 4, 6, 19, 22, 24], vec![1, 4, 19, 22], vec![1, 4, 19, 22], vec![1, 5, 6, 19, 23, 24], vec![1, 6, 19, 24], vec![1, 19],
vec![2, 3, 4, 20, 21, 22], vec![2, 3, 5, 20, 21, 23], vec![2, 4, 20, 22], vec![-2, -6, -20, -24], vec![3, 4, 6, 21, 22, 24], vec![3, 5, 6, 21, 23, 24], vec![-4, -5, -22, -23], vec![4, 6, 22, 24], vec![4, 22], vec![1, 2, 25, 26, 31, 32],
vec![1, 4, 25, 28, 31, 34], vec![1, 5, 25, 29, 31, 35], vec![1, 6, 25, 30, 31, 36], vec![1, 25, 31], vec![2, 3, 26, 27, 32, 33], vec![2, 4, 26, 28, 32, 34], vec![2, 5, 26, 29, 32, 35], vec![2, 26, 32], vec![3, 4, 27, 28, 33, 34], vec![3, 5, 27, 29, 33, 35],
vec![3, 6, 27, 30, 33, 36], vec![4, 6, 28, 30, 34, 36], vec![5, 6, 29, 30, 35, 36], vec![5, 29, 35], vec![6, 30, 36], vec![1, 2, 4, 25, 26, 28], vec![1, 2, 5, 25, 26, 29], vec![1, 2, 25, 26], vec![-1, -3, -25, -27], vec![1, 4, 6, 25, 28, 30],
vec![1, 5, 6, 25, 29, 30], vec![1, 5, 25, 29], vec![1, 6, 25, 30], vec![2, 3, 4, 26, 27, 28], vec![2, 3, 5, 26, 27, 29], vec![2, 5, 26, 29], vec![-2, -6, -26, -30], vec![3, 4, 6, 27, 28, 30], vec![3, 5, 6, 27, 29, 30], vec![-4, -5, -28, -29],
vec![5, 6, 29, 30], vec![1, 2, 4, 31, 32, 34], vec![1, 2, 5, 31, 32, 35], vec![1, 2, 31, 32], vec![-1, -3, -31, -33], vec![1, 4, 6, 31, 34, 36], vec![1, 4, 31, 34], vec![1, 5, 6, 31, 35, 36], vec![1, 5, 31, 35], vec![1, 6, 31, 36],
vec![1, 6, 31, 36], vec![1, 31], vec![2, 3, 4, 32, 33, 34], vec![2, 3, 5, 32, 33, 35], vec![2, 5, 32, 35], vec![-2, -6, -32, -36], vec![3, 4, 6, 33, 34, 36], vec![3, 5, 6, 33, 35, 36], vec![-4, -5, -34, -35], vec![4, 6, 34, 36],
vec![5, 6, 35, 36], vec![6, 36], vec![1, 2, 4], vec![1, 2, 5], vec![1, 2], vec![1, 4, 6], vec![1, 4], vec![1, 5, 6], vec![1, 6], vec![1],
vec![7, 8, 13, 14, 19, 20], vec![7, 10, 13, 16, 19, 22], vec![7, 11, 13, 17, 19, 23], vec![7, 12, 13, 18, 19, 24], vec![8, 9, 14, 15, 20, 21], vec![8, 10, 14, 16, 20, 22], vec![8, 11, 14, 17, 20, 23], vec![8, 14, 20], vec![9, 10, 15, 16, 21, 22], vec![9, 11, 15, 17, 21, 23],
vec![9, 12, 15, 18, 21, 24], vec![9, 15, 21], vec![10, 12, 16, 18, 22, 24], vec![10, 16, 22], vec![11, 12, 17, 18, 23, 24], vec![11, 17, 23], vec![7, 8, 13, 14, 25, 26], vec![7, 10, 13, 16, 25, 28], vec![7, 11, 13, 17, 25, 29], vec![7, 12, 13, 18, 25, 30],
vec![8, 9, 14, 15, 26, 27], vec![8, 10, 14, 16, 26, 28], vec![8, 11, 14, 17, 26, 29], vec![8, 14, 26], vec![9, 10, 15, 16, 27, 28], vec![9, 11, 15, 17, 27, 29], vec![9, 12, 15, 18, 27, 30], vec![9, 15, 27], vec![10, 12, 16, 18, 28, 30], vec![10, 16, 28],
vec![11, 12, 17, 18, 29, 30], vec![11, 17, 29], vec![7, 8, 10, 13, 14, 16], vec![7, 8, 11, 13, 14, 17], vec![-7, -9, -13, -15], vec![7, 10, 12, 13, 16, 18], vec![7, 11, 12, 13, 17, 18], vec![8, 9, 10, 14, 15, 16], vec![8, 9, 11, 14, 15, 17], vec![8, 9, 14, 15],
vec![8, 10, 14, 16], vec![8, 11, 14, 17], vec![-8, -12, -14, -18], vec![9, 10, 12, 15, 16, 18], vec![9, 10, 15, 16], vec![9, 11, 12, 15, 17, 18], vec![9, 11, 15, 17], vec![-10, -11, -16, -17], vec![7, 8, 10, 19, 20, 22], vec![7, 8, 11, 19, 20, 23],
vec![7, 8, 19, 20], vec![-7, -9, -19, -21], vec![7, 10, 12, 19, 22, 24], vec![7, 10, 19, 22], vec![7, 11, 12, 19, 23, 24], vec![8, 9, 10, 20, 21, 22], vec![8, 9, 11, 20, 21, 23], vec![8, 9, 20, 21], vec![8, 10, 20, 22], vec![8, 10, 20, 22],
vec![8, 11, 20, 23], vec![-8, -12, -20, -24], vec![8, 20], vec![9, 10, 12, 21, 22, 24], vec![9, 10, 21, 22], vec![9, 11, 12, 21, 23, 24], vec![9, 11, 21, 23], vec![-10, -11, -22, -23], vec![10, 22], vec![7, 8, 10, 25, 26, 28],
vec![7, 8, 11, 25, 26, 29], vec![7, 8, 25, 26], vec![-7, -9, -25, -27], vec![7, 10, 12, 25, 28, 30], vec![7, 11, 12, 25, 29, 30], vec![7, 11, 25, 29], vec![7, 12, 25, 30], vec![8, 9, 10, 26, 27, 28], vec![8, 9, 11, 26, 27, 29], vec![8, 9, 26, 27],
vec![8, 10, 26, 28], vec![8, 11, 26, 29], vec![8, 11, 26, 29], vec![-8, -12, -26, -30], vec![8, 26], vec![9, 10, 12, 27, 28, 30], vec![9, 10, 27, 28], vec![9, 11, 12, 27, 29, 30], vec![9, 11, 27, 29], vec![-10, -11, -28, -29],
vec![11, 12, 29, 30], vec![11, 29], vec![-7, -8, -31, -32], vec![-7, -9, -31, -33], vec![-9, -31, -33], vec![-7, -31, -33], vec![-7, -9, -33], vec![-7, -9, -31], vec![-7, -10, -31, -34], vec![-7, -11, -31, -35],
vec![-7, -12, -31, -36], vec![-8, -9, -32, -33], vec![-8, -10, -32, -34], vec![-8, -11, -32, -35], vec![-8, -12, -32, -36], vec![-12, -32, -36], vec![-8, -32, -36], vec![-8, -12, -36], vec![-8, -12, -32], vec![-9, -10, -33, -34],
vec![-9, -11, -33, -35], vec![-9, -12, -33, -36], vec![-10, -11, -34, -35], vec![-11, -34, -35], vec![-10, -34, -35], vec![-10, -11, -35], vec![-10, -11, -34], vec![-10, -12, -34, -36], vec![-11, -12, -35, -36], vec![7, 8, 10],
vec![7, 8, 11], vec![7, 8], vec![7, 11, 12], vec![8, 9, 10], vec![8, 9, 11], vec![8, 10], vec![8, 11], vec![8], vec![13, 14, 19, 20, 31, 32], vec![13, 16, 19, 22, 31, 34],
vec![13, 17, 19, 23, 31, 35], vec![13, 18, 19, 24, 31, 36], vec![14, 15, 20, 21, 32, 33], vec![14, 16, 20, 22, 32, 34], vec![14, 17, 20, 23, 32, 35], vec![15, 16, 21, 22, 33, 34], vec![15, 17, 21, 23, 33, 35], vec![15, 18, 21, 24, 33, 36], vec![15, 21, 33], vec![16, 18, 22, 24, 34, 36],
vec![16, 22, 34], vec![17, 18, 23, 24, 35, 36], vec![18, 24, 36], vec![13, 14, 16, 19, 20, 22], vec![13, 14, 17, 19, 20, 23], vec![-13, -15, -19, -21], vec![13, 16, 18, 19, 22, 24], vec![13, 17, 18, 19, 23, 24], vec![14, 15, 16, 20, 21, 22], vec![14, 15, 17, 20, 21, 23],
vec![14, 15, 20, 21], vec![14, 16, 20, 22], vec![14, 17, 20, 23], vec![-14, -18, -20, -24], vec![15, 16, 18, 21, 22, 24], vec![15, 16, 21, 22], vec![15, 16, 21, 22], vec![15, 17, 18, 21, 23, 24], vec![15, 17, 21, 23], vec![15, 18, 21, 24],
vec![15, 21], vec![-16, -17, -22, -23], vec![16, 18, 22, 24], vec![16, 22], vec![13, 14, 25, 26, 31, 32], vec![13, 16, 25, 28, 31, 34], vec![13, 17, 25, 29, 31, 35], vec![13, 18, 25, 30, 31, 36], vec![14, 15, 26, 27, 32, 33], vec![14, 16, 26, 28, 32, 34],
vec![14, 17, 26, 29, 32, 35], vec![15, 16, 27, 28, 33, 34], vec![15, 17, 27, 29, 33, 35], vec![15, 18, 27, 30, 33, 36], vec![15, 27, 33], vec![16, 18, 28, 30, 34, 36], vec![17, 18, 29, 30, 35, 36], vec![17, 29, 35], vec![18, 30, 36], vec![13, 14, 16, 25, 26, 28],
vec![13, 14, 17, 25, 26, 29], vec![-13, -15, -25, -27], vec![13, 16, 18, 25, 28, 30], vec![13, 17, 18, 25, 29, 30], vec![14, 15, 16, 26, 27, 28], vec![14, 15, 17, 26, 27, 29], vec![14, 15, 26, 27], vec![14, 16, 26, 28], vec![14, 17, 26, 29], vec![-14, -18, -26, -30],
vec![15, 16, 18, 27, 28, 30], vec![15, 16, 27, 28], vec![15, 17, 18, 27, 29, 30], vec![15, 17, 27, 29], vec![15, 17, 27, 29], vec![15, 18, 27, 30], vec![15, 27], vec![-16, -17, -28, -29], vec![17, 18, 29, 30], vec![17, 29],
vec![13, 14, 16, 31, 32, 34], vec![13, 14, 17, 31, 32, 35], vec![-13, -15, -31, -33], vec![13, 16, 18, 31, 34, 36], vec![13, 17, 18, 31, 35, 36], vec![14, 15, 16, 32, 33, 34], vec![14, 15, 17, 32, 33, 35], vec![-14, -18, -32, -36], vec![15, 16, 18, 33, 34, 36], vec![15, 16, 33, 34],
vec![15, 17, 18, 33, 35, 36], vec![15, 17, 33, 35], vec![15, 18, 33, 36], vec![15, 18, 33, 36], vec![15, 33], vec![-16, -17, -34, -35], vec![16, 18, 34, 36], vec![17, 18, 35, 36], vec![18, 36], vec![14, 15, 16],
vec![14, 15, 17], vec![15, 16, 18], vec![15, 16], vec![15, 17, 18], vec![15, 17], vec![15, 18], vec![15], vec![-19, -20, -25, -26], vec![-19, -21, -25, -27], vec![-21, -25, -27],
vec![-19, -25, -27], vec![-19, -21, -27], vec![-19, -21, -25], vec![-19, -22, -25, -28], vec![-19, -23, -25, -29], vec![-19, -24, -25, -30], vec![-20, -21, -26, -27], vec![-20, -22, -26, -28], vec![-20, -23, -26, -29], vec![-20, -24, -26, -30],
vec![-24, -26, -30], vec![-20, -26, -30], vec![-20, -24, -30], vec![-20, -24, -26], vec![-21, -22, -27, -28], vec![-21, -23, -27, -29], vec![-21, -24, -27, -30], vec![-22, -23, -28, -29], vec![-23, -28, -29], vec![-22, -28, -29],
vec![-22, -23, -29], vec![-22, -23, -28], vec![-22, -24, -28, -30], vec![-23, -24, -29, -30], vec![19, 20, 22, 31, 32, 34], vec![19, 20, 23, 31, 32, 35], vec![-19, -21, -31, -33], vec![19, 22, 24, 31, 34, 36], vec![19, 22, 31, 34], vec![19, 23, 24, 31, 35, 36],
vec![19, 24, 31, 36], vec![20, 21, 22, 32, 33, 34], vec![20, 21, 23, 32, 33, 35], vec![-20, -24, -32, -36], vec![21, 22, 24, 33, 34, 36], vec![21, 22, 33, 34], vec![21, 23, 24, 33, 35, 36], vec![21, 24, 33, 36], vec![-22, -23, -34, -35], vec![22, 24, 34, 36],
vec![22, 24, 34, 36], vec![22, 34], vec![24, 36], vec![19, 20, 22], vec![19, 22, 24], vec![19, 22], vec![20, 21, 22], vec![20, 21, 23], vec![20, 22], vec![21, 22, 24],
vec![21, 22], vec![22, 24], vec![22], vec![22], vec![25, 26, 28, 31, 32, 34], vec![25, 26, 29, 31, 32, 35], vec![25, 26, 31, 32], vec![-25, -27, -31, -33], vec![25, 28, 30, 31, 34, 36], vec![25, 29, 30, 31, 35, 36],
vec![25, 29, 31, 35], vec![25, 30, 31, 36], vec![26, 27, 28, 32, 33, 34], vec![26, 27, 29, 32, 33, 35], vec![26, 29, 32, 35], vec![-26, -30, -32, -36], vec![27, 28, 30, 33, 34, 36], vec![27, 29, 30, 33, 35, 36], vec![27, 29, 33, 35], vec![27, 30, 33, 36],
vec![-28, -29, -34, -35], vec![29, 30, 35, 36], vec![29, 30, 35, 36], vec![29, 35], vec![30, 36], vec![25, 26, 29], vec![25, 29, 30], vec![26, 27, 28], vec![26, 27, 29], vec![26, 29],
vec![27, 29, 30], vec![27, 29], vec![29, 30], vec![29], vec![31, 32, 35], vec![31, 34, 36], vec![31, 35, 36], vec![31, 36], vec![33, 34, 36], vec![33, 35, 36],
vec![33, 36], vec![34, 36], vec![35, 36], vec![36], vec![36], ];
        let true_clause_set: HashSet<Vec<i32>> = HashSet::from_iter(true_clause.iter().cloned());
        let attempted_clause_set: HashSet<Vec<i32>> = HashSet::from_iter(sat_problem.clauses.iter().cloned());
        assert_eq!(true_clause_set, attempted_clause_set, "The clauses generated do not match the expected clauses");
     }
    #[test]
    fn test_SAT_solution() {
        let graph = Graph::from_graph6(&String::from("TiXAIa?_C@O?_@_C]UVhguebKKfBAUUUb~~?"));
        let sat_precursor = get_sat_precursor(14, 7, 0);
        let sat_problem = create_sat_problem(&graph, &sat_precursor);
        let mut sat_solver: Solver = Default::default();
        let solution = 
            vec![-24, -33, 34, -25, -4, -10, 19, 36, -6, 27, -28, -13, 22, 9, 11, 15, 5, 2, -7, -17, 30, 31, 20, -35, 1, 18, -14, 8, -32, -3, -23, -26, 29, -12, 16, -21];
        assert!(sat_precursor.edge_to_var.len() == solution.len(), "Edge to variable mapping size does not match solution size");
        sat_problem.clauses.iter().for_each(|clause| {
            sat_solver.add_clause(clause.clone());
        });
        sat_solver.solve_with(solution).expect("Failed to solve SAT problem with given solution");
        let culprit_edges = sat_precursor.edge_to_var
            .iter()
            .filter_map(|(edge, var)| {
                if sat_solver.failed(i32::try_from(*var).expect("Failed to convert var index to i32")) {
                    Some(edge)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        println!("Culprit edges: {:?}", culprit_edges);
        println!("num vars in sat problem: {}", sat_solver.num_variables());
        assert!(sat_solver.status().expect("Failed to get solver status"), "SAT solver did not find a solution");
    }
}