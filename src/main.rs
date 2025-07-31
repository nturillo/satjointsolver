#![allow(non_snake_case)]
use core::num;
use std::fs::{File, OpenOptions};
use std::io::{self, BufRead, Write};
use std::path::Path;
use std::env;
use mimalloc::MiMalloc;
use itertools::{iproduct, Itertools};
use std::collections::HashSet;
use std::collections::HashMap;
use cadical::Solver;
use rayon::prelude::*;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;


fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    let path = Path::new("../../pastings/case15/d6_case15_pastes_unique.g6");
    let file = File::open(&path)?;
    let reader = io::BufReader::new(file);
    let lines: Vec<String> = reader.lines().collect::<Result<_, _>>()?;

    println!("Number of graphs read: {}", lines.len());

    // Convert each line from graph6 format to a Graph object, create the SAT problem, and solve it
    let glued_graphs: Vec<Graph> = lines.into_par_iter().filter_map(|line| {
        let graph = Graph::from_graph6(&line);
        let sat_problem = create_sat_problem(&graph);
        let mut sat_solver: Solver = Default::default();
        sat_problem.clauses.iter().for_each(|clause| {
            sat_solver.add_clause(clause.clone());
        });
        sat_solver.solve().expect("Failed to solve SAT problem");
        Graph::from_sat_sol(&graph, &sat_problem, &sat_solver)
    }).collect();

    println!("Number of glued graphs found: {}", glued_graphs.len());

    Ok(())
}

#[derive(Debug, Clone)]
struct Graph {
    num_vertices: usize,
    // The adjacency matrix is represented as a vector of BitSet, where each BitSet represents
    // the neighbors of a vertex. The i-th BitSet has a bit set for each vertex j such that there is an edge from i to j.
    adjacency_matrix: Vec<BitSet>,
    structure: GraphStructure,
}
impl Graph {
    fn new(adjacency_matrix: Vec<BitSet>) -> Self {
        let structure = GraphStructure::from_adjacency_matrix(&adjacency_matrix);
        let num_vertices = adjacency_matrix.len();
        Graph { num_vertices, adjacency_matrix, structure }
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
    fn from_graph6(g6_str: &String) -> Self {
        Graph::new(decode_g6(g6_str))
    }
    fn from_sat_sol(unglued_graph: &Graph, sat_problem: &SatProblem, solver: &Solver) -> Option<Graph> {
        if !solver.status().expect("Failed to get solver status"){
            return None;
        }

        let A = unglued_graph.structure.A.clone();
        let B = unglued_graph.structure.B.clone();
        let edges = A.cartesian_product(B);

        let mut glued_graph = unglued_graph.clone();
        for (i, j) in edges {
            let var_index: i32 = i32::try_from(*sat_problem.edge_to_var
                .get(&(i, j))
                .expect("Edge not found in edge_to_var map"))
                .expect("Failed to convert edge index to i32");

            if let Some(value) = solver.value(var_index) {
                if value {
                    glued_graph.add_edge(i, j);
                }
            }
        }

        Some(glued_graph)
    }
}
type BitSet = u32;

#[derive(Debug, Clone)]
pub struct SatProblem {
    pub clauses: Vec<Vec<i32>>,
    pub edge_to_var: HashMap<(usize, usize), u32>,
}

#[derive(Debug, Clone)]
pub struct GraphStructure {
    a: usize,
    b: usize,
    a_nbhd: BitSet,
    b_nbhd: BitSet,
    K_bits: BitSet, // Vertices adjacent to both a and b
    A_bits: BitSet, // Vertices adjacent to b but not a, sometimes called h
    B_bits: BitSet, // Vertices adjacent to a but not b, sometimes called g
    A: std::ops::Range<usize>,
    B: std::ops::Range<usize>,
    K: std::ops::Range<usize>,
}
impl GraphStructure {
    fn from_adjacency_matrix(adjacency_matrix: &Vec<BitSet>) -> Self {
        // the graph is expected to be in this vertex order:
        // a, b, A, B, K
        let n = adjacency_matrix.len();
        const a: usize = 0;
        const b: usize = 1;
        let a_nbhd = adjacency_matrix[a];
        let b_nbhd = adjacency_matrix[b];
        let K_bits = a_nbhd & b_nbhd;
        let A_bits = b_nbhd & !K_bits & !(1 << (n - a - 1));
        let B_bits = a_nbhd & !K_bits & !(1 << (n - b - 1));
        let A = 2..(2 + A_bits.count_ones() as usize);
        let B = (2 + A_bits.count_ones() as usize)
            ..(2 + A_bits.count_ones() as usize + B_bits.count_ones() as usize);
        let K = (n - K_bits.count_ones() as usize)..n;

        GraphStructure { a, b, a_nbhd, b_nbhd, K_bits, A_bits, B_bits, A, B, K }
    }
}

fn create_sat_problem(graph: &Graph) -> SatProblem {
    let edge_to_var = get_edge_to_var(graph);
    let clauses = get_glue_clauses(graph, &edge_to_var);
    SatProblem { clauses, edge_to_var }
}

fn get_edge_to_var(graph: &Graph) -> HashMap<(usize, usize), u32> {
    let A = &graph.structure.A;
    let B = &graph.structure.B;

    let mut edge_to_var: HashMap<(usize, usize), u32> = HashMap::new();
    edge_to_var.extend(iproduct!(A.clone(), B.clone())
        .enumerate()
        .map(|(i, (a, b))| {
        let var_index = i as u32 + 1; // Start variable indices from 1
        ((a, b), var_index)
    }));
    edge_to_var
}



fn get_glue_clauses(graph: &Graph, edge_to_var: &HashMap<(usize, usize), u32>) -> Vec<Vec<i32>> {
    let mut clauses: Vec<Vec<i32>> = Vec::new();

    let A = &graph.structure.A;
    let B = &graph.structure.B;
    let Kab = &graph.structure.K.clone().chain([graph.structure.a, graph.structure.b]);

    // We want all the ways of picking five elements such that at least one is from A and at least one is from B.
    // We will use the following notation: (A_count, B_count, Kab_count)
    let compositions: Vec<(usize, usize, usize)> = vec![(1, 1, 3), (1, 2, 2), (1, 3, 1), (2, 1, 2), (2, 2, 1), (3, 1, 1),
        (2, 3, 0), (3, 2, 0), (4, 1, 0), (1, 4, 0), (5, 0, 0), (0, 5, 0)];

    for (A_count, B_count, Kab_count) in &compositions {
        let A_combinations = A.clone().combinations(*A_count);
        let B_combinations = B.clone().combinations(*B_count);
        let Kab_combinations = Kab.clone().combinations(*Kab_count);
        for (A_verts, B_verts, Kab_verts) in iproduct!(A_combinations, B_combinations, Kab_combinations) {
            let mut check_edges = vec![];

            // (A ∪ B) × K
            for &u in A_verts.iter().chain(B_verts.iter()) {
                for &v in &Kab_verts {
                    check_edges.push((u, v));
                }
            }
            // K × K and A × A and B × B
            check_edges.extend(Kab_verts.iter().cloned().combinations(2).map(|v| (v[0], v[1])));
            check_edges.extend(A_verts.iter().cloned().combinations(2).map(|v| (v[0], v[1])));
            check_edges.extend(B_verts.iter().cloned().combinations(2).map(|v| (v[0], v[1])));

            // (A × B)
            let clause_edges: Vec<(usize, usize)> = iproduct!(A_verts.iter(), B_verts.iter())
                .map(|(&x, &y)| (x, y))
                .collect();

            let num_missing_edges = check_edges.iter()
                .filter(|&&(i, j)| !graph.has_edge(i, j))
                .count();

            // clauses for independent sets of size 5
            if num_missing_edges == check_edges.len() { // 10 = 5 choose 2
                let k5bar_clause: Vec<i32> = clause_edges
                    .iter()
                    .map(|&(i, j)| i32::try_from(edge_to_var[&(i, j)]).expect("Failed to convert glue index to i32 in k5bar_clause"))
                    .collect();
                clauses.push(k5bar_clause);
            }
            // clauses for cliques of size 5
            else if num_missing_edges <= 1 {
                let k5_clause: Vec<i32> = clause_edges
                    .iter()
                    .map(|&(i, j)| -i32::try_from(edge_to_var[&(i, j)]).expect("Failed to convert glue index to i32 in k5_clause"))
                    .collect();
                clauses.push(k5_clause);
            }
            // clauses for cliques of size 5 minus an edge
            if num_missing_edges == 0 {
                for (i,j) in &clause_edges {
                    let j5_clause: Vec<i32> = clause_edges
                        .iter()
                        .filter(|&&(x, y)| x != *i || y != *j)
                        .map(|&(x, y)| -i32::try_from(edge_to_var[&(x, y)]).expect("Failed to convert glue index to i32 in j5_clause"))
                        .chain(std::iter::once(i32::try_from(edge_to_var[&(*i, *j)]).expect("Failed to convert glue index to i32 in j5_clause")))
                        .collect();
                    clauses.push(j5_clause);
                }
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