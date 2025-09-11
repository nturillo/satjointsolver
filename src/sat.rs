use crate::graph::*;
use std::collections::HashMap;
use serde_json::json;
use std::process::{Command, Stdio};
use itertools::{Itertools, iproduct};
use rayon::prelude::*;
use std::path::Path;
use std::fs::File;
use std::io::{self, Write, BufRead};
use cadical::Solver;

pub fn run_satsolver(x: usize, infile_str: &str) -> Result<(), Box<dyn std::error::Error + 'static>> {
    let mut x = x;
    let path = Path::new(infile_str);
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
            glued_graph.to_g6()
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


#[derive(Debug, Clone)]
pub struct SatProblem<'a> {
    pub clauses: Vec<Vec<i32>>,
    pub edge_to_var: &'a HashMap<Edge, i32>,
}
pub fn create_sat_problem<'a>(graph: &Graph, sat_precursor: &'a SatPrecursor) -> SatProblem<'a> {
    let clauses = get_clauses(graph, sat_precursor);
    SatProblem {
        clauses,
        edge_to_var: &sat_precursor.edge_to_var,
    }
}
pub struct SatPrecursor {
    pub edge_to_var: HashMap<Edge, i32>,
    // This is a mapping from edges to variable indices, which is used to create the SAT clauses
    pub edge_sets: Vec<(Vec<Edge>, Vec<Edge>)>,
    // This is a vector of tuples (check_edges, clause_edges)
    // check_edges are edges that are already determined in the graph
    // clause_edges are considered edges for gluing
    pub symmetry_clauses: Vec<Vec<i32>>,
    // This is a vector of symmetry breaking clauses, which
    // are used to reduce the search space when there are extension vertices.
    // These clauses insist that the vectors of edges of
    // the extension vertices are ordered lexicographically.
}

pub fn get_symm_break_clauses(n: usize, x: usize, edge_to_var: &HashMap<Edge, i32>) -> Vec<Vec<i32>> {
    //
    // This function creates symmetry breaking clauses for the SAT problem.
    // It ensures that the edges of the extension vertices are ordered lexicographically.
    // Calls Python script symm_break.py to generate the clauses using sympy.
    //
    if x <= 1 {
        return vec![]; // No symmetry breaking needed if there are no extension vertices
    }
    let X = (n..(n + x))
        .map(|i| {
            (2..n + x)
                .map(|j| edge_to_var[&Edge::new(i, j)])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let symbol_count = edge_to_var.len() + 1; // plus one since vars start at 1
    let json_payload = json!({
        "X": X,
        "symbol_count": symbol_count
    })
    .to_string();

    let mut python_call = Command::new("python3")
        .arg("src/symm_break.py")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Failed to start Python script");
    let stdin = python_call.stdin.as_mut().expect("Failed to open stdin");
    stdin
        .write_all(json_payload.as_bytes())
        .expect("Failed to write to stdin");
    let output = python_call
        .wait_with_output()
        .expect("Failed to read output from Python script");
    let dimacs = String::from_utf8(output.stdout).expect("Python output not valid UTF-8");
    dimacs
        .lines() // parse dimacs
        .filter(|line| !line.starts_with('p') && !line.is_empty())
        .map(|line| {
            line.split_whitespace()
                .filter_map(|s| {
                    let value = s.parse::<i32>().expect("Failed to parse DIMACS line");
                    if value != 0 {
                        Some(value)
                    } else {
                        None // Ignore nonpositive values
                    }
                })
                .collect()
        })
        .collect::<Vec<Vec<i32>>>()
}

pub fn get_sat_precursor(deg: usize, K_size: usize, x: usize) -> SatPrecursor {
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
    let n = 2 + 2 * A_size + K_size;
    let A = 2..(2 + A_size);
    let B = (2 + A_size)..(2 + 2 * A_size);
    let X = (n)..(n + x);
    let ABK = 2..(n);

    let AB_edges = iproduct!(A.clone(), B.clone()).map(|(a, b)| Edge::new(a, b));
    let X_edges = iproduct!(X.clone(), ABK)
        .chain(
            X.clone()
                .combinations_with_replacement(2)
                .map(|v| (v[0], v[1])),
        )
        .map(|(a, b)| Edge::new(a, b));
    let edges = AB_edges.chain(X_edges);

    edge_to_var.extend(edges.enumerate().map(|(i, edge)| {
        let var_index = i32::try_from(i).expect("Failed to convert index to i32") + 1; // Start variable indices from 1
        (edge, var_index)
    }));
    let edge_sets = (0..n + x)
        .combinations(5)
        .par_bridge()
        .filter_map(|set| {
            let edges = set.iter().combinations(2).map(|v| Edge::new(*v[0], *v[1]));
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

    // Create symmetry breaking clauses
    let symmetry_clauses = get_symm_break_clauses(n, x, &edge_to_var);
    SatPrecursor {
        edge_to_var,
        edge_sets,
        symmetry_clauses,
    }
}

#[allow(dead_code)]
fn regular_clauses(
    num_missing_edges: usize,
    check_edge_len: usize,
    clause_edges: &[Edge],
    edge_to_var: &HashMap<Edge, i32>,
) -> Vec<Vec<i32>> {
    //
    // Creates clauses to avoid the forbidden subgraphs J5, K5-bar in the regular case.
    //
    let mut clauses = Vec::new();
    // clauses for independent sets of size 5
    if num_missing_edges == check_edge_len {
        // all edges are missing
        let k5bar_clause: Vec<i32> = clause_edges.iter().map(|edge| edge_to_var[edge]).collect();
        clauses.push(k5bar_clause);
    }
    // clauses for cliques of size 5
    else if num_missing_edges <= 1 {
        let k5_clause: Vec<i32> = clause_edges.iter().map(|edge| -edge_to_var[edge]).collect();
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
    clauses
}

#[allow(dead_code)]
fn complement_clauses(
    num_missing_edges: usize,
    check_edge_len: usize,
    clause_edges: &[Edge],
    edge_to_var: &HashMap<Edge, i32>,
) -> Vec<Vec<i32>> {
    //
    // Creates clauses to avoid the forbidden subgraphs K5, J5-bar in the complement case.
    //
    let mut clauses = Vec::new();
    // clauses for cliques of size 5
    if num_missing_edges == 0 {
        // all edges are present
        let k5_clause: Vec<i32> = clause_edges.iter().map(|edge| -edge_to_var[edge]).collect();
        clauses.push(k5_clause);
    }
    // clauses for independent sets of size 5
    if num_missing_edges >= check_edge_len - 1 {
        let k5bar_clause: Vec<i32> = clause_edges.iter().map(|edge| edge_to_var[edge]).collect();
        clauses.push(k5bar_clause);
    }
    // clauses for independent sets of size 5 plus an edge
    if num_missing_edges == check_edge_len {
        // all edges are missing
        for edge in clause_edges {
            let j5_clause: Vec<i32> = clause_edges
                .iter()
                .filter(|&edge2| edge2 != edge)
                .map(|edge| edge_to_var[edge])
                .collect();
            clauses.push(j5_clause);
        }
    }
    clauses
}

fn get_clauses(graph: &Graph, sat_precursor: &SatPrecursor) -> Vec<Vec<i32>> {
    //
    // This function creates the clauses for the SAT problem based on the graph and the sat_precursor.
    // These clauses ensure that the graph avoids the desired forbidden subgraphs,
    // either J5, K5-bar in the regular case, or K5, J5-bar in the complement case.
    //
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let edge_to_var = &sat_precursor.edge_to_var;

    for (check_edges, clause_edges) in &sat_precursor.edge_sets {
        let num_missing_edges = check_edges
            .iter()
            .filter(|&&edge| !graph.has_edge(edge))
            .count();

        #[cfg(feature = "regular")]
        {
            let regular_clauses = regular_clauses(
                num_missing_edges,
                check_edges.len(),
                clause_edges,
                edge_to_var,
            );
            clauses.extend(regular_clauses);
        }
        #[cfg(feature = "complement")]
        {
            let complement_clauses = complement_clauses(
                num_missing_edges,
                check_edges.len(),
                clause_edges,
                edge_to_var,
            );
            clauses.extend(complement_clauses);
        }
    }
    clauses.extend(sat_precursor.symmetry_clauses.iter().cloned());
    clauses
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
