use crate::graph::*;
use std::collections::HashMap;
use serde_json::json;
use std::process::{Command, Stdio};
use itertools::{Itertools, iproduct};
use rayon::prelude::*;
use std::io::{Write};

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