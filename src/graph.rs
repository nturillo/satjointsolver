use crate::sat::SatProblem;
use cadical::Solver;
use itertools::Itertools;
use nauty_Traces_sys::{
    densenauty, nauty_check, optionblk, statsblk, ADDONEEDGE, empty_graph, NAUTYVERSIONID,
    SETWORDSNEEDED, TRUE, WORDSIZE,
};
use rayon::iter::empty;
use std::io::{self, Write};
use std::os::raw::c_int;

#[derive(Debug, Clone)]
pub struct Graph {
    num_vertices: usize,
    // The adjacency matrix is represented as a vector of BitSet, where each BitSet represents
    // the neighbors of a vertex. The i-th BitSet has a bit set for each vertex j such that there is an edge from i to j.
    adjacency_matrix: Vec<BitSet>,
}
impl Graph {
    pub fn new(adjacency_matrix: Vec<BitSet>) -> Self {
        let num_vertices = adjacency_matrix.len();
        Graph {
            num_vertices,
            adjacency_matrix,
        }
    }
    pub fn with_capacity(num_vertices: usize) -> Self {
        let adjacency_matrix = vec![0; num_vertices];
        Graph {
            num_vertices,
            adjacency_matrix
        }
    }
    pub fn has_edge(&self, edge: Edge) -> bool {
        self.adjacency_matrix[edge.0] & self.get_bit(edge.1) != 0
    }
    pub fn add_edge(&mut self, edge: Edge) {
        self.adjacency_matrix[edge.0] |= self.get_bit(edge.1);
        self.adjacency_matrix[edge.1] |= self.get_bit(edge.0);
    }
    pub fn neighbor_set(&self, u: usize) -> BitSet {
        self.adjacency_matrix[u]
    }
    pub fn anti_neighbor_set (&self, i: usize) -> BitSet {
        !self.get_bit(i) & !self.neighbor_set(i) & ((1 << self.num_vertices()) - 1)
    }
    pub fn bitset_to_vec(&self, bitset: BitSet) -> Vec<usize> {
        (0..self.num_vertices()).filter(|&i| (bitset & self.get_bit(i)) != 0).collect()
    }
    pub fn num_vertices(&self) -> usize {
        self.num_vertices
    }
    pub fn get_bit(&self, i: usize) -> BitSet {
        1 << (self.num_vertices() - i - 1) as BitSet
    }
    pub fn canon_string(&self) -> String {
        // invoke nauty to get canonical labeling
        let mut options = optionblk::default();
        options.getcanon = TRUE;
        let mut stats = statsblk::default();
        let n = self.num_vertices();
        let m = SETWORDSNEEDED(n);

        unsafe {
            nauty_check(WORDSIZE as c_int, m as c_int, n as c_int, NAUTYVERSIONID as c_int);
        }

        let mut g = empty_graph(m, n);
        (0..n).tuple_combinations()
            .filter(|(v, w)| self.has_edge(Edge(*v, *w)))
            .for_each(|(v, w)| {
                ADDONEEDGE(&mut g, v, w, m);
            });
        let mut lab = vec![0; n];
        let mut ptn = vec![0; n];
        let mut orbits = vec![0; n];
        let mut g_canon = empty_graph(m, n);
        unsafe {
                densenauty(
                    g.as_mut_ptr(),
                    lab.as_mut_ptr(),
                    ptn.as_mut_ptr(),
                    orbits.as_mut_ptr(),
                    &mut options,
                    &mut stats,
                    m as c_int,
                    n as c_int,
                    g_canon.as_mut_ptr(),
                );
            }
        let canon_graph = Graph::new(
            (0..n).map(|i| g_canon[i] as BitSet).collect()
        );
        graph_to_g6(&canon_graph)
    }
    pub fn orbit_representatives(&self) -> Vec<usize> {
        let mut options = optionblk::default();
        let mut stats = statsblk::default();
        let n = self.num_vertices();
        let m = SETWORDSNEEDED(n);
        unsafe {
            nauty_check(WORDSIZE as c_int, m as c_int, n as c_int, NAUTYVERSIONID as c_int);
        }
        let mut lab = vec![0; n];
        let mut ptn = vec![0; n];
        let mut orbits = vec![0; n];
        let mut g = empty_graph(m, n);
        (0..n).tuple_combinations()
            .filter(|(v, w)| self.has_edge(Edge(*v, *w)))
            .for_each(|(v, w)| {
                ADDONEEDGE(&mut g, v, w, m);
            });
        unsafe {
            densenauty(
                g.as_mut_ptr(),
                lab.as_mut_ptr(),
                ptn.as_mut_ptr(),
                orbits.as_mut_ptr(),
                &mut options,
                &mut stats,
                m as c_int,
                n as c_int,
                std::ptr::null_mut(),
            );
        }
        // create a hash from the vec of orbits
        std::collections::HashSet::<usize>::from_iter(
            orbits.into_iter().map(|x| x as usize)
        ).into_iter().collect::<Vec<usize>>()
    }
    pub fn extend(&self, x: usize) -> Graph {
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
    pub fn from_subgraph(&self, subset: BitSet) -> Graph {
        let mut res = Graph::with_capacity(subset.count_ones() as usize);
        let potential_edges = self
            .bitset_to_vec(subset)
            .into_iter()
            .combinations(2)
            .map(|v| Edge(v[0], v[1]));
        for e in potential_edges {
            if self.has_edge(e) { res.add_edge(e); }
        }
        res
    }
    pub fn from_graph6(g6_str: &String) -> Self {
        Graph::new(decode_g6(g6_str))
    }
    pub fn from_sat_sol(
        unglued_graph: &Graph,
        sat_problem: &SatProblem,
        solver: &Solver,
    ) -> Option<Graph> {
        if !solver.status().expect("Failed to get solver status") {
            return None;
        }

        let mut glued_graph = unglued_graph.clone();
        let edge_to_var = sat_problem.edge_to_var;
        // iterate over the edges in the SAT problem
        for (edge, var_index) in edge_to_var {
            if solver
                .value(i32::try_from(*var_index).expect("Failed to convert var_index"))
                .expect("Failed to get variable value")
            {
                glued_graph.add_edge(*edge);
            }
        }

        Some(glued_graph)
    }
}

pub struct Subgraph<'a> {
    pub graph: &'a Graph,
    pub bitvec: Vec<usize>
}
// implement vf2's trait (i.e. interface) for subgraphs to be able to use its
// isomorphism iter
impl <'a> vf2::Graph for Subgraph<'a> {
    type EdgeLabel = ();
    type NodeLabel = usize;

    fn is_directed(&self) -> bool { false }
    fn node_count(&self) -> usize { self.bitvec.len() }
    fn contains_edge(&self, source: usize, target: usize) -> bool {
        let edge = Edge(self.bitvec[source], self.bitvec[target]);
        self.graph.has_edge(edge)
    }
    fn edge_label(&self, source: vf2::NodeIndex, target: vf2::NodeIndex) -> Option<&Self::EdgeLabel> {
        if self.contains_edge(source, target) { return Some(&()) }
        None
    }
    fn neighbors(&self, node: vf2::NodeIndex, direction: vf2::Direction) -> impl Iterator<Item = vf2::NodeIndex> {
        let neighborset = self.graph.neighbor_set(self.bitvec[node]);
        let mut res: Vec<usize> = vec![];
        for (i, v) in self.bitvec.iter().enumerate() {
            let bit = self.graph.get_bit(*v);
            if (bit & neighborset) == bit {
                res.push(i);
            }
        }
        res.into_iter()
    }
    fn node_label(&self, node: vf2::NodeIndex) -> Option<&Self::NodeLabel> {
        Some(&self.bitvec[node])
    }
}

pub type BitSet = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Edge(pub usize, pub usize);

impl Edge {
    pub fn new(a: usize, b: usize) -> Self {
        if a <= b { Edge(a, b) } else { Edge(b, a) }
    }
}

pub fn decode_g6(line: &String) -> Vec<u32> {
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

pub fn graph_to_g6(graph: &Graph) -> String {
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

#[cfg(test)]
mod tests {
    use vf2::Graph as _;

    use super::*;

    #[test]
    fn test_subgraph() {
        let mut G = Graph::with_capacity(4);
        let a_nbhd = 0b1111;
        G.add_edge(Edge(0, 1));
        G.add_edge(Edge(2, 3));
        let K = Subgraph{graph: &G, bitvec: G.bitset_to_vec(a_nbhd)};

        assert!(K.node_count() == 4);
        (0..4).combinations(2).for_each(
            |edge_vec| {
                let edge = Edge(edge_vec[0], edge_vec[1]);
                assert!(
                    K.contains_edge(edge_vec[0], edge_vec[1]) == G.has_edge(edge)
                );
            }
        );

        assert!(K.neighbors(0, vf2::Direction::Outgoing).collect::<Vec<_>>() == vec![1]);
        assert!(K.neighbors(1, vf2::Direction::Outgoing).collect::<Vec<_>>() == vec![0]);
        assert!(K.neighbors(2, vf2::Direction::Outgoing).collect::<Vec<_>>() == vec![3]);
        assert!(K.neighbors(3, vf2::Direction::Outgoing).collect::<Vec<_>>() == vec![2]);
 
    }
}