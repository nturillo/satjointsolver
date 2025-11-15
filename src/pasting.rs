// pasting is the process of making the gluing problems by pasting together
// two pointed graphs A, B along a shared subgraph K

use crate::graph::{Edge, Graph, Subgraph, read_graphs_from_file, setword};
use core::num;
use std::collections::HashMap;
use itertools::Itertools;
use std::io::{BufRead, Write};
use std::fs::File;
use std::io::BufWriter;
use rayon::prelude::*;

struct PointedGraph<'a> {
    graph: &'a Graph,
    point: usize, // marked vertex in graph; representative from its orbit
    K_to_canon: Vec<usize>, // mapping from K in graph to canonical K
    canon_to_K: Vec<usize>, // mapping from canonical K to K in graph
}

pub fn run_pasting(infile: &str, outdir: &str, dry: bool) -> Result<(), Box<dyn std::error::Error + 'static>> {
    // bool - if true, don't actual calculate the pastes, just count the number of them per K isomorphism class

    let graphs = read_graphs_from_file(infile);
    let start = std::time::Instant::now();
    let mut K_class_to_graphs: HashMap<String, Vec<PointedGraph>> = HashMap::new();
    let mut K_class_to_num_graphs: HashMap<String, u128> = HashMap::new();

    for graph in &graphs {
        let orbit_reps = graph.orbit_representatives();
        for v in orbit_reps {
            let K_bits: setword = graph.neighbor_set(v);
            let K_vec = graph.bitset_to_vec(K_bits);
            let K_canon= graph.canon(&K_vec);
            let K_string = K_canon.to_g6();
            let K_to_canon= get_k_mappings(
                // map from graph's K to canonical K
                &Subgraph::new(graph, K_vec.clone()),
                &Subgraph::new(&K_canon, K_canon.bitset_to_vec(K_canon.get_all_bits()))
            ).next().unwrap();
            let canon_to_K = get_k_mappings(
                &Subgraph::new(&K_canon, K_canon.bitset_to_vec(K_canon.get_all_bits())),
                &Subgraph::new(graph, K_vec.clone())
            ).next().unwrap();
            let pointed_graph = PointedGraph {
                graph,
                point: v,
                K_to_canon,
                canon_to_K,
            };
            K_class_to_graphs.entry(K_string)
                .or_insert_with(Vec::new)
                .push(pointed_graph);
        }
    }

    let elapsed = start.elapsed();
    println!("Found {} K_classes in {} graphs in {:?}", K_class_to_graphs.len(), graphs.len(), elapsed);
    println!();

    let start2 = std::time::Instant::now();
    let K_class_file  = format!("{}/K_classes.txt", outdir);
    let mut kclass_writer: Option<BufWriter<File>> = None;
    if !dry {
        kclass_writer = Some(BufWriter::new(File::create(&K_class_file).expect("Failed to create K_class file")));
    }
    for (i, (K_class, gs)) in K_class_to_graphs.iter().enumerate() {
        let mut num_pastes_actual: u128 = 0;
        println!("Processing {} graphs in K_class {:?}, number {}", gs.len(), K_class, i);

        let K_canon = Graph::from_graph6(&K_class);
        let K_automorphisms = get_k_mappings(
            &Subgraph::new(&K_canon, K_canon.bitset_to_vec(K_canon.get_all_bits())),
            &Subgraph::new(&K_canon, K_canon.bitset_to_vec(K_canon.get_all_bits()))
        ).collect::<Vec<_>>();

        let num_pastes = (gs.len() * gs.len() * K_automorphisms.len()) as u128;
        K_class_to_num_graphs.insert(K_class.to_string(), num_pastes);

        if !dry {
        if let Some(ref mut w) = kclass_writer {
            writeln!(w, "{} {}", i, K_class).expect("Failed to write to K_class file");
        }
        let outfile = format!("{}/K_class_{}.g6", outdir, i);
        let file = File::create(&outfile).expect("Failed to create/truncate output file");
        let mut writer = BufWriter::new(file);

        gs.iter()
            .for_each(|G|{
                let pastes = gs.par_iter()
                    .flat_map(|H| {
                        try_paste_together(G, H, &K_automorphisms)
                    })
                    .collect::<Vec<_>>();
                num_pastes_actual += pastes.len() as u128;
                pastes.iter()
                    .for_each(|pastes| {
                        let g6_str = pastes.to_g6();
                        writeln!(writer, "{}", g6_str).expect("Failed to write to output file");
                    });
            });
        writer.flush().expect("Failed to flush buffer");
        }

        #[cfg(debug_assertions)]
        {
            assert!((num_pastes == num_pastes_actual) | dry);
        }

        println!("Processed K_class {} with {} pastes", K_class, num_pastes);
    }
    let elapsed2 = start2.elapsed();
    println!("Processed all K_classes in {:?}", elapsed2);

    if dry {
        print_paste_stats(&K_class_to_num_graphs);
    }
    Ok(())
}

fn print_paste_stats(map: &HashMap<String, u128>) {
    let total: u128 = map.values().sum();
    // Create a vector of (key, value) pairs and sort by value descending
    let mut items: Vec<(&String, &u128)> = map.iter().collect();
    items.sort_by(|a, b| b.1.cmp(a.1)); // sort by value descending

    // Print sorted list with percentages
    println!();
    for (key, value) in items {
        let percent = (*value as f64 / total as f64) * 100.0;
        println!("K_class: {:<10} {:>5} ({:>5.2}%)", key, value, percent);
    }
    println!("Total: {},", total);
}

fn get_k_mappings<'a>(
    K1: &'a Subgraph,
    K2: &'a Subgraph,
) -> impl Iterator<Item = Vec<usize>> + 'a {
    vf2::isomorphisms(K1,K2).iter()
        .map(|mapping| {
            let mut iso = vec![0; K1.graph.num_vertices()];
            mapping.iter().enumerate()
                .for_each(|(i, &v)| {
                    iso[K1.bitvec[i]] = K2.bitvec[v];
                });
            iso
        })
}

fn try_paste_together(
    G_pointed: &PointedGraph,
    H_pointed: &PointedGraph,
    K_automorphisms: &Vec<Vec<usize>>,
) -> Vec<Graph> {
    let G = G_pointed.graph;
    let H = H_pointed.graph;
    let a = G_pointed.point;
    let b = H_pointed.point;

    let degree = G.num_vertices();
    let a_nbhd = G.neighbor_set(a);
    let b_nbhd = H.neighbor_set(b);
    let K_in_G = G.bitset_to_vec(a_nbhd);
    let K_size = K_in_G.len();
    let A = G.bitset_to_vec(G.anti_neighbor_set(a));
    let B = H.bitset_to_vec(H.anti_neighbor_set(b));

    let F_size: usize = 2*degree as usize - K_size;
    let mut F = Graph::new(vec![0; F_size]);

    let mut G_to_F: HashMap<usize, usize> = HashMap::new();
    let mut H_to_F: HashMap<usize, usize> = HashMap::new();
    G_to_F.insert(a, 0);
    H_to_F.insert(b, 1);
    G_to_F.extend(A.iter().enumerate().map(|(i, &v)| (v, i + 2)));
    H_to_F.extend(B.iter().enumerate().map(|(i, &v)| (v, i + 2 + A.len())));
    G_to_F.extend(
        K_in_G.iter().enumerate().map(|(i, &v)| (v, i + 2 + A.len() + B.len()))
    );

    assert!(2 + A.len() + B.len() + K_size == F_size);

    F.add_edge(Edge(0, 1)); // (a,b)
    for (u, v) in (0..G.num_vertices()).tuple_combinations() {
        // add edges from G
        if G.has_edge(Edge(u, v)) {
            F.add_edge(Edge(G_to_F[&u], G_to_F[&v]));
        }
    }
    for v in K_in_G.iter() {
        F.add_edge(Edge(G_to_F[&v], 1)); // K vertices connected to b
    }
    for (&u, &v) in B.iter().tuple_combinations() {
        // add edges within B
        if H.has_edge(Edge(u, v)) {
            F.add_edge(Edge(H_to_F[&u], H_to_F[&v]));
        }
    }
    for v in B.iter() {
        F.add_edge(Edge(0, H_to_F[&v])); // a connected to all vertices in B
    }
    for v in A.iter() {
        F.add_edge(Edge(1, G_to_F[&v])); // b connected to all vertices in A
    }

    let K1_bitvec = G.bitset_to_vec(a_nbhd);
    let K2_bitvec = H.bitset_to_vec(b_nbhd);
    let K1 = Subgraph::new(&G, K1_bitvec);
    let K2 = Subgraph::new(&H, K2_bitvec);

    K_automorphisms.iter()
        .map(|mapping| {
            let mut F_copy = F.clone();
            for &v in B.iter() {
                let v_nbhd = H.neighbor_set(v) & b_nbhd;
                let v_in_F = H_to_F.get(&v).expect("Vertex not found in H_to_F");
                H.bitset_to_vec(v_nbhd)
                    .iter()
                    .for_each(|&u| {
                        let u_to_G = G_pointed.canon_to_K[mapping[H_pointed.K_to_canon[u]]];
                        let u_in_F = G_to_F.get(&u_to_G).expect("Vertex not found in G_to_F");
                        F_copy.add_edge(Edge(*v_in_F, *u_in_F));
                    });
            }
            F_copy
        })
        .collect::<Vec<Graph>>()
}

fn read_graphs_and_orbits_from_file(infile: &str) -> Vec<(Graph, Vec<usize>)> {
    // each line of the file is
    // graph6_string orbit_rep_1 orbit_rep_2 ... orbit_rep_k
    let path = std::path::Path::new(infile);
    let file = std::fs::File::open(&path).expect("Failed to open input file");
    let reader = std::io::BufReader::new(file);
    let mut graphs_with_orbits: Vec<(Graph, Vec<usize>)> = Vec::new();
    for line in reader.lines() {
        let line = line.expect("Failed to read line from input file");
        let mut parts = line.split_whitespace();
        if let Some(g6_str) = parts.next() {
            let g = Graph::from_graph6(&g6_str.to_string());
            let orbit: Vec<usize> = parts
                .map(|s| s.parse::<usize>().expect("Failed to parse orbit representative"))
                .collect();
            graphs_with_orbits.push((g, orbit));
        }
    }
    graphs_with_orbits
}

#[cfg(test)]
mod tests {
    use vf2::Graph as _;

    use super::*; // This allows you to access functions/types from the outer module.

    #[test]
    fn test_mappings() {
        let mut G = Graph::with_capacity(4);
        let a_nbhd = 0b1111;
        G.add_edge(Edge(0, 2));
        G.add_edge(Edge(1, 2));
        G.add_edge(Edge(2, 3));

        let H = G.clone();
        let b_nbhd = a_nbhd.clone();

        let K1 = Subgraph::new(&G, G.bitset_to_vec(a_nbhd));
        let K2 = Subgraph::new(&H, H.bitset_to_vec(b_nbhd));
        let k_mapping_count = get_k_mappings(&K1, &K2).count();
        assert!(k_mapping_count == 6);

        get_k_mappings(&K1, &K2)
            .for_each(|mapping| {
                for (u, v) in (0..4).tuple_combinations() {
                    assert!(K1.contains_edge(u, v) == K2.contains_edge(mapping[u], mapping[v]));
                }
            });
    }
    #[test]
    fn test_mappings2() {
        for i in 1..10 {
            let G = Graph::new(vec![0; i]);
            let a_nbhd = (1 << i) - 1;
            let i_factorial = (1..=i as u128).product::<u128>();
            let K = Subgraph::new(&G, G.bitset_to_vec(a_nbhd));
            assert!(get_k_mappings(&K, &K).count() == i_factorial as usize);
        }
    }
}
