// pasting is the process of making the gluing problems by pasting together
// two pointed graphs A, B along a shared subgraph K

use crate::graph::{BitSet, Edge, Graph, Subgraph};
use std::collections::HashMap;
use itertools::Itertools;


/*
pub fn get_all_pastes(infile: &str, outdir: &str, complement: bool) -> Result<(), Infallible> {
    let graphs = todo!();
    println!("Read {} graphs from {}", graphs.len(), infile);
    println!();
    let start = std::time::Instant::now();
    let mut K_class_to_graphs: HashMap<CanonLabeling, Vec<(u8, &Graph)>> = HashMap::new();

    for graph in &graphs {
        for v in 0..graph.num_vertices() {
            let K_bits: BitSet = graph.neighbor_set(v);
            let K = petgraph_from_graph(graph, K_bits);
            let K_class = CanonLabeling::from_graph(&K, 0, 0);
            K_class_to_graphs.entry(K_class)
                .or_insert_with(Vec::new)
                .push((v, graph));
        }
    }

    let elapsed = start.elapsed();
    println!("Found {} K_classes in {} graphs in {:?}", K_class_to_graphs.len(), graphs.len(), elapsed);
    println!();

    let start2 = std::time::Instant::now();
    for (K_class, gs) in K_class_to_graphs {
        let mut num_pastes: u128 = 0;
        println!("Processing {} graphs in K_class {:?}", gs.len(), K_class);
        let outfile = format!("{}/K_class_{}.g6", outdir, K_class);

        let file = File::create(&outfile).expect("Failed to create/truncate output file");
        let mut writer = BufWriter::new(file);

        gs.iter()
            .for_each(|(a, G)|{
                let pastes = gs.par_iter()
                    .flat_map(|(b, H)| {
                        try_paste_together(*a, G, *b, H, complement)
                    })
                    .collect::<Vec<_>>();
                num_pastes += pastes.len() as u128;
                write_graphs_to_buffer(&pastes, &mut writer);
            });
        writer.flush().expect("Failed to flush buffer");
        println!("Processed K_class {} with {} pastes", K_class, num_pastes);
    }
    let elapsed2 = start2.elapsed();
    println!("Processed all K_classes in {:?}", elapsed2);
    Ok(())
}
*/

fn get_k_mappings<'a>(
    K1: &'a Subgraph,
    K2: &'a Subgraph,
) -> impl Iterator<Item = Vec<usize>> + 'a {
    vf2::isomorphisms(K1,K2).iter()
}

fn try_paste_together(
    a: usize,
    G: &Graph,
    b: usize,
    H: &Graph,
    complement: bool,
) -> Vec<Graph> {
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

    let K1 = Subgraph{graph: &G, bitvec: G.bitset_to_vec(a_nbhd)};
    let K2 = Subgraph{graph: &H, bitvec: H.bitset_to_vec(b_nbhd)};

    get_k_mappings(&K1, &K2)
        .map(|mapping| {
            let mut F_copy = F.clone();
            for &v in B.iter() {
                let v_nbhd = H.neighbor_set(v) & b_nbhd;
                H.bitset_to_vec(v_nbhd)
                    .iter()
                    .for_each(|&u| {
                        let v_in_F = H_to_F.get(&v).expect("Vertex not found in H_to_F");
                        let u_to_G = mapping.get(u).expect("Vertex not found in mapping");
                        let u_in_F = G_to_F.get(u_to_G).expect("Vertex not found in G_to_F");
                        F_copy.add_edge(Edge(*v_in_F, *u_in_F));
                    });
            }
            F_copy
        })
        .collect::<Vec<Graph>>()
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

        let K1 = Subgraph{graph: &G, bitvec: G.bitset_to_vec(a_nbhd)};
        let K2 = Subgraph{graph: &H, bitvec: H.bitset_to_vec(b_nbhd)};
        let k_mappings: Vec<_> = get_k_mappings(&K1, &K2).collect();
        let k_mapping_count = get_k_mappings(&K1, &K2).count();
        //assert!(k_mapping_count == 2);

        get_k_mappings(&K1, &K2)
            .for_each(|mapping| {
                for (u, v) in (0..8).tuple_combinations() {
                    assert!(K1.contains_edge(u, v) == K2.contains_edge(mapping[u], mapping[v]));
                }
            });
    }
    #[test]
    fn test_mappings2() {
        for i in 1..10 {
            let G = Graph::new(vec![0; i]);
            let a_nbhd = (1 << i) - 1; // all vertices are neighbors
            let i_factorial = (1..=i as u128).product::<u128>();
            let K = Subgraph{graph: &G, bitvec: G.bitset_to_vec(a_nbhd)};
            assert!(get_k_mappings(&K, &K).count() == i_factorial as usize);
        }
    }
}