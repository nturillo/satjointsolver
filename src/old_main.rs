use std::fs::{File, OpenOptions};
use std::io::{self, BufRead, Write};
use std::path::Path;
use std::env;
use mimalloc::MiMalloc;
use itertools::Itertools;
use std::collections::HashSet;
use std::collections::HashMap;
use cadical::Solver;
use rayon::prelude::*;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    if let Ok(lines) = read_lines("./case13sort/size22.txt") {
        lines.flatten().collect::<Vec<String>>().into_par_iter().for_each(|line| {
            let graph= decode_g6(&line);
            let mut file = OpenOptions::new()
                                .write(true)
                                .append(true)
                                .open("sol_22.txt")
                                .unwrap();
                                file.write_all(((u8::from(solve(graph, 4))).to_string() + &line + "\n").as_bytes()).unwrap();
        });
    }
}

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
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

// fn compress_g6(graph: &Vec<u32>, n: usize) -> String {
//     let mut count = 0;
//     let size = (n * (n - 1)) / 2;
//     let size6 = size + (6 - size % 6) % 6;
//     let mut bit_vect = vec![0; size6];
//     for i in 0..n - 1 {
//         let pointer = 1u32 << (n - i - 2);
//         for j in 0..i + 1 {
//             bit_vect[count] = (graph[j] & pointer) >> (n - i - 2);
//             count += 1;
//         }
//     }
//     let mut string_vect = String::new();
//     string_vect.push((n + 63) as u8 as char);
//     for i in (0..size6).step_by(6) {
//         string_vect.push((63 + bit_vect[i..i + 6].into_iter().enumerate().fold(0, |acc, (j, x)| acc | x << (5 - j))) as u8 as char);
//     }
//     string_vect
// }

#[inline(always)]
fn bit_to_index(mut x: u32, n: usize) ->  HashSet<usize> {
    let num_ones = x.count_ones() as usize;
    let mut index_vect= HashSet::new();
    for _i in 0..num_ones {
        let index = x.ilog2() as usize;
        index_vect.insert(n - index - 1);
        x ^= 1 << index;
    }
    index_vect
}

fn solve(adj: Vec<u32>, x: usize) -> bool {
    let n = adj.len();
    let mut glue: HashMap<(usize, usize), usize> = HashMap::new();
    let mut ext: HashMap<(usize, usize), usize> = HashMap::new();

    let ab = (1 << (n - 1)) | (1 << (n - 2));
    let (a, b) = (bit_to_index(adj[0] & !ab, n), bit_to_index(adj[1] & !ab, n));
    let g: HashSet<&usize>  = a.difference(&b).collect(); 
    let h: HashSet<&usize> = b.difference(&a).collect();  // input graphs should this vertex order: a, b, h-vertices, g-vertices, k-vertices

    for j in 2..(n + x) {
        for i in n..(n + x) {
            if j < i {
                ext.insert((j, i), ext.len() + 1);
            }
        }
    }
    for (&i, &j) in g.iter().cartesian_product(&h) {
        glue.insert((*j, *i), glue.len() + 1 + ext.len() + 20*3);
    }
    

    let pos_k = (2..(n + x)).combinations(4);
    let pos_i = (0..(n + x)).combinations(6);
    let mut sat: Solver = Default::default();
    let file_name = "order22.cnf";
    let current_dir = env::current_dir().expect("Failed to get current directory");
    let file_path = current_dir.join(file_name);
    let _ = sat.read_dimacs(&file_path);
    for sub in pos_k {
        let edge_sub = sub.iter().combinations(2);
        let mut clause: Vec<i32> = Vec::new();
        let mut const_val = 0;
        for edge in edge_sub {
            let (&fir, &sec) = (edge[0], edge[1]);
            if h.contains(&fir) && g.contains(&sec) {
                clause.push(-TryInto::<i32>::try_into(glue[&(fir, sec)]).unwrap());
            } else if sec >= n { 
                if fir > 1 {
                    clause.push(-TryInto::<i32>::try_into(ext[&(fir, sec)]).unwrap());
                }
            } else {
                const_val += (adj[fir] >> (n - sec - 1)) & 1;
            }
        }
        if const_val as usize + clause.len() == 6 {
            sat.add_clause(clause);
        }
    }
    for sub in pos_i {
        let edge_sub = sub.iter().combinations(2);
        let mut clause: Vec<i32> = Vec::new();
        let mut const_val = 0;
        for edge in edge_sub {
            let (&fir, &sec) = (edge[0], edge[1]);
            if h.contains(&fir) && g.contains(&sec) {
                clause.push(glue[&(fir, sec)].try_into().unwrap());
            } else if sec >= n {
                if fir > 1 {
                    clause.push(ext[&(fir, sec)].try_into().unwrap());
                }
            } else {
                const_val += (adj[fir] >> (n - sec - 1)) & 1;
            }
        }
        if const_val == 0 {
            for i in 0..clause.len() {
                let mut small_clause = Vec::new();
                for (j, var) in clause.iter().enumerate() {
                    if j != i {
                        small_clause.push(*var)
                    }
                }
                sat.add_clause(small_clause);
            }
        } else if const_val == 1 {
            sat.add_clause(clause);
        }
    }
    
    sat.solve().unwrap()
    // Code for enumerating all solutions
    // let mut num = 0;
    // while sat.solve().unwrap() {
    //     let mut clause: Vec<i32> = Vec::new();
    //     let mut sol: Vec<u32> = adj.clone();
    //     sol.iter_mut().for_each(|row| *row <<= x);
    //     sol.append(&mut vec![0; x]);

    //     for (&(i, j), &var) in glue.iter() {
    //         let val = sat.value(var.try_into().unwrap()).unwrap();
    //         clause.push((1 - 2*i32::from(val)) * TryInto::<i32>::try_into(var).unwrap());
    //         sol[i] |= u32::from(val) << (n + x - j - 1);
    //         sol[j] |= u32::from(val) << (n + x - i - 1);
    //     }
    //     for (&(i, j), &var) in ext.iter() {
    //         let val = sat.value(var.try_into().unwrap()).unwrap();
    //         clause.push((1 - 2*i32::from(val)) * TryInto::<i32>::try_into(var).unwrap());
    //         sol[i] |= u32::from(val) << (n + x - j - 1);
    //         sol[j] |= u32::from(val) << (n + x - i - 1);
    //     }

    //     let mut file = OpenOptions::new()
    //     .write(true)
    //     .append(true)
    //     .open("sol_22.txt")
    //     .unwrap();
    //     file.write_all((compress_g6(&sol, sol.len()) + "\n").as_bytes()).unwrap();
        
    //     // let mut flag = false;
    //     // for sub in  (0..(n + x)).combinations(4) {
    //     //     let mut check = 0;
    //     //     for edge in sub.iter().combinations(2) {
    //     //         check += (sol[*edge[0]] >> (n + x - edge[1] - 1)) & 1;
    //     //     }
    //     //     if check == 6 {
    //     //         flag = true;
    //     //     }
    //     // }
    //     // for sub in  (0..(n + x)).combinations(6) {
    //     //     let mut check = 0;
    //     //     for edge in sub.iter().combinations(2) {
    //     //         check += (sol[*edge[0]] >> (n + x - edge[1] - 1)) & 1;
    //     //     }
    //     //     if check < 2 {
    //     //         flag = true;
    //     //     }
    //     // }
    //     // if flag {
    //     //     println!("error");
    //     // }

    //     sat.add_clause(clause);
    //     num += 1;
    // }
    // // let _ = sat.write_dimacs(Path::new("fish.txt"));
    // num
    // sat.solve().unwrap()
}