// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use z3tracer::{report::*, syntax::Term, Model, ModelConfig};

use multiset::HashMultiSet;
use petgraph::graph::Graph;
use plotters::prelude::*;
use std::{collections::*, io::Write, path::PathBuf, fs::File, io};
use structopt::StructOpt;

/// Test utility for the parsing and the analysis of Z3 log files.
#[derive(Debug, StructOpt)]
#[structopt(name = "z3tracer")]
struct Options {
    #[structopt(flatten)]
    config: ModelConfig,

    /// Print out extra debugging options
    #[structopt(long)]
    debug: bool,

    /// Shortcut for all the --plot-* options.
    #[structopt(long)]
    plot_all: bool,

    /// Output a PNG file (for each input file) to represent quantifier instantiations
    /// over time.
    #[structopt(long)]
    plot_instantiations: bool,

    /// Output a PNG file (for each input file) to represent "user" quantifier
    /// instantiations (defined based on a prefix of their name).
    #[structopt(long)]
    plot_user_instantiations: bool,

    /// Output a PNG file (for each input file) to represent backtracking (aka "scoped" computations).
    #[structopt(long)]
    plot_scopes: bool,

    /// Output a PNG file (for each input file) to represent conflicts on top of quantifier instantiations.
    #[structopt(long)]
    plot_conflicts: bool,

    /// Output a PNG file (for each input file) to represent conflicts on top of user quantifier instantiations.
    #[structopt(long)]
    plot_user_conflicts: bool,

    /// Output a PNG file (for each input file) to represent the causal graph between quantifier instantiations.
    #[structopt(long)]
    plot_instantiation_graph: bool,

    /// Output a PNG file (for each input file) to represent the causal graph between
    /// quantifier instantiations as well as conflict.
    #[structopt(long)]
    plot_instantiation_graph_with_conflicts: bool,

    /// Whether to prune nodes that are not "user" instantiations in
    /// --plot-instantiation-graph*. Note: Depending on the connectivity of the graph,
    /// this may lose transitive dependencies between user nodes.
    #[structopt(long)]
    keep_only_user_instantiations_in_graphs: bool,

    /// Use a single node for all conflicts in graph.
    #[structopt(long)]
    merge_conflicts_in_graphs: bool,

    /// How to select "user" instantiations.
    #[structopt(long, default_value = "outputbpl")]
    user_instantiation_prefix: String,

    /// How many instantiations to represent.
    #[structopt(long, default_value = "10")]
    keep_top_instantiations: usize,

    #[structopt(long, parse(from_os_str))]
    instantiation_tree: Option<PathBuf>,

    #[structopt(long, parse(from_os_str))]
    flat_instantiations: Option<PathBuf>,

    /// Path to the Z3 log files.
    #[structopt(parse(from_os_str))]
    inputs: Vec<PathBuf>,
}

// Compute top instantiated terms and retrieve the "timestamps" at which instantiations occur for each of the top terms.
fn get_instantiations(model: &Model) -> Vec<(String, Vec<usize>)> {
    IntoIterSorted::from(model.most_instantiated_terms())
        .map(|(_count, id)| {
            let mut timestamps = model
                .term_data(&id)
                .unwrap()
                .instantiation_timestamps
                .clone();
            timestamps.sort_unstable();
            let name = model.id2name(&id).unwrap_or_else(|| "??".to_string());
            (name, timestamps)
        })
        .collect()
}

fn get_dependency_graph(
    model: &Model,
    with_conflicts: bool,
    keep_only_user_instantiations: Option<&str>,
    merge_conflicts_in_graphs: bool,
) -> petgraph::Graph<String, String> {
    // Define nodes as the names of QIs (e.g. the names of quantified expressions in the source code).
    let nodes = model
        .instantiations()
        .iter()
        .filter_map(|(k, _)| {
            if model.key2name(k).is_some() {
                model.key2name(k)
            } else {
                None
            }
        })
        .collect::<HashSet<_>>();

    // Define weighted edges (counting dependencies in the original graph of QIs).
    let edges = {
        let mut map = HashMap::new();
        for (k, qi) in model.instantiations() {
            if let Some(name) = model.key2name(k) {
                let deps = map.entry(name).or_insert_with(HashMultiSet::new);
                for qik in &qi.qi_deps {
                    if let Some(n) = model.key2name(&qik.key) {
                        deps.insert(n);
                    }
                }
            }
        }
        map
    };

    // Translate the graph into `petgraph` for drawing purposes.
    let mut graph = Graph::<String, String>::new();

    let mut pg_nodes = HashMap::new();
    for node in &nodes {
        if let Some(prefix) = keep_only_user_instantiations {
            if !node.starts_with(prefix) {
                continue;
            }
        }
        let n = graph.add_node(node.to_string());
        pg_nodes.insert(node.to_string(), n);
    }

    for (n, d) in edges.iter() {
        if let Some(n) = pg_nodes.get(n) {
            for m in d.distinct_elements() {
                let c = d.count_of(m);
                if let Some(m) = pg_nodes.get(m) {
                    graph.add_edge(*n, *m, c.to_string());
                }
            }
        }
    }

    if with_conflicts {
        if merge_conflicts_in_graphs {
            // Adding one node for all conflicts.
            let n0 = graph.add_node("all conflicts".into());
            let mut outgoing = HashMultiSet::new();
            for c in model.conflicts() {
                for d in &c.qi_deps {
                    if let Some(m) = model.key2name(&d.key) {
                        outgoing.insert(m)
                    }
                }
            }
            for m in outgoing.distinct_elements() {
                let c = outgoing.count_of(m);
                if let Some(m) = pg_nodes.get(m) {
                    graph.add_edge(n0, *m, c.to_string());
                }
            }
        } else {
            // Adding conflicts separately (with multiplicities as weights)
            for c in model.conflicts() {
                let mut outgoing = HashMultiSet::new();
                for d in &c.qi_deps {
                    if let Some(m) = model.key2name(&d.key) {
                        outgoing.insert(m)
                    }
                }
                if outgoing.is_empty() {
                    // Skip dependency-less conflicts.
                    continue;
                }
                let n = graph.add_node(format!("conflict@{}", c.timestamp));
                for m in outgoing.distinct_elements() {
                    let c = outgoing.count_of(m);
                    if let Some(m) = pg_nodes.get(m) {
                        graph.add_edge(n, *m, c.to_string());
                    }
                }
            }
        }
    }
    graph
}

fn main() {
    let mut options = Options::from_args();
    if options.plot_all {
        options.plot_instantiations = true;
        options.plot_user_instantiations = true;
        options.plot_scopes = true;
        options.plot_conflicts = true;
        options.plot_user_conflicts = true;
        options.plot_instantiation_graph = true;
        options.plot_instantiation_graph_with_conflicts = true;
    }
    for input in &options.inputs {
        let file_name = input.to_str().unwrap().to_string();
        eprintln!("Processing {}", file_name);
        let model = process_file(options.config.clone(), &input).unwrap();
        eprintln!("Done processing {}", file_name);

        if options.debug {
            eprintln!("# Terms: {}", model.terms().len());
            for term in model.terms() {
                println!("Term: {:?}", term);
            }
            eprintln!("# Instantiations: {}", model.instantiations().len());
            for inst in model.instantiations() {
                println!("Instantiation: {:?}", inst);
            }
        }

        if let Some(flat) = &options.flat_instantiations {
            print_flat_instantiations(flat, &model)
                .expect("Could not write flat instantiations");

            continue;
        }

        if let Some(tree) = &options.instantiation_tree {
            print_instantiation_tree(tree, &model)
                .expect("Could not write instantiation tree");

            continue;
        }

        if !options.config.annotated_proof {
            let mut quant_costs = model.quant_costs();
            println!("Got {} costs", quant_costs.len());
            quant_costs.sort_by_key(|v| v.instantiations * v.cost);
            quant_costs.reverse();
            for cost in quant_costs {
                println!(
                    "{} created {} instantiations and cost {}",
                    cost.quant, cost.instantiations, cost.cost
                );
            }
        }

        if !options.plot_instantiations
            && !options.plot_user_instantiations
            && !options.plot_scopes
            && !options.plot_conflicts
            && !options.plot_user_conflicts
            && !options.plot_instantiation_graph
            && !options.plot_instantiation_graph_with_conflicts
        {
            continue;
        }

        let instantiations = get_instantiations(&model);
        let user_instantiations = instantiations
            .clone()
            .into_iter()
            .filter(|(n, _)| n.starts_with(&options.user_instantiation_prefix))
            .collect::<Vec<_>>();
        let conflicts = model
            .conflicts()
            .map(|c| {
                (
                    c.timestamp,
                    c.qi_deps
                        .iter()
                        .map(|k| model.key2name(&k.key).unwrap_or_else(|| "??".to_string()))
                        .collect::<BTreeSet<_>>(),
                )
            })
            .collect::<Vec<_>>();

        if options.plot_instantiations {
            let path = std::path::PathBuf::from(file_name.clone() + ".qis.png");
            eprintln!(
                "Writing instantiation charts to {}",
                path.to_str().unwrap_or("")
            );
            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_instantiations(
                root,
                &instantiations,
                "Top Quantifiers Instantiations",
                options.keep_top_instantiations,
            )
            .unwrap();
        }

        if options.plot_user_instantiations {
            let path = std::path::PathBuf::from(file_name.clone() + ".user_qis.png");
            eprintln!(
                "Writing user instantiation charts to {}",
                path.to_str().unwrap_or("")
            );
            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_instantiations(
                root,
                &user_instantiations,
                "Top User Quantifiers Instantiations",
                options.keep_top_instantiations,
            )
            .unwrap();
        }

        if options.plot_scopes {
            let path = std::path::PathBuf::from(file_name.clone() + ".scopes.png");
            eprintln!("Writing scope charts to {}", path.to_str().unwrap_or(""));

            let scopes = model
                .scopes()
                .iter()
                .map(|s| (s.timestamp, s.level))
                .collect::<Vec<(usize, u64)>>();
            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_scopes(root, &scopes, "Backtracking levels").unwrap();
        }

        if options.plot_conflicts {
            let path = std::path::PathBuf::from(file_name.clone() + ".conflicts.png");
            eprintln!("Writing conflict charts to {}", path.to_str().unwrap_or(""));

            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_instantiations_with_conflicts(
                root,
                &instantiations,
                "Top Quantifiers Instantiations + Conflicts",
                options.keep_top_instantiations,
                &conflicts,
            )
            .unwrap();
        }

        if options.plot_user_conflicts {
            let path = std::path::PathBuf::from(file_name.clone() + ".user_conflicts.png");
            eprintln!(
                "Writing user conflict charts to {}",
                path.to_str().unwrap_or("")
            );

            let backend = BitMapBackend::new(&path, (1000, 800));
            let root = backend.into_drawing_area();
            plot_instantiations_with_conflicts(
                root,
                &user_instantiations,
                "Top User Quantifiers Instantiations + Conflicts",
                options.keep_top_instantiations,
                &conflicts,
            )
            .unwrap();
        }

        let keep_only_user_instantiations = if options.keep_only_user_instantiations_in_graphs {
            Some(options.user_instantiation_prefix.as_str())
        } else {
            None
        };

        if options.plot_instantiation_graph {
            let path = std::path::PathBuf::from(file_name.clone() + ".qis_graph.dot");
            eprintln!(
                "Writing dependency graph to {}",
                path.to_str().unwrap_or("")
            );

            let g = get_dependency_graph(&model, false, keep_only_user_instantiations, false);
            let mut f = std::fs::File::create(path.clone()).unwrap();
            writeln!(f, "{}", petgraph::dot::Dot::new(&g)).unwrap();

            std::process::Command::new("dot")
                .args(&["-O", "-Tpng", path.to_str().unwrap()])
                .status()
                .expect("Error running `dot` (is graphviz installed?)");
        }

        if options.plot_instantiation_graph_with_conflicts {
            let path = std::path::PathBuf::from(file_name.clone() + ".qis_and_conflicts_graph.dot");
            eprintln!(
                "Writing dependency graph with conflicts to {}",
                path.to_str().unwrap_or("")
            );

            let g = get_dependency_graph(
                &model,
                true,
                keep_only_user_instantiations,
                options.merge_conflicts_in_graphs,
            );
            let mut f = std::fs::File::create(path.clone()).unwrap();
            writeln!(f, "{}", petgraph::dot::Dot::new(&g)).unwrap();

            std::process::Command::new("dot")
                .args(&["-O", "-Tpng", path.to_str().unwrap()])
                .status()
                .expect("Error running `dot` (is graphviz installed?)");
        }
    }
}

fn print_flat_instantiations(target: &PathBuf, model: &Model) -> io::Result<()> {
    println!("Found {} instantiations", model.instantiations().len());
    let mut builtins = 0;
    let mut file = File::create(target)?;
    for (_key, inst) in model.instantiations() {
        let qident = inst.frame.quantifier();

        if qident.is_builtin() {
            builtins += 1;
            continue;
        }

        let quantifier = model.term(qident).expect("MISSING QIDENT");

        if let Term::Quant {
            name,
            body,
            var_names: Some(var_names),
            ..
        } = quantifier {
            // Bind variable names.
            let mut venv = BTreeMap::new();
            for (i, vn) in var_names.iter().enumerate() {
                // inst.frame.terms().get(i)
                venv.insert(i as u64, vn.name.clone());
            }
            
            write!(file, "{}\n", name)?;
            write!(file, "{}\n", &model.id_to_sexp(&venv, &body).expect("Could not build body"))?;

            let terms = inst.frame.terms();

            for (i, term) in terms.iter().enumerate() {
                write!(file, "{} = {}\n", &var_names[i].name, &model.id_to_sexp(&venv, &term).expect("Could not build term"))?;
            }

            write!(file, "[end]\n")?;
        }
    }

    println!("Found {} builtins", builtins);
    Ok(())
}

fn print_instantiation_tree(target: &PathBuf, model: &Model) -> io::Result<()> {
    println!("Found {} instantiations", model.instantiations().len());
    let mut builtins = 0;
    let mut file = File::create(target)?;
    for (key, inst) in model.instantiations() {
        let qident = inst.frame.quantifier();

        if qident.is_builtin() {
            builtins += 1;
            continue;
        }

        let terms = inst.frame.terms();

        let quantifier = model.term(qident).expect("MISSING QIDENT");
        if let Term::Quant {
            name,
            var_names: Some(var_names),
            ..
        } = quantifier
        {
            write!(file, "{:?}", key)?;

            write!(file, " {} [", name)?;
            let vars = var_names
                .iter()
                .enumerate()
                .map(|(i, var)| {
                    format!(
                        "{}={}",
                        var.name.clone(),
                        model.global_id_to_sexp(&terms[i]).expect("MISSING ID")
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            write!(file, "{}]", vars)?;
            
            if let Ok(parent) = model.get_parent(qident) {
                write!(file, " {:?}", parent)?;
            }

            if name.contains("51:18!3") {
                println!("{:?} {:?}\n>{}", qident, model.scoped_term_data(qident), 
                    model.global_id_to_sexp(qident).unwrap());
            }

            write!(file, "\n")?;
        }
    }
    println!("Found {} builtins", builtins);
    Ok(())
}
