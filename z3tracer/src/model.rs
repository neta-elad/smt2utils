// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use once_cell::sync::Lazy;
use petgraph::graph::Graph;
use petgraph::visit::DfsPostOrder;
use petgraph::Direction;
use smt2parser::concrete::Symbol;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet};
use std::fmt::Write;
use structopt::StructOpt;
use std::hash::{Hasher, Hash};

use crate::{
    error::{RawError, RawResult, Result},
    lexer::Lexer,
    parser::{LogVisitor, Parser, ParserConfig},
    syntax::{
        Equality, Ident, Literal, MatchedTerm, Meaning, QiFrame, QiInstance, QiKey, Term, VarName,
        Visitor
    },
};

// https://github.com/TeXitoi/structopt/issues/333
#[cfg_attr(not(doc), allow(missing_docs))]
#[cfg_attr(doc, doc = "Configuration for the analysis of Z3 traces.")]
#[derive(Debug, Default, Clone, StructOpt)]
pub struct ModelConfig {
    #[structopt(flatten)]
    pub parser_config: ParserConfig,

    /// Whether to log quantifier instantiations (QIs).
    #[structopt(long)]
    pub display_qi_logs: bool,

    /// Whether to show detailed instantiations
    #[structopt(long)]
    pub detailed_instantiations: bool,

    /// Whether to show annotated proof to find least instantiations
    #[structopt(long)]
    pub annotated_proof: bool,

    /// Whether to display variable instantiations in QIs
    #[structopt(long)]
    pub with_qi_variables: bool,

    /// Whether to display triggers in QIs.
    #[structopt(long)]
    pub with_qi_triggers: bool,

    /// Whether to display terms produced by QIs.
    #[structopt(long)]
    pub with_qi_produced_terms: bool,

    /// Whether to display terms used by QIs.
    #[structopt(long)]
    pub with_qi_used_terms: bool,

    /// Whether to log term equalities.
    #[structopt(long)]
    pub log_term_equalities: bool,

    /// Whether to log term equalities (internal loop).
    #[structopt(long)]
    pub log_internal_term_equalities: bool,

    /// Whether to run consistency checks for identifiers, equations, etc.
    #[structopt(long)]
    pub skip_log_consistency_checks: bool,

    #[structopt(long)]
    pub detailed_skolemization: bool,
}

/// Information on a term in the model.
#[derive(Debug, Clone)]
pub struct TermData {
    /// Term definition.
    pub term: Term,
    /// Known instantiations (applicable when `term` is a quantified expression).
    pub instantiations: Vec<QiKey>,
    /// Timestamps (line numbers in Z3 logs) of instantiations.
    pub instantiation_timestamps: Vec<usize>,
    /// Track the relative creation time of this term. Currently, this is the line
    /// number in the Z3 log.
    pub timestamp: usize,
}

/// Scoped information on a term.
#[derive(Debug, Default, Clone)]
pub struct ScopedTermData {
    /// QI that made this term an active "enode", if any.
    pub enode_qi: Option<QiRef>,
    /// Truth assignment (applicable when the term is a boolean formula).
    pub assignment: Option<Assignment>,
    /// First known proof of this term in the current backtracking
    /// stack (applicable when the term is a boolean formula).
    pub proof: Option<ProofRef>,
    /// Tentative root for the term's equality class. `None` iff the term is its own root.
    pub eq_class: Option<Ident>,
    /// Dependencies to QI keys (when the term is not a proof, this represents the
    /// requirements for equality to the current E-class representant).
    pub qi_deps: BTreeSet<QiRef>,
    /// Temporary data reflecting dependencies to a `quant-inst` proof term (same use case
    /// as qi_deps). When the current scope is finalized, proof_deps are revisited
    /// to add the corresponding qi_deps. Then, this field is cleared. (This whole
    /// hack is needed because we learn the QI key of `quant-inst` proof term after they
    /// are used.)
    proof_deps: BTreeSet<ProofRef>,
}

/// Information on a truth assignment.
#[derive(Debug, Clone)]
pub struct Assignment {
    /// Value.
    pub sign: bool,
    /// Relative creation time (currently, the line number in the Z3 log).
    pub timestamp: usize,
    /// Scope in which the assignment was made.
    pub scope_index: usize,
}

/// Information on justifications by proof terms.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct ProofRef {
    /// Proof term id.
    pub id: Ident,
    /// Scope in which the proof was made.
    pub scope_index: usize,
}

/// Information on a Quantifier Instantiation.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct QiRef {
    /// Key of the QI
    pub key: QiKey,
    /// Scope in which the QI was made.
    pub scope_index: usize,
}

/// Information on a conflict.
#[derive(Debug, Clone)]
pub struct Conflict {
    /// The conflict clause that was proven.
    pub lits: Vec<Literal>,
    /// Relative creation time (currently, the line number in the Z3 log).
    pub timestamp: usize,
    /// Dependencies to QI keys (see ScopedTermData).
    pub qi_deps: BTreeSet<QiRef>,
    /// Temporary data reflecting dependencies to a `quant-inst` proof term (idem).
    proof_deps: BTreeSet<ProofRef>,
}

/// Information on a scope.
#[derive(Debug, Default, Clone)]
pub struct Scope {
    /// Start time.
    pub timestamp: usize,
    /// Level.
    pub level: u64,
    /// Index of the parent scope in the model.
    pub parent_index: Option<usize>,
    /// Scoped data on terms.
    pub terms: BTreeMap<Ident, ScopedTermData>,
    /// Conflict.
    pub conflict: Option<Conflict>,
    /// Track the last proof of the scope. (Used to explain the conflict.)
    pub last_proof: Option<Ident>,
    /// QIs that happened during this scope. (Used to resolve proof_deps)
    pub instantiations: Vec<QiKey>,
    /// Whether equality pointers needs consolidation in this scope.
    needs_consolidation: bool,
}

/// Information on a QI instance that is pending (i.e. waiting for
/// `[end-instance]`).
#[derive(Debug, Clone)]
pub struct PendingQiInstance {
    /// Hexadecimal key of the instantiation.
    pub key: QiKey,
    /// The QI instance.
    pub instance: QiInstance,
    /// Timestamp of the QI. Right now this is the line number in the Z3 logs where
    /// the instantiation occurs.
    pub timestamp: usize,
}

/// Quantifier instantiation data.
#[derive(Clone, Debug)]
pub struct QuantInstantiation {
    /// Main declaration as returned by `[new-match]` or `[inst-discovered]` logs.
    pub frame: QiFrame,
    /// Corresponding "instance" data collected between `[instance]` and `[end-instance]` logs.
    pub instances: Vec<QiInstance>,
    /// Dependencies to QI keys (see ScopedTermData).
    pub qi_deps: BTreeSet<QiRef>,
    /// Temporary data reflecting dependencies to a `quant-inst` proof term (idem).
    proof_deps: BTreeSet<ProofRef>,
}

/// Data about how much work a quantifier created
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
pub struct QuantCost {
    pub quant: String,
    /// Raw number of times this quantifier was instantiated
    pub instantiations: u64,
    /// Heuristic cost metric from previous Z3 profilers
    pub cost: u64,
}

/// Main state of the Z3 tracer.
#[derive(Default, Debug)]
pub struct Model {
    // Configuration.
    config: ModelConfig,
    // Terms indexed by identifier.
    terms: BTreeMap<Ident, TermData>,
    // Quantifier instantiations indexed by (hexadecimal) key.
    instantiations: BTreeMap<QiKey, QuantInstantiation>,
    // Stack of pending quantifier instantiations.
    pending_instances: Vec<PendingQiInstance>,
    // Number of Z3 log callbacks already executed.
    processed_logs: usize,
    // Scopes.
    scopes: Vec<Scope>,
    // Current scope.
    current_scope: Scope,
    // Known quantifiers
    known_quantifiers: BTreeMap<u64, QiKey>,
}

impl Assignment {
    pub fn as_str(&self) -> &'static str {
        if self.sign {
            "true"
        } else {
            "false"
        }
    }
}

fn maybe_index_min(i: Option<usize>, j: Option<usize>) -> Option<usize> {
    match (i, j) {
        (Some(i), Some(j)) => Some(std::cmp::min(i, j)),
        (Some(i), None) | (None, Some(i)) => Some(i),
        (None, None) => None,
    }
}

use std::sync::atomic::{AtomicUsize, Ordering};

static NAMED_ID: AtomicUsize = AtomicUsize::new(0);

fn next_id() -> usize {
    NAMED_ID.fetch_add(1, Ordering::SeqCst)
}

fn symbol_to_string(symbol: &str) -> String {
    if symbol == "if" {
        return "ite".to_owned()
    }

    let mut string = symbol.to_string();
    if symbol.contains("#") {
        string.insert(symbol.len(), '|');
        string.insert(0, '|');
    }

    string
}

impl Model {
    /// Build a new Z3 tracer.
    /// Experimental. Use `Model::default()` instead if possible.
    pub fn new(config: ModelConfig) -> Self {
        Self {
            config,
            ..Model::default()
        }
    }

    pub fn config(&self) -> &ModelConfig {
        &self.config
    }

    /// Process some input.
    pub fn process<R>(
        &mut self,
        path_name: Option<String>,
        input: R,
        line_count: usize,
    ) -> Result<()>
    where
        R: std::io::BufRead,
    {
        let lexer = Lexer::new(path_name, input, line_count);
        let config = self.config.parser_config.clone();
        Parser::new(config, lexer, self).parse()
    }

    /// All terms in the model.
    pub fn terms(&self) -> &BTreeMap<Ident, TermData> {
        &self.terms
    }

    /// All instantiations in the model.
    pub fn instantiations(&self) -> &BTreeMap<QiKey, QuantInstantiation> {
        &self.instantiations
    }

    pub fn known_quantifiers(&self) -> &BTreeMap<u64, QiKey> {
        &self.known_quantifiers
    }

    /// Number of Z3 logs that were processed.
    pub fn processed_logs(&self) -> usize {
        self.processed_logs
    }

    /// All (finalized) scopes in the model.
    pub fn scopes(&self) -> &Vec<Scope> {
        &self.scopes
    }

    /// The current scope in the model.
    pub fn current_scope(&self) -> &Scope {
        &self.current_scope
    }

    /// Construct a max-heap of the (most) instantiated quantified terms.
    pub fn most_instantiated_terms(&self) -> BinaryHeap<(usize, Ident)> {
        self.terms
            .iter()
            .filter_map(|(id, term)| {
                let c = term.instantiation_timestamps.len();
                if c > 0 {
                    Some((c, id.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    /// The QIs seen as explaining the successive conflicts.
    pub fn conflicts(&self) -> impl Iterator<Item = &Conflict> {
        self.scopes
            .iter()
            .filter_map(|scope| scope.conflict.as_ref())
    }

    /// Retrieve a particular term.
    pub fn term(&self, id: &Ident) -> RawResult<&Term> {
        let t = &self
            .terms
            .get(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?
            .term;
        Ok(t)
    }

    pub fn is_closed(&self, id: &Ident) -> RawResult<bool> {
        Ok(self.free_variables_missing(id, 0)? == 0)
    }

    pub fn free_variables_missing(&self, id: &Ident, variables: u64) -> RawResult<u64> {
        use Term::*;
        match self.term(id)? {
            App { args, .. } => args.iter().try_fold(0, |acc, x| {
                Ok(acc.max(self.free_variables_missing(x, variables)?))
            }),
            Var { index } => Ok(if index < &variables {
                0
            } else {
                1 + index - variables
            }),
            Quant {
                body, var_names, ..
            } => self.free_variables_missing(
                body,
                variables
                    + var_names
                        .as_ref()
                        .map(|vars| vars.len() as u64)
                        .unwrap_or(0),
            ),
            Lambda { params, body, .. } => self.free_variables_missing(body, variables + params),
            Proof { property, .. } => self.free_variables_missing(property, variables),
            Builtin { .. } => Ok(0),
        }
    }

    /// Calculate the cost imposed by each quantifier
    pub fn quant_costs(&self) -> Vec<QuantCost> {
        // Select instantations that resulted from a trigger match
        let quantifier_inst_matches =
            self.instantiations()
                .iter()
                .filter(|(_, quant_inst)| match quant_inst.frame {
                    QiFrame::Discovered { .. } => false,
                    QiFrame::NewMatch { .. } => true,
                });

        // Track which instantiations caused which enodes to appear
        let mut term_blame = HashMap::new();
        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            for inst in &quant_inst.instances {
                for node_ident in &inst.enodes {
                    term_blame.insert(node_ident, qi_key);
                }
            }
        }

        // Create a graph over QuantifierInstances,
        // where U->V if U produced an e-term that
        // triggered U
        let mut graph = Graph::<QiKey, ()>::new();
        let mut node_map = HashMap::new();
        let genv = BTreeMap::new();
        for (qi_key, qi_instance) in quantifier_inst_matches.clone() {
            let index = graph.add_node(*qi_key);
            node_map.insert(qi_key, index);

            if !self.config.detailed_instantiations {
                continue;
            }

            let quantifier = self.term(qi_instance.frame.quantifier()).unwrap();

            if let Term::Quant {
                name,
                var_names: Some(var_names),
                body,
                ..
            } = quantifier
            {
                println!(
                    "quantifier {} = {}",
                    name,
                    self.id_to_sexp(&genv, body).unwrap()
                );
                for (i, term) in qi_instance.frame.terms().iter().enumerate() {
                    let var_name = var_names.get(i).unwrap();
                    println!(
                        "qi-instance-term {} = {}",
                        var_name.name,
                        self.id_to_sexp(&genv, term).unwrap()
                    );
                }
            }
        }
        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            match &quant_inst.frame {
                QiFrame::Discovered { .. } => {
                    panic!("We filtered out all of the Discovered instances already!")
                }
                QiFrame::NewMatch { used: u, .. } => {
                    for used in u.iter() {
                        match used {
                            MatchedTerm::Trigger(t) => {
                                match term_blame.get(&t) {
                                    None => (), //println!("Nobody to blame for {:?}", t),
                                    Some(qi_responsible) =>
                                    // Quantifier instantiation that produced the triggering term
                                    {
                                        let qi_responsible_index =
                                            node_map.get(qi_responsible).unwrap();
                                        let qi_key_index = node_map.get(qi_key).unwrap();
                                        graph.add_edge(*qi_responsible_index, *qi_key_index, ());
                                        ()
                                    }
                                }
                            }
                            MatchedTerm::Equality(_t1, _t2) => (), // TODO: Unclear whether/how to use this case
                        }
                    }
                }
            }
        }

        // Compute the in-degree of each QuantifierInstance
        let mut in_degree: HashMap<QiKey, u64> = HashMap::new();
        let (some_qi_key, _) = quantifier_inst_matches.clone().next().unwrap();
        let some_index = node_map.get(&some_qi_key).unwrap();
        let mut dfs = DfsPostOrder::new(&graph, *some_index);
        for qi_root in graph.externals(Direction::Incoming) {
            // For each root of the graph
            dfs.move_to(qi_root); // Keep visit map from the previous DFS traversal
            while let Some(index) = dfs.next(&graph) {
                let qi_key = &graph[index];
                match in_degree.get_mut(&graph[index]) {
                    None => {
                        in_degree.insert(*qi_key, 1);
                        ()
                    }
                    Some(count) => *count += 1,
                }
            }
        }

        // Compute the cost of each QuantifierInstance
        //   cost(i) = 1 + sum_{(i, n) \in edges} cost(n) / in-degree(n)
        // i.e., the cost of an instance is shared equally by all
        // instances that caused it
        // See 4.3.1 of "Programming with Triggers" by Michał Moskal,
        // SMT Workshop 2009 (https://moskal.me/pdf/prtrig.pdf)
        let mut qi_cost: HashMap<QiKey, u64> = HashMap::new();
        let mut dfs = DfsPostOrder::new(&graph, *some_index);
        for qi_root in graph.externals(Direction::Incoming) {
            dfs.move_to(qi_root); // Keep visit map from the previous DFS traversal
            while let Some(index) = dfs.next(&graph) {
                let qi_key = &graph[index];
                let mut sum = 0;
                for neighbor in graph.neighbors_directed(index, Direction::Outgoing) {
                    let neighbor_key = &graph[neighbor];
                    sum +=
                        qi_cost.get(neighbor_key).unwrap() / in_degree.get(neighbor_key).unwrap();
                }
                qi_cost.insert(*qi_key, 1 + sum);
            }
        }

        // Finally, compute the cost of each quantifier
        //   = sum_{i \in instances} cost(i)
        let mut quant_cost: HashMap<String, QuantCost> = HashMap::new();
        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            let quant_id = quant_inst.frame.quantifier();
            let qi_cost = qi_cost.get(qi_key).expect(
                format!(
                    "failed to find qi_key {:?} for quant_id {:?} in qi_cost",
                    qi_key, quant_id
                )
                .as_str(),
            );
            let quant_term = self
                .term(&quant_id)
                .expect(format!("failed to find {:?} in the profiler's model", quant_id).as_str());
            let quant_name = match quant_term {
                Term::Quant { name, .. } => name,
                _ => panic!("Term for quantifier isn't a Quant"),
            };
            match quant_cost.get_mut(quant_name) {
                None => {
                    let cost = QuantCost {
                        quant: quant_name.to_string(),
                        instantiations: 1,
                        cost: *qi_cost,
                    };
                    quant_cost.insert(quant_name.clone(), cost);
                    ()
                }
                Some(cost) => {
                    cost.instantiations += 1;
                    cost.cost += qi_cost;
                    ()
                }
            }
        }
        quant_cost.into_values().collect::<Vec<_>>()
    }

    pub fn get_parent(&self, id: &Ident) -> RawResult<&QiKey> {
        let hash = self.auto_hash_term(id)?;
        self.known_quantifiers.get(&hash).ok_or(RawError::MissingIdentifier)
        // if let Some(parent) = self.known_quantifiers.get(&hash) {
        //     Ok(parent)
        // } else {
        //     let hash = self.auto_hash_term(&self.eq_class(id))?;
            
        // }
    }

    pub fn auto_hash_term(&self, id: &Ident) -> RawResult<u64> {
        let mut hasher = DefaultHasher::new();
        Ok(self.hash_term(&mut hasher, &self.eq_class(id))?.finish())
    }

    pub fn hash_term<'a, H: Hasher,>(&self, mut hasher: &'a mut H, id: &Ident) -> RawResult<&'a mut H> {
        let term = self.term(id)?;
        use Term::*;

        match term {
            App { meaning: Some(meaning), .. } => {
                meaning.hash(hasher);
            }
            App {
                name,
                args,
                ..
            } => {
                name.hash(hasher);
                for arg in args {
                    hasher = self.hash_term(hasher, arg)?;
                }
            }
            Quant { name, params, triggers, body, var_names } => {
                name.hash(hasher);
                params.hash(hasher);

                for arg in triggers {
                    hasher = self.hash_term(hasher, arg)?;
                }

                hasher = self.hash_term(hasher, body)?;

                var_names.hash(hasher);
            },
            Lambda { name, params, triggers, body } => {
                name.hash(hasher);
                params.hash(hasher);


                for arg in triggers {
                    hasher = self.hash_term(hasher, arg)?;
                }

                hasher = self.hash_term(hasher, body)?;
            },
            Proof { name, args, property } => {
                name.hash(hasher);

                for arg in args {
                    hasher = self.hash_term(hasher, arg)?;
                }

                hasher = self.hash_term(hasher, property)?;
            },
            Var { index } => {
                index.hash(hasher);
            },
            Builtin { name } => {
                name.hash(hasher);
            }
        }

        Ok(hasher)
    }

    fn find_unknown_quantifiers(&self, id: &Ident) -> RawResult<BTreeSet<u64>> {
        // println!("finding unknown {:?}", id);
        let term = self.term(id)?;
        let mut unknowns = BTreeSet::new();

        use Term::*;

        match term {
            App {
                args,
                ..
            } => {
                for arg in args {
                    unknowns.append(&mut self.find_unknown_quantifiers(arg)?);
                }
            }
            Quant { name, body, .. } => {
                if name.contains("PagedBetreeidfy.51:18!3") {
                    println!("@ {:?} {}", id, self.global_id_to_sexp(id)?);
                }

                let hash = self.auto_hash_term(id)?;

                if !self.known_quantifiers.contains_key(&hash) {
                    // println!("added {:?} as {:?}", id, hash);
                    unknowns.insert(hash);
                    unknowns.append(&mut self.find_unknown_quantifiers(body)?);
                }

                // let eq_id = self.eq_class(id);
                // let eq_hash = self.auto_hash_term(&eq_id)?;

                // if !self.known_quantifiers.contains_key(&eq_hash) {
                //     println!("added {:?} (which is eq to {:?}) as {:?}", id, eq_id, eq_hash);
                //     unknowns.insert(eq_hash);
                // }
            },
            Lambda { body, .. } => {
                unknowns.append(&mut self.find_unknown_quantifiers(body)?);
            },
            Proof { property , .. } => {
                unknowns.append(&mut self.find_unknown_quantifiers(property)?);
            },
            _ => {},
        }

        Ok(unknowns)
    }

    // Obtain a writeable entry in the current scope. The first time, this will trigger a
    // "copy-on-write" from the most recent ancestor scope that knows about `id` (if any).
    fn scoped_term_data_mut(&mut self, id: &Ident) -> &mut ScopedTermData {
        // Sadly, the borrow-checker complains about:
        //   if let Some(e) = self.current_scope.terms.get_mut(id) { return e; }
        if self.current_scope.terms.contains_key(id) {
            return self.current_scope.terms.get_mut(id).unwrap();
        }
        // For new entries, first recover data from the most recent ancestor.
        let data = self.scoped_term_data(id).clone();
        self.current_scope.terms.entry(id.clone()).or_insert(data)
    }

    // Access the most recent scoped information about `id`.
    pub fn scoped_term_data(&self, id: &Ident) -> &ScopedTermData {
        static DEFAULT: Lazy<ScopedTermData> = Lazy::new(ScopedTermData::default);
        let mut scope = &self.current_scope;
        loop {
            if let Some(data) = scope.terms.get(id) {
                return data;
            }
            match scope.parent_index {
                Some(i) => {
                    scope = &self.scopes[i];
                }
                None => {
                    return &DEFAULT;
                }
            }
        }
    }

    pub fn eq_class(&self, id: &Ident) -> Ident {
        self.scoped_term_data(id).eq_class.as_ref().unwrap_or(id).clone()
    }

    fn term_assignment(&self, id: &Ident) -> Option<&Assignment> {
        self.scoped_term_data(id).assignment.as_ref()
    }

    fn term_proof(&self, id: &Ident) -> Option<&ProofRef> {
        self.scoped_term_data(id).proof.as_ref()
    }

    fn term_equality_class(&mut self, id: &Ident) -> Ident {
        // Query and consolidate the equality class of id.
        let data = self.scoped_term_data(id);
        if data.eq_class.is_none() {
            // id is a root but somehow we never queried its class (until now).
            self.scoped_term_data_mut(id).eq_class = Some(id.clone());
            return id.clone();
        }
        let cid = data.eq_class.clone().unwrap();
        if &cid == id {
            // id == cid is still a root.
            return cid;
        }
        // Since cid != id, we have to check if cid is still a class root.
        let new_cid = self.term_equality_class(&cid);
        if new_cid == cid {
            // cid is still a root.
            return cid;
        }
        // cid is no longer a root. Need to update the entry of id and
        // re-import deps from cid.
        let cdata = self.scoped_term_data(&cid);
        let c_qi_deps = cdata.qi_deps.clone();
        let c_proof_deps = cdata.proof_deps.clone();
        self.current_scope.needs_consolidation = true;
        let data = self.scoped_term_data_mut(id);
        data.eq_class = Some(new_cid.clone());
        data.qi_deps.extend(c_qi_deps);
        data.proof_deps.extend(c_proof_deps);
        new_cid
    }

    /// Retrieve a particular term, including metadata.
    pub fn term_data(&self, id: &Ident) -> RawResult<&TermData> {
        let t = self
            .terms
            .get(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?;
        Ok(t)
    }

    pub fn global_id_to_sexp(&self, id: &Ident) -> RawResult<String> {
        let global_venv = BTreeMap::new();
        self.id_to_sexp(&global_venv, id)
    }

    /// Display a term given by id.
    pub fn id_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, id: &Ident) -> RawResult<String> {
        self.term_to_sexp(venv, self.term(id)?)
    }

    /// Display a term by id.
    pub fn term_to_sexp(&self, venv: &BTreeMap<u64, Symbol>, term: &Term) -> RawResult<String> {
        use Term::*;
        match term {
            App {
                meaning: Some(meaning),
                ..
            } => Ok(meaning.sexp.clone()),
            App {
                name,
                args,
                meaning: None,
            } => {
                if args.is_empty() {
                    Ok(symbol_to_string(name))
                } else if name == "pattern" && args.len() == 1 {
                    Ok(format!(
                        "({})",
                        args.iter()
                            .map(|id| self.id_to_sexp(venv, id))
                            .collect::<RawResult<Vec<_>>>()?
                            .join(" ")
                    ))
                } else {
                    Ok(format!(
                        "({} {})",
                        symbol_to_string(name),
                        args.iter()
                            .map(|id| self.id_to_sexp(venv, id))
                            .collect::<RawResult<Vec<_>>>()?
                            .join(" ")
                    ))
                }
            }
            Var { index } => match venv.get(index) {
                Some(s) => Ok(format!("{}", s)),
                None => Ok(format!("_{}", index)),
            },
            Quant {
                name,
                params,
                triggers,
                body,
                var_names,
            } => {
                let original_venv = venv;
                let mut venv = venv.clone();
                let vars = match var_names {
                    None => format!("{}", params),
                    Some(var_names) => {
                        for (key, value) in original_venv.iter() {
                            venv.insert(*key + var_names.len() as u64, value.clone());
                        }
                        for (i, vn) in var_names.iter().enumerate() {
                            venv.insert(i as u64, vn.name.clone());
                        }
                        var_names
                            .iter()
                            .map(|vn| format!("({} {})", vn.name, vn.sort))
                            .collect::<Vec<_>>()
                            .join(" ")
                    }
                };
                let patterns = triggers
                    .iter()
                    .map(|id| Ok(format!(":pattern {}", self.id_to_sexp(&venv, id)?)))
                    .collect::<RawResult<Vec<_>>>()?
                    .join(" ");
                Ok(format!(
                    "({} ({}) (! {} :qid {} {}))",
                    if self.config.annotated_proof {
                        "forall"
                    } else {
                        "QUANT"
                    },
                    vars,
                    self.id_to_sexp(&venv, body)?,
                    name,
                    patterns
                ))
            }
            Lambda {
                name,
                params,
                triggers,
                body,
            } => {
                let vars = format!("{}", params);
                let patterns = triggers
                    .iter()
                    .map(|id| Ok(format!(":pattern {}", self.id_to_sexp(venv, id)?)))
                    .collect::<RawResult<Vec<_>>>()?
                    .join(" ");
                Ok(format!(
                    "(LAMBDA ({}) (! {} :qid {} {}))",
                    vars,
                    self.id_to_sexp(venv, body)?,
                    name,
                    patterns
                ))
            }
            Proof {
                name,
                args,
                property,
            } => Ok(format!(
                "(PROOF {} {}{})",
                name,
                args.iter()
                    .map(|id| Ok(self.id_to_sexp(venv, id)? + " "))
                    .collect::<RawResult<Vec<_>>>()?
                    .join(""),
                self.id_to_sexp(venv, property)?,
            )),
            Builtin { name } => Ok(name.clone().unwrap_or_else(String::new)),
        }
    }

    fn append_id_subterms(&self, deps: &mut BTreeSet<Ident>, id: &Ident) -> RawResult<()> {
        deps.insert(id.clone());
        self.append_term_subterms(deps, self.term(id)?)
    }

    fn append_term_subterms(&self, deps: &mut BTreeSet<Ident>, term: &Term) -> RawResult<()> {
        term.visit(&mut |id| self.append_id_subterms(deps, id))
    }

    fn has_log_consistency_checks(&self) -> bool {
        !self.config.skip_log_consistency_checks
    }

    /// Print debug information about a quantifier instantiation.
    fn log_instance(&self, key: QiKey) -> RawResult<()> {
        let inst = self
            .instantiations
            .get(&key)
            .ok_or(RawError::InvalidInstanceKey)?;
        match &inst.frame {
            QiFrame::Discovered { .. } => (),
            QiFrame::NewMatch {
                quantifier,
                terms,
                trigger,
                used,
            } => {
                let qident = quantifier.clone();
                let quantifier = self.term(quantifier)?;
                if let Term::Quant {
                    name,
                    var_names: Some(var_names),
                    ..
                } = quantifier
                {
                    // Bind variable names.
                    let mut venv = BTreeMap::new();
                    for (i, vn) in var_names.iter().enumerate() {
                        venv.insert(i as u64, vn.name.clone());
                    }
                    if self.config.with_qi_triggers {
                        // Trim the outer "pattern" application.
                        let trigger = match self.term(trigger)? {
                            Term::App { name, args, .. }
                                if name == "pattern" && args.len() == 1 =>
                            {
                                &args[0]
                            }
                            _ => trigger,
                        };
                        println!("{} :: {{ {} }}", name, self.id_to_sexp(&venv, trigger)?);
                    } else if !self.config.annotated_proof {
                        println!("{}", name);
                    }
                    // Print instantiation terms.
                    let global_venv = BTreeMap::new();
                    if self.config.with_qi_variables {
                        for (i, vn) in var_names.iter().enumerate() {
                            println!(
                                "  {} <-- {}",
                                vn.name.clone(),
                                self.id_to_sexp(&global_venv, &terms[i])?
                            );
                        }
                        
                        println!("The quantifier was {:?} came from {:?}", 
                            &qident,
                            self.get_parent(&qident));
                    }
                    if self.config.with_qi_used_terms {
                        // Print 'used' terms.
                        for u in used {
                            use MatchedTerm::*;
                            match u {
                                Trigger(id) => {
                                    println!("  ! {}", self.id_to_sexp(&global_venv, id)?);
                                }
                                Equality(id1, id2) => {
                                    println!(
                                        "  !! {} == {}",
                                        self.id_to_sexp(&global_venv, id1)?,
                                        self.id_to_sexp(&global_venv, id2)?
                                    );
                                }
                            }
                        }
                    }
                    if self.config.annotated_proof {
                        let quantifier_name = name.as_str();
                        let mut terms_string = String::new();
                        for u in used {
                            use MatchedTerm::*;
                            match u {
                                Trigger(id) => {
                                    write!(
                                        &mut terms_string,
                                        ", {}",
                                        self.id_to_sexp(&global_venv, id)?
                                    )
                                    .expect("Could not write terms string");
                                }
                                Equality(id1, id2) => {
                                    write!(
                                        &mut terms_string,
                                        ", {} == {}",
                                        self.id_to_sexp(&global_venv, id1)?,
                                        self.id_to_sexp(&global_venv, id2)?
                                    )
                                    .expect("Could not write terms string");
                                }
                            }
                        }
                        terms_string = terms_string.replace("|", "");
                        for instance in &inst.instances {
                            let instance_term = self
                                .term(instance.term.as_ref().ok_or(RawError::MissingIdentifier)?)?;
                            if let Term::Proof { property, .. } = instance_term {
                                let p = self.term(property)?;
                                println!(
                                    "(assert (! {} :named |NN{}{}{}|))",
                                    self.term_to_sexp(&global_venv, p)?,
                                    next_id(),
                                    if quantifier_name.starts_with("|") {
                                        &quantifier_name[1..quantifier_name.len() - 2]
                                    } else {
                                        quantifier_name
                                    },
                                    terms_string
                                );
                            }
                        }
                    }
                    if self.config.with_qi_produced_terms {
                        for instance in &inst.instances {
                            // Print maximal produced terms (aka attached enodes).
                            let mut subterms = BTreeSet::new();
                            for e in instance.enodes.iter().rev() {
                                if !subterms.contains(e) {
                                    let t = self.term(e)?;
                                    self.append_term_subterms(&mut subterms, t)?;
                                    println!("  --> {}", self.term_to_sexp(&global_venv, t)?);
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn check_ident(&self, id: &Ident) -> RawResult<()> {
        if self.terms.contains_key(id) || id.is_builtin() {
            Ok(())
        } else {
            Err(RawError::UndefinedIdent(id.clone()))
        }
    }

    fn check_ident_is_not_a_proof(&self, id: &Ident) -> RawResult<()> {
        match self.term(id)? {
            Term::Proof { .. } => Err(RawError::UnexpectedProofTerm(id.clone())),
            Term::Lambda { body, .. } => self.check_ident_is_not_a_proof(body),
            _ => Ok(()),
        }
    }

    fn term_mut(&mut self, id: &Ident) -> RawResult<&mut Term> {
        let t = &mut self.term_data_mut(id)?.term;
        Ok(t)
    }

    fn term_data_mut(&mut self, id: &Ident) -> RawResult<&mut TermData> {
        if id.is_builtin() {
            // Builtins are added lazily
            let timestamp = self.processed_logs;
            let entry = self.terms.entry(id.clone()).or_insert_with(|| TermData {
                term: Term::Builtin {
                    name: id.namespace.clone(),
                },
                instantiations: Vec::new(),
                instantiation_timestamps: Vec::new(),
                timestamp,
            });
            return Ok(&mut *entry);
        }
        let t = self
            .terms
            .get_mut(id)
            .ok_or_else(|| RawError::UndefinedIdent(id.clone()))?;
        Ok(t)
    }

    fn make_terms_equal(
        &mut self,
        id0: &Ident,
        id1: &Ident,
        ext_qi_deps: &[QiRef],
        ext_proof_deps: &[ProofRef],
    ) -> Ident {
        let cid0 = self.term_equality_class(id0);
        let cid1 = self.term_equality_class(id1);
        use std::cmp::Ordering::*;
        let (id0, cid0, id1, cid1) = match cid0.cmp(&cid1) {
            Equal => {
                return cid1;
            }
            // Use the older term as class root.
            Less => (id1, cid1, id0, cid0),
            Greater => (id0, cid0, id1, cid1),
        };
        // Need to update the entry of cid0 and re-import deps from
        // id1.
        let cdata = self.scoped_term_data(id1);
        let c_qi_deps = cdata.qi_deps.clone();
        let c_proof_deps = cdata.proof_deps.clone();
        self.current_scope.needs_consolidation = true;
        let data = self.scoped_term_data_mut(&cid0);
        data.eq_class = Some(cid1.clone());
        data.qi_deps.extend(c_qi_deps);
        data.proof_deps.extend(c_proof_deps);
        // Adding external deps as well.
        data.qi_deps.extend(ext_qi_deps.iter().cloned());
        data.proof_deps.extend(ext_proof_deps.iter().cloned());
        if self.config.log_internal_term_equalities {
            eprintln!(
                "{}: @{} {:?} -> {:?} ==> {:?} <- {:?}",
                self.processed_logs, self.current_scope.level, id0, cid0, cid1, id1
            );
        }
        cid1
    }

    // Due to lazy logging of equalities by Z3, sometimes we discover an equality that
    // belongs to an ancestor scope. We'd like this equality to survive backtracking and
    // be visible in future (cousin) scopes. Therefore, in addition to setting the current
    // scope, we retro-actively modify the ancestor scope on the active backtracking branch.
    fn make_terms_equal_at_scope(
        &mut self,
        ancestor_scope_index: usize,
        id0: &Ident,
        id1: &Ident,
        ext_qi_deps: &[QiRef],
        ext_proof_deps: &[ProofRef],
    ) -> Ident {
        // Start with the current scope.
        if self.config.log_term_equalities {
            println!(
                "{}: @{}..={} {:?} == {:?}",
                self.processed_logs,
                self.scopes
                    .get(ancestor_scope_index)
                    .unwrap_or(&self.current_scope)
                    .level,
                self.current_scope.level,
                id0,
                id1,
            );
        }
        let cid = self.make_terms_equal(id0, id1, ext_qi_deps, ext_proof_deps);
        let mut parent_index = self.current_scope.parent_index;
        while let Some(index) = parent_index {
            if index < ancestor_scope_index {
                break;
            }
            // Also modify ancestor.
            std::mem::swap(&mut self.current_scope, &mut self.scopes[index]);
            self.make_terms_equal(id0, id1, ext_qi_deps, ext_proof_deps);
            // Do not consolidate scope for now.
            std::mem::swap(&mut self.current_scope, &mut self.scopes[index]);
            // Next scope index
            parent_index = self.scopes[index].parent_index;
        }
        cid
    }

    fn term_max_scope_index(&self, id: &Ident) -> usize {
        let data = self.scoped_term_data(id);
        let mut index = 0;
        for qi in &data.qi_deps {
            if qi.scope_index > index {
                index = qi.scope_index;
            }
        }
        for proof in &data.proof_deps {
            if proof.scope_index > index {
                index = proof.scope_index;
            }
        }
        index
    }

    // Verify that the two terms are equal.
    // On success, return the earliest ancestor scope index where the equality is verified.
    fn check_equality(&mut self, id1: &Ident, id2: &Ident) -> Option<usize> {
        let c1 = self.term_equality_class(id1);
        let c2 = self.term_equality_class(id2);
        if c1 != c2 {
            println!(
                "{}: @{} {:?} -> {:?} =/= {:?} <- {:?}",
                self.processed_logs, self.current_scope.level, id1, c1, c2, id2
            );
            return None;
        }
        let index = std::cmp::max(
            self.term_max_scope_index(id1),
            self.term_max_scope_index(id2),
        );
        Some(index)
    }

    // On success, return the earliest ancestor scope index where the equality is verified.
    fn check_literal_equality(
        &self,
        eid: &Ident,
        id1: &Ident,
        id2: &Ident,
    ) -> RawResult<Option<usize>> {
        let term = self.term(eid)?;
        let assignment = self.term_assignment(eid);
        // Normal case.
        if let Some([eid1, eid2]) = term.matches_equality() {
            let proof = self.term_proof(eid);
            let scope_index = maybe_index_min(
                proof.map(|p| p.scope_index),
                assignment.map(|p| p.scope_index),
            );
            if scope_index.is_none() {
                return Err(RawError::MissingProof(eid.clone()));
            }
            if (&eid1 == id1 && &eid2 == id2) || (&eid1 == id2 && &eid2 == id1) {
                return Ok(scope_index);
            }
        }
        // Assigned term.
        if eid == id1 {
            match (assignment, self.term(id2)?) {
                (Some(assignment), Term::App { name, args, .. })
                    if args.is_empty() && assignment.as_str() == name.as_str() =>
                {
                    return Ok(Some(assignment.scope_index));
                }
                _ => (),
            }
        }
        Ok(None)
    }

    fn check_congruence_equality(
        &self,
        eqs: &[(Ident, Ident)],
        id1: &Ident,
        id2: &Ident,
    ) -> RawResult<bool> {
        let eqs = eqs.iter().cloned().collect::<HashSet<_>>();
        self.check_matching_ids(&eqs, id1, id2)
    }

    fn check_matching_ids(
        &self,
        eqs: &HashSet<(Ident, Ident)>,
        id1: &Ident,
        id2: &Ident,
    ) -> RawResult<bool> {
        if id1 == id2 {
            return Ok(true);
        }
        if eqs.contains(&(id1.clone(), id2.clone())) {
            return Ok(true);
        }
        let t1 = self.term(id1)?;
        let t2 = self.term(id2)?;
        self.check_matching_terms(eqs, t1, t2)
    }

    fn check_matching_terms(
        &self,
        eqs: &HashSet<(Ident, Ident)>,
        t1: &Term,
        t2: &Term,
    ) -> RawResult<bool> {
        use Term::*;
        match (t1, t2) {
            (
                App {
                    name: n1, args: a1, ..
                },
                App {
                    name: n2, args: a2, ..
                },
            ) if n1 == n2 && a1.len() == a2.len() => {
                for i in 0..a1.len() {
                    if !self.check_matching_ids(eqs, &a1[i], &a2[i])? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn consolidate_equality_classes(&mut self) {
        let ids = self
            .current_scope
            .terms
            .iter()
            .filter_map(|(id, data)| {
                if data.eq_class.is_some() {
                    Some(id.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        for id in ids {
            self.term_equality_class(&id);
        }
        self.current_scope.needs_consolidation = false;
    }

    fn add_deps_from_term<Q, P>(&self, qi_deps: &mut Q, proof_deps: &mut P, id: &Ident)
    where
        Q: std::iter::Extend<QiRef>,
        P: std::iter::Extend<ProofRef>,
    {
        let data = self.scoped_term_data(id);
        qi_deps.extend(data.qi_deps.iter().cloned());
        proof_deps.extend(data.proof_deps.iter().cloned());
    }

    fn proof_to_qi_deps<'a, I>(&'a self, proofs: I) -> BTreeSet<QiRef>
    where
        I: Iterator<Item = &'a ProofRef>,
    {
        let mut deps = BTreeSet::new();
        for proof in proofs {
            let index = proof.scope_index;
            if let Some(s) = self.current_scope.terms.get(&proof.id) {
                deps.extend(s.qi_deps.iter().map(|qi| QiRef {
                    key: qi.key,
                    scope_index: std::cmp::max(qi.scope_index, index),
                }));
            }
        }
        deps
    }

    /// Finalize dependencies by resolving proof_deps and scope.last_proof.
    fn finalize_dependencies(&mut self) {
        // Terms
        let mut new_qi_deps = Vec::<(Ident, BTreeSet<QiRef>)>::new();
        for (id, data) in &self.current_scope.terms {
            let deps = self.proof_to_qi_deps(data.proof_deps.iter());
            new_qi_deps.push((id.clone(), deps));
        }
        for (id, deps) in new_qi_deps {
            let data = self.current_scope.terms.get_mut(&id).unwrap();
            data.qi_deps.extend(deps);
            data.proof_deps.clear();
        }
        // QIs
        let mut new_qi_deps = Vec::<(QiKey, BTreeSet<QiRef>)>::new();
        for key in &self.current_scope.instantiations {
            let deps =
                self.proof_to_qi_deps(self.instantiations.get(key).unwrap().proof_deps.iter());
            new_qi_deps.push((*key, deps));
        }
        for (key, deps) in new_qi_deps {
            let inst = self.instantiations.get_mut(&key).unwrap();
            inst.qi_deps.extend(deps);
            inst.proof_deps.clear();
        }
        // Conflict
        if self.current_scope.conflict.is_some() {
            let deps = self.proof_to_qi_deps(
                self.current_scope
                    .conflict
                    .as_ref()
                    .unwrap()
                    .proof_deps
                    .iter(),
            );
            let conflict = self.current_scope.conflict.as_mut().unwrap();
            conflict.qi_deps.extend(deps);
            conflict.proof_deps.clear();
        }
    }

    fn push_current_scope(&mut self, new_scope: Scope) {
        // TODO: consolidate equalities in all scopes?
        if self.current_scope.needs_consolidation {
            self.consolidate_equality_classes();
        }
        self.finalize_dependencies();
        // Rotate current scope.
        let previous_scope = std::mem::replace(&mut self.current_scope, new_scope);
        self.scopes.push(previous_scope);
    }
}

impl LogVisitor for &mut Model {
    fn add_term(&mut self, ident: Ident, term: Term) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            term.visit(&mut |id| self.check_ident(id))?;
        }
        // (hack) Detect repeated definitions. In this case, we want to
        // propagate dependencies found on the previous version of the Ident.
        if let Some(prev_ident) = ident.previous_version() {
            if let Some(entry) = self.terms.get(&prev_ident) {
                if entry.term == term {
                    let prev_data = self.scoped_term_data(&prev_ident).clone();
                    *self.scoped_term_data_mut(&ident) = prev_data;
                }
            }
        }
        // Handle proof terms and their scoped dependency information.
        if let Term::Proof {
            name,
            args,
            property,
        } = &term
        {
            self.current_scope.last_proof = Some(ident.clone());
            if self.scoped_term_data(property).proof.is_none() {
                self.scoped_term_data_mut(property).proof = Some(ProofRef {
                    id: ident.clone(),
                    scope_index: self.scopes.len(),
                });
                if let Some([id1, id2]) = self.term(property)?.matches_equality() {
                    // Optimization: handle equality early here rather than later in add_equality.
                    let data = self.scoped_term_data(&ident);
                    let qi_deps = data.qi_deps.iter().cloned().collect::<Vec<_>>();
                    let proof_deps = data.proof_deps.iter().cloned().collect::<Vec<_>>();
                    self.make_terms_equal(&id1, &id2, &qi_deps, &proof_deps);
                }
            }
            let mut data = std::mem::take(self.scoped_term_data_mut(&ident));
            if name == "quant-inst" {
                // Track dependencies to this proof term (starting with itself).
                data.proof_deps.insert(ProofRef {
                    id: ident.clone(),
                    scope_index: self.scopes.len(),
                });
            }
            // (hack) If the object of the proof already has dependencies, propagate them.
            let prop_data = self.scoped_term_data(property);
            data.qi_deps.extend(prop_data.qi_deps.iter().cloned());
            data.proof_deps.extend(prop_data.proof_deps.iter().cloned());
            // Propagate dependencies from sub-proofs.
            for arg in args {
                let arg_data = self.scoped_term_data(arg);
                data.qi_deps.extend(arg_data.qi_deps.iter().cloned());
                data.proof_deps.extend(arg_data.proof_deps.iter().cloned());
            }
            *self
                .current_scope
                .terms
                .get_mut(&ident)
                .expect("already in current scope") = data;
        }
        if self.has_log_consistency_checks()
            && matches!(term, Term::App { .. } | Term::Quant { .. })
        {
            term.visit(&mut |id| self.check_ident_is_not_a_proof(id))?;
        }
        let data = TermData {
            term,
            instantiations: Vec::new(),
            instantiation_timestamps: Vec::new(),
            timestamp: self.processed_logs,
        };
        self.terms.insert(ident, data);
        Ok(())
    }

    fn add_instantiation(&mut self, key: QiKey, frame: QiFrame) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            frame.visit(&mut |id| self.check_ident(id))?;
        }
        let mut qi_deps = BTreeSet::new();
        let mut proof_deps = BTreeSet::new();
        // Verify used equalities
        if let QiFrame::NewMatch { used, .. } = &frame {
            for u in used {
                if let MatchedTerm::Equality(id1, id2) = u {
                    if self.has_log_consistency_checks() && self.check_equality(id1, id2).is_none()
                    {
                        return Err(RawError::CannotCheckEquality(id1.clone(), id2.clone()));
                    }
                    self.add_deps_from_term(&mut qi_deps, &mut proof_deps, id1);
                    self.add_deps_from_term(&mut qi_deps, &mut proof_deps, id2);
                }
            }
        }

        let quantifier = frame.quantifier();
        let frame_clone = frame.clone();

        self.term_data_mut(quantifier)?.instantiations.push(key);
        self.instantiations.insert(
            key,
            QuantInstantiation {
                frame,
                instances: Vec::new(),
                qi_deps,
                proof_deps,
            },
        );

        let name = self.global_id_to_sexp(frame_clone.quantifier())?;

        if false && !name.contains("basic") {
            println!("found quantifier instantiation {}\n{:?}",
                    name,
                    frame_clone.terms().iter()
                    .map(|id| self.global_id_to_sexp(id))
                    .collect::<RawResult<Vec<_>>>()?
                    .join(" ")
                );
        }
        Ok(())
    }

    fn start_instance(&mut self, key: QiKey, instance: QiInstance) -> RawResult<()> {
        self.processed_logs += 1;
        // Ident check.
        if self.has_log_consistency_checks() {
            instance.visit(&mut |id| self.check_ident(id))?;
        }
        if let Some(id) = &instance.term {
            let qi = QiRef {
                key,
                scope_index: 0,
            };
            self.scoped_term_data_mut(id).qi_deps.insert(qi);
        }
        self.pending_instances.push(PendingQiInstance {
            key,
            instance,
            timestamp: self.processed_logs,
        });
        Ok(())
    }

    fn end_instance(&mut self) -> RawResult<()> {
        self.processed_logs += 1;
        let PendingQiInstance {
            key,
            instance,
            timestamp,
        } = self
            .pending_instances
            .pop()
            .ok_or(RawError::InvalidEndOfInstance)?;

        let inst = self
            .instantiations
            .get(&key)
            .ok_or(RawError::InvalidInstanceKey)?;

        if !inst.frame.quantifier().is_builtin() {
            let hash = self.auto_hash_term(inst.frame.quantifier())?;

            // println!("Key {:?} is {:?} hashed {:?}", key, inst.frame.quantifier(), hash);

            if let Some(t) = &instance.term {
                for unknown_id in self.find_unknown_quantifiers(t)? {
                    if unknown_id != hash {
                        // println!("adding {:?} to {:?}", unknown_id, key);
                        self.known_quantifiers.insert(unknown_id, key);
                    }
                }
            }
        }

        let inst = self
            .instantiations
            .get_mut(&key)
            .ok_or(RawError::InvalidInstanceKey)?;
        inst.instances.push(instance);
        let quantifier = inst.frame.quantifier().clone();
        self.term_data_mut(&quantifier)?
            .instantiation_timestamps
            .push(timestamp);
        if self.config.display_qi_logs || self.config.annotated_proof {
            self.log_instance(key)?;
        }
        Ok(())
    }

    fn add_equality(&mut self, id: Ident, eq: Equality) -> RawResult<()> {
        use Equality::*;

        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            eq.visit(&mut |id| self.check_ident(id))?;
        }
        let (cid, scope_index, qi_deps, proof_deps) = match &eq {
            Root => {
                // Nothing to do.
                return Ok(());
            }
            Literal(eid, cid) => {
                let scope_index = self.check_literal_equality(eid, &id, cid)?;
                if self.has_log_consistency_checks() && scope_index.is_none() {
                    return Err(RawError::CannotProcessEquality(id, eq));
                }
                let data = self.scoped_term_data(eid);
                (
                    cid,
                    scope_index.unwrap_or(0),
                    data.qi_deps.iter().cloned().collect(),
                    data.proof_deps.iter().cloned().collect(),
                )
            }
            Congruence(eqs, cid) => {
                let mut scope_index = 0;
                let mut qi_deps = Vec::new();
                let mut proof_deps = Vec::new();
                for (id1, id2) in eqs {
                    let index = match self.check_equality(id1, id2) {
                        Some(i) => i,
                        None => {
                            if self.has_log_consistency_checks() {
                                return Err(RawError::CannotCheckEquality(
                                    id1.clone(),
                                    id2.clone(),
                                ));
                            } else {
                                0
                            }
                        }
                    };
                    if index > scope_index {
                        scope_index = index;
                    }
                    self.add_deps_from_term(&mut qi_deps, &mut proof_deps, id1);
                    self.add_deps_from_term(&mut qi_deps, &mut proof_deps, id2);
                }
                if self.has_log_consistency_checks()
                    && !self.check_congruence_equality(eqs, &id, cid)?
                {
                    return Err(RawError::CannotProcessEquality(id, eq));
                }
                (cid, scope_index, qi_deps, proof_deps)
            }
            Theory(_, cid) => (cid, 0, Vec::new(), Vec::new()),
            Axiom(cid) => (cid, 0, Vec::new(), Vec::new()),
            Unknown(cid) => (cid, 0, Vec::new(), Vec::new()),
        };
        self.make_terms_equal_at_scope(scope_index, &id, cid, &qi_deps, &proof_deps);
        Ok(())
    }

    fn attach_meaning(&mut self, id: Ident, m: Meaning) -> RawResult<()> {
        self.processed_logs += 1;
        match self.term_mut(&id)? {
            Term::App { meaning, .. } => {
                *meaning = Some(m);
                Ok(())
            }
            _ => Err(RawError::CannotAttachMeaning(id)),
        }
    }

    fn attach_var_names(&mut self, id: Ident, names: Vec<VarName>) -> RawResult<()> {
        self.processed_logs += 1;
        match self.term_mut(&id)? {
            Term::Quant {
                var_names, params, ..
            } if names.len() == *params => {
                *var_names = Some(names);
            }
            _ => {
                return Err(RawError::CannotAttachVarNames(id));
            }
        }
        Ok(())
    }

    fn attach_enode(&mut self, id: Ident, _generation: u64) -> RawResult<()> {
        self.processed_logs += 1;
        // Ignore commands outside of [instance]..[end-of-instance].
        if !self.pending_instances.is_empty() {
            let pending_instance = self.pending_instances.last_mut().unwrap();
            let key = pending_instance.key;
            pending_instance.instance.enodes.push(id.clone());
            // TODO check that this was None.
            self.scoped_term_data_mut(&id).enode_qi = Some(QiRef {
                key,
                scope_index: 0,
            });
        }
        Ok(())
    }

    fn tool_version(&mut self, _s1: String, _s2: String) -> RawResult<()> {
        self.processed_logs += 1;
        Ok(())
    }

    fn begin_check(&mut self, _i: u64) -> RawResult<()> {
        self.processed_logs += 1;
        Ok(())
    }

    fn assign(&mut self, lit: Literal, _s: String) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        let timestamp = self.processed_logs;
        let assignment = Assignment {
            sign: lit.sign,
            timestamp,
            scope_index: self.scopes.len(),
        };
        let data = self.scoped_term_data_mut(&lit.id);
        // TODO check that this was None.
        data.assignment = Some(assignment);
        if let Some(key) = &data.enode_qi {
            // Assignments of a QI-produced term are seen as "depending" on the QI.
            data.qi_deps.insert(key.clone());
        }
        Ok(())
    }

    fn conflict(&mut self, lits: Vec<Literal>, _s: String) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            lits.visit(&mut |id| self.check_ident(id))?;
        }
        let mut qi_deps = BTreeSet::new();
        let mut proof_deps = BTreeSet::new();
        if let Some(proof) = &self.current_scope.last_proof {
            // In practice, a [conflict] log is preceded by its proof.
            self.add_deps_from_term(&mut qi_deps, &mut proof_deps, proof);
        }
        self.current_scope.conflict = Some(Conflict {
            lits,
            timestamp: self.processed_logs,
            qi_deps,
            proof_deps,
        });
        Ok(())
    }

    fn push(&mut self, level: u64) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() && level != self.current_scope.level {
            return Err(RawError::InvalidPush(level));
        }
        let scope = Scope {
            timestamp: self.processed_logs,
            level: level + 1,
            parent_index: Some(self.scopes.len()),
            ..Scope::default()
        };
        self.push_current_scope(scope);
        Ok(())
    }

    fn pop(&mut self, num: u64, current_level: u64) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks()
            && (current_level != self.current_scope.level || num > current_level || num == 0)
        {
            return Err(RawError::InvalidPop(num, current_level));
        }
        let level = current_level - num;
        let parent_index = {
            let mut index = self.current_scope.parent_index;
            while let Some(i) = index {
                if self.scopes[i].level <= level {
                    break;
                }
                index = self.scopes[i].parent_index;
            }
            index
        };
        let scope = Scope {
            timestamp: self.processed_logs,
            level, // same level as "parent": we are iterating on the same level
            parent_index,
            ..Scope::default()
        };
        self.push_current_scope(scope);
        Ok(())
    }

    fn resolve_lit(&mut self, _i: u64, lit: Literal) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        Ok(())
    }

    fn resolve_process(&mut self, lit: Literal) -> RawResult<()> {
        self.processed_logs += 1;
        if self.has_log_consistency_checks() {
            lit.visit(&mut |id| self.check_ident(id))?;
        }
        Ok(())
    }
}
