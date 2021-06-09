// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The visiting traits expected by the SMT2 parser.

use crate::{Binary, Decimal, Hexadecimal, Numeral};
use itertools::Itertools;
use serde::{Deserialize, Serialize};

pub trait ConstantVisitor {
    type T;

    fn visit_numeral_constant(&mut self, value: Numeral) -> Self::T;
    fn visit_decimal_constant(&mut self, value: Decimal) -> Self::T;
    fn visit_hexadecimal_constant(&mut self, value: Hexadecimal) -> Self::T;
    fn visit_binary_constant(&mut self, value: Binary) -> Self::T;
    fn visit_string_constant(&mut self, value: String) -> Self::T;
}

pub trait SymbolVisitor {
    type T;

    fn visit_fresh_symbol(&mut self, value: String) -> Self::T;

    // If it is not a valid bound symbol, return an error containing the value.
    fn visit_bound_symbol(&mut self, value: String) -> Result<Self::T, String> {
        Ok(self.visit_fresh_symbol(value))
    }

    // If it is not a valid bound symbol, create a fresh one.
    fn visit_any_symbol(&mut self, value: String) -> Self::T {
        self.visit_bound_symbol(value)
            .unwrap_or_else(|v| self.visit_fresh_symbol(v))
    }

    fn bind_symbol(&mut self, _symbol: &Self::T) {}

    fn unbind_symbol(&mut self, _symbol: &Self::T) {}
}

pub trait KeywordVisitor {
    type T;

    fn visit_keyword(&mut self, value: String) -> Self::T;
}

pub trait SExprVisitor<Constant, Symbol, Keyword> {
    type T;

    fn visit_constant_s_expr(&mut self, value: Constant) -> Self::T;
    fn visit_symbol_s_expr(&mut self, value: Symbol) -> Self::T;
    fn visit_keyword_s_expr(&mut self, value: Keyword) -> Self::T;
    fn visit_application_s_expr(&mut self, values: Vec<Self::T>) -> Self::T;
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum Index<Symbol> {
    Numeral(Numeral),
    Symbol(Symbol),
}

impl<S> Index<S> {
    /// Remap the symbols of an Index value.
    pub(crate) fn remap<F, V, T>(self, v: &mut V, f: F) -> Index<T>
    where
        F: Copy + Fn(&mut V, S) -> T,
    {
        use Index::*;
        match self {
            Numeral(n) => Numeral(n),
            Symbol(s) => Symbol(f(v, s)),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum Identifier<Symbol> {
    Simple {
        symbol: Symbol,
    },
    Indexed {
        symbol: Symbol,
        indices: Vec<Index<Symbol>>,
    },
}

impl<S> Identifier<S> {
    /// Remap the symbols of an Identifier value.
    pub(crate) fn remap<F, V, T>(self, v: &mut V, f: F) -> Identifier<T>
    where
        F: Copy + Fn(&mut V, S) -> T,
    {
        use Identifier::*;
        match self {
            Simple { symbol } => Simple {
                symbol: f(v, symbol),
            },
            Indexed { symbol, indices } => Indexed {
                symbol: f(v, symbol),
                indices: indices.into_iter().map(|i| i.remap(v, f)).collect(),
            },
        }
    }
}

pub trait SortVisitor<Symbol> {
    type T;

    fn visit_simple_sort(&mut self, identifier: Identifier<Symbol>) -> Self::T;
    fn visit_parameterized_sort(
        &mut self,
        identifier: Identifier<Symbol>,
        parameters: Vec<Self::T>,
    ) -> Self::T;
}

pub trait QualIdentifierVisitor<Identifier, Sort> {
    type T;

    fn visit_simple_identifier(&mut self, identifier: Identifier) -> Self::T;
    fn visit_sorted_identifier(&mut self, identifier: Identifier, sort: Sort) -> Self::T;
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum AttributeValue<Constant, Symbol, SExpr> {
    None,
    Constant(Constant),
    Symbol(Symbol),
    SExpr(Vec<SExpr>),
}

impl<T1, T2, T3> AttributeValue<T1, T2, T3> {
    /// Remap the generically-typed values of an AttributeValue.
    pub(crate) fn remap<V, F1, F2, F3, R1, R2, R3>(
        self,
        v: &mut V,
        f1: F1,
        f2: F2,
        f3: F3,
    ) -> AttributeValue<R1, R2, R3>
    where
        F1: Fn(&mut V, T1) -> R1,
        F2: Fn(&mut V, T2) -> R2,
        F3: Fn(&mut V, T3) -> R3,
    {
        use AttributeValue::*;
        match self {
            None => None,
            Constant(value) => Constant(f1(v, value)),
            Symbol(value) => Symbol(f2(v, value)),
            SExpr(values) => SExpr(values.into_iter().map(|x| f3(v, x)).collect()),
        }
    }
}

pub trait TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> {
    type T;

    fn visit_constant(&mut self, constant: Constant) -> Self::T;

    fn visit_qual_identifier(&mut self, qual_identifier: QualIdentifier) -> Self::T;

    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Self::T;

    fn visit_let(&mut self, var_bindings: Vec<(Symbol, Self::T)>, term: Self::T) -> Self::T;

    fn visit_forall(&mut self, vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T;

    fn visit_exists(&mut self, vars: Vec<(Symbol, Sort)>, term: Self::T) -> Self::T;

    fn visit_match(&mut self, term: Self::T, cases: Vec<(Vec<Symbol>, Self::T)>) -> Self::T;

    fn visit_attributes(
        &mut self,
        term: Self::T,
        attributes: Vec<(Keyword, AttributeValue<Constant, Symbol, SExpr>)>,
    ) -> Self::T;
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct ConstructorDec<Symbol, Sort> {
    pub symbol: Symbol,
    pub selectors: Vec<(Symbol, Sort)>,
}

impl<T1, T2> ConstructorDec<T1, T2> {
    /// Remap the generically-typed values of a ConstructorDec value.
    pub(crate) fn remap<V, F1, F2, R1, R2>(
        self,
        v: &mut V,
        f1: F1,
        f2: F2,
    ) -> ConstructorDec<R1, R2>
    where
        F1: Fn(&mut V, T1) -> R1,
        F2: Fn(&mut V, T2) -> R2,
    {
        ConstructorDec {
            symbol: f1(v, self.symbol),
            selectors: self
                .selectors
                .into_iter()
                .map(|(s1, s2)| (f1(v, s1), f2(v, s2)))
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct DatatypeDec<Symbol, Sort> {
    pub parameters: Vec<Symbol>,
    pub constructors: Vec<ConstructorDec<Symbol, Sort>>,
}

impl<T1, T2> DatatypeDec<T1, T2> {
    /// Remap the generically-typed values of a DatatypeDec value.
    pub(crate) fn remap<V, F1, F2, R1, R2>(self, v: &mut V, f1: F1, f2: F2) -> DatatypeDec<R1, R2>
    where
        F1: Copy + Fn(&mut V, T1) -> R1,
        F2: Copy + Fn(&mut V, T2) -> R2,
    {
        DatatypeDec {
            parameters: self.parameters.into_iter().map(|x| f1(v, x)).collect(),
            constructors: self
                .constructors
                .into_iter()
                .map(|c| c.remap(v, f1, f2))
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct FunctionDec<Symbol, Sort> {
    pub name: Symbol,
    pub parameters: Vec<(Symbol, Sort)>,
    pub result: Sort,
}

impl<T1, T2> FunctionDec<T1, T2> {
    /// Remap the generically-typed values of a FunctionDec value.
    pub(crate) fn remap<V, F1, F2, R1, R2>(self, v: &mut V, f1: F1, f2: F2) -> FunctionDec<R1, R2>
    where
        F1: Copy + Fn(&mut V, T1) -> R1,
        F2: Copy + Fn(&mut V, T2) -> R2,
    {
        FunctionDec {
            name: f1(v, self.name),
            parameters: self
                .parameters
                .into_iter()
                .map(|(s1, s2)| (f1(v, s1), f2(v, s2)))
                .collect(),
            result: f2(v, self.result),
        }
    }
}

pub trait CommandVisitor<Term, Symbol, Sort, Keyword, Constant, SExpr> {
    type T;

    fn visit_assert(&mut self, term: Term) -> Self::T;

    fn visit_check_sat(&mut self) -> Self::T;

    fn visit_check_sat_assuming(&mut self, literals: Vec<(Symbol, bool)>) -> Self::T;

    fn visit_declare_const(&mut self, symbol: Symbol, sort: Sort) -> Self::T;

    fn visit_declare_datatype(
        &mut self,
        symbol: Symbol,
        datatype: DatatypeDec<Symbol, Sort>,
    ) -> Self::T;

    fn visit_declare_datatypes(
        &mut self,
        datatypes: Vec<(Symbol, Numeral, DatatypeDec<Symbol, Sort>)>,
    ) -> Self::T;

    fn visit_declare_fun(&mut self, symbol: Symbol, parameters: Vec<Sort>, sort: Sort) -> Self::T;

    fn visit_declare_sort(&mut self, symbol: Symbol, arity: Numeral) -> Self::T;

    fn visit_define_fun(&mut self, sig: FunctionDec<Symbol, Sort>, term: Term) -> Self::T;

    fn visit_define_fun_rec(&mut self, sig: FunctionDec<Symbol, Sort>, term: Term) -> Self::T;

    fn visit_define_funs_rec(&mut self, funs: Vec<(FunctionDec<Symbol, Sort>, Term)>) -> Self::T;

    fn visit_define_sort(&mut self, symbol: Symbol, parameters: Vec<Symbol>, sort: Sort)
        -> Self::T;

    fn visit_echo(&mut self, message: String) -> Self::T;

    fn visit_exit(&mut self) -> Self::T;

    fn visit_get_assertions(&mut self) -> Self::T;

    fn visit_get_assignment(&mut self) -> Self::T;

    fn visit_get_info(&mut self, flag: Keyword) -> Self::T;

    fn visit_get_model(&mut self) -> Self::T;

    fn visit_get_option(&mut self, keyword: Keyword) -> Self::T;

    fn visit_get_proof(&mut self) -> Self::T;

    fn visit_get_unsat_assumptions(&mut self) -> Self::T;

    fn visit_get_unsat_core(&mut self) -> Self::T;

    fn visit_get_value(&mut self, terms: Vec<Term>) -> Self::T;

    fn visit_pop(&mut self, level: Numeral) -> Self::T;

    fn visit_push(&mut self, level: Numeral) -> Self::T;

    fn visit_reset(&mut self) -> Self::T;

    fn visit_reset_assertions(&mut self) -> Self::T;

    fn visit_set_info(
        &mut self,
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    ) -> Self::T;

    fn visit_set_logic(&mut self, symbol: Symbol) -> Self::T;

    fn visit_set_option(
        &mut self,
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    ) -> Self::T;
}

/// A visitor for the entire SMT2 syntax.
pub trait Smt2Visitor:
    ConstantVisitor<T = <Self as Smt2Visitor>::Constant>
    + SymbolVisitor<T = <Self as Smt2Visitor>::Symbol>
    + KeywordVisitor<T = <Self as Smt2Visitor>::Keyword>
    + SExprVisitor<
        <Self as Smt2Visitor>::Constant,
        <Self as Smt2Visitor>::Symbol,
        <Self as Smt2Visitor>::Keyword,
        T = <Self as Smt2Visitor>::SExpr,
    > + QualIdentifierVisitor<
        Identifier<<Self as Smt2Visitor>::Symbol>,
        <Self as Smt2Visitor>::Sort,
        T = <Self as Smt2Visitor>::QualIdentifier,
    > + SortVisitor<<Self as Smt2Visitor>::Symbol, T = <Self as Smt2Visitor>::Sort>
    + TermVisitor<
        <Self as Smt2Visitor>::Constant,
        <Self as Smt2Visitor>::QualIdentifier,
        <Self as Smt2Visitor>::Keyword,
        <Self as Smt2Visitor>::SExpr,
        <Self as Smt2Visitor>::Symbol,
        <Self as Smt2Visitor>::Sort,
        T = <Self as Smt2Visitor>::Term,
    > + CommandVisitor<
        <Self as Smt2Visitor>::Term,
        <Self as Smt2Visitor>::Symbol,
        <Self as Smt2Visitor>::Sort,
        <Self as Smt2Visitor>::Keyword,
        <Self as Smt2Visitor>::Constant,
        <Self as Smt2Visitor>::SExpr,
        T = <Self as Smt2Visitor>::Command,
    >
{
    type Constant;
    type QualIdentifier;
    type Keyword;
    type Sort;
    type SExpr;
    type Symbol;
    type Term;
    type Command;
}

impl<Symbol> std::fmt::Display for Index<Symbol>
where
    Symbol: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨numeral⟩ | ⟨symbol⟩
        match self {
            Index::Numeral(num) => write!(f, "{}", num),
            Index::Symbol(sym) => write!(f, "{}", sym),
        }
    }
}

impl<Symbol> std::fmt::Display for Identifier<Symbol>
where
    Symbol: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨symbol⟩ | ( _ ⟨symbol⟩ ⟨index⟩+ )
        match self {
            Identifier::Simple { symbol } => write!(f, "{}", symbol),
            Identifier::Indexed { symbol, indices } => {
                write!(f, "(_ {} {})", symbol, indices.iter().format(" "))
            }
        }
    }
}

impl<Constant, Symbol, SExpr> std::fmt::Display for AttributeValue<Constant, Symbol, SExpr>
where
    Constant: std::fmt::Display,
    Symbol: std::fmt::Display,
    SExpr: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨spec_constant⟩ | ⟨symbol⟩ | ( ⟨s_expr⟩∗ ) |
        use AttributeValue::*;
        match self {
            None => Ok(()),
            Constant(c) => write!(f, "{}", c),
            Symbol(s) => write!(f, "{}", s),
            SExpr(values) => write!(f, "({})", values.iter().format(" ")),
        }
    }
}

impl<Symbol, Sort> std::fmt::Display for ConstructorDec<Symbol, Sort>
where
    Symbol: std::fmt::Display,
    Sort: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ( ⟨symbol⟩ ⟨selector_dec⟩∗ )
        write!(
            f,
            "({} {})",
            self.symbol,
            self.selectors
                .iter()
                .format_with(" ", |(symbol, sort), f| f(&format_args!(
                    "({} {})",
                    symbol, sort
                )))
        )
    }
}

impl<Symbol, Sort> std::fmt::Display for DatatypeDec<Symbol, Sort>
where
    Symbol: std::fmt::Display,
    Sort: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ( ⟨constructor_dec⟩+ ) | ( par ( ⟨symbol⟩+ ) ( ⟨constructor_dec⟩+ ) )
        if self.parameters.is_empty() {
            write!(f, "({})", self.constructors.iter().format(" "))
        } else {
            let symbols = format!("({})", self.parameters.iter().format(" "));
            let constructors = format!("({})", self.constructors.iter().format(" "));
            write!(f, "(par {} {})", symbols, constructors)
        }
    }
}

impl<Symbol, Sort> std::fmt::Display for FunctionDec<Symbol, Sort>
where
    Symbol: std::fmt::Display,
    Sort: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨symbol⟩ ( ⟨sorted_var⟩∗ ) ⟨sort⟩
        let params = self
            .parameters
            .iter()
            .format_with(" ", |(symbol, sort), f| {
                f(&format_args!("({} {})", symbol, sort))
            });
        write!(f, "{} ({}) {}", self.name, params, self.result)
    }
}
