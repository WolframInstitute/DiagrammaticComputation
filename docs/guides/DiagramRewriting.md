---
Template: Guide
Name: DiagramRewriting
Title: Diagram Rewriting
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/guide/DiagramRewriting
Description: Pattern-based rewriting of diagrams via hypergraph matching, with standard rule schemas
Keywords: [rewriting, rule, hypergraph, commutation, annihilation, eraser, propagation, ZX]
RelatedGuides: [Diagrams, DiagramSurgery]
---

## Abstract

A <code>[DiagramRule]()</code> describes how a piece of a diagram is replaced by
another piece. Matching is done against the diagram's *hypergraph* view —
<code>[DiagramHypergraph]()</code> — so the rules are insensitive to embedding and
naming. The rewriting front-end (<code>[DiagramReplace]()</code>, <code>[DiagramReplaceList]()</code>,
<code>[DiagramNestReplace]()</code>) mirrors the ordinary <code>[Replace]()</code>/<code>[ReplaceList]()</code>/
<code>[ReplaceRepeated]()</code> family; a small library of named schemas (commutation,
eraser, annihilation, propagation) provides the standard structural laws
that come up in ZX-style and process-theoretic calculi.

## Functions

### Rewriting

- `DiagramReplace` — replace the first matching subdiagram by a rule
- `DiagramReplaceList` — list every possible single replacement
- `DiagramNestReplace` — iteratively apply rewrite rules
- `DiagramExpressionReplace` — replace at the expression level inside a diagram

### Rules

- `DiagramRule` — bidirectional rewrite rule between two diagrams
- `RemoveDiagramRule` — wrapper that marks a rule for removal during a rewrite

### Hypergraph view

- `DiagramHypergraph` — hypergraph representation used for matching
- `DiagramHypergraphRule` — hypergraph form of a diagram rewrite rule

### Standard schemas

- `CommutationRule` — commutativity between two operations
- `EraserRule` — discarding rule for a process
- `AnnihilationRule` — pairwise annihilation of two processes
- `DuplicateAnnihilationRule` — annihilation between a copy and an erase
- `EraserAnnihilationRule` — annihilation of an erase with its dual
- `DuplicateEraserRule` — interaction of a copy with an erase
- `PropagationRule` — propagation of a unit through a process

### Auxiliary diagrams

- `EraserDiagram` — distinguished erase / discard diagram
- `DiagramCopySplit` — split a copy diagram across a node
