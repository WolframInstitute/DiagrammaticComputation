---
Template: Symbol
Name: DiagramHypergraph
Context: Wolfram`DiagrammaticComputation`Rewriting`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramHypergraph
Keywords: [hypergraph, matching, view, rewriting]
SeeAlso: [DiagramHypergraphRule, DiagramRule, DiagramsGraph]
RelatedGuides: [DiagramRewriting]
---

## Usage

<code>[DiagramHypergraph]()[$d$]</code> returns the hypergraph representation of the diagram $d$ used for rule matching.

## Details & Options

- In the hypergraph view, each subdiagram becomes a hyperedge labelled with its expression, and each shared port becomes a vertex shared by the corresponding hyperedges.
- The matcher of <code>[DiagramReplace]()</code> operates on this view, so two diagrams that differ only in port naming or layout match the same rules.

## Basic Examples

Hypergraph of a small composition:

```wl
DiagramHypergraph @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```
