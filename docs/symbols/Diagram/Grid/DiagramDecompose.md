---
Template: Symbol
Name: DiagramDecompose
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramDecompose
Keywords: [decompose, expression tree, subdiagram]
SeeAlso: [DiagramArrange, DiagramGrid, DiagramSubdiagrams]
RelatedGuides: [DiagramGrid, DiagramSurgery]
---

## Usage

<code>[DiagramDecompose]()[$d$]</code> decomposes the diagram $d$ into an expression tree of subdiagrams.

## Details & Options

- The result is the structural skeleton of $d$ — a nested <code>[DiagramComposition]()</code> / <code>[DiagramProduct]()</code> / <code>[DiagramNetwork]()</code> expression whose leaves are the singleton subdiagrams of $d$.
- This is the canonical way to *read* the structure of a built diagram; for *patterns over* this structure, use <code>[DiagramSubdiagrams]()</code> and the surgery functions.

## Basic Examples

Decompose a composition of a product:

```wl
d = DiagramRightComposition[Diagram[A, a, {x, y}], DiagramProduct[Diagram[B, x, b], Diagram[C, y, c]]];
DiagramDecompose[d]
```

## Properties and Relations

The inverse direction is implicit in <code>[DiagramArrange]()</code>, which expands the
expression tree by introducing identity, permutation and spider wires.
