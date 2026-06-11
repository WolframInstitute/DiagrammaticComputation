---
Template: Symbol
Name: DiagramMap
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramMap
Keywords: [map, transform, traverse, recursive, leaves]
SeeAlso: [DiagramMapAt, DiagramReplacePart, Map]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramMap]()[$f$, $d$]</code> applies the function $f$ to every singleton subdiagram of $d$ and returns the rebuilt diagram.

<code>[DiagramMap]()[$f$, $d$, $lvl$]</code> descends at most $lvl$ levels, applying $f$ to whatever subdiagrams it reaches there.

<code>[DiagramMap]()[$f$][$d$]</code> is the operator form.

## Details & Options

- Compositions, products, sums and networks are traversed and rebuilt with their options; $f$ transforms the leaves and is expected to return something <code>[Diagram]()</code> accepts.
- With a finite level, subtrees below the cutoff are passed to $f$ whole.

## Basic Examples

Relabel every leaf diagram:

```wl
DiagramMap[Diagram[#, "Expression" -> "Z"] &, DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]]
```
