---
Template: Symbol
Name: DiagramPositions
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramPositions
Keywords: [positions, indices, addressing, levelspec]
SeeAlso: [DiagramSubdiagrams, DiagramPosition, DiagramExtract]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramPositions]()[$d$]</code> returns an association of position → subdiagram for every subdiagram of $d$.

<code>[DiagramPositions]()[$d$, $lvl$]</code> includes positions down to level $lvl$.

<code>[DiagramPositions]()[$d$, {$min$, $max$}]</code> includes positions between levels $min$ and $max$.

## Details & Options

- Positions are integer-list addresses into the diagram's expression tree, in the same convention as <code>[Position]()</code> and <code>[Extract]()</code>; the empty position <code>{}</code> is the diagram itself.
- The level specification follows the <code>[Level]()</code> conventions: <code>{$lvl$}</code> is exactly level $lvl$, and negative levels count from the deepest position.

## Basic Examples

Positions of all subdiagrams, keyed to the subdiagrams:

```wl
DiagramPositions @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```

Only the immediate subdiagrams:

```wl
DiagramPositions[Diagram[DiagramProduct[Diagram["A", a, c], Diagram["B", b]] /* Diagram["C", {c, b}, e]], {1}]
```
