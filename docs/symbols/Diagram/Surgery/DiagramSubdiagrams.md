---
Template: Symbol
Name: DiagramSubdiagrams
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramSubdiagrams
Keywords: [subdiagrams, decomposition, recurse, levelspec]
SeeAlso: [DiagramPositions, DiagramCases, DiagramDecompose]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramSubdiagrams]()[$d$]</code> returns a list of every subdiagram of $d$, including $d$ itself.

<code>[DiagramSubdiagrams]()[$d$, $lvl$]</code> returns the subdiagrams down to level $lvl$.

<code>[DiagramSubdiagrams]()[$d$, {$min$, $max$}]</code> returns the subdiagrams between levels $min$ and $max$.

## Details & Options

- The list is ordered by recursive descent through <code>[DiagramComposition]()</code>, <code>[DiagramProduct]()</code>, <code>[DiagramSum]()</code> and <code>[DiagramNetwork]()</code> — the values of <code>[DiagramPositions]()</code>.
- <code>{1}</code> gives the immediate subdiagrams; level specifications follow the <code>[Level]()</code> conventions.

## Basic Examples

List all subdiagrams of a composition:

```wl
DiagramSubdiagrams @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```

Only the deepest-level subdiagrams of a nested diagram:

```wl
DiagramSubdiagrams[Diagram[DiagramProduct[Diagram["A", a, c], Diagram["B", b]] /* Diagram["C", {c, b}, e]], {-1}]
```
