---
Template: Symbol
Name: DiagramCases
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramCases
Keywords: [cases, extract, pattern]
SeeAlso: [DiagramPosition, DiagramPattern, DiagramExtract, Cases]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramCases]()[$d$, $patt$]</code> returns the subdiagrams of $d$ matching the <code>[DiagramPattern]()</code> $patt$.

## Details & Options

- Behaves like <code>[Cases]()</code>, but matching is by diagram structure (via <code>[DiagramPattern]()</code>).

## Basic Examples

Collect every singleton subdiagram:

```wl
DiagramCases[
  DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]],
  DiagramPattern[_, {_}, {_}]
]
```
