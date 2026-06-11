---
Template: Symbol
Name: DiagramGridWidth
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramGridWidth
Keywords: [grid, width, layout, metric]
SeeAlso: [DiagramGridHeight, DiagramGridWidthHeight, DiagramGrid]
RelatedGuides: [DiagramGrid]
---

## Usage

<code>[DiagramGridWidth]()[$d$]</code> gives the width of the diagram's grid layout — the number of columns required to lay out $d$ as a 2D grid.

## Basic Examples

```wl
DiagramGridWidth @ DiagramProduct[Diagram["A", a, b], Diagram["B", c, d]]
```
