---
Template: Symbol
Name: DiagramGridWidthHeight
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramGridWidthHeight
Keywords: [grid, dimensions, layout, metric]
SeeAlso: [DiagramGridWidth, DiagramGridHeight, DiagramGrid]
RelatedGuides: [DiagramGrid]
---

## Usage

<code>[DiagramGridWidthHeight]()[$d$]</code> gives <code>{width, height}</code> of the diagram's grid layout in one call.

## Basic Examples

```wl
DiagramGridWidthHeight @ DiagramProduct[Diagram["A", a, b], Diagram["B", c, d]]
```
