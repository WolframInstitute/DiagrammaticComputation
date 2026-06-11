---
Template: Symbol
Name: DiagramGridHeight
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramGridHeight
Keywords: [grid, height, layout, metric]
SeeAlso: [DiagramGridWidth, DiagramGridWidthHeight, DiagramGrid]
RelatedGuides: [DiagramGrid]
---

## Usage

<code>[DiagramGridHeight](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramGridHeight)[$d$]</code> gives the height of the diagram's grid layout -- the number of rows required to lay out $d$ as a 2D grid.

## Basic Examples

```wl
DiagramGridHeight @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```

![output](images/DiagramGridHeight-out-1.png)
