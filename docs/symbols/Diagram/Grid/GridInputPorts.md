---
Template: Symbol
Name: GridInputPorts
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/GridInputPorts
Keywords: [grid, input ports, layout]
SeeAlso: [GridOutputPorts, DiagramGrid, DiagramArrange]
RelatedGuides: [DiagramGrid]
---

## Usage

<code>[GridInputPorts]()[$d$]</code> returns the input ports of a diagram's grid layout, in the left-to-right order they appear along the top of the grid.

## Basic Examples

```wl
GridInputPorts @ DiagramArrange @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```
