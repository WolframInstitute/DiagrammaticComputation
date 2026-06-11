---
Template: Symbol
Name: GridOutputPorts
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/GridOutputPorts
Keywords: [grid, output ports, layout]
SeeAlso: [GridInputPorts, DiagramGrid, DiagramArrange]
RelatedGuides: [DiagramGrid]
---

## Usage

<code>[GridOutputPorts](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/GridOutputPorts)[$d$]</code> returns the output ports of a diagram's grid layout, in the left-to-right order they appear along the bottom of the grid.

## Basic Examples

```wl
GridOutputPorts @ DiagramArrange @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```

![output](images/GridOutputPorts-out-1.png)
