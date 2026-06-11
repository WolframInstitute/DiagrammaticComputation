---
Template: Symbol
Name: DiagramSplit
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramSplit
Keywords: [split, partition, repartition, ports, currying]
SeeAlso: [Diagram, DiagramReverse, DiagramFlip, IdentityDiagram]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramSplit]()[$d$, $k$]</code> moves $k$ ports from the output side of $d$ to the input side (or, with $k$ negative, the other direction), repartitioning its ports.

## Details & Options

- Repartitioning a diagram is the diagrammatic analogue of currying / uncurrying a function: it shifts the boundary between inputs and outputs while leaving the underlying process untouched.
- Used together with <code>[CapDiagram]()</code> and <code>[CupDiagram]()</code> it implements process / state duality.

## Basic Examples

Move one output of a diagram to its inputs:

```wl
DiagramSplit[Diagram["A", a, {x, y}], 1]
```
