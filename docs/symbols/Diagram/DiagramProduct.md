---
Template: Symbol
Name: DiagramProduct
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramProduct
Keywords: [product, parallel, horizontal, tensor, CircleTimes, monoidal]
SeeAlso: [Diagram, DiagramComposition, DiagramNetwork, DiagramSum, RowDiagram, PortProduct]
RelatedGuides: [Diagrams, DiagramGrid]
---

## Usage

<code>[DiagramProduct]()[$d_1$, $d_2$, $d_3$, …]</code> represents the parallel (tensor) composition of the diagrams $d_i$.

## Details & Options

- The product diagram has as inputs the <code>[PortProduct]()</code> of the inputs of the $d_i$ in order, and as outputs the <code>[PortProduct]()</code> of the outputs in order.
- The infix shorthand <code>$d_1$ \[CircleTimes] $d_2$</code> evaluated inside <code>[Diagram]()</code> produces a <code>[DiagramProduct]()</code>.
- The product is associative; the unit is <code>[EmptyDiagram]()</code>.

## Basic Examples

Compose diagrams in parallel:

```wl
DiagramProduct[Diagram["A", {a, b}, c], Diagram["B", d, e]]
```

Use <code>[CircleTimes]()</code>:

```wl
Diagram[Diagram["A", a, b] \[CircleTimes] Diagram["B", c, d]]
```

## Properties and Relations

<code>[DiagramProduct]()</code> is the parallel analogue of <code>[DiagramComposition]()</code>
(sequential). At the tensor level it corresponds to <code>[TensorProduct]()</code> /
<code>[KroneckerProduct]()</code>. The layout-level analogue is <code>[RowDiagram]()</code>.
