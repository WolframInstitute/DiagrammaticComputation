---
Template: Symbol
Name: DiagramTensor
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramTensor
Keywords: [tensor, contraction, evaluation, tensor network, array]
SeeAlso: [TensorDiagram, DiagramFunction, ArrayDot, TensorContract]
RelatedGuides: [Diagrams, DiagramConversion]
---

## Usage

<code>[DiagramTensor]()[$d$]</code> returns a symbolic tensor expression representing the diagram $d$ as a tensor contraction.

## Details & Options

- Composition becomes <code>[ArrayDot]()</code> / <code>[TensorContract]()</code> and product becomes <code>[TensorProduct]()</code>. Singleton diagrams become symbolic arrays whose dimensions are taken from the diagram's port types.
- The result is an inactive tensor expression — wrap in <code>[Activate]()</code> to evaluate when the underlying tensors are concrete.
- Inverse direction: <code>[TensorDiagram]()</code> lifts a tensor expression back to a diagram.

## Basic Examples

Express a composite diagram as a contracted tensor:

```wl
diagram = Diagram[Diagram["A", a, b] \[CircleTimes] Diagram["C", d, e] \[CircleDot] Diagram["B", c, d]];
DiagramTensor[diagram]
```

Inspect the dimensions of the result:

```wl
TensorDimensions[Activate @ DiagramTensor[diagram]]
```

## Properties and Relations

<code>[DiagramTensor]()</code> and <code>[TensorDiagram]()</code> are inverse: the round-trip
restores the original diagram up to the underlying tensor network.
