---
Template: Symbol
Name: TensorDiagram
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/TensorDiagram
Keywords: [tensor, conversion, import, matrix, vector, ArraySymbol]
SeeAlso: [DiagramTensor, ToDiagram, DiagramFunction]
RelatedGuides: [Diagrams, DiagramConversion]
---

## Usage

<code>[TensorDiagram]()[$tensor$]</code> represents the tensor expression $tensor$ as a diagram.

## Details & Options

- Numeric arrays become diagrams with their leg dimensions exposed as port types: a vector has one output, a matrix has one input and one output, a rank-$n$ array has $n$ ports.
- <code>[VectorSymbol]()</code>, <code>[MatrixSymbol]()</code>, <code>[ArraySymbol]()</code> and <code>[ArrayDot]()</code> / <code>[TensorContract]()</code> / <code>[TensorProduct]()</code> expressions all lift into diagrams in the obvious way.

## Basic Examples

A vector (rank-1) becomes a diagram with one output:

```wl
TensorDiagram[{1, 2, 3, 4}]
```

A matrix (rank-2) becomes a diagram with one input and one output:

```wl
TensorDiagram[{{1, 2}, {3, 4}}]
```

Symbolic arrays lift directly:

```wl
TensorDiagram[MatrixSymbol[M, {3, 4}]]
```

```wl
TensorDiagram[ArraySymbol[A, {3, 4, 5}]]
```

Contracted tensor expressions become composite diagrams:

```wl
TensorDiagram[Dot[VectorSymbol[v, 2], VectorSymbol[w, 2]]]
```

## Properties and Relations

<code>[TensorDiagram]()</code> is the inverse of <code>[DiagramTensor]()</code>.
