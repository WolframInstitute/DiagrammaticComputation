---
Template: Symbol
Name: DiagramPermute
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramPermute
Keywords: [permute, reorder, ports, cycles, transpose]
SeeAlso: [DiagramSplit, DiagramReverse, PermutationDiagram, Permute, Cycles]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramPermute]()[$d$, $perm$]</code> permutes the ports of the diagram $d$ by the permutation $perm$.

<code>[DiagramPermute]()[$d$, $perm$, $dualQ$]</code> controls whether ports moved across the input/output boundary are dualised.

## Details & Options

- $perm$ is a <code>[Cycles]()</code> object (or anything <code>[Permute]()</code> accepts) acting on the flattened port list — output ports first, then input ports.
- A permutation within the outputs composes a <code>[PermutationDiagram]()</code> after $d$; one within the inputs composes it before; a permutation crossing the boundary additionally bends wires like <code>[DiagramSplit]()</code>.
- For a singleton tensor-annotated diagram, the permutation is recorded as a <code>[Transpose]()</code> of the underlying tensor.

## Basic Examples

Swap the two output ports of a process:

```wl
DiagramPermute[Diagram[A, {a, b}, {x, y}], Cycles[{{1, 2}}]]
```

Permute ports across the input/output boundary:

```wl
DiagramPermute[Diagram[A, {a, b}, {x, y}], Cycles[{{1, 3}}]]
```

## Properties and Relations

<code>[DiagramReverse]()</code> is the special case of reversing the port order; <code>[DiagramSplit]()</code> moves the input/output boundary without reordering.
