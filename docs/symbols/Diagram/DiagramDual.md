---
Template: Symbol
Name: DiagramDual
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramDual
Keywords: [dual, conjugate, reverse arrows, transpose]
SeeAlso: [Diagram, DiagramFlip, DiagramReverse, PortDual]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramDual]()[$d$]</code> changes the direction of every port of the diagram $d$ — outputs become inputs and vice versa, with each port dualised.

## Details & Options

- <code>[DiagramDual]()</code> is an involution: <code>[DiagramDual]()[[DiagramDual]()[$d$]] == $d$</code>.
- It is *port-wise* duality: each port is replaced by its <code>[PortDual]()</code>, and the input/output lists are swapped.
- The shorthand <code>$d^*$</code> produces a <code>[DiagramDual]()</code>.

## Basic Examples

Reverse the direction of all ports of a diagram:

```wl
DiagramDual[Diagram["A", {a, b, c}, {x, y}]]
```

## Properties and Relations

<code>[DiagramDual]()</code> is one of three involutions on diagrams: <code>[DiagramFlip]()</code>
swaps inputs and outputs without dualising ports, and <code>[DiagramReverse]()</code>
reverses the *order* of the ports without changing their direction.
