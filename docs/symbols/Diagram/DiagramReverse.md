---
Template: Symbol
Name: DiagramReverse
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramReverse
Keywords: [reverse, horizontal reflection, port ordering]
SeeAlso: [Diagram, DiagramDual, DiagramFlip, DiagramPermute, Reverse]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramReverse]()[$d$]</code> reflects the diagram $d$ horizontally — reverses the order of its input ports and the order of its output ports.

## Details & Options

- <code>[DiagramReverse]()</code> is an involution.
- It does not change port directions; only the ordering of inputs and outputs is reversed.

## Basic Examples

Reverse the port order of a diagram:

```wl
DiagramReverse[Diagram["A", {a, b, c}, {x, y}]]
```

## Properties and Relations

<code>[DiagramReverse]()</code> is the horizontal counterpart of <code>[DiagramFlip]()</code>
(vertical). For more general re-orderings use <code>[DiagramPermute]()</code>.
