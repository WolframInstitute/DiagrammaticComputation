---
Template: Symbol
Name: DiagramSum
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramSum
Keywords: [sum, direct sum, additive, choice, CirclePlus, biproduct]
SeeAlso: [Diagram, DiagramProduct, DiagramComposition, DiagramNetwork, PortSum]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramSum]()[$d_1$, $d_2$, $d_3$, …]</code> represents the direct sum (additive choice) of the diagrams $d_i$.

## Details & Options

- The sum diagram has as inputs the <code>[PortSum]()</code> of the inputs of the $d_i$, and as outputs the <code>[PortSum]()</code> of the outputs. Categorically, this is the biproduct in additive monoidal categories.
- The infix shorthand <code>$d_1$ \[CirclePlus] $d_2$</code> evaluated inside <code>[Diagram]()</code> produces a <code>[DiagramSum]()</code>.
- The sum is associative; the unit is <code>[ZeroDiagram]()</code>.

## Basic Examples

Sum two diagrams:

```wl
DiagramSum[Diagram["A", {a, b}, c], Diagram["B", d, e]]
```

## Properties and Relations

<code>[DiagramSum]()</code> is the additive analogue of <code>[DiagramProduct]()</code>
(multiplicative). The closely-related logical reading is <code>[Alternatives]()</code> — a
diagram representing "either".
