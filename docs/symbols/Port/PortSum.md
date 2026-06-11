---
Template: Symbol
Name: PortSum
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/PortSum
Keywords: [port, sum, direct sum, CirclePlus, additive, choice]
SeeAlso: [Port, PortProduct, PortMinus, DiagramSum]
RelatedGuides: [Ports]
---

## Usage

<code>[PortSum]()[$p_1$, $p_2$, …]</code> represents the direct sum of the ports $p_i$.

## Details & Options

- The sum of ports is again a port whose type is the <code>[CirclePlus]()</code> of the component types.
- <code>[PortSum]()</code> is associative; the unit is the zero port <code>[Port]()["0"]</code>.
- The infix shorthand <code>$p_1$ \[CirclePlus] $p_2$</code> evaluated inside <code>[Port]()</code> produces a <code>[PortSum]()</code>.

## Basic Examples

Build a sum of two ports:

```wl
Port[a \[CirclePlus] b]
```

## Properties and Relations

<code>[PortSum]()</code> is the port-level analogue of <code>[DiagramSum]()</code> — taking the
direct sum of two diagrams matches their input and output port sums.
