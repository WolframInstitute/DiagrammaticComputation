---
Template: Symbol
Name: PortProduct
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/PortProduct
Keywords: [port, product, tensor, parallel, CircleTimes, monoidal]
SeeAlso: [Port, PortSum, PortDual, PortPower, DiagramProduct]
RelatedGuides: [Ports]
---

## Usage

<code>[PortProduct]()[$p_1$, $p_2$, …]</code> represents the parallel (tensor) product of the ports $p_i$.

## Details & Options

- The product of ports is again a port whose type is the <code>[CircleTimes]()</code> of the component types.
- <code>[PortProduct]()</code> is associative; the unit is the empty port <code>[Port]()["1"]</code>.
- The infix shorthand <code>$p_1$ \[CircleTimes] $p_2$</code> evaluated inside <code>[Port]()</code> produces a <code>[PortProduct]()</code>.
- Dualising distributes with reversal: <code>[PortDual]()[[PortProduct]()[$p_1$, $p_2$]] == [PortProduct]()[[PortDual]()[$p_2$], [PortDual]()[$p_1$]]</code>.

## Basic Examples

Build a product of two ports:

```wl
PortProduct[Port[a], Port[b]]
```

Using <code>[CircleTimes]()</code>:

```wl
Port[a \[CircleTimes] b]
```

## Properties and Relations

<code>[PortProduct]()</code> is the port-level analogue of <code>[DiagramProduct]()</code> — composing
diagrams in parallel matches their input and output port products.
