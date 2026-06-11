---
Template: Symbol
Name: PortMinus
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/PortMinus
Keywords: [port, minus, negation, additive inverse, sum]
SeeAlso: [Port, PortSum, PortDual]
RelatedGuides: [Ports]
---

## Usage

<code>[PortMinus]()[$p$]</code> represents the additive inverse of the port $p$ inside a <code>[PortSum]()</code>.

## Details & Options

- <code>[PortMinus]()</code> is used to express formal subtractions in a port sum; <code>[Port]()[$a$ - $b$]</code> normalises to <code>[PortSum]()[[Port]()[$a$], [PortMinus]()[[Port]()[$b$]]]</code>.
- Sequential negation is involutive: <code>[PortMinus]()[[PortMinus]()[$p$]] == $p$</code>.

## Basic Examples

Build a signed port sum:

```wl
Port[a - b]
```
