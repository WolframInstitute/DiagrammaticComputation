---
Template: Symbol
Name: ZeroPortQ
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/ZeroPortQ
Keywords: [port, predicate, zero, unit, direct sum]
SeeAlso: [PortQ, EmptyPortQ, Port, PortSum]
RelatedGuides: [Ports]
---

## Usage

<code>[ZeroPortQ]()[$p$]</code> gives <code>[True]()</code> if $p$ is the unit port for <code>[PortSum]()</code> (the zero port).

## Details & Options

- The zero port is the identity element of <code>[PortSum]()</code>: summing any port with the zero port returns it unchanged.
- It is constructed by <code>[Port]()["0"]</code>.

## Basic Examples

The zero port is zero:

```wl
ZeroPortQ[Port["0"]]
```

A non-zero port is not:

```wl
ZeroPortQ[Port[a]]
```
