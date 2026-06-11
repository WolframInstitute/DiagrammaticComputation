---
Template: Symbol
Name: EmptyPortQ
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/EmptyPortQ
Keywords: [port, predicate, empty, unit, monoidal]
SeeAlso: [PortQ, ZeroPortQ, Port, PortProduct]
RelatedGuides: [Ports]
---

## Usage

<code>[EmptyPortQ]()[$p$]</code> gives <code>[True]()</code> if $p$ is the unit port for <code>[PortProduct]()</code> (the empty product).

## Details & Options

- The empty port is the identity element of <code>[PortProduct]()</code>: composing any port with the empty port returns it unchanged.
- It is constructed by <code>[Port]()["1"]</code> or <code>[Port]()[$p^0$]</code>.

## Basic Examples

The empty port is empty:

```wl
EmptyPortQ[Port["1"]]
```

A non-empty port is not:

```wl
EmptyPortQ[Port[a]]
```
