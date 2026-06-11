---
Template: Symbol
Name: PortQ
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/PortQ
Keywords: [port, predicate, validation]
SeeAlso: [Port, EmptyPortQ, ZeroPortQ, DiagramQ]
RelatedGuides: [Ports]
---

## Usage

<code>[PortQ]()[$expr$]</code> gives <code>[True]()</code> if $expr$ is a valid <code>[Port]()</code> and <code>[False]()</code> otherwise.

## Details & Options

- <code>[PortQ]()</code> returns <code>[True]()</code> only for objects constructed via the public <code>[Port]()</code>, <code>[PortDual]()</code>, <code>[PortProduct]()</code>, <code>[PortSum]()</code> etc. constructors — it checks structural validity, not just the head.
- Use it as a guard in patterns and option checks (e.g. <code>_? PortQ</code>).

## Basic Examples

A constructed port is valid:

```wl
PortQ[Port[a]]
```

Anything else is not:

```wl
PortQ["hello"]
```
