---
Template: Symbol
Name: DiagramQ
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramQ
Keywords: [diagram, predicate, validation]
SeeAlso: [Diagram, PortQ, EmptyDiagramQ]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramQ]()[$expr$]</code> gives <code>[True]()</code> if $expr$ is a valid <code>[Diagram]()</code> and <code>[False]()</code> otherwise.

## Details & Options

- <code>[DiagramQ]()</code> checks structural validity, not just the head. Use it as a guard in patterns and option checks (e.g. <code>_? DiagramQ</code>).

## Basic Examples

A constructed diagram is valid:

```wl
DiagramQ[Diagram["A", a, b]]
```

Anything else is not:

```wl
DiagramQ[42]
```
