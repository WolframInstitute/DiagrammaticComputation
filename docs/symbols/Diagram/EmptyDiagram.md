---
Template: Symbol
Name: EmptyDiagram
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/EmptyDiagram
Keywords: [empty, identity, unit, monoidal product]
SeeAlso: [Diagram, IdentityDiagram, EmptyDiagramQ, ZeroDiagram, DiagramProduct]
RelatedGuides: [Diagrams]
---

## Usage

<code>[EmptyDiagram]()[]</code> is the empty diagram — the unit of <code>[DiagramProduct]()</code> and <code>[DiagramComposition]()</code>.

## Details & Options

- The empty diagram has no subdiagrams and identity port mappings (its input and output port lists are empty).
- <code>[DiagramProduct]()[$d$, [EmptyDiagram]()[]] == $d$</code> and similarly for any other position.

## Basic Examples

The unit of the tensor product:

```wl
EmptyDiagram[]
```

## Properties and Relations

<code>[EmptyDiagram]()</code> is the multiplicative identity; <code>[ZeroDiagram]()</code> is its
additive counterpart. Use <code>[EmptyDiagramQ]()</code> to test.
