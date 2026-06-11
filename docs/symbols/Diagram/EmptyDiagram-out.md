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

<code>[EmptyDiagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/EmptyDiagram)[]</code> is the empty diagram — the unit of <code>[DiagramProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramProduct)</code> and <code>[DiagramComposition](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramComposition)</code>.

## Details & Options

- The empty diagram has no subdiagrams and identity port mappings (its input and output port lists are empty).
- <code>[DiagramProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramProduct)[$d$, [EmptyDiagram]()[]] == $d$</code> and similarly for any other position.

## Basic Examples

The unit of the tensor product:

```wl
EmptyDiagram[]
```

![output](images/EmptyDiagram-out-1.png)

## Properties and Relations

<code>[EmptyDiagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/EmptyDiagram)</code> is the multiplicative identity; <code>[ZeroDiagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/ZeroDiagram)</code> is its additive counterpart. Use <code>[EmptyDiagramQ](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/EmptyDiagramQ)</code> to test.
