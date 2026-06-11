---
Template: Symbol
Name: DiagramCopySplit
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramCopySplit
Keywords: [copy, split, distribute, rule]
SeeAlso: [CopyDiagram, PropagationRule, DiagramRule]
RelatedGuides: [DiagramRewriting]
---

## Usage

<code>[DiagramCopySplit]()[$d$]</code> rewrites a copy of $d$ into the composition of two parallel copies of $d$, distributing a <code>[CopyDiagram]()</code> across $d$.

## Details & Options

- Encodes the law <code>copy ∘ d = (d ⊗ d) ∘ copy</code> when $d$ is a *natural* diagram (one whose meaning duplicates across the classical structure).

## Basic Examples

```wl
DiagramCopySplit[Diagram["A", a, b]]
```
