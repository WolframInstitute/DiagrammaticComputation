---
Template: Symbol
Name: SimplifyDiagram
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/SimplifyDiagram
Keywords: [simplify, absorb identity, normalise]
SeeAlso: [DiagramGraphSimplify, IdentityDiagram, DiagramArrange]
RelatedGuides: [Diagrams]
---

## Usage

<code>[SimplifyDiagram]()[$d$]</code> simplifies the diagram $d$ by absorbing identity wires and other trivially-redundant structure.

## Details & Options

- Removes <code>[IdentityDiagram]()</code> wires from compositions and contracts unary spiders, leaving a structurally simpler diagram with the same meaning.
- Does *not* apply rewriting rules — those go through <code>[DiagramReplace]()</code> / <code>[DiagramNestReplace]()</code>.

## Basic Examples

Remove an identity wire from a composition:

```wl
SimplifyDiagram[DiagramComposition[IdentityDiagram[a], Diagram["A", b, a]]]
```
