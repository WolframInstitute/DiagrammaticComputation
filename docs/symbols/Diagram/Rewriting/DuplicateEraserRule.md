---
Template: Symbol
Name: DuplicateEraserRule
Context: Wolfram`DiagrammaticComputation`Rewriting`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DuplicateEraserRule
Keywords: [duplicate, eraser, copy, discard, rule, interaction net]
SeeAlso: [CopyDiagram, EraserDiagram, DuplicateAnnihilationRule, DiagramRule]
RelatedGuides: [DiagramRewriting]
---

## Usage

<code>[DuplicateEraserRule]()[$in$, $out$]</code> returns a rewrite rule expressing that a copy node with one leg erased reduces to an identity wire from $in$ to $out$.

## Details & Options

- Encodes the interaction-net copy–erase law: erasing one branch of a copy leaves a plain wire on the surviving branch.

## Basic Examples

The copy–erase law:

```wl
DuplicateEraserRule[x, y]
```
