---
Template: Symbol
Name: DiagramExpressionReplace
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramExpressionReplace
Keywords: [replace, expression, internal, data]
SeeAlso: [DiagramReplace, DiagramMap, Replace]
RelatedGuides: [DiagramRewriting]
---

## Usage

<code>[DiagramExpressionReplace]()[$d$, $rules$]</code> applies the ordinary Wolfram Language replacement $rules$ to the expression carried inside every subdiagram of $d$.

## Details & Options

- Operates at the *data* level: it rewrites the <code>"Expression"</code> field of each subdiagram, leaving port structure intact.
- Use this when you need to rename or rewrite the symbols labelling diagrams without touching their connectivity.

## Basic Examples

Rename a singleton diagram's label:

```wl
DiagramExpressionReplace[Diagram["A", a, b], "A" -> "A'"]
```
