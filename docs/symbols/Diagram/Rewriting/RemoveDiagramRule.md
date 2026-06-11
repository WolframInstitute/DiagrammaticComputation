---
Template: Symbol
Name: RemoveDiagramRule
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/RemoveDiagramRule
Keywords: [remove, rule, deletion, rewrite]
SeeAlso: [DiagramRule, DiagramReplace, DiagramNestReplace, DiagramDelete]
RelatedGuides: [DiagramRewriting]
---

## Usage

<code>[RemoveDiagramRule]()[$d$]</code> constructs a rewrite rule that deletes subdiagrams matching the diagram $d$, reconnecting the wires it leaves behind.

## Details & Options

- The resulting rule replaces a match of $d$ with identity wires on its ports, so the surrounding diagram stays connected.
- Use with <code>[DiagramReplace]()</code> / <code>[DiagramNestReplace]()</code> like any other rule.

## Basic Examples

A rule deleting any subdiagram labelled <code>"A"</code> with one input and one output:

```wl
RemoveDiagramRule[Diagram["A", \[FormalY], \[FormalX]]]
```

Apply it to a composition:

```wl
DiagramReplace[
  DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]],
  RemoveDiagramRule[Diagram["A", \[FormalY], \[FormalX]]]
]
```
