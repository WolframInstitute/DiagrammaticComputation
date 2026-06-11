---
Template: Symbol
Name: DiagramPositions
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramPositions
Keywords: [positions, indices, addressing]
SeeAlso: [DiagramSubdiagrams, DiagramPosition, DiagramExtract]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramPositions]()[$d$]</code> returns the list of positions of every subdiagram of $d$.

## Details & Options

- Positions are integer-list addresses into the diagram's expression tree, in the same convention as <code>[Position]()</code> and <code>[Extract]()</code> on Wolfram Language expressions.
- The empty position <code>{}</code> refers to the diagram itself.

## Basic Examples

List the positions of all subdiagrams:

```wl
DiagramPositions @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```
