---
Template: Symbol
Name: DiagramSubdiagrams
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramSubdiagrams
Keywords: [subdiagrams, decomposition, recurse]
SeeAlso: [DiagramPositions, DiagramCases, DiagramDecompose]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramSubdiagrams]()[$d$]</code> returns a list of every subdiagram of $d$, including $d$ itself.

## Details & Options

- The list is ordered by recursive descent through <code>[DiagramComposition]()</code>, <code>[DiagramProduct]()</code>, <code>[DiagramSum]()</code> and <code>[DiagramNetwork]()</code>.

## Basic Examples

List all subdiagrams of a composition:

```wl
DiagramSubdiagrams @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```
