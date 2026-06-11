---
Template: Symbol
Name: DiagramReplacePart
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramReplacePart
Keywords: [replace part, position, edit, splice]
SeeAlso: [DiagramMapAt, DiagramInsert, DiagramDelete, ReplacePart]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramReplacePart]()[$d$, {$i$, $j$, …} -> $new$]</code> replaces the subdiagram of $d$ at position {$i$, $j$, …} with the diagram $new$.

<code>[DiagramReplacePart]()[$d$, {$pos_1$, $pos_2$, …} -> $new$]</code> replaces the subdiagrams at all the positions $pos_i$ with $new$.

## Details & Options

- Positions follow the <code>[DiagramPositions]()</code> convention; the diagram analogue of <code>[ReplacePart]()</code>.
- To compute the replacement from the existing subdiagram (or its position), use <code>[DiagramMapAt]()</code>.

## Basic Examples

Swap out the second subdiagram:

```wl
DiagramReplacePart[
  DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]],
  {2} -> Diagram["X", c, b]
]
```
