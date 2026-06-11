---
Template: Symbol
Name: DiagramMapAt
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramMapAt
Keywords: [map at, transform, position, targeted]
SeeAlso: [DiagramMap, DiagramReplacePart, MapAt]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramMapAt]()[$f$, $d$, {$i$, $j$, …}]</code> applies $f$ to the subdiagram of $d$ at position {$i$, $j$, …}.

<code>[DiagramMapAt]()[$f$, $d$, {$pos_1$, $pos_2$, …}]</code> applies $f$ at all the positions $pos_i$.

<code>[DiagramMapAt]()[$f$, $pos$][$d$]</code> is the operator form.

## Details & Options

- $f$ receives two arguments — the subdiagram and its position — and its result is wrapped back into a <code>[Diagram]()</code>.
- Positions follow the <code>[DiagramPositions]()</code> convention; the diagram analogue of <code>[MapAt]()</code>.

## Basic Examples

Restyle only the second subdiagram:

```wl
DiagramMapAt[Diagram[#, "Shape" -> "Circle"] &, DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]], {2}]
```

The function also receives the position:

```wl
DiagramMapAt[Diagram[#1, "Expression" -> ToString[#2]] &, DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]], {2}]
```
