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

<code>[DiagramReplacePart](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramReplacePart)[$d$, {$i$, $j$, …} -> $new$]</code> replaces the subdiagram of $d$ at position {$i$, $j$, …} with the diagram $new$.

<code>[DiagramReplacePart](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramReplacePart)[$d$, {$pos_1$, $pos_2$, …} -> $new$]</code> replaces the subdiagrams at all the positions $pos_i$ with $new$.

## Details & Options

- Positions follow the <code>[DiagramPositions](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramPositions)</code> convention; the diagram analogue of <code>[ReplacePart](https://reference.wolfram.com/language/ref/ReplacePart.html)</code>.
- To compute the replacement from the existing subdiagram (or its position), use <code>[DiagramMapAt](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramMapAt)</code>.

## Basic Examples

Swap out the second subdiagram:

```wl
DiagramReplacePart[
  DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]],
  {2} -> Diagram["X", c, b]
]
```

![output](images/DiagramReplacePart-out-1.png)
