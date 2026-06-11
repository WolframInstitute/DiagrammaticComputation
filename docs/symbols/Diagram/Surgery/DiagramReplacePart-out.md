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

<code>[DiagramReplacePart](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramReplacePart)[$d$, $position$ -> $new$]</code> replaces the subdiagram of $d$ at $position$ with $new$.

<code>[DiagramReplacePart](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramReplacePart)[$d$, {$pos_1$ -> $new_1$, $pos_2$ -> $new_2$, ...}]</code> replaces at several positions.

## Basic Examples

Swap out the second subdiagram:

```wl
DiagramReplacePart[
  DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]],
  {2} -> Diagram["B'", c, b]
]
```

![output](images/DiagramReplacePart-out-1.png)
