---
Template: Symbol
Name: DiagramInsert
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramInsert
Keywords: [insert, position, splice]
SeeAlso: [DiagramExtract, DiagramDelete, DiagramReplacePart, Insert]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramInsert](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramInsert)[$d$, $sub$, $position$]</code> inserts the subdiagram $sub$ at $position$ inside $d$.

## Basic Examples

Insert an identity wire into a composition:

```wl
DiagramInsert[
  DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]],
  IdentityDiagram[b],
  {2}
]
```

![output](images/DiagramInsert-out-1.png)
