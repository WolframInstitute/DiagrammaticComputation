---
Template: Guide
Name: DiagramSurgery
Title: Diagram Surgery
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/guide/DiagramSurgery
Description: "Inspect, locate, map over and edit the subdiagrams of a composite diagram"
Keywords: [surgery, position, pattern, map, replace, extract, insert, delete, subdiagram]
RelatedGuides: [Diagrams, DiagramRewriting]
---

## Abstract

A composite diagram has a tree of subdiagrams that mirrors its compositional structure, and these subdiagrams can be inspected, matched and edited the same way ordinary expressions can. The functions in this guide are the diagram analogues of <code>[Position](https://reference.wolfram.com/language/ref/Position.html)</code>, <code>[Cases](https://reference.wolfram.com/language/ref/Cases.html)</code>, <code>[Map](https://reference.wolfram.com/language/ref/Map.html)</code>, <code>[MapAt](https://reference.wolfram.com/language/ref/MapAt.html)</code>, <code>[Extract](https://reference.wolfram.com/language/ref/Extract.html)</code>, <code>[Insert](https://reference.wolfram.com/language/ref/Insert.html)</code>, <code>[Delete](https://reference.wolfram.com/language/ref/Delete.html)</code> and <code>[ReplacePart](https://reference.wolfram.com/language/ref/ReplacePart.html)</code> — they work on the diagram's subdiagram tree, using <code>[DiagramPattern](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramPattern)</code> for matching. This is the plumbing under <code>DiagramRewriting</code>; reach for it when you want non-pattern edits or want to write a custom rewriter.

## Functions

### Inspection

- `DiagramSubdiagrams` — list all subdiagrams of a diagram
- `DiagramPositions` — positions of every subdiagram

### Patterns

- `DiagramPattern` — diagram-shaped pattern for matching subdiagrams

### Locating

- `DiagramPosition` — positions of subdiagrams matching a pattern
- `DiagramCases` — extract subdiagrams matching a pattern

### Editing

- `DiagramMap` — apply a function to every subdiagram recursively
- `DiagramMapAt` — apply a function at specific positions
- `DiagramExtract` — extract the subdiagram at a position
- `DiagramInsert` — insert a subdiagram at a position
- `DiagramDelete` — delete the subdiagram at a position
- `DiagramReplacePart` — replace subdiagrams at specific positions
