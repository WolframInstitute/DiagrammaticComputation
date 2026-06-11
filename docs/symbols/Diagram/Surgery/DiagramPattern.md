---
Template: Symbol
Name: DiagramPattern
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramPattern
Keywords: [pattern, match, blank, diagram pattern]
SeeAlso: [DiagramPosition, DiagramCases, DiagramReplace, DiagramRule]
RelatedGuides: [DiagramSurgery, DiagramRewriting]
---

## Usage

<code>[DiagramPattern]()[$expr$, $inputs$, $outputs$]</code> represents a diagram-shaped pattern for matching against subdiagrams.

## Details & Options

- A <code>[DiagramPattern]()</code> is to <code>[Diagram]()</code> what a pattern with blanks is to an ordinary expression. The $expr$, $inputs$ and $outputs$ slots accept patterns (including <code>_</code>, <code>[Blank]()</code>, named patterns and conditionals).
- Used as the matcher in <code>[DiagramPosition]()</code>, <code>[DiagramCases]()</code>, <code>[DiagramReplace]()</code> and <code>[DiagramRule]()</code>.

## Basic Examples

Match any singleton diagram with one input and one output:

```wl
DiagramPattern[_, {_}, {_}]
```
