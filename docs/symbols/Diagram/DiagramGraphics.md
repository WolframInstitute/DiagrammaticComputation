---
Template: Symbol
Name: DiagramGraphics
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramGraphics
Keywords: [graphics, single node, render, box]
SeeAlso: [Diagram, DiagramGrid, DiagramDraw]
RelatedGuides: [Diagrams, DiagramGrid]
---

## Usage

<code>[DiagramGraphics]()[$d$]</code> returns a graphical representation of the diagram $d$ as a single labelled node with attached input and output ports.

## Details & Options

- Used by <code>[Diagram]()</code> itself to render an opaque diagram. Unlike <code>[DiagramGrid]()</code>, it does *not* decompose composite diagrams into a grid of subdiagrams — the whole diagram is shown as one box.
- Accepts the same shape-, port-, and label-related options as <code>[Diagram]()</code>.

## Basic Examples

Show single-node graphics for a <code>[Diagram]()</code>:

```wl
DiagramGraphics[Diagram["A", {a, b}, c]]
```

A composite diagram is also rendered as a single node:

```wl
DiagramGraphics[DiagramProduct[Diagram["A", a, b], Diagram["B", c, d]]]
```

## Properties and Relations

<code>[DiagramGraphics]()</code> is the *node* view; <code>[DiagramGrid]()</code> is the
*decomposed* view that lays subdiagrams out in a 2D grid.
