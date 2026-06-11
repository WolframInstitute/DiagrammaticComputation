---
Template: Symbol
Name: DiagramDraw
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramDraw
Keywords: [interactive, draw, canvas, GUI, palette]
SeeAlso: [Diagram, DiagramGrid, DiagramGraphics, MoleculeDraw]
RelatedGuides: [DiagramDrawing]
---

## Usage

<code>[DiagramDraw]()[]</code> opens an interactive canvas for sketching a diagram and returns the constructed <code>[Diagram]()</code> expression.

<code>[DiagramDraw]()[$d$]</code> opens the canvas seeded with the existing diagram $d$.

## Details & Options

- Boxes, ports and wires are placed by hand on the canvas. The resulting diagram can be copied back into a notebook and used like any other <code>[Diagram]()</code>.
- Useful for sketching small examples and exporting them as symbolic diagrams. For programmatic construction, use the <code>[Diagram]()</code> family directly.

## Basic Examples

Open the drawing canvas:

```wl
DiagramDraw[]
```

The canvas returns a constructed <code>[Diagram]()</code> expression once drawing is complete.
