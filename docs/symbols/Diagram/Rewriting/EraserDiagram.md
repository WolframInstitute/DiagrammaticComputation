---
Template: Symbol
Name: EraserDiagram
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/EraserDiagram
Keywords: [eraser, discard, counit, terminal]
SeeAlso: [CapDiagram, CopyDiagram, EraserRule, EraserAnnihilationRule]
RelatedGuides: [DiagramRewriting]
---

## Usage

<code>[EraserDiagram]()[$p$]</code> is the canonical erase / discard diagram on the port $p$ — one input, no outputs.

## Details & Options

- The eraser is the counit of the classical-structure on a wire: composing it with <code>[CopyDiagram]()</code> projects out one of the copies.
- Together with <code>[CopyDiagram]()</code> and <code>[MergeDiagram]()</code> it generates the standard structural rewrites in <code>[EraserRule]()</code> and friends.

## Basic Examples

```wl
EraserDiagram[a]
```
