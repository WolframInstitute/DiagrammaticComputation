---
Template: Symbol
Name: DiagramGraphSimplify
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramGraphSimplify
Keywords: [simplify, graph, wire, contraction]
SeeAlso: [SimplifyDiagram, DiagramsGraph, DiagramsNetGraph]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramGraphSimplify]()[$g$]</code> simplifies a diagram graph $g$ by deleting wire-shaped vertices and reconnecting the edges that passed through them.

## Details & Options

- The argument is a <code>[Graph]()</code> whose vertices carry <code>"Diagram"</code> annotations — the form produced by a diagram's <code>"Graph"</code> property.
- Vertices whose diagram is empty, or whose shape is a pure wire bundle (<code>"Wires"[…]</code> — identities, permutations), are removed; their incoming and outgoing edges are joined according to the wire connectivity.
- This is the graph-level engine behind a diagram's <code>"Simplify"</code> option; the diagram-level counterpart is <code>[SimplifyDiagram]()</code>.

## Basic Examples

Simplify away an identity wire from a composition's graph:

```wl
g = DiagramComposition[IdentityDiagram[a], Diagram["A", b, a]]["Graph"]
```

```wl
DiagramGraphSimplify[g]
```
