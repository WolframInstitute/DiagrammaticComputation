---
Template: Symbol
Name: DiagramsNetGraph
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramsNetGraph
Keywords: [net graph, layout, network, diagram graph]
SeeAlso: [DiagramsGraph, DiagramsPortGraph, DiagramNetwork]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramsNetGraph]()[{$d_1$, …}]</code> returns a network graph view of the diagrams suitable for use as a backbone in a <code>[DiagramNetwork]()</code> layout.

## Details & Options

- Used internally by <code>[DiagramNetwork]()</code> when arranging into a grid. The graph carries the connectivity needed by the network layout method (<code>"NetworkMethod"</code> option).

## Basic Examples

Net graph of a small network:

```wl
DiagramsNetGraph[{Diagram["A", a, b], Diagram["B", b, c]}]
```
