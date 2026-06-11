---
Template: Symbol
Name: DiagramsGraph
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramsGraph
Keywords: [graph, diagram graph, connectivity, network]
SeeAlso: [DiagramsPortGraph, DiagramsNetGraph, DiagramHypergraph]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramsGraph]()[{$d_1$, …}]</code> returns a graph view of the diagrams where each vertex is a whole diagram and each edge is a shared wire between two diagrams.

## Details & Options

- The coarser counterpart of <code>[DiagramsPortGraph]()</code>: vertices are diagrams (not ports), edges represent any matched port pair.

## Basic Examples

Graph of two diagrams sharing a wire:

```wl
DiagramsGraph[{Diagram["A", a, b], Diagram["B", b, c]}]
```
