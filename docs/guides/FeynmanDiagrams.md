---
Template: Guide
Name: FeynmanDiagrams
Title: Feynman Diagrams
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/guide/FeynmanDiagrams
Description: Build, render and enumerate Feynman-style diagrams over a topology graph
Keywords: [Feynman, topology, propagator, vertex, particle physics, FeynArts]
RelatedGuides: [Diagrams]
---

## Abstract

Feynman diagrams are a particular use of the diagrammatic calculus where
vertices are field interactions and edges (wires) are propagators. These
functions bridge [FeynArts](http://www.feynarts.de) and the diagram
representation: topologies created with <code>FeynArts\`CreateTopologies</code>
(optionally with field insertions from <code>FeynArts\`InsertFields</code>)
convert to graphs and on to <code>[Diagram]()</code> networks, with
propagators drawn in the conventional wiggly / dashed / solid-line styles.
FeynArts must be installed and loaded for these functions to operate.

## Functions

### Diagram

- `FeynmanDiagram` — construct a diagram network from a topology graph

### Topologies

- `TopologyGraph` — convert a FeynArts topology to a graph
- `TopologyGraphs` — convert a FeynArts topology list, one graph per field insertion
- `TopologyGraphics` — FeynArts graphics data for a topology with insertions
- `FeynArtsTopologyGraphics` — render a topology in the FeynArts house style

### Styling

- `WigglyArcFunction` — propagator line-style function (straight, dashed, wiggly, helix)
