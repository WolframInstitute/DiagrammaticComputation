---
Template: Symbol
Name: TopologyGraph
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/TopologyGraph
Keywords: [topology, graph, Feynman, FeynArts]
SeeAlso: [TopologyGraphs, TopologyGraphics, FeynmanDiagram]
RelatedGuides: [FeynmanDiagrams]
---

## Usage

<code>[TopologyGraph]()[$topology$]</code> converts a FeynArts <code>Topology</code> object into a <code>[Graph]()</code>.

## Details & Options

- The $topology$ is a <code>FeynArts\`Topology[…]</code> expression as produced by <code>FeynArts\`CreateTopologies</code>.
- Incoming and outgoing external legs become <code>[DirectedEdge]()</code>s; internal propagators become <code>[UndirectedEdge]()</code>s. Each edge is tagged with its propagator type and field content.
- Vertex coordinates are taken from the FeynArts shape data, so the graph lays out like the conventional FeynArts rendering.

## Basic Examples

Load FeynArts:

```wl
Needs["FeynArts`"]
FeynArts`$FAVerbose = 0;
```

Create the tree-level 2 → 2 topologies and convert the first one to a graph:

```wl
top = First @ CreateTopologies[0, 2 -> 2];
TopologyGraph[top]
```

## Properties and Relations

<code>[TopologyGraphs]()</code> maps this conversion over a whole <code>TopologyList</code>, optionally applying field insertions. The resulting graph is the input format expected by <code>[FeynmanDiagram]()</code>.
