---
Template: Symbol
Name: TopologyGraphics
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/TopologyGraphics
Keywords: [topology, graphics, FeynArts, render]
SeeAlso: [FeynArtsTopologyGraphics, TopologyGraph, FeynmanDiagram]
RelatedGuides: [FeynmanDiagrams]
---

## Usage

<code>[TopologyGraphics]()[$topology$ -> $insertions$]</code> computes the FeynArts graphics data (<code>DiagramGraphics</code>) for a topology with field insertions.

## Details & Options

- A low-level helper: it resolves vertex placements and propagator shapes through the FeynArts shape database and returns one <code>FeynArts\`DiagramGraphics</code> object per insertion.
- <code>[FeynArtsTopologyGraphics]()</code> wraps this and renders the result to ordinary <code>[Graphics]()</code>; use that for display.

## Basic Examples

Compute the graphics data for a topology and its field insertions (one <code>DiagramGraphics</code> per inserted graph):

```wl
#| eval: false
TopologyGraphics[topology -> insertedGraphs]
```

For rendered output, use <code>[FeynArtsTopologyGraphics]()</code>, which feeds this data through the FeynArts renderer:

```wl
Needs["FeynArts`"]
FeynArts`$FAVerbose = 0;
```

```wl
FeynArtsTopologyGraphics[First @ CreateTopologies[0, 2 -> 2]]
```
