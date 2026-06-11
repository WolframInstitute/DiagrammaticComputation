---
Template: Symbol
Name: TopologyGraphs
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/TopologyGraphs
Keywords: [topology, graphs, Feynman, FeynArts, insertions]
SeeAlso: [TopologyGraph, FeynmanDiagram, TopologyGraphics]
RelatedGuides: [FeynmanDiagrams]
---

## Usage

<code>[TopologyGraphs]()[$topologies$]</code> converts a FeynArts <code>TopologyList</code> into a list of <code>[Graph]()</code>s.

<code>[TopologyGraphs]()[$topology$ -> $insertions$]</code> produces one graph per field insertion, with edges labelled by the inserted fields.

## Details & Options

- The $topologies$ argument is a <code>FeynArts\`TopologyList</code> from <code>FeynArts\`CreateTopologies</code>, or the result of <code>FeynArts\`InsertFields</code> (whose entries are <code>$topology$ -> $insertions$</code> rules).
- For inserted topologies every combination of fields yields its own graph; edges carry <code>{$index$, $field$}</code> tags that <code>[FeynmanDiagram]()</code> uses to choose line styles and labels.
- The following options can be given:

| Option | Default | Description |
| --- | --- | --- |
| <code>DirectedEdges</code> | <code>[False]()</code> | use directed edges for internal propagators |

- Options of <code>[Graph]()</code> are also accepted and passed through.

## Basic Examples

Load FeynArts:

```wl
Needs["FeynArts`"]
FeynArts`$FAVerbose = 0;
```

Convert all tree-level 2 → 2 topologies:

```wl
TopologyGraphs[CreateTopologies[0, 2 -> 2]]
```

Insert Standard Model fields and get one graph per insertion:

```wl
ins = InsertFields[CreateTopologies[0, 2 -> 2],
  {F[2, {1}], -F[2, {1}]} -> {F[2, {2}], -F[2, {2}]},
  InsertionLevel -> {Classes}];
TopologyGraphs[ins]
```
