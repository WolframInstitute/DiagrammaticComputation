---
Template: Symbol
Name: ToDiagramNetwork
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/ToDiagramNetwork
Keywords: [network, conversion, flatten, refactor]
SeeAlso: [DiagramNetwork, DiagramComposition, DiagramProduct, DiagramArrange]
RelatedGuides: [Diagrams]
---

## Usage

<code>[ToDiagramNetwork]()[$d$]</code> rewrites a composite diagram $d$ as a <code>[DiagramNetwork]()</code>, exposing the port-name connectivity.

## Details & Options

- Flattens nested <code>[DiagramComposition]()</code> and <code>[DiagramProduct]()</code> structure into a single network whose subdiagrams are joined by shared port names.
- The reverse direction is implicit in <code>[DiagramArrange]()</code>, which converts an arbitrary diagram into a layout-friendly form.

## Basic Examples

Convert a composite diagram to a network:

```wl
ToDiagramNetwork[DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]]
```
