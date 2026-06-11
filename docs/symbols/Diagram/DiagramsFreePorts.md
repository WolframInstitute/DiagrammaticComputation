---
Template: Symbol
Name: DiagramsFreePorts
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramsFreePorts
Keywords: [free ports, dangling, boundary]
SeeAlso: [DiagramsPortGraph, DiagramsGraph, DiagramsNetGraph, DiagramNetwork]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramsFreePorts]()[{$d_1$, $d_2$, …}]</code> returns the free ports of the diagrams $d_i$ — the ports whose expression occurs exactly once across all of them.

## Details & Options

- A port occurring twice (or more) is shared between subdiagrams and would be joined in a <code>[DiagramNetwork]()</code> of the $d_i$; the remaining single-occurrence ports are the network's boundary.
- The result is a list of held port expressions; input ports appear wrapped in <code>[PortDual]()</code>.

## Basic Examples

Two diagrams sharing the input port <code>a</code> have free ports <code>b</code> and <code>c</code>:

```wl
DiagramsFreePorts[{Diagram["A", a, b], Diagram["B", a, c]}]
```
