---
Template: Symbol
Name: DiagramAssignPorts
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramAssignPorts
Keywords: [assign, ports, rename, naming]
SeeAlso: [DiagramMatchPorts, Diagram, DiagramArrange]
RelatedGuides: [DiagramGrid, DiagramSurgery]
---

## Usage

<code>[DiagramAssignPorts]()[$d$, {$i_1$, …}, {$o_1$, …}]</code> assigns the explicit input ports $i_1, …$ and output ports $o_1, …$ to the diagram $d$.

<code>[DiagramAssignPorts]()[$d$, $rules$]</code> renames ports according to a list of <code>oldName -> newName</code> rules.

## Details & Options

- Useful when grafting a diagram into a network with specific port-name conventions.
- The number of new input and output ports must match the existing arities.

## Basic Examples

Rename the ports of a diagram:

```wl
DiagramAssignPorts[Diagram["A", a, b], {x}, {y}]
```
