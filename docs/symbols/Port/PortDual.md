---
Template: Symbol
Name: PortDual
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/PortDual
Keywords: [port, dual, ingoing, outgoing, conjugate]
SeeAlso: [Port, PortProduct, PortSum, DiagramDual]
RelatedGuides: [Ports]
---

## Usage

<code>[PortDual]()[$p$]</code> represents the dual of the port $p$ — same expression and type, opposite direction.

<code>[PortDual]()[$expr$, $type$]</code> constructs a dual port directly from an expression and type.

## Details & Options

- An input port and its dual output port have the same name but opposite roles in composition: a <code>[Diagram]()</code> accepting input <code>[Port]()[$a$]</code> connects to one producing output <code>[PortDual]()[$a$]</code>.
- <code>[PortDual]()</code> is an involution: <code>[PortDual]()[[PortDual]()[$p$]] == $p$</code>.
- For composite ports, duality distributes: <code>[PortDual]()[[PortProduct]()[$p_1$, $p_2$]] == [PortProduct]()[[PortDual]()[$p_2$], [PortDual]()[$p_1$]]</code> (note the reversal).

## Basic Examples

Build a dual port:

```wl
PortDual[a]
```

A dual port is outgoing as an input and ingoing as an output:

```wl
Diagram["A", PortDual[a], PortDual[b]]
```

## Scope

Composing a port with its dual produces a closed wire:

```wl
DiagramComposition[IdentityDiagram[a], IdentityDiagram[a]]
```

## Properties and Relations

<code>[PortDual]()</code> is the port-level analogue of <code>[DiagramDual]()</code>.
