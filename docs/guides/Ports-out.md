---
Template: Guide
Name: Ports
Title: Ports
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/guide/Ports
Description: Symbolic ports — the typed input and output endpoints of a diagram
Keywords: [port, type, dual, product, sum, unit, tagged]
RelatedGuides: [Diagrams]
---

## Abstract

A <code>[Port](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Port)</code> is the typed endpoint of a diagram. Every <code>[Diagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Diagram)</code> carries a list of input ports and a list of output ports; composing diagrams works by matching ports of compatible *types*. Ports have a small algebra of their own — they can be made dual (reversed in direction), tensored together with <code>[PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)</code>, summed with <code>[PortSum](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortSum)</code>, raised to a power, tagged with context-specific annotations, and tested with predicates. This guide collects the operations that build and transform ports independently of the diagrams they appear in.

## Functions

### Construction

- `Port` — construct a symbolic port from an expression and an optional type
- `PortDual` — toggle a port between ingoing and outgoing
- `PortProduct` — parallel composition (tensor) of ports
- `PortSum` — direct sum of ports
- `PortMinus` — additive inverse of a port in a sum
- `PortPower` — repeated product of a port

### Distinguished ports

- `PortNeutral` — neutral / unit port for the monoidal product

### Predicates

- `PortQ` — test whether an expression is a valid port
- `EmptyPortQ` — test whether a port is the unit of <code>[PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)</code>
- `ZeroPortQ` — test whether a port is the unit of <code>[PortSum](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortSum)</code>

### Tagging

- `TagPort` — annotate a port with additional tag data
- `UntagPort` — strip tag annotations from a port
