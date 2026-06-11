---
Template: Guide
Name: Diagrams
Title: Diagrams
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/guide/Diagrams
Description: Abstract compositional diagrammatic calculus for Wolfram Language
Keywords: [string diagram, monoidal category, tensor network, compositional, rewriting, port, wire]
RelatedGuides: [Ports, DiagramGrid, DiagramConversion, DiagramSurgery, DiagramDrawing, DiagramRewriting, FeynmanDiagrams]
Links: ["[Paclet repository](https://github.com/WolframResearch/DiagrammaticComputation)"]
---

## Abstract

In physics, computation and mathematics, inputs are related to outputs by compositional processes that compose in series and in parallel. These processes have a natural graphical syntax — *string diagrams* — and the `Wolfram`DiagrammaticComputation`` paclet provides a uniform symbolic representation of them, along with tools for composing, transforming, rewriting, simplifying and visualising diagrams. A <code>[Diagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Diagram)</code> is a morphism in a symmetric monoidal category with typed input and output <code>[Port](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Port)</code>s; everything else in this guide builds on those two primitives.

## Functions

### Predicates

- `DiagramQ` — test whether an expression is a valid diagram

### Construction

- `Diagram` — symbolic diagram with input and output ports
- `ToDiagram` — convert graphs, trees, hypergraphs, networks and lambda terms to a diagram
- `SingletonDiagram` — wrap a diagram as a single opaque node with specified ports

### Special diagrams

- `EmptyDiagram` — diagram with no subdiagrams and identity port mappings
- `ZeroDiagram` — additive identity for direct sums
- `IdentityDiagram` — identity morphism on a port
- `PermutationDiagram` — permutation morphism on a tuple of ports
- `CapDiagram` — connect two input ports with a cap
- `CupDiagram` — connect two output ports with a cup
- `CopyDiagram` — duplicate a port onto multiple outputs
- `MergeDiagram` — merge multiple inputs to a single output
- `SpiderDiagram` — many-to-many junction at a single point

### Composition

- `DiagramComposition` — sequential (vertical) composition
- `DiagramRightComposition` — sequential composition read left-to-right
- `DiagramProduct` — parallel (horizontal) composition / tensor product
- `DiagramSum` — direct sum of diagrams (additive choice)
- `DiagramNetwork` — orderless composition by port name
- `ToDiagramNetwork` — re-express a composite diagram as a network

### Transformations

- `DiagramDual` — reverse the direction of every port
- `DiagramFlip` — reflect the diagram top-to-bottom (swap inputs and outputs)
- `DiagramReverse` — reflect the diagram left-to-right (reverse port order)
- `DiagramPermute` — permute the ports of a diagram
- `DiagramSplit` — partition the ports of a diagram between inputs and outputs
- `SimplifyDiagram` — simplify a diagram by absorbing identity wires
- `DiagramGraphSimplify` — simplify the underlying port graph

### Visualisation

- `DiagramGraphics` — render a diagram as a single node
- `DiagramGrid` — render a diagram with its subdiagrams arranged in a grid
- `DiagramArrange` — insert wires, identities and permutations to make a diagram grid-arrangeable
- `DiagramDecompose` — decompose a composite diagram into an expression tree of sub-diagrams
- `DiagramDraw` — interactive tool for drawing diagrams

### Layout

- `RowDiagram` — arrange diagrams horizontally
- `ColumnDiagram` — arrange diagrams vertically

### Ports

- `Port` — construct a diagram port
- `PortDual` — toggle a port between ingoing and outgoing
- `PortProduct` — parallel composition of ports
- `PortSum` — direct sum of ports

### Conversions

- `DiagramFunction` — extract a pure function from a diagram
- `DiagramTensor` — extract a symbolic tensor expression from a diagram
- `TensorDiagram` — convert a tensor expression to a diagram

### Surgery

- `DiagramSubdiagrams` — list all subdiagrams
- `DiagramPositions` — positions of every subdiagram
- `DiagramPosition` — positions of subdiagrams matching a pattern
- `DiagramCases` — extract subdiagrams matching a pattern
- `DiagramMap` — apply a function to every subdiagram
- `DiagramMapAt` — apply a function at specific positions
- `DiagramExtract` — extract the subdiagram at a position
- `DiagramInsert` — insert a subdiagram at a position
- `DiagramDelete` — delete the subdiagram at a position
- `DiagramReplacePart` — replace subdiagrams at specific positions

### Rewriting

- `DiagramReplace` — replace the first matching subdiagram
- `DiagramReplaceList` — list every possible single replacement
- `DiagramNestReplace` — iteratively apply rewrite rules
- `DiagramRule` — bidirectional diagram rewrite rule
- `DiagramHypergraph` — hypergraph view of a diagram for matching
- `DiagramHypergraphRule` — hypergraph view of a diagram rewrite rule
