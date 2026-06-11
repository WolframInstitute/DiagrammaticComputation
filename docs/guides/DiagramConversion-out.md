---
Template: Guide
Name: DiagramConversion
Title: Converting To and From Diagrams
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/guide/DiagramConversion
Description: "Convert graphs, trees, hypergraphs, tensors, lambda terms and system models to and from diagrams"
Keywords: [conversion, graph, tree, hypergraph, tensor, lambda, NetGraph, SystemModel]
RelatedGuides: [Diagrams]
---

## Abstract

A diagram is a useful intermediate representation between many graphical data structures: graphs, trees, hypergraphs, tensor expressions, neural networks, lambda terms and system models all have diagrammatic readings. <code>[ToDiagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/ToDiagram)</code> is the universal entry point for getting *into* the diagram representation; <code>[DiagramFunction](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramFunction)</code> and <code>[DiagramTensor](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramTensor)</code> are the dual exits back to ordinary Wolfram Language expressions; and <code>[TensorDiagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/TensorDiagram)</code> imports the tensor side directly.

## Functions

### Importing to a diagram

- `ToDiagram` — convert graphs, trees, hypergraphs, NetGraphs, lambda terms and system models to a diagram
- `TensorDiagram` — convert a tensor expression to a diagram

### Exporting from a diagram

- `DiagramFunction` — extract a pure function from a diagram
- `DiagramTensor` — extract a symbolic tensor expression from a diagram
