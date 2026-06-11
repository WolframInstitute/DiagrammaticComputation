---
Template: Guide
Name: DiagramGrid
Title: Diagram Grid Layout
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/guide/DiagramGrid
Description: "Lay diagrams out as a 2D grid of cells, with wires and arrange/decompose helpers"
Keywords: [layout, grid, row, column, arrange, decompose, foliation]
RelatedGuides: [Diagrams, DiagramDrawing]
---

## Abstract

A diagram is *grid-arrangeable* when it can be drawn as a rectangular grid of cells in which composition runs vertically and product runs horizontally. This guide covers the tools that turn an arbitrary composite diagram into a grid: row and column constructors that build grids directly, <code>[DiagramGrid](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramGrid)</code> which renders the grid, <code>[DiagramArrange](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramArrange)</code> which inserts identities, permutations and spiders so the diagram *can* be gridded, and <code>[DiagramDecompose](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramDecompose)</code> which recovers the expression tree of subdiagrams from a built diagram.

## Functions

### Grid layout

- `DiagramGrid` — render a diagram with its subdiagrams arranged in a 2D grid
- `RowDiagram` — arrange diagrams horizontally (product)
- `ColumnDiagram` — arrange diagrams vertically (composition)

### Arrangement

- `DiagramArrange` — insert wires, identities, permutations and spiders to make a diagram grid-arrangeable
- `DiagramDecompose` — decompose a composite diagram into an expression tree of subdiagrams

### Port matching

- `DiagramMatchPorts` — align the ports of adjacent subdiagrams in a grid layout
- `DiagramAssignPorts` — assign explicit ports to a diagram's inputs and outputs

### Grid metrics

- `GridInputPorts` — input ports of a grid layout
- `GridOutputPorts` — output ports of a grid layout
- `DiagramGridWidth` — width of a diagram's grid layout
- `DiagramGridHeight` — height of a diagram's grid layout
- `DiagramGridWidthHeight` — width and height of a diagram's grid layout
- `DiagramGridTree` — tree of grid cells of a diagram's grid layout
