---
Template: Symbol
Name: ColumnDiagram
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/ColumnDiagram
Keywords: [column, vertical, layout, composition]
SeeAlso: [RowDiagram, DiagramComposition, DiagramGrid]
RelatedGuides: [DiagramGrid]
---

## Usage

<code>[ColumnDiagram]()[{$d_1$, $d_2$, …}]</code> arranges the diagrams $d_i$ in a vertical column.

## Details & Options

- Equivalent in structure to <code>[DiagramComposition]()[$d_1$, $d_2$, …]</code> but with default port-arrow display tuned for a column layout.

## Basic Examples

A simple two-diagram column:

```wl
ColumnDiagram[{Diagram["A", a, b], Diagram["B", b, c]}]
```

A column whose pieces have different arity:

```wl
ColumnDiagram[{Diagram["A", a, {b, c}], Diagram["B", {d, c, b}, e]}]
```

## Properties and Relations

<code>[ColumnDiagram]()</code> is the layout-level counterpart of <code>[DiagramComposition]()</code>
(the algebraic sequential composition). For the horizontal version, see
<code>[RowDiagram]()</code>.
