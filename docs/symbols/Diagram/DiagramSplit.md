---
Template: Symbol
Name: DiagramSplit
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramSplit
Keywords: [split, partition, repartition, ports, currying, transpose]
SeeAlso: [DiagramPermute, DiagramFlip, CapDiagram, CupDiagram, DiagramTensor]
RelatedGuides: [Diagrams]
---

## Usage

<code>[DiagramSplit]()[$d$, $n$]</code> repartitions the ports of $d$ so that its first $n$ ports become outputs and the remaining ones inputs.

<code>[DiagramSplit]()[$d$]</code> turns every port into an output, making $d$ a state.

<code>[DiagramSplit]()[$d$, $n$, $dualQ$]</code> controls whether the moved ports are dualised.

<code>[DiagramSplit]()[$d$, $n$, $dualQ$, $flipQ$]</code> bends the moved wires around the other side.

## Details & Options

- Ports are counted in the flattened order: outputs first, then inputs. A negative $n$ counts back from the total arity, <code>-[Infinity]()</code> makes every port an input, and the default <code>[Infinity]()</code> makes every port an output.
- The repartitioning composes $d$ with a pure wire diagram that bends the moved ports around, so the underlying process is unchanged — this is the diagrammatic analogue of currying a function or transposing tensor legs between covariant and contravariant positions.
- With $dualQ$ set to <code>[False]()</code>, the moved ports keep their direction and are wrapped in <code>[PortDual]()</code> instead.
- With $flipQ$ set to <code>[True]()</code>, the bending wires pass on the opposite side of the retained ports.

## Basic Examples

Make all five ports of a process into outputs:

```wl
DiagramSplit[Diagram[A, {a, b, c}, {x, y}]]
```

Repartition to three outputs and two inputs:

```wl
DiagramSplit[Diagram[A, {a, b, c}, {x, y}], 3]
```

Turn the process into a costate, with every port an input:

```wl
DiagramSplit[Diagram[A, {a, b, c}, {x, y}], 0]
```

## Properties and Relations

Splitting at the existing output arity is the identity; <code>[DiagramSplit]()[$d$, 0]</code> and <code>[DiagramSplit]()[$d$]</code> realise the process–state correspondence built from <code>[CapDiagram]()</code> / <code>[CupDiagram]()</code> bends.
