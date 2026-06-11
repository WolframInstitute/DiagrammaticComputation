---
Template: Symbol
Name: SingletonDiagram
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/SingletonDiagram
Keywords: [singleton, atomic, opaque, box]
SeeAlso: [Diagram, IdentityDiagram, EmptyDiagram]
RelatedGuides: [Diagrams]
---

## Usage

<code>[SingletonDiagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/SingletonDiagram)[$d$]</code> wraps the diagram $d$ as a single opaque node, hiding its internal structure.

<code>[SingletonDiagram](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/SingletonDiagram)[$d$, {$i_1$, ...}, {$o_1$, ...}]</code> wraps $d$ with explicit input and output ports $i_1, ...$ and $o_1, ...$.

## Details & Options

- Useful when an already-built diagram should be treated as an atomic process -- for example, to display it as a single box rather than decomposed, or to compose it with others without exposing its substructure.
- The wrapped diagram preserves its data and behaviour under composition, but <code>[DiagramDecompose](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramDecompose)</code> and surgery tools see it as a single node.

## Basic Examples

Wrap a composite as an opaque singleton:

```wl
SingletonDiagram[DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]]
```

![output](images/SingletonDiagram-out-1.png)
