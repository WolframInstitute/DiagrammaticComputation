---
Template: Symbol
Name: DuplicateAnnihilationRule
Context: Wolfram`DiagrammaticComputation`Rewriting`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DuplicateAnnihilationRule
Keywords: [duplicate, annihilation, copy, rule, interaction net]
SeeAlso: [AnnihilationRule, CopyDiagram, EraserDiagram, DiagramRule]
RelatedGuides: [DiagramRewriting]
---

## Usage

<code>[DuplicateAnnihilationRule]()[{$x_1$, …, $x_n$}, {$y_1$, …, $y_n$}]</code> returns a rewrite rule annihilating two facing copy nodes into parallel identity wires connecting $x_i$ to $y_i$.

## Details & Options

- Encodes the interaction-net duplication–annihilation law: when a copy meets its co-copy head-on, both disappear and their legs join pairwise.
- The following options can be given:

| Option | Default | Description |
| --- | --- | --- |
| <code>"Bend"</code> | <code>[False]()</code> | use a cup to bend the second copy node up |
| <code>"Reverse"</code> | <code>[False]()</code> | reverse the order of the output legs |

## Basic Examples

The annihilation law for binary copy nodes:

```wl
DuplicateAnnihilationRule[{x1, x2}, {y1, y2}]
```
