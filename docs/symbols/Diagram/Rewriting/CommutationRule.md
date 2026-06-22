---
Template: Symbol
Name: CommutationRule
Context: Wolfram`DiagrammaticComputation`Rewriting`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/CommutationRule
Keywords: [commutation, exchange, rule, interaction net]
SeeAlso: [DiagramRule, EraserRule, AnnihilationRule, PropagationRule]
RelatedGuides: [DiagramRewriting]
---

## Usage

<code>[CommutationRule]()[{$x_1$, …}, {$y_1$, …}]</code> returns a rewrite rule commuting a generic process past a copy node, with input ports $x_i$ and output ports $y_i$.

<code>[CommutationRule]()[$expr_1$, $expr_2$, {$x_1$, …}, {$y_1$, …}]</code> commutes processes labelled $expr_1$ and $expr_2$.

<code>[CommutationRule]()[$d$, $c$]</code> commutes the unary-input diagrams $d$ and $c$ past each other.

## Details & Options

- Encodes the interaction-net commutation law: two distinct nodes meeting head-on exchange places, each getting duplicated across the other's legs.
- A dual port (<code>SuperStar</code>) marks legs entering from the opposite side.
- The following options can be given:

| Option | Default | Description |
| --- | --- | --- |
| <code>"Bend"</code> | <code>[False]()</code> | bend the second node up with a cup |
| <code>"Dual"</code> | <code>[False]()</code> | dualise the second node |
| <code>"Polarized"</code> | <code>[True]()</code> | show port direction arrows |
| <code>"Floating"</code> | <code>[True]()</code> | allow node ports to match in any order |

## Basic Examples

Commute two unary processes:

```wl
CommutationRule[Diagram["A", a, a], Diagram["B", a, a]]
```

The generic copy-commutation law with mixed-direction legs:

```wl
CommutationRule[{x1, SuperStar[x2]}, {y1, y2}]
```
