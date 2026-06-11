---
Template: Symbol
Name: SpiderDiagram
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/SpiderDiagram
Keywords: [spider, junction, frobenius, ZX, special, branching]
SeeAlso: [CopyDiagram, MergeDiagram, CapDiagram, CupDiagram]
RelatedGuides: [Diagrams, DiagramRewriting]
---

## Usage

<code>[SpiderDiagram]()[{$i_1$, …}, {$o_1$, …}]</code> creates a many-to-many junction with input ports $i_1, …$ and output ports $o_1, …$ all meeting at a single point.

## Details & Options

- A spider is the multi-port generalisation of <code>[IdentityDiagram]()</code>, <code>[CopyDiagram]()</code>, <code>[MergeDiagram]()</code>, <code>[CapDiagram]()</code> and <code>[CupDiagram]()</code> — all of these are special cases.
- It is the basic structural junction in ZX-style and other process-theoretic calculi.
- Spiders fuse: two spiders meeting at a shared wire merge into a single spider whose legs are the union (this is the spider law).

## Basic Examples

A 2-to-3 spider:

```wl
SpiderDiagram[{a, b}, {c, d, e}]
```

## Properties and Relations

<code>[CopyDiagram]()</code> is the special case 1-to-many; <code>[MergeDiagram]()</code> is many-to-1;
<code>[CapDiagram]()</code> is 2-to-0 and <code>[CupDiagram]()</code> is 0-to-2; <code>[IdentityDiagram]()</code>
is 1-to-1.
