---
Template: Symbol
Name: UntagPort
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/UntagPort
Keywords: [port, tag, untag, annotation, strip]
SeeAlso: [TagPort, Port]
RelatedGuides: [Ports]
---

## Usage

<code>[UntagPort]()[$p$]</code> strips all tag annotations from the port $p$.

<code>[UntagPort]()[$p$, $tag$]</code> strips a specific tag from the port.

## Details & Options

- The inverse of <code>[TagPort]()</code>: removes the entries set in the port's <code>"Tags"</code> option.
- Calling <code>[UntagPort]()</code> with no second argument clears the tag list entirely.

## Basic Examples

Strip tags from a tagged port:

```wl
UntagPort[TagPort[Port[a], "input"]]
```
