---
Template: Symbol
Name: PortPower
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/PortPower
Keywords: [port, power, repetition, tensor, product]
SeeAlso: [Port, PortProduct, PortDual]
RelatedGuides: [Ports]
---

## Usage

<code>[PortPower]()[$p$, $n$]</code> represents the $n$-fold product of the port $p$ with itself.

## Details & Options

- For a non-negative integer $n$, <code>[Port]()[$p^n$]</code> expands to <code>[PortProduct]()[$p$, $p$, …]</code> with $n$ factors.
- For a negative integer $n$, the expansion uses <code>[PortDual]()[$p$]</code> repeated <code>|n|</code> times.

## Basic Examples

A port tensored with itself three times:

```wl
Port[a^3]
```

A negative power dualises:

```wl
Port[a^-2]
```
