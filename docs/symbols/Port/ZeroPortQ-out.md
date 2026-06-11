---
Template: Symbol
Name: ZeroPortQ
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/ZeroPortQ
Keywords: [port, predicate, zero, unit, direct sum]
SeeAlso: [PortQ, EmptyPortQ, Port, PortSum]
RelatedGuides: [Ports]
---

## Usage

<code>[ZeroPortQ](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/ZeroPortQ)[$p$]</code> gives <code>[True](https://reference.wolfram.com/language/ref/True.html)</code> if $p$ is the unit port for <code>[PortSum](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortSum)</code> (the zero port).

## Details & Options

- The zero port is the identity element of <code>[PortSum](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortSum)</code>: summing any port with the zero port returns it unchanged.
- It is constructed by <code>[Port](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Port)["0"]</code>.

## Basic Examples

The zero port is zero:

```wl
ZeroPortQ[Port["0"]]
```

![output](images/ZeroPortQ-out-1.png)

A non-zero port is not:

```wl
ZeroPortQ[Port[a]]
```

![output](images/ZeroPortQ-out-2.png)
