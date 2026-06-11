---
Template: Symbol
Name: EmptyPortQ
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/EmptyPortQ
Keywords: [port, predicate, empty, unit, monoidal]
SeeAlso: [PortQ, ZeroPortQ, Port, PortProduct]
RelatedGuides: [Ports]
---

## Usage

<code>[EmptyPortQ](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/EmptyPortQ)[$p$]</code> gives <code>[True](https://reference.wolfram.com/language/ref/True.html)</code> if $p$ is the unit port for <code>[PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)</code> (the empty product).

## Details & Options

- The empty port is the identity element of <code>[PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)</code>: composing any port with the empty port returns it unchanged.
- It is constructed by <code>[Port](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Port)["1"]</code> or <code>[Port](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Port)[$p^0$]</code>.

## Basic Examples

The empty port is empty:

```wl
EmptyPortQ[Port["1"]]
```

![output](images/EmptyPortQ-out-1.png)

A non-empty port is not:

```wl
EmptyPortQ[Port[a]]
```

![output](images/EmptyPortQ-out-2.png)
