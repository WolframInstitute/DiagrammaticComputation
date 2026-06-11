---
Template: Symbol
Name: PortProduct
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/PortProduct
Keywords: [port, product, tensor, parallel, CircleTimes, monoidal]
SeeAlso: [Port, PortSum, PortDual, PortPower, DiagramProduct]
RelatedGuides: [Ports]
---

## Usage

<code>[PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)[$p_1$, $p_2$, ...]</code> represents the parallel (tensor) product of the ports $p_i$.

## Details & Options

- The product of ports is again a port whose type is the <code>[CircleTimes](https://reference.wolfram.com/language/ref/CircleTimes.html)</code> of the component types.
- <code>[PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)</code> is associative; the unit is the empty port <code>[Port](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Port)["1"]</code>.
- The infix shorthand <code>$p_1$ \[CircleTimes] $p_2$</code> evaluated inside <code>[Port](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Port)</code> produces a <code>[PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)</code>.
- Dualising distributes with reversal: <code>[PortDual](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortDual)[[PortProduct]()[$p_1$, $p_2$]] == [PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)[[PortDual]()[$p_2$], [PortDual](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortDual)[$p_1$]]</code>.

## Basic Examples

Build a product of two ports:

```wl
PortProduct[Port[a], Port[b]]
```

![output](images/PortProduct-out-1.png)

Using <code>[CircleTimes](https://reference.wolfram.com/language/ref/CircleTimes.html)</code>:

```wl
Port[a \[CircleTimes] b]
```

![output](images/PortProduct-out-2.png)

## Properties and Relations

<code>[PortProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortProduct)</code> is the port-level analogue of <code>[DiagramProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramProduct)</code> -- composing diagrams in parallel matches their input and output port products.
