---
Template: Symbol
Name: PortNeutral
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/PortNeutral
Keywords: [port, neutral, unit, identity, ambient]
SeeAlso: [Port, PortProduct, PortSum, EmptyPortQ]
RelatedGuides: [Ports]
---

## Usage

<code>[PortNeutral](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/PortNeutral)[$p$]</code> marks the port $p$ as *neutral* -- a unit-like port that acts as the identity under composition.

## Details & Options

- A neutral port is invisible to composition: connecting a diagram to a neutral port leaves it unchanged.
- This is useful for marking "ambient" inputs (e.g. a constant context) that should not consume external wires.
- Neutrality is recorded as the <code>"NeutralQ"</code> option of the underlying <code>[Port](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/Port)</code>.

## Basic Examples

Construct a neutral port:

```wl
PortNeutral[a]
```

![output](images/PortNeutral-out-1.png)

```wl
PortNeutral[a]["NeutralQ"]
```

![output](images/PortNeutral-out-2.png)
