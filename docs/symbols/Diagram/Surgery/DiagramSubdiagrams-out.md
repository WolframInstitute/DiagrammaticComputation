---
Template: Symbol
Name: DiagramSubdiagrams
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
URI: Wolfram/DiagrammaticComputation/ref/DiagramSubdiagrams
Keywords: [subdiagrams, decomposition, recurse]
SeeAlso: [DiagramPositions, DiagramCases, DiagramDecompose]
RelatedGuides: [DiagramSurgery]
---

## Usage

<code>[DiagramSubdiagrams](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramSubdiagrams)[$d$]</code> returns a list of every subdiagram of $d$, including $d$ itself.

## Details & Options

- The list is ordered by recursive descent through <code>[DiagramComposition](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramComposition)</code>, <code>[DiagramProduct](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramProduct)</code>, <code>[DiagramSum](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramSum)</code> and <code>[DiagramNetwork](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/DiagrammaticComputation/ref/DiagramNetwork)</code>.

## Basic Examples

List all subdiagrams of a composition:

```wl
DiagramSubdiagrams @ DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
```

![output](images/DiagramSubdiagrams-out-1.png)
