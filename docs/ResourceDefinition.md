---
Template: Paclet
ResourceType: Paclet
Name: Wolfram/DiagrammaticComputation
Context: Wolfram`DiagrammaticComputation`
Paclet: Wolfram/DiagrammaticComputation
Description: Abstract compositional diagrammatic calculus
ContributedBy: Nik Murzin, Ian Ford
Keywords: [diagram, string diagram, port, wire, composition, monoidal category, tensor network, rewriting, process theory]
MainGuide: Documentation/English/Guides/Diagrams.nb
License: MIT
WolframVersion: 14.2+
Categories: [Graphs & Networks, Visualization & Graphics]
Disclosures: [PacletDependencies]
SourceControlURL: https://github.com/WolframInstitute/DiagrammaticComputation
Links: ["[Paclet sources on GitHub](https://github.com/WolframInstitute/DiagrammaticComputation)"]
---

## Details & Options

- A [Diagram]() is a symbolic process with typed input and output [Port]()s — a morphism in a symmetric monoidal category. Diagrams compose sequentially ([DiagramComposition]()), in parallel ([DiagramProduct]()), additively ([DiagramSum]()), or orderlessly by port name ([DiagramNetwork]()).
- Composite diagrams render as 2D grids ([DiagramGrid]()) or single nodes ([DiagramGraphics]()); arbitrary networks arrange into grids automatically by inserting identities, permutations, caps, cups and spiders ([DiagramArrange]()).
- Diagrams convert to and from other compositional structures: graphs, trees, hypergraphs, neural networks and system models via [ToDiagram](), symbolic tensor contractions via [DiagramTensor]() and [TensorDiagram](), and executable dataflow functions via [DiagramFunction]().
- Subdiagrams can be located, mapped over and edited ([DiagramCases](), [DiagramMap](), [DiagramReplacePart]()) and rewritten by hypergraph-matched rules ([DiagramReplace](), [DiagramRule]()), including the standard interaction-net rule schemas.
- The paclet depends on the [WolframInstitute/Hypergraph](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/Hypergraph/) paclet for rule matching.

## Usage

The paclet provides [Diagram]() and [Port]() with constructors [ToDiagram](), [TensorDiagram](), [IdentityDiagram](), [PermutationDiagram](), [CapDiagram](), [CupDiagram](), [CopyDiagram](), [SpiderDiagram](); compositions [DiagramComposition](), [DiagramProduct](), [DiagramSum](), [DiagramNetwork](), [RowDiagram](), [ColumnDiagram](); transformations [DiagramDual](), [DiagramFlip](), [DiagramReverse](), [DiagramArrange](), [SimplifyDiagram](); conversions [DiagramFunction](), [DiagramTensor](); surgery [DiagramCases](), [DiagramMap](), [DiagramMapAt](), [DiagramExtract](), [DiagramInsert](), [DiagramDelete](); and rewriting [DiagramReplace](), [DiagramReplaceList](), [DiagramNestReplace](), [DiagramRule]().

## Basic Examples

Create a simple diagram with one input and two output ports:

```wl
Diagram[A, x, {y, z}]
```

---

Compose diagrams in sequence and in parallel; matching port names wire together:

```wl
DiagramComposition[
  Diagram["g", {a, d}, {x}],
  DiagramProduct[DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]], Diagram["h", e, d]],
  Diagram["i", {c, e}]
]
```

---

Wire diagrams into a network, joining all equivalent ports regardless of position:

```wl
DiagramNetwork[Diagram[A, {a, b}, d], Diagram[B, c, a], Diagram[C, {x, c}, b]]
```

## Scope

Annotate diagram labels with functions and run the diagram as a dataflow:

```wl
DiagramFunction[ColumnDiagram[{
  Diagram[Annotation["3", "Function" -> (3 &)], input],
  Diagram[Annotation["[2\[Times]]", "Function" -> (2 # &)], input, doubled],
  Diagram[Annotation["", "Function" -> (Sequence @@ {#, #} &)], doubled, {a, b}, "Shape" -> "Point"],
  RowDiagram[{Diagram[Annotation["[+1]", "Function" -> (# + 1 &)], a, incremented], Diagram[Annotation["[^2]", "Function" -> (#^2 &)], b, squared]}],
  Diagram[Annotation["[+]", "Function" -> Plus], {incremented, squared}, result]
}, Alignment -> Center]][]
```

---

Extract the tensor contraction a composite diagram represents:

```wl
DiagramTensor[Diagram[Diagram["A", a, b] \[CircleTimes] Diagram["C", d, e] \[CircleDot] Diagram["B", c, d]]]
```

---

Rewrite a diagram by a rule with pattern ports:

```wl
DiagramReplace[
  DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]],
  Diagram["A", \[FormalY], \[FormalX]] -> Diagram["X", \[FormalY], \[FormalX]]
]
```

## Hero Image

The steps of a tiramisu cream as a dataflow diagram — matching resource names
wire automatically into a process diagram:

```wl
With[{
  recipe = ColumnDiagram[{
    RowDiagram[{Diagram["Crack Egg", "egg", {"white", "yolk"}], Diagram["Crack Egg", "egg", {"white", "yolk"}], IdentityDiagram["sugar"]}],
    RowDiagram[{Diagram["Whisk", {"white", "white"}, "whisked whites"], Diagram["Beat", {"yolk", "yolk", "sugar"}, "yolky paste"]}],
    Diagram["Stir", {"yolky paste", "mascarpone"}, "thick paste"],
    Diagram["Fold", {"whisked whites", "thick paste"}, "crema di mascarpone"]
  }]
},
  ImageResize[
    Rasterize[
      Notebook[{Cell[BoxData[ToBoxes[
        Framed[
          Column[{
            Style["DiagrammaticComputation", 26, Bold, GrayLevel[0.15], FontFamily -> "Source Sans Pro"],
            Style["Abstract compositional diagrammatic calculus", 13, GrayLevel[0.45], FontFamily -> "Source Sans Pro"],
            Spacer[10],
            recipe["Grid", ImageSize -> {Automatic, 430}]
          }, Alignment -> Center, Spacings -> 0.8],
          Background -> White, FrameMargins -> 30, FrameStyle -> None
        ]
      ]], "Output"]}, LightDark -> "Light", StyleDefinitions -> "Default.nb"],
      ImageResolution -> 144, Background -> White
    ],
    {Automatic, 600}
  ]
]
```

## Author Notes

The documentation pages and this definition notebook were drafted with the
assistance of Claude (Anthropic), supervised and reviewed by Nik Murzin. The
kernel code is hand-written; symbol reference pages, guides and tech notes were
model-generated from the source code and existing notebooks, then verified by
evaluating every example against the paclet.
