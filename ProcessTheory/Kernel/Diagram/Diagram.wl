BeginPackage["ProcessTheory`Diagram`", {"ProcessTheory`Utilities`", "ProcessTheory`Port`", "ProcessTheory`Diagram`Grid`"}];

Diagram
DiagramQ

DiagramDual
DiagramFlip
DiagramReverse

DiagramProduct
DiagramSum
DiagramComposition
DiagramNetwork

DiagramGraphics
DiagramsFreePorts
DiagramsPortGraph
DiagramsGraph
DiagramsNetGraph

DiagramSplit
DiagramPermute

DiagramTensor
TensorDiagram
DiagramFunction


Begin["ProcessTheory`Diagram`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Diagram::usage = "Diagram[expr] represents a symbolic diagram with input and output ports"

Options[Diagram] := Sort @ DeleteDuplicatesBy[First] @ Join[Options[DiagramGraphics], Options[DiagramGrid], Options[DiagramsNetGraph]];

$DiagramHiddenOptions = {"Expression" -> None, "OutputPorts" -> {}, "InputPorts" -> {}, "DiagramOptions" -> {}};

$DiagramProperties = Sort @ {
    "Properties", "HoldExpression", "ProductQ", "SumQ", "CompositionQ", "NetworkQ", "SubDiagrams",
    "Ports", "PortArrows", "Arity", "FlattenOutputs", "FlattenInputs", "Flatten", "View", "Name", "Tensor", "Function", "Shape",
    "Diagram", "PortGraph", "Graph", "NetGraph", "Grid"
}


(* ::Subsection:: *)
(* Validation *)

diagramQ[HoldPattern[Diagram[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "OutputPorts" -> {___Port ? PortQ}, "InputPorts" -> {___Port ? PortQ}, "DiagramOptions" -> OptionsPattern[]}]]

diagramQ[___] := False


x_Diagram /; System`Private`HoldNotValidQ[x] && diagramQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

DiagramQ[x_Diagram] := System`Private`HoldValidQ[x]

DiagramQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

Diagram[SuperStar[d_], opts : OptionsPattern[]] := DiagramDual[Diagram[d], opts]

Diagram[OverBar[d_], opts : OptionsPattern[]] := DiagramFlip[Diagram[d], opts]

Diagram[OverTilde[d_], opts : OptionsPattern[]] := DiagramReverse[Diagram[d], opts]

Diagram[CircleTimes[ds___], opts : OptionsPattern[]] := DiagramProduct[##, opts] & @@ (Diagram /@ {ds})

Diagram[CirclePlus[ds___], opts : OptionsPattern[]] := DiagramSum[##, opts] & @@ (Diagram /@ {ds})

Diagram[(CircleDot | Composition)[ds___], opts : OptionsPattern[]] := DiagramComposition[##, opts] & @@ (Diagram /@ {ds})

Diagram[HoldPattern[RightComposition[ds___]], opts : OptionsPattern[]] := DiagramComposition[##, opts] & @@ Reverse[Diagram /@ {ds}]

Diagram[ds : Except[OptionsPattern[], _List], opts : OptionsPattern[]] := DiagramNetwork[##, opts] & @@ (Diagram /@ ds)


(* overwrite ports *)

Diagram[d_ ? DiagramQ, {}, {}, opts : OptionsPattern[]] := Diagram[Unevaluated @@ d["HoldExpression"], {}, {}, opts]

Diagram[d_ ? DiagramQ, inputs_, {}, opts : OptionsPattern[]] := Diagram[Unevaluated @@ d["HoldExpression"], Replace[inputs, Inherited :> d["InputPorts"]], {}, opts]

Diagram[d_ ? DiagramQ, {}, opts : OptionsPattern[]] := Diagram[d, Inherited, {}, opts]

Diagram[d_ ? DiagramQ, output : Except[OptionsPattern[]], opts : OptionsPattern[]] := Diagram[d, Inherited, output, opts]

Diagram[d_ ? DiagramQ, inputs_, outputs : Except[OptionsPattern[]], opts : OptionsPattern[]] :=
    Diagram[Unevaluated @@ d["HoldExpression"], Replace[inputs, Inherited :> d["InputPorts"]], Replace[outputs, Inherited :> d["OutputPorts"]], opts]

Diagram[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[d, Inherited, Inherited, opts]


(* default constructor *)

Diagram[expr : {} | Except[_Association | _Diagram | OptionsPattern[]],
    inputs_List,
    outputs_List,
    opts : OptionsPattern[]
] :=
    Diagram[    
        FilterRules[{
            "Expression" :> expr,
            "OutputPorts" -> Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[outputs]],
            "InputPorts" -> Comap[Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[inputs]], "Dual"],
            opts
        },
            Join[Options[Diagram], $DiagramHiddenOptions, Options[DiagramGraphics], Options[DiagramsNetGraph], Options[DiagramGrid]]
        ]
    ]

Diagram[expr_, inputs_List, output : Except[_List | OptionsPattern[]], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], Unevaluated[inputs], Unevaluated[{output}], opts]

Diagram[expr_, input : Except[_List], outputs_List, opts : OptionsPattern[]] := Diagram[Unevaluated[expr], Unevaluated[{input}], Unevaluated[outputs], opts]

Diagram[expr_, input : Except[_List], output : Except[_List | OptionsPattern[]], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], Unevaluated[{input}], Unevaluated[{output}], opts]

Diagram[expr_, output : Except[_List | OptionsPattern[]], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], {}, Unevaluated[{output}], opts]

Diagram[expr_, outputs : Except[OptionsPattern[], _List], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], {}, Unevaluated[outputs], opts]

Diagram[expr : Except[_Association | _Diagram | OptionsPattern[]], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], {}, {}, opts]


(* merge options *)

inheritExpresion[expr_, deps_List, def_ : Automatic] := With[{pos = Position[expr, Inherited]},
    ReplacePart[expr, DeleteCases[Catenate[(dep |-> (# -> ResourceFunction["LookupPart"][dep, Sequence @@ #, Automatic] & /@ pos)) /@ deps], _ -> Inherited]] /. Inherited -> def
]


mergeOptions[opts_List] := Normal @ GroupBy[opts, First,
    If[ MatchQ[#[[1, 1]], "PortArrows" | "PortLabels"],
        Map[
            With[{len = Max[Length /@ #, 1]}, inheritExpresion[#1, {##2}] & @@ (PadRight[#, len, #] & /@ #)] &,
            Thread[Developer`ToList /@ PadRight[Developer`ToList[#], 2, #] & /@ #[[All, 2]]]
        ]
        ,
        #[[1, 2]]
    ] &
]

Diagram[opts : OptionsPattern[]] := Diagram[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> mergeOptions @ FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[Diagram]], opts, $DiagramHiddenOptions},
        Join[$DiagramHiddenOptions]
    ]|>
]]

Diagram[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[Replace[Normal[Merge[{opts, d["Data"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* ::Subsubsection:: *)
(* Unary ops *)

DiagramDual[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    Replace[d["HoldExpression"], {
        _[(head : (DiagramSum | DiagramComposition | DiagramProduct | DiagramNetwork | DiagramReverse | DiagramFlip))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramDual[#, opts] & /@ {ds})),
        _[DiagramDual[x_]] :> "Expression" :> x,
        _ :> "Expression" :> DiagramDual[d]
    }],
    "OutputPorts" -> Through[d["OutputPorts"]["Dual"]],
    "InputPorts" -> Through[d["InputPorts"]["Dual"]],
    "DiagramOptions" -> d["DiagramOptions"]
]

DiagramFlip[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    Replace[d["HoldExpression"], {
        _[DiagramComposition[ds___]] :> ("Expression" :> DiagramComposition[##] & @@ Reverse[DiagramFlip[#, opts] & /@ {ds}]),
        _[(head : (DiagramSum | DiagramProduct | DiagramNetwork | DiagramReverse | DiagramDual))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramFlip[#, opts] & /@ {ds})),
        _[DiagramFlip[x_]] :> "Expression" :> x,
        _ :> "Expression" :> DiagramFlip[d]
    }],
    "OutputPorts" -> d["InputPorts"],
    "InputPorts" -> d["OutputPorts"],
    "PortArrows" -> Reverse[fillAutomatic[d["OptionValue"["PortArrows"], opts], d["Arities"], True]],
    "PortLabels" -> Reverse[fillAutomatic[d["OptionValue"["PortLabels"], opts], d["Arities"], Automatic]],
    "DiagramOptions" -> d["DiagramOptions"]
]

DiagramReverse[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    Replace[d["HoldExpression"], {
        _[DiagramProduct[ds___]] :> ("Expression" :> DiagramProduct[##] & @@ Reverse[DiagramReverse[#, opts] & /@ {ds}]),
        _[(head : (DiagramSum | DiagramComposition | DiagramNetwork | DiagramFlip | DiagramDual))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramReverse[#, opts] & /@ {ds})),
        _[DiagramReverse[x_]] :> "Expression" :> x,
        _ :> "Expression" :> DiagramReverse[d]
    }],
    "OutputPorts" -> Reverse[Through[d["OutputPorts"]["Reverse"]]],
    "InputPorts" -> Reverse[Through[d["InputPorts"]["Reverse"]]],
    "PortArrows" -> (Reverse /@ fillAutomatic[d["OptionValue"["PortArrows"], opts], d["Arities"], True]),
    "PortLabels" -> (Reverse /@ fillAutomatic[d["OptionValue"["PortLabels"], opts], d["Arities"], Automatic]),
    "DiagramOptions" -> d["DiagramOptions"]
]


(* ::Subsubsection:: *)
(* Binary ops *)

(* sum *)


Options[DiagramSum] = Options[Diagram]

DiagramSum[d_Diagram, opts : OptionsPattern[]] := Diagram[d, opts]

DiagramSum[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{subDiagrams = If[#["SumQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}},
    Diagram[
        opts,
        "Expression" :> DiagramSum[##] & @@ subDiagrams,
        "OutputPorts" -> Replace[Through[{ds}["OutputPorts"]], {{} -> PortSum[], ps_ :> PortSum @@ ps}, 1],
        "InputPorts" -> Replace[Through[{ds}["InputPorts"]], {{} -> PortSum[]["Dual"], ps_ :> PortSum @@ ps}, 1]
    ]
]

(* horizontal product *)

Options[DiagramProduct] = Options[Diagram]

DiagramProduct[d_Diagram, opts : OptionsPattern[]] := Diagram[d, opts]

DiagramProduct[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{subDiagrams = If[#["ProductQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}},
    Diagram[
        opts,
        "Expression" :> DiagramProduct[##] & @@ subDiagrams,
        "OutputPorts" -> Replace[Through[{ds}["OutputPorts"]], {{} -> PortProduct[], ps_ :> PortProduct @@ ps}, 1],
        "InputPorts" -> Replace[Through[{ds}["InputPorts"]], {{} -> PortProduct[]["Dual"], ps_ :> PortProduct @@ ps}, 1]
    ]
]


(* vertical product *)

collectPorts[ports_List] := If[ports === {}, {},
    Fold[
        {
            Join[#2[[1]], DeleteElements[#1[[1]], 1 -> #2[[2]]]],
            Join[#1[[2]], DeleteElements[#2[[2]], 1 -> #1[[1]]]]
        } &,
        ports
    ]
]

Options[DiagramComposition] = Join[{"PortFunction" -> Function[#["Name"]]}, Options[Diagram]]

DiagramComposition[d_Diagram, opts : OptionsPattern[]] := Diagram[d, opts]

DiagramComposition[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{
    subDiagrams = If[#["CompositionQ"], Splice[#["SubDiagrams"]], #] & /@ {ds},
    func = OptionValue["PortFunction"]
}, {
    ports = collectPorts[{func /@ #["OutputPorts"], func /@ Through[#["InputPorts"]["Dual"]]} & /@ Through[Reverse[{ds}]["Flatten"]]]
},
    Diagram[
        opts,
        "Expression" :> DiagramComposition[##] & @@ subDiagrams,
        "OutputPorts" -> (Port[Unevaluated @@ #] & /@ ports[[1]]),
        "InputPorts" -> (Port[Unevaluated @@ #]["Dual"] & /@ ports[[2]])
    ]
]


(* network of diagrams exposing free ports *)

Options[DiagramNetwork] := DeleteDuplicatesBy[First] @ Join[{"PortFunction" -> Function[#["Name"]]}, Options[Diagram], Options[DiagramsNetGraph]]
DiagramNetwork[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{
    subDiagrams = If[#["NetworkQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}
},
    Diagram[
        opts,
        "Expression" :> DiagramNetwork[ds],

        Block[{graph = DiagramsGraph[subDiagrams, FilterRules[{opts}, Options[DiagramsGraph]]], diagrams = Through[subDiagrams["Flatten"]], freeWires, edges},
            freeWires = Cases[Pick[VertexList[graph], VertexDegree[graph], 1], _HoldForm];
            edges = EdgeList[graph];
            {
                "InputPorts" -> Cases[edges, DirectedEdge[Alternatives @@ freeWires, {diagramId_, 1, portId_}] :> diagrams[[diagramId]]["InputPorts"][[portId]]],
                "OutputPorts" -> Cases[edges, DirectedEdge[{diagramId_, 2, portId_}, Alternatives @@ freeWires] :> diagrams[[diagramId]]["OutputPorts"][[portId]]]
            }
        ]
    ]
]


(* ::Subsection:: *)
(* Properties *)


(* dispatch properties *)

(d_Diagram ? DiagramQ)[prop_, opts___] := DiagramProp[d, prop, opts] 


(* property definitions *)

DiagramProp[_, "Properties"] := Sort[$DiagramProperties]

DiagramProp[HoldPattern[Diagram[data_]], "Data"] := data

DiagramProp[HoldPattern[Diagram[data_Association]], prop_] /; ! MemberQ[prop, $DiagramProperties] && KeyExistsQ[data, prop] := Lookup[data, prop]

DiagramProp[d_, "HoldExpression"] := Extract[d["Data"], "Expression", HoldForm]

collectUnaries[(head : DiagramDual | DiagramFlip | DiagramReverse)[d_Diagram]] := Prepend[collectUnaries[d["HoldExpression"]], head]
collectUnaries[HoldForm[d_]] := collectUnaries[Unevaluated[d]]
collectUnaries[_] := {}

DiagramProp[d_, "DualQ"] := OddQ[Count[collectUnaries[d["HoldExpression"]], DiagramDual]]

DiagramProp[d_, "FlipQ"] := OddQ[Count[collectUnaries[d["HoldExpression"]], DiagramFlip]]

DiagramProp[d_, "ReverseQ"] := OddQ[Count[collectUnaries[d["HoldExpression"]], DiagramReverse]]

DiagramProp[d_, "ProductQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramProduct]]

DiagramProp[d_, "SumQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramSum]]

DiagramProp[d_, "CompositionQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramComposition]]

DiagramProp[d_, "NetworkQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramNetwork]]

DiagramProp[d_, "Dual", opts___] := DiagramDual[d, opts]

DiagramProp[d_, "Flip", opts___] := DiagramFlip[d, opts]

DiagramProp[d_, "Reverse", opts___] := DiagramReverse[d, opts]

DiagramProp[d_, "Head"] := Replace[d["HoldExpression"], {
    HoldForm[(head : DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[___]] :> head,
    _ -> Null
}]

DiagramProp[d_, "SubDiagrams"] := Replace[d["HoldExpression"], {
    HoldForm[(DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[ds___]] :> {ds},
    _ -> {}
}]

DiagramProp[d_, "Ports", dualQ : _ ? BooleanQ : False] := Join[d["OutputPorts"], If[dualQ, PortDual, Identity] /@ d["InputPorts"]]

DiagramProp[d_, "OutputArity"] := Length[d["OutputPorts"]]

DiagramProp[d_, "InputArity"] := Length[d["InputPorts"]]

DiagramProp[d_, "Arity"] := Length[d["Ports"]]

DiagramProp[d_, "Arities"] := {d["InputArity"], d["OutputArity"]}

DiagramProp[d_, "MaxArity"] := Max[d["OutputArity"], d["InputArity"]]

DiagramProp[d_, "FlatOutputPorts"] := Catenate[Through[d["OutputPorts"]["ProductList"]]]

DiagramProp[d_, "FlattenOutputs"] := Diagram[d, "OutputPorts" -> d["FlatOutputPorts"]]

DiagramProp[d_, "FlatInputPorts"] := Catenate[Through[d["InputPorts"]["ProductList"]]]

DiagramProp[d_, "FlattenInputs"] := Diagram[d, "InputPorts" -> d["FlatInputPorts"]]

DiagramProp[d_, "Flatten"] := d["FlattenOutputs"]["FlattenInputs"]

DiagramProp[d_, "FlatPorts"] := Join[d["FlatOutputPorts"], d["FlatInputPorts"]]

DiagramProp[d_, "FlattenNetworks"] := If[d["NetworkQ"],
    Diagram[d, "Expression" :> DiagramNetwork[##] & @@ (If[#["NetworkQ"], Splice[#["SubDiagrams"]], #] & /@ Through[d["SubDiagrams"]["FlattenNetworks"]])],
    With[{ds = d["SubDiagrams"]}, If[ds === {}, d, Diagram[d, "Expression" -> d["Head"] @@ Through[ds["FlattenNetworks"]]]]]
]

DiagramProp[d_, "GridInputPorts"] := GridInputPorts[d]

DiagramProp[d_, "GridOutputPorts"] := GridOutputPorts[d]

DiagramProp[d_, "Split", n : _Integer | Infinity | - Infinity : Infinity, dualQ : _ ? BooleanQ : True] := Block[{
    m = If[n >= 0, n, Max[d["Arity"] + n, 0]], outputs, inputs, dual = If[dualQ, PortDual, Identity]
},
    outputs = TakeDrop[d["OutputPorts"], UpTo[m]];
    inputs = TakeDrop[d["InputPorts"], UpTo[Max[0, m - d["OutputArity"]]]];
    Diagram[d,
        "OutputPorts" -> Join[outputs[[1]], dual /@ inputs[[1]]],
        "InputPorts" -> Join[dual /@ outputs[[2]], inputs[[2]]]
    ]
]

DiagramProp[d_, "View"] := With[{
    holdExpr = Replace[d["HoldExpression"],
        HoldForm[(head : DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[ds___]] :>
            head @@@ HoldForm[Evaluate[Flatten[Defer @@ (Function[Null, If[DiagramQ[#], #, Defer[#]], HoldFirst] /@ Unevaluated[{ds}])]]]
    ],
    outputs = Replace[Through[d["OutputPorts"]["View"]], {p : Except[HoldForm[_List | _Interpretation]]} :> p],
    inputs = Replace[Through[Through[d["InputPorts"]["Dual"]]["View"]], {p : Except[HoldForm[_List | _Interpretation]]} :> p],
    opts = d["DiagramOptions"]
},
    Function[expr, If[opts === {}, Defer[Diagram[expr, inputs, outputs]], Defer[Diagram[expr, inputs, outputs, ##]] & @@ opts] //. HoldForm[x_] :> x, HoldFirst] @@ holdExpr
]

DiagramProp[d_, "Name"] := Replace[
    d["HoldExpression"],

    HoldForm[(head : DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[ds___]] :>
        Replace[head, {
            DiagramDual -> SuperStar,
            DiagramFlip -> OverBar,
            DiagramReverse -> OverTilde,
            DiagramProduct -> CircleTimes,
            DiagramSum -> CirclePlus,
            DiagramComposition -> CircleDot,
            DiagramNetwork -> List
        }] @@@ HoldForm[Evaluate[Flatten[Defer @@ (Function[Null, If[DiagramQ[#], #["Name"], Defer[#]], HoldFirst] /@ Unevaluated[{ds}])]]]
]

DiagramProp[diagram_, "Decompose", opts : OptionsPattern[]] := DiagramDecompose[diagram, FilterRules[{opts}, Options[DiagramDecompose]]]

DiagramProp[diagram_, "Tensor" | "ArraySymbol", opts : OptionsPattern[]] := DiagramTensor[diagram, FilterRules[{opts}, Options[DiagramTensor]]]

DiagramProp[diagram_, "Function", opts : OptionsPattern[]] := DiagramFunction[diagram, FilterRules[{opts}, Options[DiagramFunction]]]

DiagramProp[d_, "Diagram" | "Graphics", opts : OptionsPattern[]] := DiagramGraphics[d, FilterRules[{opts}, Options[DiagramGraphics]], BaseStyle -> {GraphicsHighlightColor -> Automatic}]

DiagramProp[d_, "Normal"] := If[d["NetworkQ"],
    With[{g = DiagramsNetGraph[d["SubDiagrams"], "BinarySpiders" -> All, "UnarySpiders" -> False, "RemoveCycles" -> True, FilterRules[d["DiagramOptions"], Options[DiagramsNetGraph]]]},
        DiagramComposition[##, "PortFunction" -> Function[#["HoldExpression"]]] & @@ AnnotationValue[{g, Reverse[TopologicalSort[g]]}, "Diagram"]
    ],
    d
]

DiagramProp[d_, "PortGraph", opts : OptionsPattern[]] := DiagramsPortGraph[d["SubDiagrams"], opts]

DiagramProp[d_, "Graph", opts : OptionsPattern[]] := DiagramsGraph[d["SubDiagrams"], opts]

DiagramProp[d_, "Network", opts : OptionsPattern[]] := ToDiagramNetwork[d, FilterRules[{opts, d["DiagramOptions"]}, Options[ToDiagramNetwork]]]

DiagramProp[d_, "NetGraph", opts : OptionsPattern[]] := DiagramsNetGraph[d["Network"]["SubDiagrams"], FilterRules[{opts, d["DiagramOptions"]}, Options[DiagramsNetGraph]]]

DiagramProp[d_, "Arrange", opts : OptionsPattern[]] := DiagramArrange[d, opts]

DiagramProp[d_, "Grid", opts : OptionsPattern[]] := DiagramGrid[d, opts]

DiagramProp[d_, "OptionValue"[opt_], opts : OptionsPattern[]] := OptionValue[{opts, d["DiagramOptions"], Options[DiagramGraphics], Options[DiagramGrid], Options[DiagramsNetGraph]}, opt]

DiagramProp[d_, "WireQ"] := MatchQ[d["OptionValue"["Shape"]], "Wire" | "Wires" | "Wires"[_]]

DiagramProp[d_, "Shape", opts : OptionsPattern[]] := Enclose @ Block[{
    w = Replace[d["OptionValue"["Width"], opts], Automatic -> 1],
    h = Replace[d["OptionValue"["Height"], opts], Automatic -> 1],
    c = d["OptionValue"["Center"], opts],
    a = d["OptionValue"["Angle"], opts],
    func = d["OptionValue"["PortFunction"], opts],
    transform, primitives
},
    transform = GeometricTransformation[#, RotationTransform[a, c] @* If[d["FlipQ"], ReflectionTransform[{0, 1}, c], Identity] @* If[d["ReverseQ"], ReflectionTransform[{1, 0}, c], Identity]] &;
    primitives = Replace[
        d["OptionValue"["Shape"], opts],
        {
            None -> {},
            Automatic :> transform @ Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c],
            "RoundedRectangle" :> transform @ Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c, RoundingRadius -> {{Right, Bottom} -> .1 (w + h)}],
            "Triangle" :> transform @ Polygon[{{- w / 2, h / 2}, {0, - h / 2}, {w / 2, h / 2}} + Threaded[c]],
            "UpsideDownTriangle" :> transform @ Polygon[{{- w / 2, - h / 2}, {0, h / 2}, {w / 2, - h / 2}} + Threaded[c]],
            "Circle" :> transform @ Circle[c, {w, h} / 2],
            "CrossWires" :> With[{
                points = d["PortArrows", opts],
                inputs = PositionIndex[func /@ Through[d["InputPorts"]["Dual"]]],
                outputs = PositionIndex[func /@ d["OutputPorts"]]
            },
                Map[
                    ps |-> Outer[
                        BSplineCurve[{#1[[1]], 2 * #1[[1]] - #1[[2]], 2 * #2[[1]] - #2[[2]], #2[[1]]}] &,
                        ps[[2]],
                        ps[[1]],
                        1
                    ],
                    Values @ Merge[KeyUnion[{inputs, outputs}, {} &], Apply[{points[[1, #1]], points[[2, #2]]} &]]
                ]
            ],
            "Wires" :> With[{
                points = d["PortArrows", opts],
                inputs = PositionIndex[func /@ Through[d["InputPorts"]["Dual"]]],
                outputs = PositionIndex[func /@ d["OutputPorts"]]
            },
                Map[
                    ps |-> BSplineCurve[{ps[[1, 1]], 2 * ps[[1, 1]] - ps[[1, 2]], If[Length[ps] == 2, Nothing, c], 2 * #[[1]] - #[[2]], #[[1]]}] & /@ Rest[ps],
                    Values @ Merge[KeyUnion[{inputs, outputs}, {} &], Apply[Join[points[[1, #1]], points[[2, #2]]] &]]
                ]
            ],
            "Wires"[wires_] :> With[{
                ps = Catenate[d["PortArrows", opts]]
            },
                With[{p = ps[[First[#]]]},
                    BSplineCurve[{p[[1]], 2 * p[[1]] - p[[2]], 2 * #[[1]] - #[[2]], #[[1]]}] & /@ ps[[Rest[#]]]
                ] & /@ wires
            ],
            "Wire" :> With[{
                ps = Catenate[d["PortArrows", opts]]
            },
                BSplineCurve[{ps[[1, 1]], 2 * ps[[1, 1]] - ps[[1, 2]], c, 2 * #[[1]] - #[[2]], #[[1]]}] & /@ Rest[ps]
            ],
            shape_ :> transform @ GeometricTransformation[shape, TranslationTransform[c]]
        }
    ];
    If[ MatchQ[d["OptionValue"["Outline"], opts], Automatic | True],
        primitives = {primitives, EdgeForm[Directive[Dashed, Black]], FaceForm[None], transform[Rectangle[{c[[1]]- w / 2, c[[2]] - h / 2}, {c[[1]] + w / 2, c[[2]] + h / 2}]]},
        primitives
    ]
]

DiagramProp[d_, "PortArrows", opts : OptionsPattern[]] := With[{
    w = Replace[d["OptionValue"["Width"], opts], Automatic -> 1],
    h = Replace[d["OptionValue"["Height"], opts], Automatic -> 1],
    c = d["OptionValue"["Center"], opts],
    a = d["OptionValue"["Angle"], opts],
    s = d["OptionValue"["Spacing"], opts],
    shape = d["OptionValue"["Shape"], opts],
    arities = {d["InputArity"], d["OutputArity"]}
}, {
    arrows = fillAutomatic[d["OptionValue"["PortArrows"], opts], arities, True],
    transform = RotationTransform[a, c],
    placeArrow = Replace[{Right -> {{1 / 2, 0}, {1, 0}}, Left -> {{- 1 / 2, 0}, {- 1, 0}}, Top -> {{0, 1 / 2}, {0, 1}}, Bottom -> {{0, - 1 / 2}, {0, - 1}}}]
},
    {
         transform @ MapThread[
            Replace[#3, {
                Placed[_, p : Except[Automatic]] :> placeArrow[p],
                _ :> Replace[shape, {
                    "Circle" :> {1 / 2 {w Cos[#1], h Sin[#1]}, 3 / 4 {w Cos[#1], h Sin[#1]}} + Threaded[c],
                    _ :> {{(- 1 / 2 + #2) w, h / 2}, {(- 1 / 2 + #2) w, h / 2 + 1 / 4}} + Threaded[c]
                }]
            }] &,
            {
                Range[Pi, 0, - Pi / (d["InputArity"] + 1)][[2 ;; -2]],
                Range[(1 - s) / 2, (s + 1) / 2, s / (d["InputArity"] + 1)][[2 ;; -2]],
                arrows[[1]]
            }
        ]
        ,
        transform @ MapThread[
            Replace[#3, {
                Placed[_, p : Except[Automatic]] :> placeArrow[p],
                _ :> Replace[shape, {
                    "Circle" :> {1 / 2 {w Cos[#1], h Sin[#1]}, 3 / 4 {w Cos[#1], h Sin[#1]}} + Threaded[c],
                    _ :> {{(- 1 / 2 + #2) w, - h / 2}, {(- 1 / 2 + #2) w, - h / 2 - 1 / 4}} + Threaded[c]
                }]
            }] &,
            {
                Range[Pi, 2 Pi, Pi / (d["OutputArity"] + 1)][[2 ;; -2]],
                Range[(1 - s) / 2, (s + 1) / 2, s / (d["OutputArity"] + 1)][[2 ;; -2]],
                arrows[[2]]
            }
        ]
    }
]


DiagramProp[_, prop_] := Missing[prop]


(* ::Subsection:: *)
(* Formatting *)

Options[DiagramGraphics] = Join[{
    "Shape" -> Automatic,
    "Center" -> {0, 0},
    "Width" -> Automatic,
    "Height" -> Automatic,
    "Angle" -> 0,
    "Spacing" -> 1.6,
    "ShowLabel" -> Automatic,
    "LabelFunction" -> Automatic,
    "PortArrows" -> Automatic,
    "PortLabels" -> Automatic,
    "PortLabelFunction" -> Automatic,
    "Outline" -> None
}, Options[Graphics]];

DiagramGraphics[diagram_ ? DiagramQ, opts : OptionsPattern[]] := Enclose @ With[{
    points = diagram["PortArrows", opts],
    arities = {diagram["InputArity"], diagram["OutputArity"]}
}, {
    portArrows = Replace[fillAutomatic[diagram["OptionValue"["PortArrows"], opts], arities], Placed[x_, _] :> x, {2}],
    portLabels = fillAutomatic[diagram["OptionValue"["PortLabels"], opts], arities],
    labelFunction = diagram["OptionValue"["LabelFunction"], opts],
    portLabelFunction = diagram["OptionValue"["PortLabelFunction"], opts]
}, Graphics[{
    EdgeForm[Black], FaceForm[Transparent], 
    Confirm @ diagram["Shape", opts],
    Text[
        Replace[labelFunction,
            Automatic :> Function[ClickToCopy[
                If[ MatchQ[#["OptionValue"["ShowLabel"], opts], None | False],
                    "\t\t\t",
                    Replace[#["HoldExpression"], expr_ :> (expr //. d_Diagram ? DiagramQ :> RuleCondition[d["HoldExpression"]])]
                ],
                #["View"]
            ]]
        ] @ diagram,
        diagram["OptionValue"["Center"], opts]
    ],
    Arrowheads[Small],
    MapThread[{ports, ps, arrows, labels, angle} |->
        MapThread[{x, p, arrow, label} |-> {
            If[ MatchQ[arrow, None | False],
                Nothing,
                If[MatchQ[arrow, _Function], arrow[p, x], {Replace[arrow, True | Automatic -> Nothing], Arrow[If[x["DualQ"], Reverse, Identity] @ p]}]
            ],
            If[ MatchQ[label, None | False],
                Nothing,
                Replace[label, Placed[l_, pos_] | l_ :> Text[
                        Replace[portLabelFunction, Automatic -> Function[ClickToCopy[#2 /. Automatic :> If[#1["DualQ"], #1["Dual"], #1], #1["View"]]]][x, l],
                        With[{v = p[[-1]] - p[[1]], s = PadLeft[Flatten[Replace[{pos}, {{Right} -> {2, 0}, {Left} -> {- 2, 0}, {Top} -> {0, 2}, {Bottom} -> {0, - 2}, {} -> {0, 2}}]], 2, 0]}, p[[1]] + s[[2]] * v + s[[1]] * RotationTransform[angle][v]]
                    ]
                ]
            ]
        },
           {ports, ps, arrows, labels}
        ],
        {{diagram["InputPorts"], diagram["OutputPorts"]}, points, portArrows, portLabels, {Pi / 2, - Pi / 2}}
    ]
},
    FilterRules[{opts, diagram["DiagramOptions"]}, Options[Graphics]],
    FormatType -> StandardForm
]]

Diagram /: MakeBoxes[diagram : Diagram[_Association] ? DiagramQ, form_] := With[{boxes = ToBoxes[Show[
    If[diagram["NetworkQ"], diagram["NetGraph"], diagram["Graphics"]], BaseStyle -> {GraphicsHighlightColor -> Magenta}], form]},
    InterpretationBox[boxes, diagram]
]

DiagramDual /: MakeBoxes[DiagramDual[d_], form_] := With[{boxes = ToBoxes[SuperStar[d], form]}, InterpretationBox[boxes, DiagramDual[d]]]

DiagramFlip /: MakeBoxes[DiagramFlip[d_], form_] := With[{boxes = ToBoxes[OverBar[d], form]}, InterpretationBox[boxes, DiagramFlip[d]]]

DiagramReverse /: MakeBoxes[DiagramReverse[d_], form_] := With[{boxes = ToBoxes[Overscript[d, RawBoxes["\[LongLeftRightArrow]"]], form]}, InterpretationBox[boxes, DiagramReverse[d]]]

DiagramProduct /: MakeBoxes[DiagramProduct[ds___], form_] := With[{boxes = ToBoxes[CircleTimes[ds], form]}, InterpretationBox[boxes, DiagramProduct[ds]]]

DiagramSum /: MakeBoxes[DiagramSum[ds___], form_] := With[{boxes = ToBoxes[CirclePlus[ds], form]}, InterpretationBox[boxes, DiagramSum[ds]]]

DiagramComposition /: MakeBoxes[DiagramComposition[ds___], form_] := With[{boxes = ToBoxes[CircleDot[ds], form]}, InterpretationBox[boxes, DiagramComposition[ds]]]

DiagramNetwork /: MakeBoxes[DiagramNetwork[ds___], form_] := With[{boxes = ToBoxes[{ds}, form]}, InterpretationBox[boxes, DiagramNetwork[ds]]]


(* ::Subsection:: *)
(* Functions *)


Options[DiagramsPortGraph] = Options[Graph];
DiagramsPortGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := GraphSum[##, FilterRules[{opts}, Options[Graph]], VertexLabels -> Automatic] & @@
    (With[{vs = Through[#["HoldExpression"]]}, Graph[vs, UndirectedEdge @@@ Subsets[vs, {2}]]] & /@ Through[diagrams["Ports"]])


Options[DiagramsGraph] = Join[{"PortFunction" -> Function[#["Name"]]}, Options[Graph]];
DiagramsGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := Block[{
    ports = Thread[{Through[#["InputPorts"]["Dual"]] & /@ #, Through[#["OutputPorts"]]}] & @ Through[diagrams["Flatten"]],
    portFunction = OptionValue["PortFunction"],
    graph, embedding
},
    graph = Graph[
        Join[
            MapIndexed[Annotation[#2[[1]], "Diagram" -> #1] &, diagrams],
            Flatten[MapIndexed[Annotation[#2, "Port" -> #1] &, ports, {3}], 2]
        ],
        Flatten[
            MapIndexed[
                With[{diagram = #2[[1]], port = #2, wire = portFunction[#1]},
                    Switch[port[[2]], 1, {DirectedEdge[port, diagram], DirectedEdge[wire, port]}, 2, {DirectedEdge[diagram, port], DirectedEdge[port, wire]}]
                ] &,
                ports,
                {3}
            ],
            3
        ],
        VertexLabels -> MapAt[Placed[#, Center] &, {All, 2}] @ Join[
            {_ -> Automatic},
            Thread[Range[Length[diagrams]] -> Through[diagrams["HoldExpression"]]],
            Flatten[MapIndexed[#2 -> #1["Label"] &, ports, {3}], 2]
        ],
        VertexSize -> {_ -> Medium, _Integer -> Large, {__Integer} -> Medium},
        VertexShapeFunction -> {_ -> "Diamond", _Integer -> "Square", {__Integer} -> "Circle"},
        VertexStyle -> Transparent,
        PerformanceGoal -> "Quality"
    ];
    embedding = AssociationThread[
        VertexList[graph],
        GraphEmbedding[
            EdgeAdd[graph,
                Catenate[DirectedEdge @@@ Partition[Reverse @ Catenate[#], 2, 1, 1] & /@ MapAt[Reverse, MapIndexed[#2 &, ports, {3}], {All, 2}]],
                FilterRules[{opts}, {VertexCoordinates, GraphLayout}]
            ]
        ]
    ];
    embedding = <|
        embedding,
        If[Catenate[#] === {}, Nothing, With[{diagramCenter = Lookup[embedding, Catenate[#][[1, 1]]]},
            Thread[# -> SortBy[Lookup[embedding, #], ArcTan @@ (# - diagramCenter) &]] & /@ #
        ]] & /@ MapIndexed[#2 &, ports, {3}]
    |>;
    Graph[
        graph,
        FilterRules[{opts}, Options[Graph]],
        VertexCoordinates -> Normal[embedding]
    ]
]


RemoveDiagramsNetGraphCycles[inputNet_ ? DirectedGraphQ, opts : OptionsPattern[Graph]] := Enclose @ Block[{
    net = inputNet, diagrams, cycles, id, edge, cups = {}, caps = {}, cupDiagrams = {}, capDiagrams = {}, cup, cap
},
	diagrams = AssociationThread[VertexList[net], AnnotationValue[{inputNet, VertexList[net]}, "Diagram"]];
	id = Max[VertexList[net, _Integer], 0] + 1;

	While[
        Length[cycles = FindCycle[net, Infinity, 1]] > 0,

		edge = cycles[[1, -1]];
		AppendTo[cups, cup = id++];
		AppendTo[caps, cap = id++];
		AppendTo[cupDiagrams, With[{port = Lookup[diagrams, edge[[2]]]["InputPorts"][[edge[[3, -1, 3]]]]},
            Diagram["Cup", {port, port["Dual"]}, "Shape" -> "Wire", "ShowLabel" -> False]
        ]];
		AppendTo[capDiagrams, With[{port = Lookup[diagrams, edge[[1]]]["OutputPorts"][[edge[[3, 1, 3]]]]},
            Diagram["Cap", {port, port["Dual"]}, {}, "Shape" -> "Wire", "ShowLabel" -> False]
        ]];
		net = EdgeDelete[net, {edge}];
		net = VertexAdd[net, {cap, cup}];
        net = EdgeAdd[net, {
			DirectedEdge[cup, cap, {{2, 2, 1}, {1, 2, 1}}],
			DirectedEdge[cup, edge[[2]], {{2, 2, 2}, {1, edge[[3, -1, 2]], edge[[3, -1, 3]]}}],
			DirectedEdge[edge[[1]], cap, {{2, edge[[3, 1, 2]], edge[[3, 1, 3]]}, {1, 2, 2}}]
		}];
	];
	Graph[net, opts,
		AnnotationRules -> Join[
            Thread[cups -> List /@ Thread["Diagram" -> cupDiagrams]],
            Thread[caps -> List /@ Thread["Diagram" -> capDiagrams]]
        ]
	]
]

Options[DiagramsNetGraph] = Join[{
    "ShowPortLabels" -> False,
    "ShowWireLabels" -> True,
    "Scale" -> Automatic,
    "ArrowSize" -> 0.01,
    "SpiderRadius" -> 0.2,
    "Orientation" -> Automatic,
    "UnarySpiders" -> True,
    "BinarySpiders" -> True,
    "RemoveCycles" -> False
}, Options[DiagramsGraph], Options[DiagramGraphics], Options[Graph]];
DiagramsNetGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] :=
    DiagramsNetGraph[
        DiagramsGraph[diagrams, FilterRules[{opts}, {GraphLayout, FilterRules[Options[DiagramsGraph], Except[Options[Graph]]]}]],
        FilterRules[{opts}, Except[GraphLayout]]
    ]
DiagramsNetGraph[graph_Graph, opts : OptionsPattern[]] := Block[{
	diagramVertices = VertexList[graph, _Integer], vertices, edges, netGraph,
    spiderVertices, spiderDiagrams,
	diagrams, outDegrees, inDegrees,
	embedding, orientations, orientation = OptionValue["Orientation"],
	scale = Replace[OptionValue["Scale"], Automatic -> .75],
    arrowSize = OptionValue["ArrowSize"],
    rad = OptionValue["SpiderRadius"],
	portLabelsQ = TrueQ[OptionValue["ShowPortLabels"]],
	wireLabelsQ = TrueQ[OptionValue["ShowWireLabels"]],
    unarySpiders = OptionValue["UnarySpiders"],
    binarySpiders = OptionValue["BinarySpiders"],
    portFunction = OptionValue["PortFunction"]
},
	diagrams = Through[(AnnotationValue[{graph, #}, "Diagram"] & /@ diagramVertices)["Flatten"]];
	If[Length[diagrams] == 0, Return[Graphics[FilterRules[Join[{opts}, Options[graph]], Options[Graphics]]]]];
	embedding = AssociationThread[VertexList[graph], GraphEmbedding[graph]];
	If[EdgeCount[graph] == 0 && VertexCount[graph] > 1, embedding = ScalingTransform[{1, .5} / Max[#2 - #1 & @@@ CoordinateBounds[embedding]], Mean[embedding]][embedding]];
	orientations = Switch[
        orientation,
        Automatic,
        Map[
            Normalize[Lookup[#, 1] - Lookup[#, 2]] &,
            Values @ <|
                # -> <|1 -> {0, 1 / 2}, 2 -> {0, - 1 / 2}|> & /@ diagramVertices,
                KeyValueMap[
                    With[{center = Lookup[embedding, #1]}, #1 -> <|<|1 -> center, 2 -> center|>, #2|>] &,
                    GroupBy[VertexList[graph, {__Integer}], First, Mean /@ GroupBy[#, #[[2]] &, Lookup[embedding, #] &] &]
                ]
            |>
        ],
        {_ ? NumericQ, _ ? NumericQ},
        ConstantArray[orientation, Length[diagramVertices]],
        _,
        ConstantArray[{0, 1}, Length[diagramVertices]]
    ];
	{outDegrees, inDegrees} = AssociationThread[VertexList[graph] -> #] & /@ Through[{VertexOutDegree, VertexInDegree}[graph]];
	{spiderVertices, spiderDiagrams} = Replace[{{} -> {{}, {}}, sow_List :> Thread[sow]}] @ First[Reap[
		edges = Map[v |->
			Block[{in = VertexInComponent[graph, v, {1}], out = VertexOutComponent[graph, v, {1}], ports},
				ports = Join[in, out];
				If[ Length[ports] > 2 ||
                    Length[ports] == 1 && MatchQ[unarySpiders, True] ||
                    Length[ports] == 2 && (MatchQ[binarySpiders, All | Full] || MatchQ[binarySpiders, True] && SameQ @@ ports[[All, 2]])
                    ,
					Sow[{v,
                        Diagram[v,
                            Port[tag[v, #]] & /@ in,
                            Port[tag[v, #]] & /@ out,
                            If[Length[ports] == 2, {"Shape" -> "Wire", "ShowLabel" -> False}, {"Shape" -> "Circle", "ShowLabel" -> wireLabelsQ}]
                        ]
                    }];
                    Splice @ Catenate @ {
                        MapIndexed[DirectedEdge[#[[1]], v, {{2, Lookup[outDegrees, #[[1]]], #[[3]]}, {1, Length[in], #2[[1]]}}] &, in],
                        MapIndexed[DirectedEdge[v, #[[1]], {{2, Length[out], #2[[1]]}, {1, Lookup[inDegrees, #[[1]]], #[[3]]}}] &, out]
                    }
                    ,
					If[ Length[ports] < 2,
                        Nothing,
                        Block[{src, tgt, srcDegree, tgtDegree},
                            {src, tgt} = If[ ports[[1, 2]] == 1, {ports[[2]], ports[[1]]}, {ports[[1]], ports[[2]]}];
                            srcDegree = If[ src[[2]] == 1, inDegrees, outDegrees][src[[1]]];
                            tgtDegree = If[ tgt[[2]] == 1, inDegrees, outDegrees][tgt[[1]]];
                            DirectedEdge[src[[1]], tgt[[1]], {{src[[2]], srcDegree, src[[3]]}, v, {tgt[[2]], tgtDegree, tgt[[3]]}}]
                        ]
                    ]
				]
			],
			VertexList[graph, _HoldForm]
		]
	][[2]], {}];
	vertices = Join[diagramVertices, spiderVertices];
    netGraph = Graph[vertices, edges,
        AnnotationRules -> Join[
            Thread[diagramVertices -> List /@ Thread["Diagram" -> MapIndexed[
                Diagram[#1,
                    "OutputPorts" -> MapThread[
                        FirstCase[edges,
                            DirectedEdge[#2[[1]], tgtIdx_, {{2, _, #2[[3]]}, _, {1, _, portIdx_}}] :> With[{tgt = portFunction @ diagrams[[tgtIdx]]["InputPorts"][[portIdx]]["Dual"]},
                                Port[tag[tgt, {tgtIdx, 1, portIdx}]]
                            ],
                            Port[tag[#1, #2]]
                        ] &,
                        {portFunction /@ #1["OutputPorts"], Thread[{#2[[1]], 2, Range[#1["OutputArity"]]}]}
                    ],
                    "InputPorts" -> MapThread[
                        Port[tag[#1, #2]]["Dual"] &,
                        {portFunction /@ Through[#1["InputPorts"]["Dual"]], Thread[{#2[[1]], 1, Range[#1["InputArity"]]}]}
                    ]
                ] &,
                diagrams
            ]]],
            Thread[spiderVertices -> List /@ Thread["Diagram" -> spiderDiagrams]]
        ]
    ];
    If[TrueQ[OptionValue["RemoveCycles"]], netGraph = RemoveDiagramsNetGraphCycles[netGraph]];
	Graph[
		netGraph,
		FilterRules[{opts}, Options[Graph]],
		VertexCoordinates -> Thread[vertices -> Join[Lookup[embedding, diagramVertices] + Through[diagrams["OptionValue"["Center"]]], Lookup[embedding, spiderVertices]]],
		VertexShapeFunction -> Join[
			Thread[diagramVertices ->
				MapThread[{diagram, orientation} |-> With[{
						shape = First @ diagram["Graphics", "PortLabels" -> If[portLabelsQ, Automatic, None], "PortArrows" -> None, "LabelFunction" -> Function[Rotate[#["HoldExpression"], Pi]], opts],
						transform = RotationTransform[{{0, 1}, orientation}] @* ScalingTransform[scale {1, 1}]
					},
						Function[{
							Black, FaceForm[None],
							GeometricTransformation[shape, TranslationTransform[#1] @* transform]
						}]
					],
					{diagrams, orientations}
				]
			],
			Thread[spiderVertices -> With[{radius = rad * scale}, Function[Circle[#1, radius]]]]
		],
		EdgeShapeFunction -> Replace[edges, {
				edge : DirectedEdge[v_Integer, w_Integer, {{i : 1 | 2, _Integer, p_Integer}, x_, {j : 1 | 2, _Integer, q_Integer}}] :> edge -> Block[{
					point1, point2, normal1, normal2, orientation1 = orientations[[v]], orientation2 = orientations[[w]], wireCoords = Lookup[embedding, x],
                    diagram1 = diagrams[[v]], diagram2 = diagrams[[w]],
                    port1, port2,
                    points1, points2
				},
                    port1 = diagram1[Replace[i, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[p]];
                    port2 = diagram2[Replace[j, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[q]];
                    points1 = diagram1["PortArrows"][[i, p]];
                    points2 = diagram2["PortArrows"][[j, q]];
                    point1 = points1[[1]] * scale;
                    normal1 = (points1[[-1]] - points1[[1]]) * scale * 3;
                    point2 = points2[[1]] * scale;
                    normal2 = (points2[[-1]] - points2[[1]]) * scale * 3;
					point1 = RotationTransform[{{0, 1}, orientation1}] @ point1;
					normal1 = RotationTransform[{{0, 1}, orientation1}] @ normal1;
					point2 = RotationTransform[{{0, 1}, orientation2}] @ point2;
					normal2 = RotationTransform[{{0, 1}, orientation2}] @ normal2;
					With[{
                        a = VectorSymbol["p", 2], b = VectorSymbol["q", 2],
                        lindep = v == w && TrueQ[Quiet[Chop[Det[{normal1, normal2}]]] == 0]
                    },
						Function[Evaluate @ {
							Arrowheads[{
                                If[port1["DualQ"], {- arrowSize, .3}, {arrowSize, .3}],
                                If[port2["DualQ"], {arrowSize, .7}, {- arrowSize, .7}]
                            }
                            ],
							Arrow @ BSplineCurve[{
                                a + point1, a + point1 + normal1,
                                If[lindep, (a + b) / 2 + 2 * RotationTransform[Pi / 2][normal1], Nothing],
                                b + point2 + normal2, b + point2
                            }],
							If[ wireLabelsQ,
                                Text[
                                    Style[ClickToCopy[x, x], Black],
                                    If[ lindep,
                                        (a + b) / 2 + 1.25 RotationTransform[Pi / 2][normal1],
                                        (a + point1 + normal1 + b + point2 + normal2) / 2 + .1 normal1
                                    ]
                                ],
                                Nothing
                            ]
						}] /. {a :> #[[1]], b :> #[[-1]]}
					]
				],
				edge : DirectedEdge[v_Integer, _, {{i : 1 | 2, _Integer, p_Integer}, _}] | DirectedEdge[_, v_Integer, {_, {i : 1 | 2, _Integer, p_Integer}}] :> edge -> Block[{
					point, normal, orientation = orientations[[v]], portCoords = Lookup[embedding, Key[{v, i, p}]],
                    diagram = diagrams[[v]],
                    port, points
				},
                    port = diagram[Replace[i, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[p]];
                    points = diagram["PortArrows"][[i, p]];
                    point = points[[1]] * scale;
                    normal = (points[[-1]] - points[[1]]) * scale * 3;
					point = RotationTransform[{{0, 1}, orientation}] @ point;
					normal = RotationTransform[{{0, 1}, orientation}] @ normal;

					With[{a = VectorSymbol["p", 2], b = VectorSymbol["q", 2]},
						Function[Evaluate @ {
							Arrowheads[If[port["DualQ"], {{-arrowSize, .5}}, {{arrowSize, .5}}]],
							Arrow @ BSplineCurve[{a + point, a + point + normal, b + scale Normalize[portCoords - b], b + rad scale Normalize[portCoords - b]}]
						}] /. With[{s = If[IntegerQ[edge[[1]]], 1, -1]}, {a :> #[[s]], b :> #[[-s]]}]
					]
				],
				_ -> Nothing
			},
			1
		],
		VertexLabels -> (# -> If[wireLabelsQ, Placed[ClickToCopy[#, #], Center], None] & /@ spiderVertices),
		BaseStyle -> {FormatType -> StandardForm}
	]
]


DiagramsFreePorts[diagrams : {___Diagram ? DiagramQ}] := Keys @ Select[CountsBy[Catenate[Through[Through[diagrams["Flatten"]]["Ports"]]], #["HoldExpression"] &], EqualTo[1]]


Options[ToDiagramNetwork] = Join[{"PortFunction" -> (#["Name"] &), "Unique" -> True}, Options[DiagramNetwork]];

ToDiagramNetwork[d_Diagram, opts : OptionsPattern[]] := If[d["NetworkQ"],
    Diagram[d, opts],
    With[{net = DiagramNetwork[##, FilterRules[{opts, d["DiagramOptions"]}, Options[DiagramNetwork]], "PortFunction" -> (#["HoldExpression"] &)], portFunction = OptionValue["PortFunction"]},
        Diagram[net,
            "OutputPorts" -> Permute[net["OutputPorts"], FindPermutation[Through[net["OutputPorts"]["HoldExpression"]][[All, 1, 1]], portFunction /@ d["OutputPorts"]]],
            "InputPorts" -> Permute[net["InputPorts"], FindPermutation[Through[Through[net["InputPorts"]["Dual"]]["HoldExpression"]][[All, 1, 1]], portFunction /@ Through[d["InputPorts"]["Dual"]]]]
        ]
    ] & @@ ToDiagramNetwork[If[TrueQ[OptionValue["Arrange"]], d["Arrange", opts], d]["Decompose"], {}, {}, opts]
]

ToDiagramNetwork[d_Diagram, pos_, ports_, opts : OptionsPattern[]] := Block[{portFunction = OptionValue["PortFunction"], uniqueQ = TrueQ[OptionValue["Unique"]], mports = ports, port}, {
	Diagram[d,
		"OutputPorts" -> MapIndexed[
            Port @ If[ KeyExistsQ[mports, #1],
                Sow[port = #1 -> Lookup[mports, #1], "Port"];
                mports = DeleteElements[mports, 1 -> {port}];
                port[[2]]
                ,
                Interpretation[#1, Evaluate[If[uniqueQ, Join[pos, {1}, #2], pos] -> #1]]
            ] &,
            portFunction /@ d["FlatOutputPorts"]
        ],
		"InputPorts" -> MapIndexed[Port[Interpretation[#1, Evaluate[If[uniqueQ, Join[pos, {2}, #2], pos] -> #1]]]["Dual"] &, portFunction /@ Through[d["FlatInputPorts"]["Dual"]]],
        opts
	]
}
]

ToDiagramNetwork[CirclePlus[ds___], pos_, ports_, opts : OptionsPattern[]] :=
    Catenate @ MapIndexed[ToDiagramNetwork[#1, Join[pos, #2], ports, opts] &, {ds}]

ToDiagramNetwork[CircleTimes[ds___], pos_, ports_, opts : OptionsPattern[]] :=
    Catenate @ FoldPairList[With[{net = Reap[ToDiagramNetwork[#2, Append[pos, #1[[1]]], #1[[2]], opts], "Port"]}, {net[[1]], {#1[[1]] + 1, DeleteElements[#1[[2]], 1 -> Catenate[net[[2]]]]}}] &, {1, ports}, {ds}]

ToDiagramNetwork[CircleDot[ds__], pos_, ports_, opts : OptionsPattern[]] := With[{portFunction = OptionValue["PortFunction"]},
	Fold[
		{
            DiagramNetwork[##, FilterRules[{opts}, Options[DiagramNetwork]], "PortFunction" -> (#["HoldExpression"] &)] & @@
                Join[#1[[1]]["SubDiagrams"], ToDiagramNetwork[#2, Append[pos, #1[[2]]], Join[portFunction[#] -> # & /@ Through[#1[[1]]["FlatInputPorts"]["Dual"]], ports], opts]],
            #1[[2]] + 1
        } &,
		{Diagram[], 1},
		{ds}
	][[1]]["SubDiagrams"]
]

ToDiagramNetwork[{ds___}, pos_, ports_, opts : OptionsPattern[]] := Catenate[ToDiagramNetwork[#, pos, ports, "Unique" -> False, opts] & /@ {ds}]


portDimension[p_Port] := Replace[p["Type"], {SuperStar[Superscript[_, n_]] | Superscript[_, n_] :> n, _ :> p["Name"]}]

Options[DiagramTensor] = {"Kronecker" -> False, "ArrayDot" -> True}

DiagramTensor[diagram_Diagram, opts : OptionsPattern[]] := diagramTensor[diagram["Arrange"], opts]

Options[diagramTensor] = Options[DiagramTensor]

diagramTensor[diagram_Diagram, opts : OptionsPattern[]] := Replace[diagram["HoldExpression"], {
	HoldForm[DiagramDual[d_]] :> Conjugate[diagramTensor[d, opts]]
	,
	HoldForm[DiagramFlip[d_]] :> ConjugateTranspose[diagramTensor[d, opts], FindPermutation[Catenate[Reverse @ TakeDrop[Range[diagram["Arity"]], diagram["OutputArity"]]]]]
	,
	HoldForm[DiagramReverse[d_]] :> Transpose[diagramTensor[d, opts], FindPermutation[Join[Reverse @ Range[diagram["OutputArity"]], Reverse[diagram["OutputArity"] + Range[diagram["InputArity"]]]]]]
	,
	HoldForm[DiagramComposition[ds___]] :> If[TrueQ[OptionValue["ArrayDot"]],
        Fold[ArrayDot[If[DiagramQ[#1], diagramTensor[#1, opts], #1], diagramTensor[#2, opts], #2["OutputArity"]] &, {ds}]
        ,
        Dot @@ (
            If[ #["OutputArity"] == #["InputArity"] == 1
                ,
                diagramTensor[#, opts]
                ,
                ArrayReshape[diagramTensor[#, opts], {Times @@ Through[#["OutputPorts"]["Name"]], Times @@ Through[#["InputPorts"]["Name"]]}]
            ] & /@ {ds}
	    )
    ]
	,
	HoldForm[DiagramProduct[ds___]] :> If[TrueQ[OptionValue["Kronecker"]],
        With[{
            tensors = If[ #["OutputArity"] == #["InputArity"] == 1
                ,
                diagramTensor[#, opts]
                ,
                ArrayReshape[diagramTensor[#, opts], {Times @@ Through[#["OutputPorts"]["Name"]], Times @@ Through[#["InputPorts"]["Name"]]}]
            ] & /@ {ds}
        }
        ,
            ArrayReshape[
                KroneckerProduct @@ tensors
                ,
                Join[Catenate[Through[#["OutputPorts"]["Name"]] & /@ {ds}], Catenate[Through[#["InputPorts"]["Name"]] & /@ {ds}]]
            ]
        ]
        ,
        With[{
            tensors = diagramTensor[#, opts] & /@ {ds},
            indices = FoldPairList[With[{out = #2["OutputArity"], in = #2["InputArity"]}, {#1 + {Range[out], out + Range[in]}, #1 + out + in}] &, 0, {ds}]
        }
        ,
            Transpose[TensorProduct @@ tensors, FindPermutation[Flatten[Thread[indices]]]]
        ]
    ]
	,
	HoldForm[DiagramSum[ds___]] :> Plus @@ (diagramTensor[#, opts] & /@ {ds})
	,
	HoldForm[DiagramNetwork[ds___]] :> Block[{
		portFunction = diagram["OptionValue"["PortFunction"]],
		freePorts, ports, contraction, permutation
	},
		freePorts = Join[portFunction /@ diagram["OutputPorts"], portFunction[#["Dual"]] & /@ diagram["InputPorts"]];
		ports = Catenate @ MapThread[Join, {Map[portFunction, Through[{ds}["OutputPorts"]], {2}], Map[portFunction[#["Dual"]] &, Through[{ds}["InputPorts"]], {2}]}];
		contraction = Values @ Select[PositionIndex[ports], Length[#] > 1 &];
		permutation = FindPermutation[Delete[ports, List /@ Catenate[contraction]], freePorts];
		Transpose[
			TensorContract[
				TensorProduct @@ (diagramTensor[#, opts] & /@ {ds}),
				contraction
			],
			permutation
		]
	]
	,
	_ :>
        Replace[diagram["Expression"], {
            "1" -> SymbolicIdentityArray[portDimension /@ diagram["OutputPorts"]],
            Interpretation["\[Pi]", perm_Cycles] :> Transpose[SymbolicIdentityArray[portDimension /@ diagram["OutputPorts"]], perm],
            Annotation[expr_, OptionsPattern[{"Domain" -> Sequence[], "Symmetry" -> Sequence[]}]] | expr_ :>
                Switch[diagram["Arity"], 1, VectorSymbol, 2, MatrixSymbol, _, ArraySymbol][expr, portDimension /@ diagram["Ports"], OptionValue["Domain"], OptionValue["Symmetry"]]
        }]
}]

DiagramSplit[diagram_Diagram, n : _Integer | Infinity | - Infinity : Infinity, dualQ : _ ? BooleanQ : True, flipQ : _ ? BooleanQ : False] := With[
    {d = diagram["Flatten"], dual = If[dualQ, PortDual, Identity]},
    {outs = d["OutputArity"], ins = d["InputArity"], m = If[n >= 0, Min[d["Arity"], n], Max[d["Arity"] + n, 0]]}
,
	Which[
		m < outs,
        With[{outputs = TakeDrop[d["OutputPorts"], UpTo[m]]},
            DiagramComposition[
                If[ flipQ,
                    Diagram["\[DoubleStruckCapitalI]", Join[d["OutputPorts"], dual /@ outputs[[2]]], outputs[[1]],
                        "Shape" -> "Wires"[Join[Thread[{Range[m], 2 outs - m + Range[m]}], Thread[{outs - m + Range[outs - m], outs + Range[outs - m]}]]], "ShowLabel" -> False
                    ],
                    Diagram["\[DoubleStruckCapitalI]", Join[dual /@ outputs[[2]], d["OutputPorts"]], outputs[[1]],
                        "Shape" -> "Wires"[Join[Thread[{Range[outs - m], outs + Range[outs - m]}], Thread[{outs - m + Range[m], 2 outs - m + Range[m]}]]], "ShowLabel" -> False
                    ]
                ],
                d,
                "PortFunction" -> Function[#["HoldExpression"]]
            ]
        ],
		m > outs,
        With[{inputs = TakeDrop[Through[d["InputPorts"]["Dual"]], UpTo[m - outs]]},
		    DiagramComposition[
                d,
                If[ flipQ,
                    Diagram["\[DoubleStruckCapitalI]", inputs[[2]], Join[dual /@ inputs[[1]], Through[d["InputPorts"]["Dual"]]],
                        "Shape" -> "Wires"[Join[
                            Thread[{ins - (m - outs) + Range[m - outs], ins + Range[m - outs]}],
                            Thread[{Range[ins - (m - outs)], ins + (m - outs) + Range[ins - (m - outs)]}]
                        ]],
                        "ShowLabel" -> False
                    ],
                    Diagram["\[DoubleStruckCapitalI]", inputs[[2]], Join[Through[d["InputPorts"]["Dual"]], dual /@ inputs[[1]]],
                        "Shape" -> "Wires"[Join[
                            Thread[{Range[ins - (m - outs)], ins + Range[ins - (m - outs)]}],
                            Thread[{ins - (m - outs) + Range[m - outs], 2 ins - (m - outs) + Range[m - outs]}]
                        ]],
                        "ShowLabel" -> False
                    ]
                ],
                "PortFunction" -> Function[#["HoldExpression"]]
            ]
        ],
		True,
		d
	]
]

DiagramPermute[diagram_Diagram, perm_] := Enclose @ With[{d = diagram["Flatten"]}, {ports = d["Ports"], newDiagram = DiagramSplit[d]}, {newPorts = ConfirmBy[Permute[ports, perm], ListQ]},
	If[ ports === newPorts,
		newDiagram,
		DiagramComposition[piDiagram[ports, newPorts], newDiagram, "PortFunction" -> (#["HoldExpression"] &)]
	]
]


Options[TensorDiagram] = Options[Diagram]

splitPattern = _Integer | Infinity | -Infinity

TensorDiagram[HoldPattern[VectorSymbol[v_, d_, dom_ : None]], opts : OptionsPattern[]] :=
	Diagram[Annotation[v, "Domain" -> Replace[dom, None -> Sequence[]]], Port[v, Superscript[Replace[dom, None -> Reals], d]], opts]

TensorDiagram[HoldPattern[MatrixSymbol[a_, {m_, n_}, dom_ : None, sym_ : Sequence[]]], opts : OptionsPattern[]] :=
    Diagram[
        Annotation[a, "Domain" -> Replace[dom, None -> Sequence[]], "Symmetry" -> sym],
        {Port[Indexed[a, 1], Superscript[Replace[dom, None -> Reals], m]], Port[Indexed[a, 2], Superscript[Replace[dom, None -> Reals], n]]},
        opts
    ]

TensorDiagram[HoldPattern[ArraySymbol[a_, ns_List : {}, dom_ : None, sym_ : Sequence[]]], opts : OptionsPattern[]] :=
    Diagram[
        Annotation[a, "Domain" -> Replace[dom, None -> Sequence[]], "Symmetry" -> sym],
        MapIndexed[Port[Indexed[a, #2], Superscript[Replace[dom, None -> Reals], #1]] &, ns],
        opts
    ]

TensorDiagram[HoldPattern[KroneckerProduct[ts___]]] := DiagramProduct @@ (TensorDiagram /@ {ts})

TensorDiagram[HoldPattern[TensorProduct[ts___]]] := DiagramProduct @@ (DiagramSplit[TensorDiagram[#], Infinity] & /@ {ts})

TensorDiagramDot[a_, b_, k_] := With[{x = DiagramSplit[a, -k, False, True], y = DiagramSplit[b, k, False, True]},
    DiagramComposition[x, DiagramMatchPorts[y, {PortDual /@ x["InputPorts"], Automatic}]["Flatten"], "PortFunction" -> (#["HoldExpression"] &)]
]

TensorDiagram[HoldPattern[Dot[ts__]]] := Fold[TensorDiagramDot[##, 1] &, TensorDiagram /@ {ts}]

TensorDiagram[HoldPattern[ArrayDot[a_, b_, k_]]] := TensorDiagramDot[TensorDiagram[a], TensorDiagram[b], k]

TensorDiagram[HoldPattern[Transpose[a_, perm_ : {1, 2}]]] := DiagramPermute[TensorDiagram[a], perm]

TensorDiagram[SymbolicIdentityArray[ns_List]] := Diagram["\[DoubleStruckCapitalI]", Join[#, #] & @ (Interpretation[#, Evaluate[Unique["i"]]] & /@ ns), "Shape" -> "Wires", "PortLabels" -> None]

TensorDiagram[scalar_] := Diagram[scalar]



Options[DiagramFunction] = {"IndexedOutput" -> True, "PortFunction" -> None};

DiagramFunction[diagram_Diagram, opts : OptionsPattern[]] := Replace[diagram["HoldExpression"], {
	HoldForm[DiagramDual[d_]] :> DiagramFunction[d, opts]
	,
	HoldForm[DiagramFlip[d_]] :> InverseFunction[DiagramFunction[d, opts]]
	,
	HoldForm[DiagramReverse[d_]] :> Reverse @* DiagramFunction[d, opts] @* Reverse
	,
	HoldForm[DiagramComposition[ds___]] :> Composition @@ (DiagramFunction[#, opts] & /@ {ds})
	,
	HoldForm[DiagramProduct[ds___]] :> With[{args = TakeDrop[Slot /@ Range[Total[#]], #] & @ Through[{ds}["InputArity"]] /. \[FormalX] -> #},
		Function @@ If[TrueQ[OptionValue["IndexedOutput"]], Map[Catenate], Identity] @ WaitAll /@ List @@@
			Hold @ Evaluate @ Flatten[Hold @@ MapThread[If[Length[#2] == 1, With[{x = #2[[1]]}, Hold[ParallelSubmit[#1[x]]]], Hold[ParallelSubmit[#1 @@ #2]]] &, {DiagramFunction[#, opts] & /@ {ds}, args}]]
	]
	,
	HoldForm[DiagramSum[ds___]] :> (DiagramFunction[#, opts] & /@ {ds})
	,
	_ :> With[{
		f = Replace[diagram["HoldExpression"],
			HoldForm[anno_Annotation] :> Lookup[Options[anno], "Function", diagram["HoldExpression"]]
		]
	},
		If[ TrueQ[OptionValue["IndexedOutput"]],
			With[{return = Table[Indexed[#, i], {i, diagram["OutputArity"]}]},
				Function[Function[return] @ f[##]]
			],
			f
		]
	]
}]


End[];

EndPackage[];