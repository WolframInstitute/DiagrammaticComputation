BeginPackage["ProcessTheory`Diagram`", {"ProcessTheory`Utilities`", "ProcessTheory`Port`"}];

Diagram
DiagramQ

DiagramDual
DiagramFlip
DiagramReverse

DiagramProduct
DiagramSum
DiagramComposition
DiagramNetwork

DiagramCompose
DiagramJoin
DiagramArrange
DiagramDecompose
DiagramGrid

DiagramsFreePorts
DiagramsPortGraph
DiagramsGraph
DiagramsNetGraph

Begin["ProcessTheory`Diagram`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Diagram::usage = "Diagram[expr] represents a symbolic diagram with input and output ports"

Options[Diagram] = {};

$DiagramHiddenOptions = {"Expression" -> None, "OutputPorts" -> {}, "InputPorts" -> {}, "DiagramOptions" -> {}};

$DiagramProperties = Join[
    Keys[Options[Diagram]],
    {
        "Properties", "HoldExpression", "ProductQ", "SumQ", "CompositionQ", "NetworkQ", "SubDiagrams",
        "Ports", "Arity", "FlattenOutputs", "FlattenInputs", "Flatten", "View", "Name", "ArraySymbol", "Shape", "Diagram"
    }
];


(* ::Subsection:: *)
(* Validation *)

diagramQ[HoldPattern[Diagram[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "OutputPorts" -> {___Port ? PortQ}, "InputPorts" -> {___Port ? PortQ}, "DiagramOptions" -> OptionsPattern[]}]]

diagramQ[___] := False


x_Diagram /; System`Private`HoldNotValidQ[x] && diagramQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

DiagramQ[x_Diagram] := System`Private`HoldValidQ[x]

DiagramQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

Diagram[SuperStar[d_], opts : OptionsPattern[]] :=
    With[{diagram = DiagramDual[#]}, Diagram["Expression" :> DiagramDual[#], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts]] & @ Diagram[d]

Diagram[OverBar[d_], opts : OptionsPattern[]] :=
    With[{diagram = DiagramFlip[#]}, Diagram["Expression" :> DiagramFlip[#], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts]] & @ Diagram[d]

Diagram[OverTilde[d_], opts : OptionsPattern[]] :=
    With[{diagram = DiagramReverse[#]}, Diagram["Expression" :> DiagramReverse[#], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts]] & @ Diagram[d]

Diagram[CircleTimes[ds___], opts : OptionsPattern[]] := With[{diagrams = Diagram /@ {ds}}, {diagram = DiagramProduct @@ diagrams},
    Diagram["Expression" :> DiagramProduct[##], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts] & @@ diagrams
]

Diagram[CirclePlus[ds___], opts : OptionsPattern[]] := With[{diagrams = Diagram /@ {ds}}, {diagram = DiagramSum @@ diagrams},
    Diagram["Expression" :> DiagramSum[##], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts] & @@ diagrams
]

Diagram[CircleDot[ds___], opts : OptionsPattern[]] := With[{diagrams = Diagram /@ {ds}}, {diagram = DiagramComposition @@ diagrams},
    Diagram["Expression" :> DiagramComposition[##], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts] & @@ diagrams
]

Diagram[ds : Except[OptionsPattern[], _List], opts : OptionsPattern[]] := With[{diagrams = Diagram /@ ds}, {diagram = DiagramNetwork @@ diagrams},
    Diagram["Expression" :> DiagramNetwork[##], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts] & @@ diagrams
]

Diagram[expr : Except[_Association | _Diagram | OptionsPattern[]],
    outputs : {} | Except[OptionsPattern[], _List] : {},
    inputs : {} | Except[OptionsPattern[], _List] : {},
    opts : OptionsPattern[]
] :=
    Diagram[
        FilterRules[{
            "Expression" :> expr,
            "OutputPorts" -> Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[outputs]],
            "InputPorts" -> Comap[Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[inputs]], "Dual"],
            opts
        },
            Join[Options[Diagram], $DiagramHiddenOptions, Options[DiagramGraphics]]
        ]
    ]

Diagram[expr_, output : Except[_List], args___] := Diagram[Unevaluated[expr], Unevaluated[{output}], args]

Diagram[expr_, outputs_List, input : Except[_List | OptionsPattern[]], opts___] := Diagram[Unevaluated[expr], Unevaluated[outputs], Unevaluated[{input}], opts]

Diagram[expr_, output : Except[_List], input : Except[_List], opts___] := Diagram[Unevaluated[expr], Unevaluated[{output}], Unevaluated[{input}], opts]

Diagram[opts : OptionsPattern[]] := Diagram[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[DiagramGraphics]], opts, Options[Diagram], $DiagramHiddenOptions},
        Join[Options[Diagram], $DiagramHiddenOptions]
    ]|>
]]


(* overwrite ports *)

Diagram[d_ ? DiagramQ,
    outputs : Inherited | {} | Except[OptionsPattern[], _List] : Inherited,
    inputs : Inherited | {} | Except[OptionsPattern[], _List] : Inherited,
    opts : OptionsPattern[]
] := Diagram[Unevaluated @@ d["HoldExpression"], Replace[outputs, Inherited :> d["OutputPorrts"]], Replace[inputs, Inherited :> d["InputPorrts"]], opts]


(* merge options *)

Diagram[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[Replace[Normal[Merge[{opts, d["Data"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* ::Subsubsection:: *)
(* Unary ops *)

DiagramDual[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramDual[d],
    "OutputPorts" -> Through[d["OutputPorts"]["Dual"]],
    "InputPorts" -> Through[d["InputPorts"]["Dual"]]
]

DiagramFlip[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramFlip[d],
    "Shape" -> GeometricTransformation[d["Shape"], ReflectionTransform[{0, 1}]],
    "OutputPorts" -> d["InputPorts"],
    "InputPorts" -> d["OutputPorts"]
]

DiagramReverse[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramReverse[d],
    "Shape" -> GeometricTransformation[d["Shape"], ReflectionTransform[{1, 0}]],
    "OutputPorts" -> Reverse[Through[d["OutputPorts"]["Reverse"]]],
    "InputPorts" -> Reverse[Through[d["InputPorts"]["Reverse"]]]
]


(* ::Subsubsection:: *)
(* Binary ops *)

(* sum *)

DiagramSum[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{subDiagrams = If[#["SumQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}},
    Diagram[
        opts,
        "Expression" :> DiagramSum[##] & @@ subDiagrams,
        "OutputPorts" -> Replace[Through[subDiagrams["OutputPorts"]], {{} -> Port["0"], ps_ :> PortSum @@ ps}, 1],
        "InputPorts" -> Replace[Through[subDiagrams["InputPorts"]], {{} -> Port[SuperStar["0"]], ps_ :> PortSum @@ ps}, 1]
    ]
]

(* horizontal product *)

DiagramProduct[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{subDiagrams = If[#["ProductQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}},
    Diagram[
        opts,
        "Expression" :> DiagramProduct[##] & @@ subDiagrams,
        "OutputPorts" -> Replace[Through[subDiagrams["OutputPorts"]], {{} -> Port["1"], ps_ :> PortProduct @@ ps}, 1],
        "InputPorts" -> Replace[Through[subDiagrams["InputPorts"]], {{} -> Port[SuperStar["1"]], ps_ :> PortProduct @@ ps}, 1]
    ]
]


(* vertical product *)

collectPorts[ports_List] := If[ports === {}, {},
    Fold[
        {
            DeleteDuplicates @ Join[#2[[1]], DeleteElements[#1[[1]], #2[[2]]]],
            DeleteDuplicates @ Join[#1[[2]], DeleteElements[#2[[2]], #1[[1]]]]
        } &,
        ports
    ]
]

DiagramComposition[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{
    subDiagrams = If[#["CompositionQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}
}, {
    ports = collectPorts[{Through[#["OutputPorts"]["Name"]], Through[#["InputPorts"]["Name"]]} & /@ Through[Reverse[subDiagrams]["Flatten"]]]
},
    Diagram[
        opts,
        "Expression" :> DiagramComposition[##] & @@ subDiagrams,
        "OutputPorts" -> (Port[Unevaluated @@ #] & /@ ports[[1]]),
        "InputPorts" -> (Port[Unevaluated @@ #]["Dual"] & /@ ports[[2]])
    ]
]


(* network of diagrams exposing free ports *)

DiagramNetwork[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{
    subDiagrams = If[#["NetworkQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}
},
    Diagram[
        opts,
        "Expression" :> DiagramNetwork[##] & @@ subDiagrams,

        Block[{graph = DiagramsGraph[subDiagrams], diagrams = Through[subDiagrams["Flatten"]], freeWires, edges},
            freeWires = Cases[Pick[VertexList[graph], VertexDegree[graph], 1], _HoldForm];
            edges = EdgeList[graph];
            {
                "OutputPorts" -> Cases[edges, DirectedEdge[{diagramId_, 1, portId_}, Alternatives @@ freeWires] :> diagrams[[diagramId]]["OutputPorts"][[portId]]],
                "InputPorts" -> Cases[edges, DirectedEdge[Alternatives @@ freeWires, {diagramId_, 2, portId_}] :> diagrams[[diagramId]]["InputPorts"][[portId]]["Dual"]]
            }
        ]
    ]
]


idDiagram[ports_List] := Function[ps, Diagram["1", Unevaluated[{ps}], Unevaluated[{ps}], "Shape" -> "Permutation", "ShowLabel" -> False], HoldAll] @@
    Flatten[HoldForm @@ Flatten @* HoldForm /@ ports]


(* compose vertically preserving grid structure *)

DiagramCompose[{x_Diagram, y_Diagram}, OptionsPattern[]] := Module[{a = x["FlattenInputs"], b = y["FlattenOutputs"], aPorts, bPorts, aOutputs, aInputs, bOutputs, bInputs},
	aPorts = Through[Through[a["InputPorts"]["Dual"]]["HoldExpression"]];
	bPorts = Through[b["OutputPorts"]["HoldExpression"]];
    If[ ContainsNone[aPorts, bPorts],
        Return[DiagramJoin[{a, b}]]
    ];
	With[{
		idInputs = Unevaluated @@ List @@@ Hold[Evaluate @ Flatten[HoldForm @@ DeleteElements[aPorts, 1 -> bPorts]]],
		idOutputs = Unevaluated @@ List @@@ Hold[Evaluate @ Flatten[HoldForm @@ DeleteElements[bPorts, 1 -> aPorts]]]
	},
		If[idInputs =!= {}, b = DiagramJoin[{idDiagram[idInputs], b}]["Flatten"]];
		If[idOutputs =!= {}, a = DiagramJoin[{idDiagram[idOutputs], a}]["Flatten"]];
	];
	aOutputs = a["OutputPorts"];
	aInputs = a["InputPorts"];
	bOutputs = b["OutputPorts"];
	bInputs = b["InputPorts"];
	Which[
		Through[Through[aInputs["Dual"]]["HoldExpression"]] === Through[bOutputs["HoldExpression"]],
		DiagramComposition[a, b],
		Sort[Through[Through[aInputs["Dual"]]["HoldExpression"]]] === Sort[Through[bOutputs["HoldExpression"]]],
		With[{
			piOutputs = Unevaluated @@ List @@@ Hold[Evaluate @ Flatten[HoldForm @@ Through[Through[aInputs["Dual"]]["Name"]]]],
			piInputs = Unevaluated @@ List @@@ Hold[Evaluate @ Flatten[HoldForm @@ Through[bOutputs["Name"]]]]
		},
			DiagramComposition[a, Diagram["\[Pi]", piOutputs, piInputs, "Shape" -> "Permutation", "ShowLabel" -> False], b]
		],
		True,
		$Failed
	]
]

DiagramCompose[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[DiagramCompose[{##}, opts] &, xs]


(* compose horizontally preserving height *)

DiagramJoin[{x_Diagram, y_Diagram}, OptionsPattern[]] := Module[{a = x["FlattenInputs"], b = y["FlattenOutputs"], aPorts, bPorts, ha, hb},
	aPorts = Through[Through[a["InputPorts"]["Dual"]]["HoldExpression"]];
	bPorts = Through[b["OutputPorts"]["HoldExpression"]];
    ha = DecompositionHeight[a];
    hb = DecompositionHeight[b];
    Which[
        ha > hb,
        DiagramProduct[a, DiagramComposition @@ Append[ConstantArray[idDiagram[bPorts], ha - hb], b]],
        ha < hb,
        DiagramProduct[DiagramComposition @@ Prepend[ConstantArray[idDiagram[aPorts], hb - ha], a], b],
        True,
        DiagramProduct[a, b]
    ]
]

DiagramJoin[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[DiagramJoin[{##}, opts] &, xs]


DiagramArrange[d_Diagram, opts : OptionsPattern[]] := DiagramDecompose[d] //. {
    ct_CircleTimes :> DiagramJoin[List @@ Flatten[ct], opts],
    cd_CircleDot :> DiagramCompose[List @@ Flatten[cd], opts]
}


DiagramDecompose[diagram_Diagram ? DiagramQ, productTop : _ ? BooleanQ : False] := 
	Replace[diagram["HoldExpression"], {
		HoldForm[DiagramProduct[ds___]] :> If[productTop, Identity, decompositionTranspose] @ (DiagramDecompose[#] & /@ CircleTimes[ds]),
		HoldForm[DiagramComposition[ds___]] :> If[productTop, decompositionTranspose, Identity] @ (DiagramDecompose[#, True] & /@ CircleDot[ds]),
		_ :> diagram
	}]


decompositionTranspose[CircleTimes[ds___CircleDot]] := CircleDot @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[DiagramJoin[Diagram /@ {##}], True] &, List @@@ {ds}]
decompositionTranspose[CircleDot[ds___CircleTimes]] := CircleTimes @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[DiagramCompose[Diagram /@ {##} // Echo]] & , List @@@ {ds}]
decompositionTranspose[ct_CircleTimes] := CircleDot[ct]
decompositionTranspose[cd_CircleDot] := CircleTimes[cd]
decompositionTranspose[d_] := d


DecompostionWidth[d_Diagram, opts___] := decompositionWidth[DiagramDecompose[d], opts]

decompositionWidth[expr_, opt_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[opt, {Automatic -> 1, x_ :> d["OptionValue"[x]]}],
    CircleTimes[ds___] :> Total[decompositionWidth /@ {ds}],
    CircleDot[ds___] :> Max[decompositionWidth /@ {ds}]}

]

DecompositionHeight[d_Diagram, opts___] := decompositionHeight[DiagramDecompose[d], opts]

decompositionHeight[expr_, opt_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[opt, {Automatic -> 1, x_ :> d["OptionValue"[x]]}],
    CircleTimes[ds___] :> Max[decompositionHeight /@ {ds}],
    CircleDot[ds___] :> Total[decompositionHeight /@ {ds}]
}]


decompositionArrange[diagram_Diagram, {width_, height_}, _, corner_ : {0, 0}] := With[{w = Replace[width, Automatic -> 1], h = Replace[height, Automatic -> 1]},
    Diagram[diagram,
        "Width" -> w,
        "Height" -> h,
        "Center" -> corner + {w / 2, h / 2}
    ]
]

decompositionArrange[decomp : CircleTimes[ds___], {width_, height_}, {dx_, dy_}, {xMin_, yMin_}] := Block[{widths, heights, positions},
    widths = decompositionWidth /@ {ds};
    If[width =!= Automatic, widths = width * widths / Total[widths]];
    heights = decompositionHeight /@ {ds};
    positions = Prepend[Accumulate[widths], 0] + Range[0, Length[widths]] dx;
    MapIndexed[With[{i = #2[[1]]}, decompositionArrange[#1, {widths[[i]], height}, {dx, dy}, {xMin + positions[[i]], yMin}]] &, decomp]
]

decompositionArrange[decomp : CircleDot[ds___], {width_, height_}, {dx_, dy_}, {xMin_, yMin_}] := Block[{widths, heights, positions},
    heights = decompositionHeight /@ {ds};
    If[height =!= Automatic, heights = height * heights / Total[heights]];
    widths = decompositionWidth /@ {ds};
    positions = Prepend[Accumulate[heights], 0] + Range[0, Length[heights]] dy;
    MapIndexed[With[{i = #2[[1]]}, decompositionArrange[#1, {width, heights[[i]]}, {dx, dy}, {xMin, yMin - positions[[i]]}]] &, decomp]
]

decompositionArrange[decomp_, gapSizes_] := decompositionArrange[decomp, {Automatic, Automatic}, gapSizes, {0, 0}]


decompositionOutputPositions[_Diagram, pos_] := {pos}
decompositionOutputPositions[CircleTimes[ds___], pos_] := Catenate[MapIndexed[decompositionOutputPositions[#1, Join[pos, #2]] &, {ds}]]
decompositionOutputPositions[CircleDot[d_, ___], pos_] := decompositionOutputPositions[d, Append[pos, 1]]
decompositionOutputPositions[decomp_] := decompositionOutputPositions[decomp, {}]

decompositionInputPositions[_Diagram, pos_] := {pos}
decompositionInputPositions[CircleTimes[ds___], pos_] := Catenate[MapIndexed[decompositionInputPositions[#1, Join[pos, #2]] &, {ds}]]
decompositionInputPositions[CircleDot[ds___, d_], pos_] := decompositionInputPositions[d, Append[pos, Length[{ds}] + 1]]
decompositionInputPositions[decomp_] := decompositionInputPositions[decomp, {}]


Options[DiagramGrid] = Join[{"HorizontalGapSize" -> 1, "VerticalGapSize" -> 1, "DiagramLayout" -> Automatic}, Options[Graphics]]
DiagramGrid[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] := Block[{
    decomp = DiagramDecompose[DiagramArrange[diagram]],
    width, height,
    outputPositions, inputPositions, positions, wires,
    vGapSize = OptionValue["VerticalGapSize"],
    hGapSize = OptionValue["HorizontalGapSize"]
},
	width = decompositionWidth[decomp];
	height = decompositionHeight[decomp];

    decomp = decompositionArrange[decomp, {hGapSize, vGapSize}];

    outputPositions = decompositionOutputPositions[decomp];
    inputPositions = decompositionInputPositions[decomp];
    positions = Position[decomp, _Diagram, All];

    decomp = decomp //
        MapAt[Diagram[#, "PortLabels" -> {Placed[Automatic, {- 2 / 3, 1}], None}, "PortArrows" -> None] &, Complement[positions, outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabels" -> {Automatic, None}, "PortArrows" -> {Automatic, None}] &, Complement[outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabels" -> {Placed[Automatic, {- 2 / 3, 1}], Automatic}, "PortArrows" -> {None, Automatic}] &, Complement[inputPositions, outputPositions]];

    wires = Cases[decomp,
        CircleDot[ds___] :> (
            Replace[{top_, bot_} :> MapThread[
                BSplineCurve @ {#1[[1]], #1[[1]] + vGapSize (#1[[2]] - #1[[1]]), #2[[1]] + vGapSize (#2[[2]] - #2[[1]]), #2[[1]]} &,
                {
                    Catenate[Through[Extract[bot, decompositionOutputPositions[bot]]["PortPoints"]][[All, 1]]],
                    Catenate[Through[Extract[top, decompositionInputPositions[top]]["PortPoints"]][[All, 2]]]
                }]
            ] /@ Partition[{ds}, 2, 1]
        ),
        All
    ];

	Show[
        Cases[decomp, d_Diagram :> d["Graphics"], All],
        Graphics[wires],
        opts,
        BaseStyle -> {
            GraphicsHighlightColor -> Automatic
        }
    ]
]


(* ::Subsection:: *)
(* Properties *)


(* dispatch properties *)

(d_Diagram ? DiagramQ)[prop_, opts___] := DiagramProp[d, prop, opts] 


(* property definitions *)

DiagramProp[_, "Properties"] := Sort[$DiagramProperties]

DiagramProp[HoldPattern[Diagram[data_]], "Data"] := data

DiagramProp[HoldPattern[Diagram[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

DiagramProp[d_, "HoldExpression"] := Extract[d["Data"], "Expression", HoldForm]

DiagramProp[d_, "ProductQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramProduct]]

DiagramProp[d_, "SumQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramSum]]

DiagramProp[d_, "CompositionQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramComposition]]

DiagramProp[d_, "NetworkQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramNetwork]]

DiagramProp[d_, "SubDiagrams"] := Replace[d["HoldExpression"], {
    HoldForm[(DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[ds___]] :> {ds},
    _ -> {}
}]

DiagramProp[d_, "Ports"] := Join[d["OutputPorts"], d["InputPorts"]]

DiagramProp[d_, "OutputArity"] := Length[d["OutputPorts"]]

DiagramProp[d_, "InputArity"] := Length[d["InputPorts"]]

DiagramProp[d_, "Arity"] := Length[d["Ports"]]

DiagramProp[d_, "FlattenOutputs"] := Diagram[d, "OutputPorts" -> Catenate[Through[d["OutputPorts"]["ProductList"]]]]

DiagramProp[d_, "FlattenInputs"] := Diagram[d, "InputPorts" -> Catenate[Through[d["InputPorts"]["ProductList"]]]]

DiagramProp[d_, "Flatten"] := d["FlattenOutputs"]["FlattenInputs"]

DiagramProp[d_, "View"] := With[{
    expr = Replace[d["HoldExpression"],
        HoldForm[(head : DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[ds___]] :>
            head @@@ HoldForm[Evaluate[Flatten[Defer @@ (Function[Null, If[DiagramQ[#], #["View"], Defer[#]], HoldFirst] /@ Unevaluated[{ds}])]]]
    ],
    outputs = Through[d["OutputPorts"]["Label"]],
    inputs = Through[Through[d["InputPorts"]["Dual"]]["Label"]]
},
    Function[Null, Defer[Diagram[#, outputs, inputs]] //. HoldForm[x_] :> x, HoldFirst] @@ expr
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

DiagramProp[diagram_, "ArraySymbol"] := DiagramDecompose[diagram] /. {
    d_Diagram :> Switch[d["Arity"], 1, VectorSymbol, 2, MatrixSymbol, _, ArraySymbol][d["HoldExpression"], Through[d["Ports"]["Name"]]],
    CircleTimes -> TensorProduct,
    CirclePlus -> Plus,
    CircleDot -> Dot,
    SuperStar -> Conjugate,
    OverBar -> Transpose,
    OverTilde -> ConjugateTranspose
}

DiagramProp[d_, "Diagram" | "Graphics", opts : OptionsPattern[]] := DiagramGraphics[d, opts]

DiagramProp[d_, "OptionValue"[opt_], opts : OptionsPattern[]] := OptionValue[{opts, d["DiagramOptions"], Options[DiagramGraphics]}, opt]

DiagramProp[d_, "Shape", opts : OptionsPattern[]] := Enclose @ With[{
    w = d["OptionValue"["Width"], opts],
    h = d["OptionValue"["Height"], opts],
    c = d["OptionValue"["Center"], opts],
    a = d["OptionValue"["Angle"], opts]
},
    GeometricTransformation[
        Replace[
            d["OptionValue"["Shape"], opts],
            {
                Automatic :> Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c, RoundingRadius -> {{Left, Top} -> .1 (w + h)}],
                "Triangle" :> Polygon[{{- w / 2, - h / 2}, {0, h / 2}, {w / 2, - h / 2}} + Threaded[c]],
                "UpsideDownTriangle" :> Polygon[{{- w / 2, h / 2}, {0, - h / 2}, {w / 2, h / 2}} + Threaded[c]],
                "Permutation" :> With[{points = d["PortPoints", opts]},
                    ConfirmAssert[Equal @@ Length /@ points];
                    MapIndexed[
                        With[{i = #2[[1]], j = #1},
                            BSplineCurve[{
                                points[[2, i, 1]], points[[2, i, 1]] + (points[[2, i, 1]] - points[[2, i, 2]]),
                                points[[1, j, 1]] + (points[[1, j, 1]] - points[[1, j, 2]]), points[[1, j, 1]]
                            }]
                            ] &,
                        PermutationList[Confirm @ FindPermutation[Through[d["InputPorts"]["Name"]], Through[d["OutputPorts"]["Name"]]], Length[points[[1]]]]
                    ]
                ]
            }
        ],
        RotationTransform[a, c]
    ]
]

DiagramProp[d_, "PortPoints", opts : OptionsPattern[]] := With[{
    w = d["OptionValue"["Width"], opts],
    h = d["OptionValue"["Height"], opts],
    c = d["OptionValue"["Center"], opts],
    a = d["OptionValue"["Angle"], opts]
},
    {
        RotationTransform[a, c] @ Map[
            {{(- 1 / 2 + #) w, h / 2}, {(- 1 / 2 + #) w, 3 / 4 h}} + Threaded[c] &,
            Range[0, 1, 1 / (d["OutputArity"] + 1)][[2 ;; -2]]
        ],
        RotationTransform[a, c] @ Map[
            {{(- 1 / 2 + #) w, - h / 2}, {(- 1 / 2 + #) w, - 3 / 4 h}} + Threaded[c] &,
            Range[0, 1, 1 / (d["InputArity"] + 1)][[2 ;; -2]]
        ]
    }
]


DiagramProp[_, prop_] := Missing[prop]


(* ::Subsection:: *)
(* Formatting *)

Options[DiagramGraphics] = Join[{
    "Shape" -> Automatic,
    "Center" -> {0, 0},
    "Width" -> 1,
    "Height" -> 1,
    "Angle" -> 0,
    "ShowLabel" -> Automatic,
    "PortArrows" -> Automatic,
    "PortLabels" -> Automatic
}, Options[Graphics]];

DiagramGraphics[diagram_ ? DiagramQ, opts : OptionsPattern[]] := Enclose @ With[{
    points = diagram["PortPoints", opts],
    arities = {diagram["OutputArity"], diagram["InputArity"]}
}, {
    portArrows = fillAutomatic[diagram["OptionValue"["PortArrows"], opts], arities, True],
    portLabels = fillAutomatic[diagram["OptionValue"["PortLabels"], opts], arities, Automatic]
}, Graphics[{
    EdgeForm[Black], FaceForm[Transparent], 
    Confirm @ diagram["Shape", opts],
    If[ MatchQ[diagram["OptionValue"["ShowLabel"], opts], None | False], Nothing,
        Text[
            ClickToCopy[Replace[diagram["HoldExpression"], expr : Except[HoldForm[_DiagramNetwork]] :> (expr //. d_Diagram ? DiagramQ :> RuleCondition[d["HoldExpression"]])], diagram["View"]],
            diagram["OptionValue"["Center"], opts]
        ]
    ],
    Arrowheads[Small],
    MapThread[{ports, ps, arrows, labels, angle} |->
        MapThread[{x, p, arrow, label} |-> {
            If[ MatchQ[arrow, None | False],
                Nothing,
                {If[MatchQ[arrow, True | Automatic], Nothing, arrow], Arrow[If[x["DualQ"], Reverse, Identity] @ p]}
            ],
            If[ MatchQ[label, None | False],
                Nothing,
                Replace[label, Placed[l_, pos_] | l_ :> Text[
                        ClickToCopy[l /. Automatic -> If[x["DualQ"], x["Dual"], x], x["View"]],
                        With[{v = p[[-1]] - p[[1]], s = PadLeft[Flatten[Replace[{pos}, {} -> {0, 2}]], 2, 0]}, p[[1]] + s[[2]] * v + s[[1]] * RotationTransform[angle][v]]
                    ]
                ]
            ]
        },
           {ports, ps, arrows, labels}
        ],
        {{diagram["OutputPorts"], diagram["InputPorts"]}, points, portArrows, portLabels, {- Pi / 2, Pi / 2}}
    ]
},
    FilterRules[{opts, diagram["DiagramOptions"]}, Options[Graphics]],
    ImageSize -> Tiny,
    FormatType -> StandardForm,
    BaseStyle -> {
        GraphicsHighlightColor -> Magenta
    }
]]

Diagram /: MakeBoxes[diagram : Diagram[_Association] ? DiagramQ, form_] := With[{boxes = ToBoxes[If[diagram["NetworkQ"], diagram["HoldExpression"], diagram["Diagram"]], form]},
    InterpretationBox[boxes, diagram]
]

DiagramDual /: MakeBoxes[DiagramDual[d_], form_] := With[{boxes = ToBoxes[SuperStar[d], form]}, InterpretationBox[boxes, DiagramDual[d]]]

DiagramFlip /: MakeBoxes[DiagramFlip[d_], form_] := With[{boxes = ToBoxes[OverBar[d], form]}, InterpretationBox[boxes, DiagramFlip[d]]]

DiagramReverse /: MakeBoxes[DiagramReverse[d_], form_] := With[{boxes = ToBoxes[Overscript[d, RawBoxes["\[LongLeftRightArrow]"]], form]}, InterpretationBox[boxes, DiagramReverse[d]]]

DiagramProduct /: MakeBoxes[DiagramProduct[ds___], form_] := With[{boxes = ToBoxes[CircleTimes[ds], form]}, InterpretationBox[boxes, DiagramProduct[ds]]]

DiagramSum /: MakeBoxes[DiagramSum[ds___], form_] := With[{boxes = ToBoxes[CirclePlus[ds], form]}, InterpretationBox[boxes, DiagramSum[ds]]]

DiagramComposition /: MakeBoxes[DiagramComposition[ds___], form_] := With[{boxes = ToBoxes[CircleDot[ds], form]}, InterpretationBox[boxes, DiagramComposition[ds]]]

DiagramNetwork /: MakeBoxes[DiagramNetwork[ds___], form_] := With[{boxes = ToBoxes[DiagramGrid[DiagramArrange @ DiagramCompose[{ds}]], form]}, InterpretationBox[boxes, DiagramNetwork[ds]]]


(* ::Subsection:: *)
(* Functions *)


Options[DiagramsPortGraph] = Options[Graph];
DiagramsPortGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := GraphSum[##, FilterRules[{opts}, Options[Graph]], VertexLabels -> Automatic] & @@
    (With[{vs = Through[#["HoldExpression"]]}, Graph[vs, UndirectedEdge @@@ Subsets[vs, {2}]]] & /@ Through[diagrams["Ports"]])


Options[DiagramsGraph] = Options[Graph];
DiagramsGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := Block[{
    ports = Thread[{Through[#["OutputPorts"]], Through[#["InputPorts"]]}] & @ Through[diagrams["Flatten"]],
    graph, embedding
},
    graph = Graph[
        Join[
            MapIndexed[Annotation[#2[[1]], "Diagram" -> #1] &, diagrams],
            Flatten[MapIndexed[Annotation[#2, "Port" -> #1] &, ports, {3}], 2]
        ],
        Flatten[
            MapIndexed[
                With[{diagram = #2[[1]], port = #2, wire = #1["Name"]},
                    Switch[port[[2]], 1, {DirectedEdge[diagram, port], DirectedEdge[port, wire]}, 2, {DirectedEdge[port, diagram], DirectedEdge[wire, port]}]
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


Options[DiagramsNetGraph] = Join[{"ShowPortLabels" -> True, "ShowWireLabels" -> True, "Scale" -> Automatic}, Options[DiagramGraphics], Options[Graph]];
DiagramsNetGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := DiagramsNetGraph[DiagramsGraph[diagrams], opts]
DiagramsNetGraph[graph_Graph, opts : OptionsPattern[]] := Block[{
	diagramVertices = VertexList[graph, _Integer], spiderVertices, vertices, edges,
	diagrams, outDegrees, inDegrees,
	embedding, orientations,
	scale = Replace[OptionValue["Scale"], Automatic -> .75], rad = .2,
	portLabelsQ = TrueQ[OptionValue["ShowPortLabels"]],
	wireLabelsQ = TrueQ[OptionValue["ShowWireLabels"]]
},
	diagrams = Through[(AnnotationValue[{graph, #}, "Diagram"] & /@ diagramVertices)["Flatten"]];
	If[Length[diagrams] == 0, Return[Graphics[FilterRules[Join[{opts}, Options[graph]], Options[Graphics]]]]];
	embedding = AssociationThread[VertexList[graph], GraphEmbedding[graph]];
	If[EdgeCount[graph] == 0 && VertexCount[graph] > 1, embedding = ScalingTransform[{1, .5} / Max[#2 - #1 & @@@ CoordinateBounds[embedding]], Mean[embedding]][embedding]];
	orientations = Map[
        Normalize[Lookup[#, 1] - Lookup[#, 2]] &,
		Values @ <|
            GroupBy[VertexList[graph, {__Integer}], First, Mean /@ GroupBy[#, #[[2]] &, Lookup[embedding, #] &] &],
            # -> <|1 -> {0, 1 / 2}, 2 -> {0, - 1 / 2}|> & /@ Range[Length[diagrams]]
        |>
	];
	{outDegrees, inDegrees} = AssociationThread[VertexList[graph] -> #] & /@ Through[{VertexOutDegree, VertexInDegree}[graph]];
	spiderVertices = VertexList[graph, _HoldForm];
	spiderVertices = Pick[spiderVertices, VertexDegree[graph, #] & /@ spiderVertices, d_ /; d > 2];
	spiderVertices = First[Reap[
		edges = Map[v |->
			Block[{in = VertexInComponent[graph, v, {1}], out = VertexOutComponent[graph, v, {1}], ports},
				ports = Join[out, in];
				If[ Length[in] + Length[out] == 2,
					DirectedEdge[ports[[1, 1]], ports[[2, 1]], {{ports[[1, 2]], If[ports[[1, 2]] == 1, outDegrees, inDegrees][ports[[1, 1]]], ports[[1, 3]]}, v, {ports[[2, 2]], If[ports[[2, 2]] == 1, outDegrees, inDegrees][ports[[2, 1]]], ports[[2, 3]]}}],
					Sow[v]; Splice[
						If[#[[2]] == 1, DirectedEdge[#[[1]], v, {#[[2]], Lookup[outDegrees, #[[1]]], #[[3]]}], DirectedEdge[#[[1]], v, {#[[2]], Lookup[inDegrees, #[[1]]], #[[3]]}]] & /@ ports
					]
				]
			],
			VertexList[graph, _HoldForm]
		]
	][[2]], {}];
	vertices = Join[diagramVertices, spiderVertices];
	Graph[
		vertices,
		edges,
		FilterRules[{opts}, Options[Graph]],
		VertexCoordinates -> Thread[vertices -> Lookup[embedding, vertices]],
		VertexShapeFunction -> Join[
			Thread[diagramVertices ->
				MapThread[{diagram, orientation} |-> With[{
						shape = diagram["Shape", opts],
						labels = Join[
							{Text[ClickToCopy[diagram["HoldExpression"], RawBoxes @ ToBoxes[diagram["View"], StandardForm]], {0, 0}]},
							If[ portLabelsQ,
								Join[
									MapIndexed[Text[ClickToCopy[#1["HoldExpression"], RawBoxes @ ToBoxes[#1["View"], StandardForm]], {- 1 / 2 + #2[[1]] / (diagram["OutputArity"] + 1) + .1, 1.25 / 2}] &, diagram["OutputPorts"]],
									MapIndexed[Text[ClickToCopy[#1["HoldExpression"], RawBoxes @ ToBoxes[#1["View"], StandardForm]], {- 1 / 2 + #2[[1]] / (diagram["InputArity"] + 1) + .1, - 1.25 / 2}] &, diagram["InputPorts"]]
								],
								{}
							]
						],
						transform = RotationTransform[{{0, 1}, orientation}] @* ScalingTransform[scale {1, 1}]
					},
						Function[{
							Black, FaceForm[None],
							GeometricTransformation[{shape}, TranslationTransform[#1] @* transform],
							SubsetMap[TranslationTransform[#1] @* transform, labels, {All, 2}]
						}]
					],
					{Through[diagrams["Flatten"]], orientations}
				]
			],
			Thread[spiderVertices -> With[{radius = rad scale}, Function[Circle[#1, radius]]]]
		],
		EdgeShapeFunction -> Replace[edges, {
				edge : DirectedEdge[v_Integer, w_Integer, {{i : 1 | 2, n_Integer, p_Integer}, x_, {j : 1 | 2, m_Integer, q_Integer}}] :> edge -> Block[{
					point1, point2, normal1, normal2, orientation1 = orientations[[v]], orientation2 = orientations[[w]], wireCoords = Lookup[embedding, x],
                    port1 = diagrams[[v]][Replace[i, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[p]],
                    port2 = diagrams[[w]][Replace[j, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[q]]
				},
					If[ i == 1,
						point1 = {- 1 / 2 + p / (n + 1),   1 / 2} scale;
						normal1 = {0, 1} scale
						,
						point1 = {- 1 / 2 + p / (n + 1), - 1 / 2} scale;
						normal1 = - {0, 1} scale
					];
					point1 = RotationTransform[{{0, 1}, orientation1}] @ point1;
					normal1 = RotationTransform[{{0, 1}, orientation1}] @ normal1;
					If[ j == 1,
						point2 = {- 1 / 2 + q / (m + 1),   1 / 2} scale;
						normal2 = {0, 1} scale
						,
						point2 = {- 1 / 2 + q / (m + 1), - 1 / 2} scale;
						normal2 = - {0, 1} scale
					];
					point2 = RotationTransform[{{0, 1}, orientation2}] @ point2;
					normal2 = RotationTransform[{{0, 1}, orientation2}] @ normal2;
					With[{a = VectorSymbol["p", 2], b = VectorSymbol["q", 2]},
						Function[Evaluate @ {
							Arrowheads[With[{size = 0.01}, {
                                If[port1["DualQ"], {- size, .3}, {size, .3}],
                                If[port2["DualQ"], {size, .7}, {- size, .7}]
                            }
                            ]],
							Arrow @ BSplineCurve[{a + point1, a + point1 + normal1, b + point2 + normal2, b + point2}],
							If[wireLabelsQ, Text[Style[ClickToCopy[x, x], Black], (a + point1 + normal1 + b + point2 + normal2) / 2 + .1 normal1], Nothing]
						}] /. {a :> #[[1]], b :> #[[-1]]}
					]
				],
				edge : DirectedEdge[v_Integer, _, {i : 1 | 2, n_Integer, p_Integer}] :> edge -> Block[{
					point, normal, orientation = orientations[[v]], portCoords = Lookup[embedding, Key[{v, i, p}]],
                    port = diagrams[[v]][Replace[i, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[p]]
				},
					If[ i == 1,
						point = {- 1 / 2 + p / (n + 1),   1 / 2} scale;
						normal = {0, 1} scale
						,
						point = {- 1 / 2 + p / (n + 1), - 1 / 2} scale;
						normal = - {0, 1} scale
					];
					point = RotationTransform[{{0, 1}, orientation}] @ point;
					normal = RotationTransform[{{0, 1}, orientation}] @ normal;

					With[{a = VectorSymbol["p", 2], b = VectorSymbol["q", 2]},
						Function[Evaluate @ {
							Arrowheads[With[{size = 0.01}, If[port["DualQ"], {{-size, .5}}, {{size, .5}}]]],
							Arrow @ BSplineCurve[{a + point, a + point + normal, b + scale Normalize[portCoords - b], b + rad scale Normalize[portCoords - b]}]
						}] /. {a :> #[[1]], b :> #[[-1]]}
					]
				],
				_ -> Nothing
			},
			1
		],
		VertexLabels -> _HoldForm -> Placed[Automatic, Center],
		BaseStyle -> {FormatType -> StandardForm}
	]
]


DiagramsFreePorts[diagrams : {___Diagram ? DiagramQ}] := Keys @ Select[CountsBy[Catenate[Through[Through[diagrams["Flatten"]]["Ports"]]], #["HoldExpression"] &], EqualTo[1]]


End[];

EndPackage[];