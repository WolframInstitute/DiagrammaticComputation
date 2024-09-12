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

DiagramColumn
DiagramRow
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
        "Ports", "Arity", "FlattenOutputs", "FlattenInputs", "Flatten", "View", "Name", "ArraySymbol", "Shape",
        "Diagram", "PortGraph", "Graph", "NetGraph", "Grid"
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
            Join[Options[Diagram], $DiagramHiddenOptions, Options[DiagramGraphics], Options[DiagramsNetGraph], Options[DiagramGrid]]
        ]
    ]

Diagram[expr_, output : Except[_List], args___] := Diagram[Unevaluated[expr], Unevaluated[{output}], args]

Diagram[expr_, outputs_List, input : Except[_List | OptionsPattern[]], opts___] := Diagram[Unevaluated[expr], Unevaluated[outputs], Unevaluated[{input}], opts]

Diagram[expr_, output : Except[_List], input : Except[_List], opts___] := Diagram[Unevaluated[expr], Unevaluated[{output}], Unevaluated[{input}], opts]

Diagram[opts : OptionsPattern[]] := Diagram[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Join[Options[DiagramGraphics], Options[DiagramsNetGraph], Options[DiagramGrid]]], opts, Options[Diagram], $DiagramHiddenOptions},
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
    "InputPorts" -> Through[d["InputPorts"]["Dual"]],
    "DiagramOptions" -> d["DiagramOptions"]
]

DiagramFlip[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramFlip[d],
    "OutputPorts" -> d["InputPorts"],
    "InputPorts" -> d["OutputPorts"],
    "Shape" -> GeometricTransformation[Diagram[d, "Angle" -> 0, "Reflect" -> False]["Shape"], ReflectionTransform[{0, 1}]],
    "Angle" -> d["OptionValue"["Angle"]],
    "Reflect" -> d["OptionValue"["Reflect"]]
]

DiagramReverse[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramReverse[d],
    "OutputPorts" -> Reverse[Through[d["OutputPorts"]["Reverse"]]],
    "InputPorts" -> Reverse[Through[d["InputPorts"]["Reverse"]]],
    "Shape" -> GeometricTransformation[Diagram[d, "Angle" -> 0, "Reflect" -> False]["Shape"], ReflectionTransform[{1, 0}]],
    "Angle" -> d["OptionValue"["Angle"]],
    "Reflect" -> d["OptionValue"["Reflect"]]
]


(* ::Subsubsection:: *)
(* Binary ops *)

(* sum *)


Options[DiagramSum] = Options[Diagram]
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
            Join[#2[[1]], DeleteElements[#1[[1]], #2[[2]]]],
            Join[#1[[2]], DeleteElements[#2[[2]], #1[[1]]]]
        } &,
        ports
    ]
]

Options[DiagramComposition] = Join[{"PortFunction" -> Function[#["Name"]]}, Options[Diagram]]
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

Options[DiagramNetwork] = Options[Diagram]
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


makePorts[xs_List] := Function[Null, Port[Unevaluated[##]], HoldAll] @@@ Flatten @* HoldForm /@ Replace[xs, SuperStar[HoldForm[x_]] :> HoldForm[SuperStar[x]], 1]

idDiagram[xs_List] := With[{ports = makePorts[xs]},
    Diagram["1", ports, ports, "Shape" -> "CrossWires", "ShowLabel" -> False]
]
    

piDiagram[outputs_List, inputs_List] := Diagram["\[Pi]", makePorts[outputs], makePorts[inputs], "Shape" -> "CrossWires", "ShowLabel" -> False]


(* compose vertically preserving grid structure *)

Options[DiagramColumn] = Join[{"PortFunction" -> Function[#["Name"]]}, Options[Diagram]]
DiagramColumn[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{
    a = x["FlattenInputs"], b = y["FlattenOutputs"],
    func = OptionValue["PortFunction"],
    aPorts, bPorts,
    outputs, inputs
},
	aPorts = func /@ Through[a["InputPorts"]["Dual"]];
	bPorts = func /@ b["OutputPorts"];
    If[ ContainsNone[aPorts, bPorts],
        If[ aPorts === {} && bPorts === {},
            Return[DiagramComposition[a, b, opts]],
            Return[DiagramRow[{a, b}, opts]]
        ]
    ];
    inputs = DeleteElements[aPorts, 1 -> bPorts];
    If[ inputs =!= {},
        With[{seqPos = SequencePosition[aPorts, bPorts, 1]},
            If[ seqPos === {},
                b = DiagramRow[{idDiagram[inputs], b}, opts]["Flatten"],
                b = DiagramRow[{If[#1 === {}, Nothing, idDiagram[#1]], b, If[#2 === {}, Nothing, idDiagram[#2]]} & @@ TakeDrop[inputs, seqPos[[1, 1]] - 1], opts]["Flatten"]
            ]
        ];
        bPorts = func /@ b["OutputPorts"];
    ];
    outputs = DeleteElements[bPorts, 1 -> aPorts];
    If[ outputs =!= {},
        With[{seqPos = SequencePosition[bPorts, aPorts, 1]},
            If[ seqPos === {},
                a = DiagramRow[{idDiagram[outputs], a}, opts]["Flatten"],
                a = DiagramRow[{If[#1 === {}, Nothing, idDiagram[#1]], a, If[#2 === {}, Nothing, idDiagram[#2]]} & @@ TakeDrop[outputs, seqPos[[1, 1]] - 1], opts]["Flatten"]
            ]
        ]
        
    ];
    aPorts = func /@ Through[a["InputPorts"]["Dual"]];
    bPorts = func /@ b["OutputPorts"];
	Which[
		aPorts === bPorts,
		DiagramComposition[a, b, opts],
		Sort[aPorts] === Sort[bPorts],
        DiagramComposition[a, piDiagram[aPorts, bPorts], b, opts],
		True,
		$Failed
	]
]

DiagramColumn[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[DiagramColumn[{##}, opts] &, xs]


(* compose horizontally preserving height *)

Options[DiagramRow] = Join[{"PortFunction" -> Function[#["Name"]]}, Options[Diagram]]
DiagramRow[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{a = x["FlattenInputs"], b = y["FlattenOutputs"], func = OptionValue["PortFunction"], aPorts, bPorts, ha, hb},
	aPorts = func /@ Through[a["InputPorts"]["Dual"]];
	bPorts = func /@ b["OutputPorts"];
    ha = DecompositionHeight[a];
    hb = DecompositionHeight[b];
    Which[
        ha > hb,
        DiagramProduct[a, DiagramComposition[##, opts]  & @@ Append[ConstantArray[idDiagram[bPorts], ha - hb], b], opts],
        ha < hb,
        DiagramProduct[DiagramComposition[##, opts] & @@ Prepend[ConstantArray[idDiagram[aPorts], hb - ha], a], b, opts],
        True,
        DiagramProduct[a, b, opts]
    ]
]

DiagramRow[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[DiagramRow[{##}, opts] &, xs]


DiagramArrange[diagram_Diagram, opts : OptionsPattern[]] := With[{grid = DiagramDecompose[diagram]},
    Fold[
        ReplaceAt[
            #1,
            {
                ct_CircleTimes :> DiagramRow[List @@ Flatten[ct], opts],
                cd_CircleDot :> DiagramColumn[List @@ Flatten[cd], opts],
                cp_CirclePlus :> DiagramSum[List @@ Flatten[cp], opts],
                net_List :> With[{g = DiagramsNetGraph[net, "BinarySpiders" -> All, "UnarySpiders" -> False, "RemoveCycles" -> True]},
                    DiagramColumn[AnnotationValue[{g, Reverse[TopologicalSort[g]]}, "Diagram"], "PortFunction" -> Function[#["HoldExpression"]]]
                ]
            },
            #2
        ] &,
        grid,
        ReverseSort[Position[grid, _CircleTimes | _CircleDot | _CirclePlus | _List]]
    ]
]


matchPorts[d_Diagram, {outputPorts_, inputPorts_}] := Diagram[d,
    If[outputPorts === Automatic, {}, "OutputPorts" -> MapThread[If[#2 === Automatic, #1, #2] &, {d["OutputPorts"], Join[outputPorts, Drop[d["OutputPorts"], Length[outputPorts]]]}]],
    If[inputPorts === Automatic, {}, "InputPorts" -> MapThread[If[#2 === Automatic, #1, #2] &, {d["InputPorts"], Join[inputPorts, Drop[d["InputPorts"], Length[inputPorts]]]}]]
]

matchPorts[cd_CircleDot, {outputPorts_, inputPorts_}] := Block[{grid = Reverse[List @@ cd]},
    grid = Reverse @ FoldPairList[
        If[ DeleteCases[#1, Automatic] === {},
            {#2, #1},
            With[{ds = Extract[#2, gridInputPositions[#2]]},
                {outputs = Through[Catenate[Through[ds["OutputPorts"]]]["Dual"]], inputs = Catenate[Through[ds["InputPorts"]]]},
                {leftoverPorts = DeleteElements[#1, inputs]}, 
                {
                    matchPorts[#2, {Automatic, DeleteElements[#1, leftoverPorts]}],
                    ReplacePart[outputs, Thread[Position[Through[outputs["HoldExpression"]], Except[Alternatives @@ Through[leftoverPorts["HoldExpression"]]], {1}, Heads -> False] -> Automatic]]
                }
            ]
        ] &,
        inputPorts,
        grid
    ];
    CircleDot @@ FoldPairList[
        If[ DeleteCases[#1, Automatic] === {},
            {#2, #1},
            With[{ds = Extract[#2, gridOutputPositions[#2]]},
                {outputs = Catenate[Through[ds["OutputPorts"]]], inputs = Through[Catenate[Through[ds["InputPorts"]]]["Dual"]]},
                {leftoverPorts = DeleteElements[#1, outputs]}, 
                {
                    matchPorts[#2, {DeleteElements[#1, leftoverPorts], Automatic}],
                    ReplacePart[inputs, Thread[Position[Through[inputs["HoldExpression"]], Except[Alternatives @@ Through[leftoverPorts["HoldExpression"]]], {1}, Heads -> False] -> Automatic]]
                }
            ]
        ] &,
        outputPorts,
        grid
    ]
]

matchPorts[cp_CirclePlus, {outputPorts_, inputPorts_}] := matchPorts[#, {outputPorts, inputPorts}] & /@ cp

matchPorts[CircleTimes[ds___], {outputPorts_, inputPorts_}] := CircleTimes @@ MapThread[
    matchPorts[#1, {#2, #3}] &,
    {
        {ds},
        With[{outputs = Catenate[Through[Extract[#, gridOutputPositions[#]]["OutputPorts"]]] & /@ {ds}},
            If[outputPorts === Automatic, outputs, TakeList[outputPorts, Length /@ outputs]]
        ],
        With[{inputs = Catenate[Through[Extract[#, gridInputPositions[#]]["InputPorts"]]] & /@ {ds}},
            If[inputPorts === Automatic, inputs, TakeList[inputPorts, Length /@ inputs]]
        ]
    }
]

DiagramDecompose[diagram_Diagram ? DiagramQ] := With[{ports = {#["OutputPorts"], #["InputPorts"]} & @ diagram["Flatten"]},
    Replace[diagram["HoldExpression"], {
        HoldForm[DiagramProduct[ds___]] :> DiagramDecompose /@ CircleTimes[ds],
        HoldForm[DiagramComposition[ds___]] :> DiagramDecompose /@ CircleDot[ds],
        HoldForm[DiagramSum[ds___]] :> DiagramDecompose /@ CirclePlus[ds],
        HoldForm[DiagramNetwork[ds___]] :> DiagramDecompose /@ {ds},
        _ :> diagram
    }]
]

gridTranspose[CircleTimes[ds___CircleDot]] := CircleDot @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[DiagramRow[Diagram /@ {##}]] &, List @@@ {ds}]
gridTranspose[CircleDot[ds___CircleTimes]] := CircleTimes @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[DiagramColumn[Diagram /@ {##}]] & , List @@@ {ds}]
gridTranspose[ct_CircleTimes] := CircleDot[ct]
gridTranspose[cd_CircleDot] := CircleTimes[cd]
gridTranspose[d_] := d


DecompostionWidth[d_Diagram, args___] := gridWidth[DiagramDecompose[d], args]

gridWidth[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic :> d["MaxArity"], _ :> d[prop]}],
    CircleTimes[ds___] :> Total[gridWidth[#, prop] & /@ {ds}],
    (CircleDot | CirclePlus)[ds___] :> Max[gridWidth[#, prop] & /@ {ds}]
}]

DecompositionHeight[d_Diagram, args___] := gridHeight[DiagramDecompose[d], args]

gridHeight[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic -> 1, _ :> d[prop]}],
    (CircleTimes | CirclePlus)[ds___] :> Max[gridHeight[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Total[gridHeight[#, prop] & /@ {ds}],
    CircleMinus[ds___] :> {ds}
}]


gridArrange[diagram_Diagram, {width_, height_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0] := Block[{
    arity = diagram["MaxArity"],
    alignment = diagram["OptionValue"[Alignment]],
    w, h, ratio, center
},
    w = 1 / 1.6 * (1 + dx) * (1 + arity);
    h = Replace[height, Automatic -> 1] * (1 + dy) - dy;
    ratio = If[arity == 0, 0, Floor[Replace[width, Automatic -> 1] / arity]];
    center = corner + RotationTransform[angle] @ {
        (1.6 w / 2) ratio +
            (1 + dx) * Switch[
                alignment,
                Left,
                1 - ratio,
                Right,
                width - ratio arity,
                Center,
                (1 - ratio + width - ratio arity) / 2
                ,
                _,
                0
            ],
        h / 2
    };
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{dx, - dy / 2}, {width * (1 + dx) + dx, height * (1 + dy) - dy / 2}})], "Item"];
    Diagram[diagram,
        "Width" -> Replace[diagram["OptionValue"["Width"]], Automatic :> If[MatchQ[diagram["OptionValue"["Shape"]], "Circle"] || arity <= 1, 1, ratio * w]],
        "Height" -> Replace[diagram["OptionValue"["Height"]], Automatic -> h],
        "Center" -> center
    ]
]

gridArrange[grid : CircleTimes[ds___], {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{widths, relativeWidths, newHeight, positions},
    widths = gridWidth /@ {ds};
    relativeWidths = If[width =!= Automatic, width * widths / Total[widths], widths];
    newHeight = Replace[height, Automatic :> Max[gridHeight /@ {ds}]];
    relativeWidths = FoldPairList[With[{x = Floor[#1 + #2]}, {x, #2 - x}] &, 0, relativeWidths];
    If[width =!= Automatic, relativeWidths[[-1]] = width - Total[Most[relativeWidths]]];
    positions = Prepend[Accumulate[relativeWidths * (1 + dx)], 0];
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{dx, 3 / 2 dy}, {Total[relativeWidths] * (1 + dx) + dx, - newHeight * (1 + dy) + 3 / 2 dy}})], "Row"];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, {relativeWidths[[i]], newHeight}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {positions[[i]], 0}, angle]] &, grid]
]

gridArrange[grid : CircleDot[ds___], {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{heights, newWidth, positions},
    heights = gridHeight /@ {ds};
    If[height =!= Automatic, heights = height * heights / Total[heights]];
    newWidth = Replace[width, Automatic :> Max[gridWidth /@ {ds}]];
    positions = Prepend[Accumulate[heights * (1 + dy)], 0];
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{dx, 3 / 2 dy}, {newWidth * (1 + dx) + dx, - Total[heights] * (1 + dy) + 3 / 2 dy}})], "Column"];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, {newWidth, heights[[i]]}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {0, - positions[[i]]}, angle]] &, grid]
]

gridArrange[grid_, gapSizes_, angle_] := gridArrange[grid, {Automatic, Automatic}, gapSizes, {0, 0}, angle]


gridOutputPositions[_Diagram, pos_] := {pos}
gridOutputPositions[CircleTimes[ds___], pos_] := Catenate[MapIndexed[gridOutputPositions[#1, Join[pos, #2]] &, {ds}]]
gridOutputPositions[CircleDot[d_, ___], pos_] := gridOutputPositions[d, Append[pos, 1]]
gridOutputPositions[grid_] := gridOutputPositions[grid, {}]

gridInputPositions[_Diagram, pos_] := {pos}
gridInputPositions[CircleTimes[ds___], pos_] := Catenate[MapIndexed[gridInputPositions[#1, Join[pos, #2]] &, {ds}]]
gridInputPositions[CircleDot[ds___, d_], pos_] := gridInputPositions[d, Append[pos, Length[{ds}] + 1]]
gridInputPositions[grid_] := gridInputPositions[grid, {}]


Options[DiagramGrid] = Join[{
    "HorizontalGapSize" -> 1,
    "VerticalGapSize" -> 1,
    "Rotate" -> 0,
    "WireArrows" -> False,
    Dividers -> None,
    Alignment -> Left
}, Options[DiagramGraphics], Options[Graphics]
]
DiagramGrid[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] := Block[{
    grid = DiagramDecompose[DiagramArrange[diagram]],
    width, height, items, rows, columns,
    outputPositions, inputPositions, positions, wires,
    vGapSize = OptionValue["VerticalGapSize"],
    hGapSize = OptionValue["HorizontalGapSize"],
    angle = Replace[OptionValue["Rotate"], {Left -> Pi / 2, Right -> - Pi / 2, Down -> Pi, Up -> 0}],
    diagramOptions = FilterRules[{opts}, Except[Options[Graphics], Options[DiagramGraphics]]]
},
	width = gridWidth[grid];
	height = gridHeight[grid];

    grid = grid /. d_Diagram :> Diagram[d, "Angle" -> d["OptionValue"["Angle"]] + angle, Alignment -> OptionValue[Alignment]];

    {items, rows, columns} = Lookup[Reap[grid = gridArrange[grid, {hGapSize, vGapSize}, angle], _, Rule][[2]], {"Item", "Row", "Column"}];

    outputPositions = gridOutputPositions[grid];
    inputPositions = gridInputPositions[grid];
    positions = Position[grid, _Diagram, All];

    grid = grid //
        MapAt[Diagram[#, "PortLabels" -> {Placed[Automatic, {- 2 / 3, 1}], None}, "PortArrows" -> None] &, Complement[positions, outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabels" -> {Automatic, None}, "PortArrows" -> {Automatic, None}] &, Complement[outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabels" -> {Placed[Automatic, {- 2 / 3, 1}], Automatic}, "PortArrows" -> {None, Automatic}] &, Complement[inputPositions, outputPositions]];
    
    wires = Cases[grid,
        CircleDot[ds___] :> (
            Replace[{top_, bot_} :> With[{outputs = Extract[bot, gridOutputPositions[bot]], inputs = Extract[top, gridInputPositions[top]]},
                MapThread[
                    {
                        Arrowheads[
                            With[{arrowSize = Replace[OptionValue["WireArrows"], {False | None -> 0, True -> Small}], from = If[#3, 1, -1], to = If[#4, 1, -1]},
                                If[ from == - to,
                                    {{from * arrowSize, .5}},
                                    {{from * arrowSize, .3}, {to * arrowSize, .7}}
                                ]
                            ]
                        ],
                        Arrow @ BSplineCurve @ {#1[[1]], #1[[1]] + vGapSize (#1[[2]] - #1[[1]]), #2[[1]] + vGapSize (#2[[2]] - #2[[1]]), #2[[1]]}} &,
                    {
                        Catenate[Through[outputs["PortArrows"]][[All, 1]]],
                        Catenate[Through[inputs["PortArrows"]][[All, 2]]],
                        Catenate[Through[#["InputPorts"]["DualQ"]] & /@ inputs],
                        Catenate[Through[#["OutputPorts"]["DualQ"]] & /@ outputs]
                    }]
                ]
            ] /@ Partition[{ds}, 2, 1]
        ),
        All
    ];

	Show[
        Cases[grid,
            d_Diagram :> DiagramGraphics[d, diagramOptions],
            All
        ],
        Graphics[{wires, FaceForm[None], EdgeForm[Directive[Thin, Black]],
            Switch[OptionValue[Dividers], All | Automatic, items, True, {rows, columns}, _, Nothing]
        }],
        FilterRules[{opts}, Options[Graphics]],
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

DiagramProp[d_, "MaxArity"] := Max[d["OutputArity"], d["InputArity"]]

DiagramProp[d_, "FlattenOutputs"] := Diagram[d, "OutputPorts" -> Catenate[Through[d["OutputPorts"]["ProductList"]]]]

DiagramProp[d_, "FlattenInputs"] := Diagram[d, "InputPorts" -> Catenate[Through[d["InputPorts"]["ProductList"]]]]

DiagramProp[d_, "Flatten"] := d["FlattenOutputs"]["FlattenInputs"]

DiagramProp[d_, "View"] := With[{
    holdExpr = Replace[d["HoldExpression"],
        HoldForm[(head : DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[ds___]] :>
            head @@@ HoldForm[Evaluate[Flatten[Defer @@ (Function[Null, If[DiagramQ[#], #, Defer[#]], HoldFirst] /@ Unevaluated[{ds}])]]]
    ],
    outputs = Replace[Through[d["OutputPorts"]["Label"]], {p : Except[HoldForm[_List | _Interpretation]]} :> p],
    inputs = Replace[Through[Through[d["InputPorts"]["Dual"]]["Label"]], {p : Except[HoldForm[_List | _Interpretation]]} :> p],
    opts = d["DiagramOptions"]
},
    Function[expr, If[opts === {}, Defer[Diagram[expr, outputs, inputs]], Defer[Diagram[expr, outputs, inputs, ##]] & @@ opts] //. HoldForm[x_] :> x, HoldFirst] @@ holdExpr
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

DiagramProp[diagram_, "Decompose"] := DiagramDecompose[diagram]

DiagramProp[diagram_, "ArraySymbol"] := DiagramDecompose[diagram] /. {
    d_Diagram :> Switch[d["Arity"], 1, VectorSymbol, 2, MatrixSymbol, _, ArraySymbol][d["HoldExpression"], Through[d["Ports"]["Name"]]],
    CircleTimes -> TensorProduct,
    CirclePlus -> Plus,
    CircleDot -> Dot,
    SuperStar -> Conjugate,
    OverBar -> Transpose,
    OverTilde -> ConjugateTranspose
}

DiagramProp[d_, "Diagram" | "Graphics", opts : OptionsPattern[]] := DiagramGraphics[d, opts, BaseStyle -> {GraphicsHighlightColor -> Automatic}]

DiagramProp[d_, "Normal"] := If[d["NetworkQ"],
    With[{g = DiagramsNetGraph[d["SubDiagrams"], "BinarySpiders" -> All, "UnarySpiders" -> False, "RemoveCycles" -> True]},
        DiagramComposition[##, "PortFunction" -> Function[#["HoldExpression"]]] & @@ AnnotationValue[{g, Reverse[TopologicalSort[g]]}, "Diagram"]
    ],
    d
]

DiagramProp[d_, "PortGraph", opts : OptionsPattern[]] := DiagramDecompose[d] /. net_List :> DiagramsPortGraph[net, opts]

DiagramProp[d_, "Graph", opts : OptionsPattern[]] := DiagramDecompose[d] /. net_List :> DiagramsGraph[net, opts]

DiagramProp[d_, "NetGraph", opts : OptionsPattern[]] := DiagramDecompose[d] /. net_List :> DiagramsNetGraph[net, FilterRules[{opts, d["DiagramOptions"]}, Options[DiagramsNetGraph]]]

DiagramProp[d_, "Arrange", opts : OptionsPattern[]] := DiagramArrange[d, opts]

DiagramProp[d_, "Grid", opts : OptionsPattern[]] := DiagramGrid[d["Arrange"], FilterRules[{opts, d["DiagramOptions"]}, Options[DiagramGrid]]]

DiagramProp[d_, "OptionValue"[opt_], opts : OptionsPattern[]] := OptionValue[{opts, d["DiagramOptions"], Options[DiagramGraphics], Options[DiagramGrid]}, opt]

DiagramProp[d_, "Shape", opts : OptionsPattern[]] := Enclose @ Block[{
    w = Replace[d["OptionValue"["Width"], opts], Automatic -> 1],
    h = Replace[d["OptionValue"["Height"], opts], Automatic -> 1],
    c = d["OptionValue"["Center"], opts],
    a = d["OptionValue"["Angle"], opts],
    r = d["OptionValue"["Reflect"], opts],
    transform, primitives
},
    transform = GeometricTransformation[#, RotationTransform[a, c] @* If[TrueQ[r], ReflectionTransform[{1, 0}, c], Identity]] &;
    primitives = Replace[
        d["OptionValue"["Shape"], opts],
        {
            Automatic :> transform @ Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c, RoundingRadius -> {{Left, Top} -> .1 (w + h)}],
            "Triangle" :> transform @ Polygon[{{- w / 2, - h / 2}, {0, h / 2}, {w / 2, - h / 2}} + Threaded[c]],
            "UpsideDownTriangle" :> transform @ Polygon[{{- w / 2, h / 2}, {0, - h / 2}, {w / 2, h / 2}} + Threaded[c]],
            "Circle" :> transform @ Circle[c, {w, h} / 2],
            "CrossWires" :> With[{
                points = d["PortArrows", opts],
                inputs = PositionIndex[Through[Through[d["InputPorts"]["Dual"]]["HoldExpression"]]],
                outputs = PositionIndex[Through[d["OutputPorts"]["HoldExpression"]]]
            },
                Map[
                    ps |-> Outer[
                        BSplineCurve[{#1[[1]], 2 * #1[[1]] - #1[[2]], 2 * #2[[1]] - #2[[2]], #2[[1]]}] &,
                        ps[[2]],
                        ps[[1]],
                        1
                    ],
                    Values @ Merge[KeyUnion[{inputs, outputs}, {} &], Apply[{points[[2, #1]], points[[1, #2]]} &]]
                ]
            ],
            "Wires" :> With[{
                points = d["PortArrows", opts],
                inputs = PositionIndex[Through[Through[d["InputPorts"]["Dual"]]["HoldExpression"]]],
                outputs = PositionIndex[Through[d["OutputPorts"]["HoldExpression"]]]
            },
                Map[
                    ps |-> BSplineCurve[{ps[[1, 1]], 2 * ps[[1, 1]] - ps[[1, 2]], If[Length[ps] == 2, Nothing, c], 2 * #[[1]] - #[[2]], #[[1]]}] & /@ Rest[ps],
                    Values @ Merge[KeyUnion[{inputs, outputs}, {} &], Apply[Join[points[[2, #1]], points[[1, #2]]] &]]
                ]
            ],
            "Wire" :> With[{
                ps = Catenate[d["PortArrows", opts]]
            },
                BSplineCurve[{ps[[1, 1]], 2 * ps[[1, 1]] - ps[[1, 2]], c, 2 * #[[1]] - #[[2]], #[[1]]}] & /@ Rest[ps]
            ]
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
    r = d["OptionValue"["Reflect"], opts],
    shape = d["OptionValue"["Shape"], opts]
}, {
    transform = RotationTransform[a, c] @* If[TrueQ[r], ReflectionTransform[{1, 0}, c], Identity]
},
    Switch[shape,
        "Circle",
        {
            transform @ Map[
                {1 / 2 {w Cos[#], h Sin[#]}, 3 / 4 {w Cos[#], h Sin[#]}} + Threaded[c] &,
                Range[Pi, 0, - Pi / (d["OutputArity"] + 1)][[2 ;; -2]]
            ],
            transform @ Map[
                {1 / 2 {w Cos[#], h Sin[#]}, 3 / 4 {w Cos[#], h Sin[#]}} + Threaded[c] &,
                Range[Pi, 2 Pi, Pi / (d["InputArity"] + 1)][[2 ;; -2]]
            ]
        },
        _,
        {
            transform @ Map[
                {{(- 1 / 2 + #) w, h / 2}, {(- 1 / 2 + #) w, 3 / 4 h}} + Threaded[c] &,
                Range[-.3, 1.3, 1.6 / (d["OutputArity"] + 1)][[2 ;; -2]]
            ],
            transform @ Map[
                {{(- 1 / 2 + #) w, - h / 2}, {(- 1 / 2 + #) w, - 3 / 4 h}} + Threaded[c] &,
                Range[-.3, 1.3, 1.6 / (d["InputArity"] + 1)][[2 ;; -2]]
            ]
        }
    ]
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
    "Reflect" -> False,
    "ShowLabel" -> Automatic,
    "PortArrows" -> Automatic,
    "PortLabels" -> Automatic,
    "Outline" -> None
}, Options[Graphics]];

DiagramGraphics[diagram_ ? DiagramQ, opts : OptionsPattern[]] := Enclose @ With[{
    points = diagram["PortArrows", opts],
    arities = {diagram["OutputArity"], diagram["InputArity"]}
}, {
    portArrows = fillAutomatic[diagram["OptionValue"["PortArrows"], opts], arities, True],
    portLabels = fillAutomatic[diagram["OptionValue"["PortLabels"], opts], arities, Automatic]
}, Graphics[{
    EdgeForm[Black], FaceForm[Transparent], 
    Confirm @ diagram["Shape", opts],
    Text[
        ClickToCopy[
            If[ MatchQ[diagram["OptionValue"["ShowLabel"], opts], None | False],
                "",
                Replace[diagram["HoldExpression"], expr_ :> (expr //. d_Diagram ? DiagramQ :> RuleCondition[d["HoldExpression"]])]
            ],
            diagram["View"]
        ],
        diagram["OptionValue"["Center"], opts]
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
    ports = Thread[{Through[#["OutputPorts"]], Through[#["InputPorts"]["Dual"]] & /@ #}] & @ Through[diagrams["Flatten"]],
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
            Diagram["Cap", {}, {port, port["Dual"]}, "Shape" -> "Wire", "ShowLabel" -> False]
        ]];
		net = EdgeDelete[net, {edge}];
		net = VertexAdd[net, {cap, cup}];
        net = EdgeAdd[net, {
			DirectedEdge[cup, cap, {{1, 2, 1}, {2, 2, 1}}],
			DirectedEdge[cup, edge[[2]], {{1, 2, 2}, {2, edge[[3, -1, 2]], edge[[3, -1, 3]]}}],
			DirectedEdge[edge[[1]], cap, {{1, edge[[3, 1, 2]], edge[[3, 1, 3]]}, {2, 2, 2}}]
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
}, Options[DiagramGraphics], Options[Graph]];
DiagramsNetGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] :=
    DiagramsNetGraph[DiagramsGraph[diagrams, FilterRules[{opts}, GraphLayout]], FilterRules[{opts}, Except[GraphLayout]]]
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
    binarySpiders = OptionValue["BinarySpiders"]
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
				ports = Join[out, in];
				If[ Length[ports] > 2 ||
                    Length[ports] == 1 && MatchQ[unarySpiders, True] ||
                    Length[ports] == 2 && (MatchQ[binarySpiders, All | Full] || MatchQ[binarySpiders, True] && SameQ @@ ports[[All, 2]])
                    ,
					Sow[{v,
                        Diagram[v,
                            Replace[v, HoldForm[x_] :> Port[Unevaluated @ Interpretation[x, #]]] & /@ out,
                            Replace[v, HoldForm[x_] :> Port[Unevaluated @ Interpretation[x, #]]] & /@ in,
                            If[Length[ports] == 2, {"Shape" -> "Wire", "ShowLabel" -> False}, {"Shape" -> "Circle", "ShowLabel" -> wireLabelsQ}]
                        ]
                    }];
                    Splice @ Catenate @ {
                        MapIndexed[DirectedEdge[#[[1]], v, {{1, Lookup[outDegrees, #[[1]]], #[[3]]}, {2, Length[in], #2[[1]]}}] &, in],
                        MapIndexed[DirectedEdge[v, #[[1]], {{1, Length[out], #2[[1]]}, {2, Lookup[inDegrees, #[[1]]], #[[3]]}}] &, out]
                    }
                    ,
					If[ Length[ports] < 2,
                        Nothing,
                        Block[{src, tgt, srcDegree, tgtDegree},
                            {src, tgt} = If[ ports[[1, 2]] == 1, {ports[[1]], ports[[2]]}, {ports[[2]], ports[[1]]}];
                            srcDegree = If[ src[[2]] == 1, outDegrees, inDegrees][src[[1]]];
                            tgtDegree = If[ tgt[[2]] == 1, outDegrees, inDegrees][tgt[[1]]];
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
                    "OutputPorts" -> (MapThread[Replace[#1, HoldForm[x_] :> Port[Unevaluated[Interpretation[x, #2]]]] &, {Through[#1["OutputPorts"]["Name"]], Thread[{#2[[1]], 1, Range[#1["OutputArity"]]}]}]),
                    "InputPorts" -> (MapThread[Replace[#1, HoldForm[x_] :> Port[Unevaluated[Interpretation[x, #2]]]["Dual"]] &, {Through[#1["InputPorts"]["Name"]], Thread[{#2[[1]], 2, Range[#1["InputArity"]]}]}])
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
						shape = First @ diagram["Graphics", "PortLabels" -> If[portLabelsQ, Automatic, None], "PortArrows" -> None, opts],
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
                    port1 = diagram1[Replace[i, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[p]];
                    port2 = diagram2[Replace[j, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[q]];
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
                        lindep = TrueQ[Quiet[Chop[Det[{normal1, normal2}]]] == 0]
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
                    port = diagram[Replace[i, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[p]];
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


End[];

EndPackage[];