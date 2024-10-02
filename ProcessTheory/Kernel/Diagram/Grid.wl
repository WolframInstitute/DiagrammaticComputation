BeginPackage["ProcessTheory`Diagram`Grid`", {"ProcessTheory`Diagram`", "ProcessTheory`Utilities`"}];

ColumnDiagram
RowDiagram
DiagramGrid

DiagramArrange
DiagramDecompose

Begin["ProcessTheory`Diagram`Grid`Private`"];


(* compose vertically preserving grid structure *)

Options[ColumnDiagram] = Join[{"PortFunction" -> Function[#["Name"]]}, Options[Diagram]]
ColumnDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{
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
            Return[RowDiagram[{a, b}, opts]]
        ]
    ];
    inputs = DeleteElements[aPorts, 1 -> bPorts];
    If[ inputs =!= {},
        With[{seqPos = SequencePosition[aPorts, bPorts, 1]},
            If[ seqPos === {},
                b = RowDiagram[{idDiagram[inputs], b}, opts]["Flatten"],
                b = RowDiagram[{If[#1 === {}, Nothing, idDiagram[#1]], b, If[#2 === {}, Nothing, idDiagram[#2]]} & @@ TakeDrop[inputs, seqPos[[1, 1]] - 1], opts]["Flatten"]
            ]
        ];
        bPorts = func /@ b["OutputPorts"];
    ];
    outputs = DeleteElements[bPorts, 1 -> aPorts];
    If[ outputs =!= {},
        With[{seqPos = SequencePosition[bPorts, aPorts, 1]},
            If[ seqPos === {},
                a = RowDiagram[{idDiagram[outputs], a}, opts]["Flatten"],
                a = RowDiagram[{If[#1 === {}, Nothing, idDiagram[#1]], a, If[#2 === {}, Nothing, idDiagram[#2]]} & @@ TakeDrop[outputs, seqPos[[1, 1]] - 1], opts]["Flatten"]
            ]
        ]
        
    ];
    aPorts = func /@ Through[a["InputPorts"]["Dual"]];
    bPorts = func /@ b["OutputPorts"];
	Which[
		aPorts === bPorts,
		DiagramComposition[a, b, opts],
		aPorts === Reverse[bPorts] && a["WireQ"],
        DiagramComposition[DiagramReverse[a], b, opts],
        aPorts === Reverse[bPorts] && b["WireQ"],
        DiagramComposition[a, DiagramReverse[b], opts],
		Sort[aPorts] === Sort[bPorts],
        DiagramComposition[a, piDiagram[aPorts, bPorts], b, opts],
		True,
		$Failed
	]
]

ColumnDiagram[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[ColumnDiagram[{##}, opts] &, xs]


(* compose horizontally preserving height *)

Options[RowDiagram] = Join[{"PortFunction" -> Function[#["Name"]]}, Options[Diagram]]
RowDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{a = x["FlattenInputs"], b = y["FlattenOutputs"], func = OptionValue["PortFunction"], aPorts, bPorts, ha, hb},
	aPorts = func /@ Through[a["InputPorts"]["Dual"]];
	bPorts = func /@ b["OutputPorts"];
    ha = decompositionHeight[a];
    hb = decompositionHeight[b];
    Which[
        ha > hb,
        DiagramProduct[a, DiagramComposition[##, opts]  & @@ Append[ConstantArray[idDiagram[bPorts], ha - hb], b], opts],
        ha < hb,
        DiagramProduct[DiagramComposition[##, opts] & @@ Prepend[ConstantArray[idDiagram[aPorts], hb - ha], a], b, opts],
        True,
        DiagramProduct[a, b, opts]
    ]
]

RowDiagram[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[RowDiagram[{##}, opts] &, xs]


Options[DiagramArrange] = {"Network" -> True}

DiagramArrange[diagram_Diagram, opts : OptionsPattern[]] := Replace[diagram["HoldExpression"], {
    HoldForm[DiagramProduct[ds___]] :> RowDiagram[DiagramArrange[#, opts] & /@ {ds}, FilterRules[diagram["DiagramOptions"], Options[RowDiagram]]],
    HoldForm[DiagramComposition[ds___]] :> ColumnDiagram[DiagramArrange[#, opts] & /@ {ds}, FilterRules[diagram["DiagramOptions"], Options[ColumnDiagram]]],
    HoldForm[DiagramSum[ds___]] :> DiagramSum[DiagramArrange[#, opts] & /@ {ds}, FilterRules[diagram["DiagramOptions"], Options[DiagramSum]]],
    HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]],
        With[{g = DiagramsNetGraph[DiagramArrange[#, opts] & /@ {ds}, FilterRules[diagram["DiagramOptions"], Options[DiagramsNetGraph]], "BinarySpiders" -> True, "UnarySpiders" -> False, "RemoveCycles" -> True]},
            ColumnDiagram[AnnotationValue[{g, Reverse[TopologicalSort[g]]}, "Diagram"], "PortFunction" -> Function[#["HoldExpression"]], FilterRules[diagram["DiagramOptions"], Options[ColumnDiagram]]]
        ],
        DiagramNetwork[##, diagram["DiagramOptions"]] & @@ (DiagramArrange[#, opts] & /@ {ds})
    ],
    _ :> diagram
}]


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


Options[DiagramDecompose] = {"Network" -> True}

DiagramDecompose[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] :=
    Replace[diagram["HoldExpression"], {
        HoldForm[DiagramProduct[ds___]] :> (DiagramDecompose[#, opts] & /@ CircleTimes[ds]),
        HoldForm[DiagramComposition[ds___]] :> (DiagramDecompose[#, opts] & /@ CircleDot[ds]),
        HoldForm[DiagramSum[ds___]] :> (DiagramDecompose[#, opts] & /@ CirclePlus[ds]),
        HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]], DiagramDecompose[#, opts] & /@ {ds}, diagram],
        _ :> diagram
    }]

gridTranspose[CircleTimes[ds___CircleDot]] := CircleDot @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[RowDiagram[Diagram /@ {##}]] &, List @@@ {ds}]
gridTranspose[CircleDot[ds___CircleTimes]] := CircleTimes @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[ColumnDiagram[Diagram /@ {##}]] & , List @@@ {ds}]
gridTranspose[ct_CircleTimes] := CircleDot[ct]
gridTranspose[cd_CircleDot] := CircleTimes[cd]
gridTranspose[d_] := d


decompostionWidth[d_Diagram, args___] := gridWidth[DiagramDecompose[d], args]

gridWidth[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic :> d["MaxArity"], _ :> d[prop]}],
    CircleTimes[ds___] :> Total[gridWidth[#, prop] & /@ {ds}],
    (CircleDot | CirclePlus)[ds___] :> Max[gridWidth[#, prop] & /@ {ds}]
}]

decompositionHeight[d_Diagram, args___] := gridHeight[DiagramDecompose[d], args]

gridHeight[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic -> 1, _ :> Replace[d[prop], Except[_Integer] -> 1]}],
    (CircleTimes | CirclePlus)[ds___] :> Max[gridHeight[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Total[gridHeight[#, prop] & /@ {ds}]
}]


gridArrange[diagram_Diagram, {autoWidth_, autoHeight_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0] := Block[{
    arity = diagram["MaxArity"],
    alignment = diagram["OptionValue"[Alignment]],
    width = Replace[autoWidth, Automatic -> arity],
    w, h, ratio, center
},
    w = 1 / 1.6 * (1 + dx) * (1 + arity);
    h = Replace[autoHeight, Automatic -> 1];
    ratio = If[arity == 0, 0, Floor[width / arity]];
    center = corner + RotationTransform[angle] @ {
        (1.6 w / 2) ratio +
            (1 + dx) * (Replace[
                alignment, {
                Automatic | Left :> 1 - ratio,
                Right :> width - ratio * arity,
                Center :> (1 - ratio + width - ratio * arity) / 2,
                x_ ? NumericQ :> x,
                Scaled[x_ ? NumericQ] :> (1 - x) * (1 - ratio) + x * (width - ratio arity),
                _ -> 0
            }] - 1 / 2),
        - h / 2
    };
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{0, 0}, {width * (1 + dx), - h}})], "Item"];
    Diagram[diagram,
        "Width" -> Replace[diagram["OptionValue"["Width"]], Automatic :> If[MatchQ[diagram["OptionValue"["Shape"]], "Circle"] || arity <= 1, 1, ratio * w]],
        "Height" -> Replace[diagram["OptionValue"["Height"]], Automatic -> h - dy],
        "Center" -> center
    ]
]

gridArrange[grid : CircleTimes[ds___], {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{widths, relativeWidths, newHeight, positions},
    widths = gridWidth /@ {ds};
    relativeWidths = If[width =!= Automatic, width * widths / Total[widths], widths];
    newHeight = Replace[height, Automatic :> gridHeight[grid, "OptionValue"["Height"]] + dy * gridHeight[grid]];
    relativeWidths = FoldPairList[With[{x = Floor[#1 + #2]}, {x, #2 - x}] &, 0, relativeWidths];
    If[width =!= Automatic, relativeWidths[[-1]] = width - Total[Most[relativeWidths]]];
    positions = Prepend[Accumulate[relativeWidths * (1 + dx)], 0];
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{0, 0}, {Total[relativeWidths] * (1 + dx), - newHeight}})], "Row"];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, {relativeWidths[[i]], newHeight}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {positions[[i]], 0}, angle]] &, grid]
]

gridArrange[grid : CircleDot[ds___], {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{heights, newWidth, positions},
    heights = gridHeight[#, "OptionValue"["Height"]] + gridHeight[#] * dy & /@ {ds};
    If[height =!= Automatic, heights = height * heights / Total[heights]];
    newWidth = Replace[width, Automatic :> gridWidth[grid]];
    positions = Prepend[Accumulate[heights], 0];
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{0, 0}, {newWidth * (1 + dx), - Total[heights]}})], "Column"];
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
    Alignment -> Automatic
}, Options[DiagramArrange], Options[DiagramDecompose], Options[DiagramGraphics], Options[Graphics]
]
DiagramGrid[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] := Block[{
    grid = DiagramDecompose[DiagramArrange[diagram, FilterRules[{opts}, Options[DiagramArrange]]], FilterRules[{opts}, Options[DiagramDecompose]]],
    width, height, items, rows, columns,
    outputPositions, inputPositions, positions, wires,
    vGapSize = OptionValue["VerticalGapSize"],
    hGapSize = OptionValue["HorizontalGapSize"],
    angle = Replace[OptionValue["Rotate"], {Left -> Pi / 2, Right -> - Pi / 2, Down -> Pi, Up -> 0}],
    diagramOptions = FilterRules[{opts}, Except[Options[Graphics], Options[DiagramGraphics]]]
},
	width = gridWidth[grid];
	height = gridHeight[grid];

    grid = grid /. d_Diagram :> Diagram[d, "Angle" -> d["OptionValue"["Angle"]] + angle, Alignment -> Replace[d["OptionValue"[Alignment]], Automatic -> OptionValue[Alignment]]];

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


End[];

EndPackage[];

