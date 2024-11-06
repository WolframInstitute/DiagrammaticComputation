BeginPackage["ProcessTheory`Diagram`Grid`", {"ProcessTheory`Diagram`", "ProcessTheory`Utilities`"}];

ColumnDiagram
RowDiagram
DiagramGrid

DiagramArrange
DiagramDecompose

matchPorts

Begin["ProcessTheory`Diagram`Grid`Private`"];


(* compose vertically preserving grid structure *)

Options[ColumnDiagram] = Join[{"PortFunction" -> Function[#["Name"]], "Direction" -> Down}, Options[Diagram]]

ColumnDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{
    func = OptionValue["PortFunction"],
    a, b,
    aPorts, bPorts,
    outputs, inputs
},
    a = x["FlattenOutputs"];
    b = y["FlattenInputs"];
	aPorts = func /@ a["OutputPorts"];
	bPorts = func /@ Through[b["InputPorts"]["Dual"]];
    If[ ContainsNone[aPorts, bPorts],
        If[ aPorts === {} && bPorts === {},
            Return[DiagramComposition[b, a, FilterRules[{opts}, Options[DiagramComposition]]]],
            Return[RowDiagram[{b, a}, FilterRules[{opts}, Options[RowDiagram]]]]
        ]
    ];
    inputs = DeleteElements[bPorts, 1 -> aPorts];
    If[ inputs =!= {},
        With[{seqPos = SequencePosition[bPorts, aPorts, 1]},
            If[ seqPos === {}
                ,
                a = RowDiagram[{idDiagram[inputs], a}, FilterRules[{opts}, Options[RowDiagram]]]["Flatten"]
                ,
                a = RowDiagram[{If[#1 === {}, Nothing, idDiagram[#1]], a, If[#2 === {}, Nothing, idDiagram[#2]]} & @@ TakeDrop[inputs, seqPos[[1, 1]] - 1], FilterRules[{opts}, Options[RowDiagram]]]["Flatten"]
            ]
        ];
        aPorts = func /@ a["OutputPorts"];
    ];
    outputs = DeleteElements[aPorts, 1 -> bPorts];
    If[ outputs =!= {},
        With[{seqPos = SequencePosition[aPorts, bPorts, 1]},
            If[ seqPos === {},
                b = RowDiagram[{idDiagram[outputs], b}, FilterRules[{opts}, Options[RowDiagram]]]["Flatten"],
                b = RowDiagram[{If[#1 === {}, Nothing, idDiagram[#1]], b, If[#2 === {}, Nothing, idDiagram[#2]]} & @@ TakeDrop[outputs, seqPos[[1, 1]] - 1], FilterRules[{opts}, Options[RowDiagram]]]["Flatten"]
            ]
        ]
    ];
	aPorts = func /@ a["OutputPorts"];
	bPorts = func /@ Through[b["InputPorts"]["Dual"]];
	Which[
		aPorts === bPorts,
		DiagramComposition[b, a, FilterRules[{opts}, Options[DiagramComposition]]],
		aPorts === Reverse[bPorts] && a["WireQ"],
        DiagramComposition[b, DiagramReverse[a], FilterRules[{opts}, Options[DiagramComposition]]],
        aPorts === Reverse[bPorts] && b["WireQ"],
        DiagramComposition[DiagramReverse[b], a, FilterRules[{opts}, Options[DiagramComposition]]],
		Sort[aPorts] === Sort[bPorts],
        DiagramComposition[b, piDiagram[aPorts, bPorts], a, FilterRules[{opts}, Options[DiagramComposition]]],
		True,
		$Failed
	]
]

ColumnDiagram[xs : {___Diagram}, opts : OptionsPattern[]] := If[
    MatchQ[OptionValue["Direction"], Up | Top]
    ,
    Fold[ColumnDiagram[{#2, #1}, opts] &, Reverse[xs]]
    ,
    Fold[ColumnDiagram[{##}, opts] &, xs]
]
    


(* compose horizontally preserving height *)

Options[RowDiagram] = Options[ColumnDiagram]
RowDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{a = x["FlattenInputs"], b = y["FlattenOutputs"], func = OptionValue["PortFunction"], aPorts, bPorts, ha, hb},
	aPorts = func /@ Through[a["InputPorts"]["Dual"]];
	bPorts = func /@ b["OutputPorts"];
    ha = decompositionHeight[a];
    hb = decompositionHeight[b];
    Which[
        ha > hb,
        DiagramProduct[a, DiagramComposition[##, FilterRules[{opts}, Options[DiagramComposition]]]  & @@ Append[ConstantArray[idDiagram[bPorts], ha - hb], b], FilterRules[{opts}, Options[DiagramProduct]]],
        ha < hb,
        DiagramProduct[DiagramComposition[##, FilterRules[{opts}, Options[DiagramComposition]]] & @@ Prepend[ConstantArray[idDiagram[aPorts], hb - ha], a], b, FilterRules[{opts}, Options[DiagramProduct]]],
        True,
        DiagramProduct[a, b, FilterRules[{opts}, Options[DiagramProduct]]]
    ]
]

RowDiagram[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[RowDiagram[{##}, opts] &, xs]


Options[DiagramArrange] = Join[{"Network" -> True}, Options[ColumnDiagram]]

DiagramArrange[diagram_Diagram, opts : OptionsPattern[]] := Replace[diagram["HoldExpression"], {
    HoldForm[DiagramProduct[ds___]] :> RowDiagram[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[RowDiagram]]],
    HoldForm[DiagramComposition[ds___]] :> ColumnDiagram[DiagramArrange[#, opts] & /@ Reverse[{ds}], FilterRules[{opts, diagram["DiagramOptions"]}, Options[ColumnDiagram]]],
    HoldForm[DiagramSum[ds___]] :> DiagramSum[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramSum]]],
    HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]],
        With[{g = DiagramsNetGraph[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramsNetGraph]], "BinarySpiders" -> True, "UnarySpiders" -> False, "RemoveCycles" -> True]},
            ColumnDiagram[AnnotationValue[{g, TopologicalSort[g]}, "Diagram"], "PortFunction" -> Function[#["HoldExpression"]], FilterRules[{opts, diagram["DiagramOptions"]}, Options[ColumnDiagram]]]
        ],
        DiagramNetwork[##, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramNetwork]]] & @@ (DiagramArrange[#, opts] & /@ {ds})
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

matchPorts[HoldPattern[Conjugate[d_]], {outputPorts_, inputPorts_}] := Conjugate[matchPorts[d, {outputPorts, inputPorts}]]

matchPorts[HoldPattern[Transpose[d_, perm_ : None]], {outputPorts_, inputPorts_}] :=
    Transpose[matchPorts[d, TakeDrop[Permute[Join[outputPorts, inputPorts], InversePermutation[Replace[perm, None -> {1, 2}]]], Length[outputPorts]]], perm]


Options[DiagramDecompose] = {"Network" -> True}

DiagramDecompose[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] :=
    Replace[diagram["HoldExpression"], {
        HoldForm[DiagramProduct[ds___]] :> (DiagramDecompose[#, opts] & /@ CircleTimes[ds]),
        HoldForm[DiagramComposition[ds___]] :> (DiagramDecompose[#, opts] & /@ CircleDot[ds]),
        HoldForm[DiagramSum[ds___]] :> (DiagramDecompose[#, opts] & /@ CirclePlus[ds]),
        HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]], DiagramDecompose[#, opts] & /@ {ds}, diagram],
        HoldForm[DiagramFlip[d_]] :> Transpose[DiagramDecompose[d, opts], FindPermutation[Join[#1 + Range[#2], Range[#1]]] & @@ {diagram["OutputArity"], diagram["InputArity"]}],
        HoldForm[DiagramReverse[d_]] :> Transpose[DiagramDecompose[d, opts], FindPermutation[Join[Reverse[Range[#1]], Reverse[#1 + Range[#2]]]] & @@ {diagram["OutputArity"], diagram["InputArity"]}],
        HoldForm[DiagramDual[d_]] :> Conjugate[DiagramDecompose[d, opts]],
        _ :> diagram
    }]

gridTranspose[CircleTimes[ds___CircleDot]] := CircleDot @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[RowDiagram[Diagram /@ {##}]] &, List @@@ {ds}]
gridTranspose[CircleDot[ds___CircleTimes]] := CircleTimes @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[ColumnDiagram[Diagram /@ Reverse[{##}]]] & , List @@@ {ds}]
gridTranspose[ct_CircleTimes] := CircleDot[ct]
gridTranspose[cd_CircleDot] := CircleTimes[cd]
gridTranspose[d_] := d


decompostionWidth[d_Diagram, args___] := gridWidth[DiagramDecompose[d], args]

gridWidth[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic :> d["MaxArity"], _ :> d[prop]}],
    CircleTimes[ds___] :> Total[gridWidth[#, prop] & /@ {ds}],
    (CircleDot | CirclePlus)[ds___] :> Max[gridWidth[#, prop] & /@ {ds}],
    (Transpose | Conjugate)[d_, ___] :> gridWidth[d, prop],
    _ -> 1
}]

decompositionHeight[d_Diagram, args___] := gridHeight[DiagramDecompose[d], args]

gridHeight[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic -> 1, _ :> Replace[d[prop], Except[_Integer] -> 1]}],
    (CircleTimes | CirclePlus)[ds___] :> Max[gridHeight[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Total[gridHeight[#, prop] & /@ {ds}],
    (Transpose | Conjugate)[d_, ___] :> gridHeight[d, prop],
    _ -> 1
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
        h / 2
    };
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{0, 0}, {width * (1 + dx), h}})], "Item"];
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
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{0, 0}, {Total[relativeWidths] * (1 + dx), newHeight}})], "Row"];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, {relativeWidths[[i]], newHeight}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {positions[[i]], 0}, angle]] &, grid]
]

gridArrange[grid : CircleDot[ds___], {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{heights, newWidth, positions},
    heights = gridHeight[#, "OptionValue"["Height"]] + gridHeight[#] * dy & /@ {ds};
    If[height =!= Automatic, heights = height * heights / Total[heights]];
    newWidth = Replace[width, Automatic :> gridWidth[grid]];
    positions = Prepend[Accumulate[heights], 0];
    Sow[RotationTransform[angle, corner][Rectangle @@ (Threaded[corner] + {{0, 0}, {newWidth * (1 + dx), Total[heights]}})], "Column"];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, {newWidth, heights[[i]]}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {0, positions[[i]]}, angle]] &, grid]
]

gridArrange[HoldPattern[Conjugate[d_]], args___] := gridArrange[d /. diagram_Diagram :> DiagramDual[diagram], args]

gridArrange[HoldPattern[Transpose[d_, perm___]], args___] := (Sow[{perm}, "Transpose"]; gridArrange[d, args])

gridArrange[grid_, gapSizes_, angle_] := gridArrange[grid, {Automatic, Automatic}, gapSizes, {0, 0}, angle]


gridOutputPositions[_Diagram, pos_] := {pos}
gridOutputPositions[CircleTimes[ds___], pos_] := Catenate[MapIndexed[gridOutputPositions[#1, Join[pos, #2]] &, {ds}]]
gridOutputPositions[CircleDot[d_, ___], pos_] := gridOutputPositions[d, Append[pos, 1]]
gridOutputPositions[(Transpose | Conjugate)[d_, ___], pos_] := gridOutputPositions[d, pos]
gridOutputPositions[grid_] := gridOutputPositions[grid, {}]

gridInputPositions[_Diagram, pos_] := {pos}
gridInputPositions[CircleTimes[ds___], pos_] := Catenate[MapIndexed[gridInputPositions[#1, Join[pos, #2]] &, {ds}]]
gridInputPositions[CircleDot[ds___, d_], pos_] := gridInputPositions[d, Append[pos, Length[{ds}] + 1]]
gridInputPositions[(Transpose | Conjugate)[d_, ___], pos_] := gridInputPositions[d, pos]
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
    width, height, items, rows, columns, transposes,
    outputPositions, inputPositions, positions, wires,
    vGapSize = OptionValue["VerticalGapSize"],
    hGapSize = OptionValue["HorizontalGapSize"],
    angle = Replace[OptionValue["Rotate"], {Left -> - Pi / 2, Right -> Pi / 2, Bottom | True | Up -> Pi, None | False | Top | Down -> 0}],
    diagramOptions = FilterRules[{opts}, Except[Options[Graphics], Options[DiagramGraphics]]]
},
	width = gridWidth[grid];
	height = gridHeight[grid];

    grid = grid /. d_Diagram :> Diagram[d, "Angle" -> d["OptionValue"["Angle"]] + angle, Alignment -> Replace[d["OptionValue"[Alignment]], Automatic -> OptionValue[Alignment]]];

    (* TODO: do something with transpositions *)
    {items, rows, columns, transposes} = Lookup[Reap[grid = gridArrange[grid, {hGapSize, vGapSize}, angle], _, Rule][[2]], {"Item", "Row", "Column", "Transpose"}];

    outputPositions = gridOutputPositions[grid];
    inputPositions = gridInputPositions[grid];
    positions = Position[grid, _Diagram, All];

    grid = grid //
        MapAt[Diagram[#, "PortLabels" -> {None, Placed[Automatic, {- 2 / 3, 1}]}, "PortArrows" -> None] &, Complement[positions, outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabels" -> {None, Automatic}, "PortArrows" -> {None, Automatic}] &, Complement[outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabels" -> {Automatic, Placed[Automatic, {- 2 / 3, 1}]}, "PortArrows" -> {Automatic, None}] &, Complement[inputPositions, outputPositions]];
    
    wires = Cases[grid,
        CircleDot[ds___] :> (
            Replace[{bot_, top_} :> With[{outputs = Extract[top, gridOutputPositions[top]], inputs = Extract[bot, gridInputPositions[bot]]},
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
                        Arrow @ BSplineCurve @ {#1[[1]], #1[[1]] + vGapSize (#1[[2]] - #1[[1]]), #2[[1]] + vGapSize (#2[[2]] - #2[[1]]), #2[[1]]}
                    } &,
                    {
                        Catenate[Through[outputs["PortArrows"]][[All, 2]]],
                        Catenate[Through[inputs["PortArrows"]][[All, 1]]],
                        Catenate[Through[#["InputPorts"]["DualQ"]] & /@ inputs],
                        Catenate[Through[#["OutputPorts"]["DualQ"]] & /@ outputs]
                    }
                ]
            ]] /@ Partition[{ds}, 2, 1]
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

