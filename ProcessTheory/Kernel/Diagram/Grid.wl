BeginPackage["ProcessTheory`Diagram`Grid`", {"ProcessTheory`Diagram`", "ProcessTheory`Utilities`"}];

ColumnDiagram
RowDiagram
DiagramGrid

DiagramArrange
DiagramDecompose

DiagramMatchPorts

Begin["ProcessTheory`Diagram`Grid`Private`"];


(* compose vertically preserving grid structure *)

Options[ColumnDiagram] = Join[{"PortFunction" -> Function[#["Name"]], "PortOrderingFunction" -> Automatic, "Direction" -> Top}, Options[Diagram]]

ColumnDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{
    func = OptionValue["PortFunction"],
    a, b,
    aPorts, bPorts,
    rowOpts = FilterRules[{opts}, Options[RowDiagram]]
},
    a = x["FlattenOutputs"];
    b = y["FlattenInputs"];
	aPorts = func /@ a["OutputPorts"];
	bPorts = func /@ Through[b["InputPorts"]["Dual"]];
    If[ ContainsNone[aPorts, bPorts],
        If[ aPorts === {} && bPorts === {},
            Return[DiagramComposition[b, a, FilterRules[{opts}, Options[DiagramComposition]]]],
            Return[RowDiagram[{b, a}, rowOpts]]
        ]
    ];
    Replace[SequenceAlignment[Reverse[aPorts], Reverse[bPorts], Method -> "Local"], {
        {left : {l_, {}} | {{}, l_} : {}, {__}, right : {r_, {}} | {{}, r_} : {}} /; ! ({l} =!= {} && {r} =!= {} && IntersectingQ[l, r]) :> (
            Which[
                MatchQ[left, {_, {}}],
                b = RowDiagram[{b, idDiagram[l]}, rowOpts]["Flatten"],
                MatchQ[left, {{}, _}],
                a = RowDiagram[{a, idDiagram[l]}, rowOpts]["Flatten"]
            ];
            Which[
                MatchQ[right, {_, {}}],
                b = RowDiagram[{idDiagram[r], b}, rowOpts]["Flatten"],
                MatchQ[right, {{}, _}],
                a = RowDiagram[{idDiagram[r], a}, rowOpts]["Flatten"]
            ]
        ),
        _ :> With[{ins = DeleteElements[bPorts, 1 -> aPorts], outs = DeleteElements[aPorts, 1 -> bPorts]},
            If[ins =!= {}, a = RowDiagram[{idDiagram[ins], a}, rowOpts]["Flatten"]];
            If[outs =!= {}, b = RowDiagram[{idDiagram[outs], b}, rowOpts]["Flatten"]]
        ]
    }
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
        DiagramProduct[a, DiagramComposition[##, FilterRules[{opts}, Options[DiagramComposition]]] & @@ Append[ConstantArray[idDiagram[bPorts], ha - hb], b], FilterRules[{opts}, Options[DiagramProduct]]],
        ha < hb,
        DiagramProduct[DiagramComposition[##, FilterRules[{opts}, Options[DiagramComposition]]] & @@ Prepend[ConstantArray[idDiagram[aPorts], hb - ha], a], b, FilterRules[{opts}, Options[DiagramProduct]]],
        True,
        DiagramProduct[a, b, FilterRules[{opts}, Options[DiagramProduct]]]
    ]
]

RowDiagram[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[RowDiagram[{##}, opts] &, xs]


Options[DiagramArrange] = Join[{"Network" -> True, "Arrange" -> True}, Options[ColumnDiagram]]

DiagramArrange[diagram_Diagram, opts : OptionsPattern[]] := If[TrueQ[diagram["OptionValue"["Arrange"], opts]] && TrueQ[diagram["OptionValue"["Decompose"], opts]],
Replace[diagram["HoldExpression"], {
    HoldForm[DiagramProduct[ds___]] :> RowDiagram[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[RowDiagram]]],
    HoldForm[DiagramComposition[ds___]] :> ColumnDiagram[DiagramArrange[#, opts] & /@ Reverse[{ds}], FilterRules[{opts, diagram["DiagramOptions"]}, Options[ColumnDiagram]]],
    HoldForm[DiagramSum[ds___]] :> DiagramSum[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramSum]]],
    HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]],
        With[{g = DiagramsNetGraph[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramsNetGraph]], "BinarySpiders" -> True, "UnarySpiders" -> False, "RemoveCycles" -> True]},
            ColumnDiagram[AnnotationValue[{g, TopologicalSort[g]}, "Diagram"], "PortFunction" -> Function[#["HoldExpression"]], FilterRules[{opts, diagram["DiagramOptions"]}, Options[ColumnDiagram]]]
        ],
        Diagram[diagram, "Expression" :> DiagramNetwork[##] & @@ (DiagramArrange[#, opts] & /@ {ds})]
    ],
    _ :> diagram
}]
    ,
    diagram
]


matchPorts[d_Diagram, {outputPorts_, inputPorts_}] := Diagram[d,
    If[outputPorts === Automatic, {}, "OutputPorts" -> MapThread[If[#2 === Automatic, #1, #2] &, {d["OutputPorts"], Join[Port /@ outputPorts, Drop[d["OutputPorts"], Length[outputPorts]]]}]],
    If[inputPorts === Automatic, {}, "InputPorts" -> MapThread[If[#2 === Automatic, #1, #2] &, {d["InputPorts"], Join[Port /@ inputPorts, Drop[d["InputPorts"], Length[inputPorts]]]}]]
]

matchPorts[cd_CircleDot, {outputPorts_, inputPorts_}] :=
    MapAt[matchPorts[#, {Automatic, inputPorts}] &, {-1}] @ MapAt[matchPorts[#, {outputPorts, Automatic}] &, {1}] @ cd

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

matchPorts[HoldPattern[SuperStar[d_]], {outputPorts_, inputPorts_}] := SuperStar[matchPorts[d, {outputPorts, inputPorts}]]

matchPorts[HoldPattern[Transpose[d_, perm_ : None]], {outputPorts_, inputPorts_}] :=
    Transpose[matchPorts[d, TakeDrop[Permute[Join[outputPorts, inputPorts], InversePermutation[Replace[perm, None -> {1, 2}]]], Length[outputPorts]]], perm]

DiagramMatchPorts[d_Diagram, ports_] := Diagram[matchPorts[DiagramDecompose[d], ports], d["DiagramOptions"]]


Options[DiagramDecompose] = {"Network" -> True, "Unary" -> False, "Decompose" -> True, "Ports" -> False}

DiagramDecompose[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] := If[TrueQ[diagram["OptionValue"["Decompose"], opts]],
    Replace[diagram["HoldExpression"], {
        HoldForm[DiagramProduct[ds___]] :> (DiagramDecompose[#, opts] & /@ CircleTimes[ds]),
        HoldForm[DiagramComposition[ds___]] :> (DiagramDecompose[#, opts] & /@ CircleDot[ds]),
        HoldForm[DiagramSum[ds___]] :> (DiagramDecompose[#, opts] & /@ CirclePlus[ds]),
        HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]], DiagramDecompose[#, opts] & /@ {ds}, diagram],
        If[ TrueQ[OptionValue["Unary"]],
            Splice @ {
                HoldForm[DiagramFlip[d_]] :> Transpose[DiagramDecompose[d, opts], FindPermutation[Join[#1 + Range[#2], Range[#1]]] & @@ {diagram["OutputArity"], diagram["InputArity"]}],
                HoldForm[DiagramReverse[d_]] :> Transpose[DiagramDecompose[d, opts], FindPermutation[Join[Reverse[Range[#1]], Reverse[#1 + Range[#2]]]] & @@ {diagram["OutputArity"], diagram["InputArity"]}],
                HoldForm[DiagramDual[d_]] :> SuperStar[DiagramDecompose[d, opts]]
            },
            Nothing
        ],
        _ :> diagram
    }]
    ,
    diagram["Flatten"]
] // If[TrueQ[OptionValue["Ports"]], # -> {Through[diagram["InputPorts"]["Dual"]], diagram["OutputPorts"]} &, Identity]

gridTranspose[CircleTimes[ds___CircleDot]] := CircleDot @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[RowDiagram[Diagram /@ {##}]] &, List @@@ {ds}]
gridTranspose[CircleDot[ds___CircleTimes]] := CircleTimes @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[ColumnDiagram[Diagram /@ Reverse[{##}]]] & , List @@@ {ds}]
gridTranspose[ct_CircleTimes] := CircleDot[ct]
gridTranspose[cd_CircleDot] := CircleTimes[cd]
gridTranspose[d_] := d


decompostionWidth[d_Diagram, args___] := gridWidth[DiagramDecompose[d], args]

gridWidth[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic :> Max[d["MaxArity"], 1], _ :> d[prop]}],
    CircleTimes[ds___] :> Total[gridWidth[#, prop] & /@ {ds}],
    (CircleDot | CirclePlus)[ds___] :> Max[gridWidth[#, prop] & /@ {ds}],
    (Transpose | SuperStar)[d_, ___] :> gridWidth[d, prop],
    (x_ -> _) :> gridWidth[x, prop],
    _ -> 1
}]

decompositionHeight[d_Diagram, args___] := gridHeight[DiagramDecompose[d], args]

gridHeight[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic -> 1, _ :> Replace[d[prop], Except[_Integer] -> 1]}],
    (CircleTimes | CirclePlus)[ds___] :> Max[gridHeight[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Total[gridHeight[#, prop] & /@ {ds}],
    (Transpose | SuperStar)[d_, ___] :> gridHeight[d, prop],
    (x_ -> _) :> gridHeight[x, prop],
    _ -> 1
}]


circuitArrange[diagram_Diagram, {_, autoHeight_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0] := Block[{
    arity = diagram["MaxArity"], inputOrder, outputOrder, min, max,
    alignment = diagram["OptionValue"[Alignment]],
    spacing = diagram["OptionValue"["Spacing"]],
    orderingFunction = Replace[diagram["OptionValue"["PortOrderingFunction"]],
        Automatic -> Function[Replace[#["HoldName"], {HoldForm[Interpretation[_, (Subscript | Superscript)[_, order_][_]]] :> order, _ -> 0}]]
    ],
    width, w, h, center
},
    {inputOrder, outputOrder} = Replace[{orderingFunction /@ Through[diagram["InputPorts"]["Dual"]], orderingFunction /@ diagram["OutputPorts"]}, Except[_ ? NumericQ] -> 0, {2}];
    {min, max} = MinMax @ Join[inputOrder, outputOrder];
    width = max - min + 1;
    w = Replace[diagram["OptionValue"["Width"]], Automatic :> If[MatchQ[diagram["OptionValue"["Shape"]], "Circle"] || arity <= 1, 1, width]];
    h = Replace[diagram["OptionValue"["Height"]], Automatic :> Max[Replace[autoHeight, Automatic -> 1] - dy, 1]];
    center = RotationTransform[-angle] @ corner;
    center = RotationTransform[angle] @ {min - 1 + w / 2, center[[2]] + h / 2};
    Sow[RotationTransform[angle, center][Rectangle @@ (Threaded[center] + {{- w / 2, - h / 2 - dy / 2}, {w / 2, h / 2 + dy / 2}})], "Item"];
    Diagram[diagram,
        "Width" -> w, "Height" -> h,
        "PortArrows" -> {
            Placed[Automatic, Threaded[center] + {{#, h / 2}, {#, h / 2 + 1 / 4}}] & /@ (- w / 2 + inputOrder - min + 1 / 2),
            Placed[Automatic, Threaded[center] + {{#, - h / 2}, {#, - h / 2 - 1 / 4}}] & /@ (- w / 2 + outputOrder - min + 1 / 2) 
        },
        "Center" -> center
    ]
]

gridArrange[diagram_Diagram -> _, pos_, {autoWidth_, autoHeight_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0] := Block[{
    arity = diagram["MaxArity"],
    alignment = diagram["OptionValue"[Alignment]],
    spacing = diagram["OptionValue"["Spacing"]],
    width, w, h, ratio, center
},
    If[alignment === "Circuit", Return[circuitArrange[diagram, {autoWidth, autoHeight}, {dx, dy}, corner, angle]]];
    width = Replace[autoWidth, Automatic :> Max[arity, 1]];
    w = 1 / spacing * (1 + dx) * (1 + arity);
    h = Replace[autoHeight, Automatic -> 1];
    ratio = If[arity == 0, 0, Floor[width / arity]];
    center = corner + RotationTransform[angle] @ {
        (spacing * w / 2) ratio +
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
        "Height" -> Replace[diagram["OptionValue"["Height"]], Automatic :> Max[h - dy, 1]],
        "Center" -> center
    ]
]

gridArrange[grid : CircleTimes[ds___] -> {inputs_, outputs_}, pos_, {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{widths, relativeWidths, newHeight, positions},
    widths = gridWidth /@ {ds};
    relativeWidths = If[width =!= Automatic, width * widths / Total[widths], widths];
    newHeight = Replace[height, Automatic :> gridHeight[grid, "OptionValue"["Height"]] + dy * gridHeight[grid]];
    relativeWidths = FoldPairList[With[{x = Floor[#1 + #2]}, {x, #2 - x}] &, 0, relativeWidths];
    If[width =!= Automatic, relativeWidths[[-1]] = width - Total[Most[relativeWidths]]];
    positions = Prepend[Accumulate[relativeWidths * (1 + dx)], 0];
    With[{w = Total[relativeWidths] * (1 + dx), h = newHeight},
        Sow[pos -> Diagram["", inputs, outputs, "Angle" -> angle, "Center" -> corner + {w, h} / 2, "Width" -> w, "Height" -> h]["Flatten"], "Row"]
    ];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, Append[pos, i], {relativeWidths[[i]], newHeight}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {positions[[i]], 0}, angle]] &, grid]
]

gridArrange[grid : CircleDot[ds___] -> {inputs_, outputs_}, pos_, {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{heights, newWidth, positions},
    heights = gridHeight[#, "OptionValue"["Height"]] + gridHeight[#] * dy & /@ {ds};
    If[height =!= Automatic, heights = height * heights / Total[heights]];
    newWidth = Replace[width, Automatic :> gridWidth[grid]];
    positions = Prepend[Accumulate[heights], 0];
    With[{w = newWidth * (1 + dx), h = Total[heights]},
        Sow[pos -> Diagram["", inputs, outputs, "Angle" -> angle, "Center" -> corner + {w, h} / 2, "Width" -> w, "Height" -> h]["Flatten"], "Column"]
    ];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, Append[pos, i], {newWidth, heights[[i]]}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {0, positions[[i]]}, angle]] &, grid]
]

gridArrange[HoldPattern[SuperStar[d_]] -> _, args___] := gridArrange[d /. diagram_Diagram :> DiagramDual[diagram], args]

gridArrange[HoldPattern[Transpose[d_, perm___]] -> _, args___] := (Sow[{perm}, "Transpose"]; gridArrange[d, args])

gridArrange[{ds___} -> _, args___] := gridArrange[DiagramNetwork[ds], args]

gridArrange[grid_, gapSizes_, angle_] := gridArrange[grid, {}, {Automatic, Automatic}, gapSizes, {0, 0}, angle]


gridOutputPositions[_Diagram | _List, pos_] := {pos}
gridOutputPositions[CircleTimes[ds___], pos_] := Catenate[MapIndexed[gridOutputPositions[#1, Join[pos, #2]] &, {ds}]]
gridOutputPositions[CircleDot[d_, ___], pos_] := gridOutputPositions[d, Append[pos, 1]]
gridOutputPositions[(Transpose | SuperStar)[d_, ___], pos_] := gridOutputPositions[d, pos]
gridOutputPositions[grid_ -> _, pos_] := gridOutputPositions[grid, Append[pos, 1]]
gridOutputPositions[grid_] := gridOutputPositions[grid, {}]

gridInputPositions[_Diagram | _List, pos_] := {pos}
gridInputPositions[CircleTimes[ds___], pos_] := Catenate[MapIndexed[gridInputPositions[#1, Join[pos, #2]] &, {ds}]]
gridInputPositions[CircleDot[ds___, d_], pos_] := gridInputPositions[d, Append[pos, Length[{ds}] + 1]]
gridInputPositions[(Transpose | SuperStar)[d_, ___], pos_] := gridInputPositions[d, pos]
gridInputPositions[grid_ -> _, pos_] := gridInputPositions[grid, Append[pos, 1]]
gridInputPositions[grid_] := gridInputPositions[grid, {}]


Options[DiagramGrid] = Join[{
    "HorizontalGapSize" -> 1,
    "VerticalGapSize" -> 1,
    "Rotate" -> 0,
    "Wires" -> True,
    "WireArrows" -> False,
    "Frames" -> False,
    Spacings -> 1.6,
    Dividers -> None,
    Alignment -> Automatic
}, Options[DiagramArrange], Options[DiagramDecompose], Options[DiagramGraphics], Options[Graphics]
]
DiagramGrid[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] := Block[{
    grid,
    width, height, items, rows, columns, transposes,
    outputPositions, inputPositions, positions,
    vGapSize = OptionValue["VerticalGapSize"],
    hGapSize = OptionValue["HorizontalGapSize"],
    angle = Replace[OptionValue["Rotate"], {Left -> - Pi / 2, Right -> Pi / 2, Bottom | True | Up -> Pi, None | False | Top | Down -> 0}],
    spacing = OptionValue[Spacings],
    outputs, inputs,
    wiresQ = TrueQ[OptionValue["Wires"]],
    diagramOptions = FilterRules[{opts}, Except[Options[Graphics], Options[DiagramGraphics]]],
    portFunction = OptionValue["PortFunction"],
    wireArrows = OptionValue["WireArrows"]
},
    grid = DiagramDecompose[DiagramArrange[diagram, FilterRules[{opts}, Options[DiagramArrange]]], "Ports" -> True, FilterRules[{opts}, Options[DiagramDecompose]]];
    width = gridWidth[grid];
    height = gridHeight[grid];

    grid = grid /. d_Diagram :> Diagram[d,
        "Angle" -> d["OptionValue"["Angle"]] + angle,
        "Spacing" -> spacing,
        Alignment -> Replace[d["OptionValue"[Alignment]], Automatic -> OptionValue[Alignment]],
        "PortOrderingFunction" -> Replace[d["OptionValue"["PortOrderingFunction"]], Automatic -> OptionValue["PortOrderingFunction"]]
    ];

    (* TODO: do something with transpositions *)
    {items, rows, columns, transposes} = Lookup[Reap[grid = gridArrange[grid, {hGapSize, vGapSize}, angle], _, Rule][[2]], {"Item", "Row", "Column", "Transpose"}];

    outputPositions = gridOutputPositions[grid];
    inputPositions = gridInputPositions[grid];
    positions = Position[grid, _Diagram, All];

    (* outputs = Catenate[#["OutputPorts"] & /@ Extract[grid, outputPositions]];
    inputs = Catenate[Through[#["InputPorts"]["Dual"]] & /@ Extract[grid, inputPositions]]; *)

    grid = grid //
        MapAt[Diagram[#, "PortLabels" -> {None, Placed[Automatic, {- 2 / 3, 1}]}, "PortArrows" -> {Placed[None, Inherited], Placed[None, Inherited]}] &, Complement[positions, outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabels" -> {None, Inherited}, "PortArrows" -> {Placed[None, Inherited], Inherited}] &, Complement[outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabels" -> {Inherited, Placed[Automatic, {- 2 / 3, 1}]}, "PortArrows" -> {Inherited, Placed[None, Inherited]}] &, Complement[inputPositions, outputPositions]];
    
    If[OptionValue["Frames"] === All, grid = grid /. d_Diagram :> Diagram[d, "PortArrows" -> Function[{PointSize[0.01], Point[#1[[1]]]}]]];

	Show[
        Cases[grid,
            d_Diagram :> Diagram[d, "DiagramOptions" -> Join[diagramOptions, d["DiagramOptions"]]]["Graphics"],
            All
        ],
        Graphics[
            Switch[OptionValue["Frames"],
                True,
                With[{subDiagrams = DeleteDuplicates[
                        SortBy[Catenate[{rows, columns} /. _Missing -> Nothing], First],
                        MatchQ[#1[[1]], Append[#2[[1]], ___]] || MatchQ[#2[[1]], Append[#1[[1]], ___]] &][[All, 2]
                    ]
                },
                    #["Graphics", "LabelFunction" -> ("" &)][[1]] & /@ subDiagrams
                ],
                All,
                With[{subDiagrams = #[[1]] -> Diagram[#[[2]], "LabelFunction" -> ("" &),
                        "PortLabels" -> Placed[Automatic, {0, 0}],
                        "PortArrows" -> Function[{FaceForm[Directive[Opacity[1], White]], Disk[#1[[1]], 0.04]}],
                        "Width" -> Min[1, 0.95 ^ (Length[#[[1]]] / 2)] #[[2]]["OptionValue"["Width"]],
                        "Height" -> Min[1, 0.90 ^ (Length[#[[1]]] / 2)] #[[2]]["OptionValue"["Height"]]
                    ] & /@ Catenate[{rows, columns} /. _Missing -> Nothing]
                },
                {subDiagramLevels = KeyDrop[None] @ GroupBy[subDiagrams, If[# === {}, None, Most[#]] & @* First]},
                    {
                        If[ wiresQ, {
                            (* frameWires[grid,
                                ReverseSortBy[subDiagrams, First],
                                (* DeleteDuplicates[ReverseSortBy[subDiagrams, First], MatchQ[#1[[1]], Append[#2[[1]], ___]] || MatchQ[#2[[1]], Append[#1[[1]], ___]] &], *)
                                portFunction, True, vGapSize],
                            Extract[grid,
                                DeleteDuplicates[ReverseSort[subDiagrams[[All, 1]]], MatchQ[#1, Append[#2, ___]] || MatchQ[#2, Append[#1, ___]] &],
                                gridWires[#, {}, portFunction, True, vGapSize] &
                            ], *)
                            (* KeyValueMap[
                                gridWires[ReplacePart[grid, #2][[Sequence @@ #1]], {}, OptionValue["PortFunction"], True, vGapSize] &,
                                subDiagramLevels
                            ],
                            KeyValueMap[
                                frameWires[ReplacePart[grid, #2], Normal @ KeyTake[ReverseSortBy[subDiagrams, First], Prepend[#1] @ Keys[#2]], OptionValue["PortFunction"], True, vGapSize] &,
                                subDiagramLevels
                            ] *)
                            gridFrameWires[grid, {}, subDiagrams,
                                With[{d = Lookup[subDiagrams, Key[{}]]}, {ps = d["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ d["PortArrows"][[1]]}]]],
                                portFunction, wireArrows, vGapSize
                            ]
                        },
                            Nothing
                        ],
                        #[[2]]["Graphics"][[1]] & /@ subDiagrams
                    }
                ],
                _,
                    {
                        If[wiresQ, gridWires[grid, {}, portFunction, wireArrows, vGapSize], Nothing],
                        FaceForm[None], EdgeForm[Directive[Thin, Black]],
                        Switch[OptionValue[Dividers],
                            All | Automatic, items,
                            True, #["Graphics", "LabelFunction" -> ("" &), "PortArrows" -> None, "PortLabels" -> None][[1]] & /@ Catenate[{rows, columns} /. _Missing -> Nothing][[All, 2]],
                            _, Nothing
                        ]
                    }
                ]
        ],
        FilterRules[{opts}, Options[Graphics]],
        BaseStyle -> {
            GraphicsHighlightColor -> Automatic
        }
    ]
]


gridWire[wireArrows_, vGapSize_][{outDual_, out_}, {inDual_, in_}] :=
    {
        Arrowheads[
            With[{arrowSize = Replace[wireArrows, {False | None -> 0, True -> Small}], from = If[outDual, -1, 1], to = If[inDual, -1, 1]},
                If[ from == - to,
                    {{from * arrowSize, .5}},
                    {{from * arrowSize, .3}, {to * arrowSize, .7}}
                ]
            ]
        ],
        Arrow @ BSplineCurve @ {out[[1]], out[[1]] + vGapSize (out[[2]] - out[[1]]), in[[1]] + vGapSize (in[[2]] - in[[1]]), in[[1]]}
    }

gridWires[CirclePlus[ds___], args___] := gridWires[#, args] & /@ {ds}

gridWires[(Transpose | SuperStar)[d_, ___], args___] := gridWires[d, args]

mergeRules[xs_, ys_] := Catenate @ KeyValueMap[{k, v} |->
    k -> # & /@ Thread[PadRight[v, {Automatic, Min[Length /@ v]}]],
    Select[Merge[KeyUnion[GroupBy[#, First, Map[Last]] & /@ {xs, ys}], Identity], MatchQ[{_List, _List}]]
]

gridWires[CircleTimes[ds___], ports_, portFunction_, opts___] :=
    Fold[
        With[
            {inputs = Join @@ Extract[#2, gridInputPositions[#2],
                With[{ps = #["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &
            ]},
            {merge = mergeRules[#1[[2]], inputs]},
            {
                Join[#1[[1]], gridWire[opts] @@@ Values[merge], gridWires[#2, {}, portFunction, opts]],
                DeleteElements[#1[[2]], 1 -> MapAt[First, merge, {All, 2}]]
            }
        ] &,
        {{}, ports},
        {ds}
    ][[1]]

gridWires[CircleDot[ds___, d_], ports_, portFunction_, opts___] := Block[{
    inputPos = gridInputPositions[d],
    outputPos = gridOutputPositions[d],
    merge, inputs, outputs
},
    inputs = Join @@ Extract[d, inputPos, With[{ps = #["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &];
    outputs = Join @@ Extract[d, outputPos, With[{ps = #["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[2]]}]]] &];
    merge = mergeRules[ports, inputs];
    
    Join[
        gridWire[opts] @@@ Values[merge],
        gridWires[d, {}, portFunction, opts],
        gridWires[CircleDot[ds], Join[DeleteElements[ports, 1 -> MapAt[First, merge, {All, 2}]], outputs], portFunction, opts]
    ]
]

gridWires[grid_ -> _, args___] := gridWires[grid, args]

gridWires[___] := {}


frameWires[grid_, diagrams_, portFunction_, opts___] := DeleteDuplicatesBy[#[[2, 1, 1, 1]] &] @ DeleteDuplicatesBy[#[[2, 1, 1, -1]] &] @ Flatten[
    With[{subGrid = First @ Extract[grid, {#[[1]]}], diagram = #[[2]]},
        Block[{
            inputPos = gridInputPositions[subGrid],
            outputPos = gridOutputPositions[subGrid],
            mergeInput, mergeOutput, inputs, outputs
        },
            inputs = Join @@ Extract[subGrid, inputPos, With[{ps = #["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &];
            outputs = Join @@ Extract[subGrid, outputPos, With[{ps = #["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[2]]}]]] &];
            mergeInput = mergeRules[With[{ps = diagram["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[1]]}]]], inputs];
            mergeOutput = mergeRules[With[{ps = diagram["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[2]]}]]], outputs];
            
            gridWire[opts] @@@ Values[#] & /@ {mergeInput, mergeOutput}
        ]
    ] & /@ diagrams,
    2
]


gridFrameWires[CirclePlus[ds___], pos_, args___] := MapIndexed[gridFrameWires[#, Join[pos, #2], args] &, {ds}]

gridFrameWires[(Transpose | SuperStar)[d_, ___], pos_, args___] := gridFrameWires[d, Append[pos, 1], args]

gridFrameWires[grid : CircleTimes[ds___], pos_, frameDiagrams_, initPorts_, portFunction_, opts___] := Block[{
    diagram = Lookup[frameDiagrams, Key[pos]], upInputs, upOutputs, inputs, outputs, merge = {}, ports = initPorts
},
    If[ ! MissingQ[diagram],
        upInputs = With[{ps = diagram["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[1]]}]]];
        upOutputs = With[{ps = diagram["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[2]]}]]];
        merge = mergeRules[ports, upInputs];
        ports = upInputs
    ];
    Join[
        (* gridWire[opts] @@@ Values[merge], *)
        Fold[(
            diagram = Lookup[frameDiagrams, Key[Append[pos, #1[[3]]]]];
            If[ MissingQ[diagram],
                inputs = Join @@ Extract[#2, gridInputPositions[#2],
                    With[{ps = #["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &
                ];
                outputs = Join @@ Extract[#2, gridOutputPositions[#2],
                    With[{ps = #["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[2]]}]]] &
                ];
                merge = mergeRules[#1[[2]], inputs]
                ,
                inputs = With[{ps = diagram["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], diagram["PortArrows"][[1]]}]]];
                outputs = With[{ps = diagram["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], diagram["PortArrows"][[2]]}]]];
                merge = mergeRules[#1[[2]], inputs]
            ];
            merge = Join[merge, mergeRules[outputs, upOutputs]];
            {
                Join[
                    #1[[1]], gridWire[opts] @@@ Values[merge]
                    ,
                    gridFrameWires[#2, Append[pos, #1[[3]]], frameDiagrams,
                        With[{ps = diagram["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[1]]}]]],
                        portFunction, opts
                    ]
                ],
                DeleteElements[#1[[2]], 1 -> MapAt[First, merge, {All, 2}]],
                #1[[3]] + 1
            }
        ) &,
            {{}, ports, 1},
            {ds}
        ][[1]]
    ]
]

gridFrameWires[CircleDot[ds___, d_], pos_, frameDiagrams_, initPorts_, portFunction_, opts___] := Block[{
    inputPos = gridInputPositions[d],
    outputPos = gridOutputPositions[d],
    upOutputPorts, downInputPorts, downOutputPorts, inputs, outputs, merge = {}, merge1, merge2,
    diagramUp = Lookup[frameDiagrams, Key[pos]],
    diagramDown = Lookup[frameDiagrams, Key[Append[pos, Length[{ds}] + 1]]],
    ports = initPorts
},
    If[ MissingQ[diagramDown],
        inputs = Join @@ Extract[d, inputPos, With[{ps = #["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &];
        outputs = Join @@ Extract[d, outputPos, With[{ps = #["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[2]]}]]] &];
        merge = mergeRules[ports, inputs];
        ports = Join[DeleteElements[ports, 1 -> MapAt[First, merge, {All, 2}]], outputs]
        ,
        downInputPorts = With[{ps = diagramDown["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], diagramDown["PortArrows"][[1]]}]]];
        downOutputPorts = With[{ps = diagramDown["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagramDown["PortArrows"][[2]]}]]];
        outputs = Catenate @ Map[
            With[{diagramUp = Lookup[frameDiagrams, Key[Join[pos, {Length[{ds}] + 1}, Most[#]]], First[Extract[d, {#}]]]}, {ps = diagramUp["FlatOutputPorts"]},
                Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], diagramUp["PortArrows"][[2]]}]]
            ] &,
            outputPos
        ];
        merge1 = mergeRules[ports, downInputPorts];
        merge2 = mergeRules[outputs, downOutputPorts];
        merge = Join[merge1, {}];
        ports = Join[
            DeleteElements[ports, 1 -> MapAt[First, merge1, {All, 2}]],
            With[{ps = diagramDown["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], diagramDown["PortArrows"][[2]]}]]]
        ]
    ];
    (* If[ ! MissingQ[diagramUp] && Length[{ds}] == 0,
        upOutputPorts = With[{ps = diagramUp["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagramUp["PortArrows"][[2]]}]]];
        merge = Join[merge, mergeRules[Join[ports, outputs], upOutputPorts]];
        ports = Join[DeleteElements[Join[ports, outputs], 1 -> MapAt[First, merge, {All, 2}]], upOutputPorts]
    ]; *)
    Join[
        gridWire[opts] @@@ Values[merge],
        gridFrameWires[d, Append[pos, Length[{ds}] + 1], frameDiagrams, {}, portFunction, opts],
        gridFrameWires[CircleDot[ds], pos, frameDiagrams, ports, portFunction, opts]
    ]
]

(* gridFrameWires[CircleDot[], pos_, frameDiagrams_, initPorts_, portFunction_, opts___] := Block[{
    upOutputPorts, merge = {},
    diagramUp = Lookup[frameDiagrams, Key[pos]],
    ports = initPorts
}, 
    If[ ! MissingQ[diagramUp],
        upOutputPorts = With[{ps = diagramUp["FlatOutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagramUp["PortArrows"][[2]]}]]];
        merge = mergeRules[ports, upOutputPorts];
    ];
    gridWire[opts] @@@ Values[merge]
] *)

(* gridFrameWires[d_Diagram, pos_, frameDiagrams_, ports_, portFunction_, opts___] := Block[{
    inputs, diagramUp = Lookup[frameDiagrams, Key[Most[pos]]]
}, 
    If[ MissingQ[diagramUp],
        {}
        ,
        inputs = With[{ps = d["FlatInputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)  } & @@@ d["PortArrows"][[1]]}]]];
        gridWire[opts] @@@ Values[mergeRules[ports, inputs]]
    ]
] *)

gridFrameWires[___] := {}



End[];

EndPackage[];

