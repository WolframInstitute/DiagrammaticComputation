BeginPackage["ProcessTheory`Diagram`Grid`", {"ProcessTheory`Port`", "ProcessTheory`Diagram`", "ProcessTheory`Utilities`"}];

ColumnDiagram
RowDiagram
DiagramGrid

DiagramArrange
DiagramDecompose

DiagramMatchPorts
DiagramAssignPorts

GridInputPorts
GridOutputPorts

Begin["ProcessTheory`Diagram`Grid`Private`"];


(* compose vertically preserving grid structure *)

Options[ColumnDiagram] = Join[{"PortFunction" -> Function[#["Name"]], "PortOrderingFunction" -> Automatic, "Direction" -> Top}, Options[Diagram]]

ColumnDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{
    func = OptionValue["PortFunction"],
    a, b,
    as, bs,
    aPorts, bPorts
},
    a = x["FlattenOutputs"];
    b = y["FlattenInputs"];
    as = a["OutputPorts"];
    bs = Through[b["InputPorts"]["Dual"]];
	aPorts = func /@ as;
	bPorts = func /@ bs;
    If[ ContainsNone[aPorts, bPorts],
        If[ aPorts === {} && bPorts === {},
            Return[DiagramComposition[b, a, FilterRules[{opts}, Options[DiagramComposition]]]],
            Return[RowDiagram[{b, a}, FilterRules[{opts}, Options[RowDiagram]]]]
        ]
    ];
    Replace[SequenceAlignment[Reverse[aPorts], Reverse[bPorts], Method -> "Local"], {
        {left : {l_, {}} | {{}, l_} : {}, {__}, right : {r_, {}} | {{}, r_} : {}} /; ! ({l} =!= {} && {r} =!= {} && IntersectingQ[l, r]) :> (
            Which[
                MatchQ[left, {_, {}}],
                b = RowDiagram[{b, idDiagram[Take[as, - Length[l]]]}]["Flatten"],
                MatchQ[left, {{}, _}],
                a = RowDiagram[{a, idDiagram[Take[bs, - Length[l]]]}]["Flatten"]
            ];
            Which[
                MatchQ[right, {_, {}}],
                b = RowDiagram[{idDiagram[Take[as, Length[r]]], b}]["Flatten"],
                MatchQ[right, {{}, _}],
                a = RowDiagram[{idDiagram[Take[bs, Length[r]]], a}]["Flatten"]
            ]
        ),
        _ :> With[{ins = Delete[bs, FirstPositions[bPorts, aPorts]], outs = Delete[as, FirstPositions[aPorts, bPorts]]},
            If[ins =!= {}, a = RowDiagram[{idDiagram[ins], a}]["Flatten"]];
            If[outs =!= {}, b = RowDiagram[{idDiagram[outs], b}]["Flatten"]]
        ]
    }
    ];
    as = a["OutputPorts"];
    bs = Through[b["InputPorts"]["Dual"]];
	aPorts = func /@ as;
	bPorts = func /@ bs;
	Which[
		aPorts === bPorts,
		DiagramComposition[b, a, FilterRules[{opts}, Options[DiagramComposition]]],
		aPorts === Reverse[bPorts] && a["WireQ"],
        DiagramComposition[b, DiagramReverse[a], FilterRules[{opts}, Options[DiagramComposition]]],
        aPorts === Reverse[bPorts] && b["WireQ"],
        DiagramComposition[DiagramReverse[b], a, FilterRules[{opts}, Options[DiagramComposition]]],
		Sort[aPorts] === Sort[bPorts],
        DiagramComposition[b, piDiagram[as, bs, aPorts, bPorts], a, FilterRules[{opts}, Options[DiagramComposition]]],
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


setDiagram[diagram1_, diagram2_] := Diagram[diagram1, Function[Null, "Expression" :> ##, HoldAll] @@ diagram2["HoldExpression"]]

Options[DiagramArrange] = Join[{"Network" -> True, "Arrange" -> True, "NetworkMethod" -> "Foliation"}, Options[ColumnDiagram]]

DiagramArrange[diagram_Diagram, opts : OptionsPattern[]] := If[(TrueQ[diagram["OptionValue"["Arrange"], opts]] || diagram["NetworkQ"]) && TrueQ[diagram["OptionValue"["Decompose"], opts]],
Replace[diagram["HoldExpression"], {
    HoldForm[DiagramProduct[ds___]] :> setDiagram[diagram, RowDiagram[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[RowDiagram]]]],
    HoldForm[DiagramComposition[ds___]] :> setDiagram[diagram, ColumnDiagram[DiagramArrange[#, opts] & /@ Reverse[{ds}], FilterRules[{opts, diagram["DiagramOptions"]}, Options[ColumnDiagram]]]],
    HoldForm[DiagramSum[ds___]] :> setDiagram[diagram, DiagramSum[##, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramSum]]] & @@ (DiagramArrange[#, opts] & /@ {ds})],
    HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]],
        If[ Length[{ds}] == 1,
            Diagram[diagram, "Expression" :> Evaluate[DiagramArrange[ds, opts]]],
            With[{g = DiagramsNetGraph[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramsNetGraph]], "BinarySpiders" -> True, "UnarySpiders" -> False, "RemoveCycles" -> True]},
                setDiagram[
                    diagram,
                    ColumnDiagram[
                        Switch[OptionValue["NetworkMethod"],
                            "TopologicalSort", AnnotationValue[{g, TopologicalSort[g]}, "Diagram"],
                            "Stratify", RowDiagram[AnnotationValue[{g, Developer`FromPackedArray[#]}, "Diagram"]] & /@ ResourceFunction["VertexStratify"][g],
                            "Foliation", RowDiagram[AnnotationValue[{g, #}, "Diagram"]] & /@ First[ResourceFunction["GraphFoliations"][g, MaxItems -> 1]],
                            "RandomFoliation", RowDiagram[AnnotationValue[{g, #}, "Diagram"]] & /@ RandomChoice[ResourceFunction["GraphFoliations"][g]]
                        ]
                        ,
                        "PortFunction" -> Function[#["HoldExpression"]],
                        FilterRules[{opts, diagram["DiagramOptions"]}, Options[ColumnDiagram]]
                    ]
                ]
            ]
        ],
        Diagram[diagram, "Expression" :> DiagramNetwork[##] & @@ (DiagramArrange[#, opts] & /@ {ds})]
    ],
    _ :> diagram
}]
    ,
    diagram
]


matchPorts[d_Diagram, {outputPorts_, inputPorts_}] := Diagram[d,
    If[inputPorts === Automatic, Inherited, PortDual /@ MapThread[If[#2 === Automatic, #1, #2] &, {d["InputPorts"], Join[Port /@ inputPorts, Drop[d["InputPorts"], Length[inputPorts]]]}]],
    If[outputPorts === Automatic, Inherited, MapThread[If[#2 === Automatic, #1, #2] &, {d["OutputPorts"], Join[Port /@ outputPorts, Drop[d["OutputPorts"], Length[outputPorts]]]}]]
]

(* only works on arranged grid *)
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

DiagramMatchPorts[d_Diagram, ports_] := Diagram[Diagram[matchPorts[DiagramDecompose[d], ports]], "DiagramOptions" -> d["DiagramOptions"]]


assignPorts[diagram_Diagram, ports : {inputPorts_, outputPorts_}] := With[{args = Sequence[inputPorts, outputPorts, diagram["DiagramOptions"]]},
Replace[diagram["HoldExpression"], {
	HoldForm[DiagramComposition[ds___, d_]] :> Block[{leftoverPorts, pos, restPos, padPorts, f = diagram["OptionValue"["PortFunction"]]},
		FoldList[List /* Replace[{{d1_, ps_}, d2_} :> With[{inputs = PortDual /@ d2["FlatInputPorts"], outputs = d1["FlatOutputPorts"]},
				pos = DeleteMissing @ FirstPositionsWithMissing[f /@ inputs, f /@ outputs];
				restPos = Complement[Range[Length[inputs]], Catenate[pos]];
				{leftoverPorts, padPorts} = TakeDrop[ps[[1]], UpTo[Length[restPos]]];
				assignPorts[d2, {Join[ReplacePart[inputs, Join[Thread[pos -> Automatic], Thread[Take[restPos, Length[leftoverPorts]] -> leftoverPorts]]], padPorts], Automatic}]
		]],
			assignPorts[d, {inputPorts, Automatic}],
	        Reverse[{ds}]
	    ] // (
		    {newInputs} |-> {Diagram[DiagramComposition @@ #[[All, 1]], args], {newInputs[[-1, 2, 1]], #[[-1, 2, 2]]}} & @
		    FoldList[List /* Replace[{{d1_, ps_}, d2_} :> With[{inputs = PortDual /@ d1["FlatInputPorts"], outputs = d2["FlatOutputPorts"]},
				pos = DeleteMissing @ FirstPositionsWithMissing[f /@ outputs, f /@ inputs];
				restPos = Complement[Range[Length[outputs]], Catenate[pos]];
				{leftoverPorts, padPorts} = TakeDrop[ps[[2]], UpTo[Length[restPos]]];
				assignPorts[d2, {Automatic, Join[ReplacePart[outputs, Join[Thread[pos -> Automatic], Thread[Take[restPos, Length[leftoverPorts]] -> leftoverPorts]]], padPorts]}]
			]],
				assignPorts[newInputs[[-1, 1]], {Inherited, outputPorts}],
		        Reverse[Most[newInputs][[All, 1]]]
		    ]
		)
	],
	HoldForm[DiagramProduct[ds___]] :> ({Diagram[(DiagramProduct @@ #[[1]])["Flatten"], args], #[[2]]} & @ Fold[{state, d} |-> MapAt[Append[state[[1]], #] &, assignPorts[d, state[[2]]], {1}], {{}, ports}, {ds}]),
	HoldForm[DiagramSum[ds___]] :> ({Diagram[DiagramSum @@ #[[All, 1]], args], {Intersection @@ #[[2, All, 1]], Intersection @@ #[[2, All, 2]]}} & @ (assignPorts[#, ports] & /@ {ds})),
	_ :> {
		Diagram[diagram,
		    If[inheritedQ[inputPorts], Inherited, MapThread[If[inheritedQ[#2], PortDual[#1], #2] &, {diagram["FlatInputPorts"], PadRight[inputPorts, diagram["FlatInputArity"], Automatic]}]],
		    If[inheritedQ[outputPorts], Inherited, MapThread[If[inheritedQ[#2], #1, #2] &, {diagram["FlatOutputPorts"], PadRight[outputPorts, diagram["FlatOutputArity"], Automatic]}]]
		]
		,
		{
			If[inheritedQ[inputPorts], {}, Drop[inputPorts, UpTo[diagram["FlatInputArity"]]]],
			If[inheritedQ[outputPorts], {}, Drop[outputPorts, UpTo[diagram["FlatOutputArity"]]]]
		}
	}
}]
]

DiagramAssignPorts[d_Diagram, ports_] := First @ assignPorts[d, ports]


Options[DiagramDecompose] = {"Network" -> True, "Unary" -> False, "Decompose" -> True, "Ports" -> False, "Diagram" -> False}

DiagramDecompose[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] := If[TrueQ[diagram["OptionValue"["Decompose"], opts]],
    Replace[diagram["HoldExpression"], {
        HoldForm[d_Diagram] :> d,
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
] // If[TrueQ[OptionValue["Ports"]], # -> {Through[diagram["InputPorts"]["Dual"]], diagram["OutputPorts"]} &, Identity] //
    If[TrueQ[OptionValue["Diagram"]], # -> If[diagram["NodeQ"], None, diagram] &, Identity]

gridTranspose[CircleTimes[ds___CircleDot]] := CircleDot @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[RowDiagram[Diagram /@ {##}]] &, List @@@ {ds}]
gridTranspose[CircleDot[ds___CircleTimes]] := CircleTimes @@ ResourceFunction["GeneralizedMapThread"][DiagramDecompose[ColumnDiagram[Diagram /@ Reverse[{##}]]] & , List @@@ {ds}]
gridTranspose[ct_CircleTimes] := CircleDot[ct]
gridTranspose[cd_CircleDot] := CircleTimes[cd]
gridTranspose[d_] := d


decompostionWidth[d_Diagram, args___] := gridWidth[DiagramDecompose[d], args]

gridWidth[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic :> Max[d["MaxArity"], 1], _ :> d[prop]}],
    (CircleTimes | CirclePlus)[ds___] :> Total[gridWidth[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Max[gridWidth[#, prop] & /@ {ds}],
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


circuitArrange[diagram_Diagram -> d_, pos_, {_, autoHeight_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0] := Block[{
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
    Sow[pos -> Diagram[Replace[d, None -> diagram],
        "Center" -> center,
        "Width" -> w,
        "Height" -> h + dy,
        "Angle" -> angle
    ], "Item"];
    Diagram[diagram,
        "Width" -> w, "Height" -> h,
        "PortArrows" -> {
            Placed[Automatic, Threaded[center] + {{#, h / 2}, {#, h / 2 + 1 / 4}}] & /@ (- w / 2 + inputOrder - min + 1 / 2),
            Placed[Automatic, Threaded[center] + {{#, - h / 2}, {#, - h / 2 - 1 / 4}}] & /@ (- w / 2 + outputOrder - min + 1 / 2) 
        },
        "Center" -> center
    ]
]

gridArrange[diagram_Diagram -> d_, pos_, {autoWidth_, autoHeight_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0] := Block[{
    arity = diagram["MaxArity"],
    alignment = diagram["OptionValue"[Alignment]],
    spacing = diagram["OptionValue"["Spacing"]],
    width, w, h, ratio, center
},
    If[alignment === "Circuit", Return[circuitArrange[diagram -> d, pos, {autoWidth, autoHeight}, {dx, dy}, corner, angle]]];
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
    Sow[pos -> Diagram[Replace[d, None -> diagram],
        "Center" -> RotationTransform[angle, corner][corner + {width * (1 + dx), h} / 2],
        "Width" -> width * (1 + dx),
        "Height" -> h + dy / 4,
        "Shape" -> Automatic
    ], "Item"];
    Diagram[diagram,
        "Center" -> center,
        "Width" -> Replace[diagram["OptionValue"["Width"]], Automatic :> If[MatchQ[diagram["OptionValue"["Shape"]], "Circle"] || arity <= 1, 1, ratio * w]],
        "Height" -> Replace[diagram["OptionValue"["Height"]], Automatic :> Max[h - dy, 1]]
    ]
]

gridArrange[grid : (CircleTimes | CirclePlus)[ds___] -> d_, pos_, {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{widths, relativeWidths, newHeight, positions},
    widths = gridWidth /@ {ds};
    relativeWidths = If[width =!= Automatic, width * widths / Total[widths], widths];
    newHeight = Replace[height, Automatic :> gridHeight[grid, "OptionValue"["Height"]] + dy * gridHeight[grid]];
    relativeWidths = FoldPairList[With[{x = Floor[#1 + #2]}, {x, #2 - x}] &, 0, relativeWidths];
    If[width =!= Automatic, relativeWidths[[-1]] = width - Total[Most[relativeWidths]]];
    positions = Prepend[Accumulate[relativeWidths * (1 + dx)], 0];
    With[{w = Total[relativeWidths] * (1 + dx), h = newHeight},
        Sow[pos -> Diagram[d, "Center" -> RotationTransform[angle, corner][corner + {w, h} / 2], "Width" -> Replace[d["OptionValue"["Width"]], Automatic -> w], "Height" -> Replace[d["OptionValue"["Height"]], Automatic -> h]], "Row"]
    ];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, Append[pos, i], {relativeWidths[[i]], newHeight}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {positions[[i]], 0}, angle]] &, grid]
]

gridArrange[grid : CircleDot[ds___] -> d_, pos_, {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_] := Block[{heights, newWidth, positions},
    heights = gridHeight[#, "OptionValue"["Height"]] + gridHeight[#] * dy & /@ {ds};
    If[height =!= Automatic, heights = height * heights / Total[heights]];
    newWidth = Replace[width, Automatic :> gridWidth[grid]];
    positions = Prepend[Accumulate[heights], 0];
    With[{w = newWidth * (1 + dx), h = Total[heights]},
        Sow[pos -> Diagram[d, "Center" -> RotationTransform[angle, corner][corner + {w, h} / 2], "Width" -> Replace[d["OptionValue"["Width"]], Automatic -> w], "Height" -> Replace[d["OptionValue"["Height"]], Automatic -> h]], "Column"]
    ];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, Append[pos, i], {newWidth, heights[[i]] - dy / 4}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {0, positions[[i]]}, angle]] &, grid]
]

gridArrange[HoldPattern[SuperStar[d_]] -> _, args___] := gridArrange[d /. diagram_Diagram :> DiagramDual[diagram], args]

gridArrange[HoldPattern[Transpose[d_, perm___]] -> _, args___] := (Sow[{perm}, "Transpose"]; gridArrange[d, args])

gridArrange[ds_List -> d_, args___] := If[Length[ds] == 1,
    {gridArrange[ds[[1, 1]] -> d, args]},
    gridArrange[DiagramNetwork @@ ds, args]
]

gridArrange[grid_, gapSizes_, angle_] := gridArrange[grid, {}, {Automatic, Automatic}, gapSizes, {0, 0}, angle]


gridOutputPositions[_Diagram | _List, pos_] := {pos}
gridOutputPositions[{_}, pos_] := Append[pos, 1]
gridOutputPositions[(CircleTimes | CirclePlus)[ds___], pos_] := Catenate[MapIndexed[gridOutputPositions[#1, Join[pos, #2]] &, {ds}]]
gridOutputPositions[CircleDot[d_, ___], pos_] := gridOutputPositions[d, Append[pos, 1]]
gridOutputPositions[(Transpose | SuperStar)[d_, ___], pos_] := gridOutputPositions[d, pos]
gridOutputPositions[grid_ -> _, pos_] := gridOutputPositions[grid, Append[pos, 1]]
gridOutputPositions[grid_] := gridOutputPositions[grid, {}]

gridInputPositions[_Diagram | _List, pos_] := {pos}
gridInputPositions[{_}, pos_] := Append[pos, 1]
gridInputPositions[(CircleTimes | CirclePlus)[ds___], pos_] := Catenate[MapIndexed[gridInputPositions[#1, Join[pos, #2]] &, {ds}]]
gridInputPositions[CircleDot[ds___, d_], pos_] := gridInputPositions[d, Append[pos, Length[{ds}] + 1]]
gridInputPositions[(Transpose | SuperStar)[d_, ___], pos_] := gridInputPositions[d, pos]
gridInputPositions[grid_ -> _, pos_] := gridInputPositions[grid, Append[pos, 1]]
gridInputPositions[grid_] := gridInputPositions[grid, {}]

GridInputPorts[d_Diagram] := If[d["NodeQ"], d["InputPorts"], GridInputPorts[If[d["NetworkQ"], d["Arrange"], d]["Decompose"]]]
GridInputPorts[grid_] := Catenate[Extract[grid, gridInputPositions[grid], #["InputPorts"] &]]

GridOutputPorts[d_Diagram] := If[d["NodeQ"], d["OutputPorts"], GridOutputPorts[If[d["NetworkQ"], d["Arrange"], d]["Decompose"]]]
GridOutputPorts[grid_] := Catenate[Extract[grid, gridOutputPositions[grid], #["OutputPorts"] &]]

Options[DiagramGrid] = Join[{
    "HorizontalGapSize" -> 1,
    "VerticalGapSize" -> 1,
    "Rotate" -> 0,
    "Wires" -> True,
    "WireArrows" -> False,
    "Frames" -> Automatic,
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
    portFunction = With[{f = OptionValue["PortFunction"]}, #["Apply", f] &],
    wireArrows = OptionValue["WireArrows"],
    dividers
},
    grid = DiagramDecompose[DiagramArrange[diagram, FilterRules[{opts}, Options[DiagramArrange]]], "Diagram" -> True, FilterRules[{opts}, Options[DiagramDecompose]]];
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
    
    
    dividers = {
        FaceForm[None], EdgeForm[Directive[Thin, Black]],
        Switch[OptionValue[Dividers],
            All | Automatic, #["Graphics", "LabelFunction" -> ("" &), "PortArrows" -> None, "PortLabels" -> None][[1]] & /@ items[[All, 2]],
            True, #["Graphics", "LabelFunction" -> ("" &), "PortArrows" -> None, "PortLabels" -> None][[1]] & /@ Catenate[{rows, columns} /. _Missing -> Nothing][[All, 2]],
            _, Nothing
        ]
    };

    Graphics[
        Switch[OptionValue["Frames"],
            All | Automatic,
            With[{subDiagrams = #[[1]] -> Diagram[#[[2]], "LabelFunction" -> ("" &),
                    "PortLabels" -> Placed[Automatic, {0, 0}],
                    "PortArrows" -> Function[{FaceForm[Directive[Opacity[1], White]], Disk[#1[[1]], 0.04]}],
                    "Width" -> Min[1, 0.95 ^ (Length[#[[1]]] / 2)] #[[2]]["OptionValue"["Width"]],
                    "Height" -> If[#[[1]] === {}, 1.1, Min[1, 0.85 ^ (Length[#[[1]]] / 2)]] #[[2]]["OptionValue"["Height"]]
                ] & /@ If[
                    OptionValue["Frames"] === Automatic,
                    DeleteCases[
                        (pos_ -> d_Diagram) /;
                            portFunction /@ Catenate[Through[(PortDual /@ d["InputPorts"])["ProductList"]]] === Catenate[Extract[grid, {pos}, portFunction /@ Through[GridInputPorts[#]["Dual"]] &]] &&
                            portFunction /@ Catenate[Through[d["OutputPorts"]["ProductList"]]] === Catenate[Extract[grid, {pos}, portFunction /@ GridOutputPorts[#] &]]
                    ], Identity
                ] @ Replace[Catenate[{rows, columns} /. _Missing -> Nothing], {} -> items]
            },
            {subDiagramLevels = KeyDrop[None] @ GroupBy[subDiagrams, If[# === {}, None, Most[#]] & @* First]},
                {
                    (pos |-> Extract[grid,
                        {pos},
                        Diagram[#, "DiagramOptions" -> Join[
                                diagramOptions,
                                If[ AnyTrue[subDiagrams[[All, 1]], Take[pos, UpTo[Length[#]]] === # &],
                                    {"PortArrows" -> If[#["WireQ"], None, Function[{PointSize[0.01], Point[#1[[1]]]}]], "PortLabels" -> Placed[Automatic, {0.1, .5}]},
                                    {}
                                ],
                                #["DiagramOptions"]
                            ]
                        ]["Graphics"][[1]] &
                    ]) /@ positions,
                    If[ wiresQ, {
                        gridFrameWires[grid, {}, subDiagrams,
                            With[{d = Lookup[subDiagrams, Key[{}]]}, {ps = d["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ d["PortArrows"][[1]]}]]],
                            portFunction, wireArrows, vGapSize
                        ]
                    },
                        Nothing
                    ],
                    #[[2]]["Graphics"][[1]] & /@ subDiagrams,
                    dividers
                }
            ],
            (* True,
            With[{subDiagrams = DeleteDuplicates[
                    SortBy[Catenate[{rows, columns} /. _Missing -> Nothing], First],
                    MatchQ[#1[[1]], Append[#2[[1]], ___]] || MatchQ[#2[[1]], Append[#1[[1]], ___]] &][[All, 2]
                ]
            },
                {
                    Cases[grid,
                        d_Diagram :> Diagram[d, "DiagramOptions" -> Join[diagramOptions, d["DiagramOptions"]]]["Graphics"][[1]],
                        All
                    ],
                    #["Graphics", "LabelFunction" -> ("" &)][[1]] & /@ subDiagrams,
                    dividers
                }
            ], *)
            _,
            {
                Cases[grid,
                    d_Diagram :> Diagram[d, "DiagramOptions" -> Join[diagramOptions, d["DiagramOptions"]]]["Graphics"][[1]],
                    All
                ],
                If[wiresQ, gridWires[grid, {}, portFunction, wireArrows, vGapSize], Nothing],
                dividers
            }
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
        Arrow @ BSplineCurve @ With[{p = out[[1]] + vGapSize (out[[2]] - out[[1]]), q = in[[1]] + vGapSize (in[[2]] - in[[1]])},
            If[
                Dot[p - q, out[[1]] - in[[1]]] > 0,
                {out[[1]], p, q, in[[1]]},
                {out[[1]], in[[1]]}
            ]
        ]
    }

gridWires[CirclePlus[ds___], args___] := gridWires[#, args] & /@ {ds}

gridWires[(Transpose | SuperStar)[d_, ___], args___] := gridWires[d, args]

mergeRules[xs_, ys_] := Catenate @ KeyValueMap[{k, v} |->
    k -> # & /@ Thread[PadRight[v, {Automatic, Min[Length /@ v]}]],
    Select[Merge[KeyUnion[GroupBy[Replace[#, ((CircleTimes | CirclePlus)[zs___] -> x_) :> Splice[# -> x & /@ {zs}], 1], First, Map[Last]] & /@ {xs, ys}], Identity], MatchQ[{_List, _List}]]
]

gridWires[CircleTimes[ds___], ports_, portFunction_, opts___] :=
    Fold[
        With[
            {inputs = Join @@ Extract[#2, gridInputPositions[#2],
                With[{ps = #["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &
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
    inputs = Join @@ Extract[d, inputPos, With[{ps = #["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &];
    outputs = Join @@ Extract[d, outputPos, With[{ps = #["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[2]]}]]] &];
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
            inputs = Join @@ Extract[subGrid, inputPos, With[{ps = #["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &];
            outputs = Join @@ Extract[subGrid, outputPos, With[{ps = #["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[2]]}]]] &];
            mergeInput = mergeRules[With[{ps = diagram["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[1]]}]]], inputs];
            mergeOutput = mergeRules[With[{ps = diagram["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[2]]}]]], outputs];
            
            gridWire[opts] @@@ Values[#] & /@ {mergeInput, mergeOutput}
        ]
    ] & /@ diagrams,
    2
]


(* gridFrameWires[CirclePlus[ds___], pos_, args___] := MapIndexed[gridFrameWires[#, Join[pos, #2], args] &, {ds}] *)

gridFrameWires[(Transpose | SuperStar)[d_, ___], pos_, args___] := gridFrameWires[d, Append[pos, 1], args]

gridFrameWires[{d_} | d_Diagram, args___] := gridFrameWires[CircleTimes[d], args]

gridFrameWires[grid : (CircleTimes | CirclePlus)[ds___], pos_, frameDiagrams_, initPorts_, portFunction_, opts___] := Block[{
    diagram = Lookup[frameDiagrams, Key[pos]], upInputs = None, upOutputs = None, inputs, outputs, merge = {}, ports = initPorts
},
    If[ ! MissingQ[diagram],
        upInputs = With[{ps = diagram["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[1]]}]]];
        upOutputs = With[{ps = diagram["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[2]]}]]];
        merge = mergeRules[ports, upInputs];
        ports = upInputs
    ];
    Join[
        (* gridWire[opts] @@@ Values[merge], *)
        Fold[(
            diagram = Lookup[frameDiagrams, Key[Append[pos, #1[[3]]]]];
            If[ MissingQ[diagram],
                inputs = Join @@ Extract[#2, gridInputPositions[#2],
                    With[{ps = #["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &
                ];
                outputs = Join @@ Extract[#2, gridOutputPositions[#2],
                    With[{ps = #["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[2]]}]]] &
                ];
                merge = mergeRules[#1[[2]], inputs]
                ,
                inputs = With[{ps = diagram["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], diagram["PortArrows"][[1]]}]]];
                outputs = With[{ps = diagram["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], diagram["PortArrows"][[2]]}]]];
                merge = mergeRules[#1[[2]], inputs]
            ];
            If[ upOutputs =!= None,
                With[{mergeOutput = mergeRules[upOutputs, outputs]},
                    merge = Join[merge, mergeOutput];
                    upOutputs = DeleteElements[upOutputs, 1 -> MapAt[First, mergeOutput, {All, 2}]]
                ]   
            ];
            {
                Join[
                    #1[[1]], gridWire[opts] @@@ Values[merge]
                    ,
                    If[ DiagramQ[#2], {},
                        gridFrameWires[#2, Append[pos, #1[[3]]], frameDiagrams,
                            With[{ps = diagram["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagram["PortArrows"][[1]]}]]],
                            portFunction, opts
                        ]
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
        inputs = Join @@ Extract[d, inputPos, With[{ps = #["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[1]]}]]] &];
        outputs = Join @@ Extract[d, outputPos, With[{ps = #["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], #["PortArrows"][[2]]}]]] &];
        merge = mergeRules[ports, inputs];
        ports = Join[outputs, DeleteElements[ports, 1 -> MapAt[First, merge, {All, 2}]]]
        ,
        downInputPorts = With[{ps = diagramDown["InputPorts"]}, Thread[portFunction /@ Through[ps["Dual"]] -> Thread[{Through[ps["DualQ"]], diagramDown["PortArrows"][[1]]}]]];
        downOutputPorts = With[{ps = diagramDown["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagramDown["PortArrows"][[2]]}]]];
        outputs = Catenate @ Map[
            With[{diagramUp = Lookup[frameDiagrams, Key[Join[pos, {Length[{ds}] + 1}, Most[#]]], First[Extract[d, {#}]]]}, {ps = diagramUp["OutputPorts"]},
                Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], diagramUp["PortArrows"][[2]]}]]
            ] &,
            outputPos
        ];
        merge1 = mergeRules[ports, downInputPorts];
        merge2 = mergeRules[outputs, downOutputPorts];
        merge = Join[merge1, {}];
        ports = Join[
            With[{ps = diagramDown["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Through[ps["DualQ"]], diagramDown["PortArrows"][[2]]}]]],
            DeleteElements[ports, 1 -> MapAt[First, merge1, {All, 2}]]
        ]
    ];
    If[ ! MissingQ[diagramUp] && Length[{ds}] == 0,
        upOutputPorts = With[{ps = diagramUp["OutputPorts"]}, Thread[portFunction /@ ps -> Thread[{Not /@ Through[ps["DualQ"]], {#1, #1 + (#1 - #2)} & @@@ diagramUp["PortArrows"][[2]]}]]];
        merge = Join[merge, mergeRules[Join[ports, outputs], upOutputPorts]];
        ports = Join[DeleteElements[Join[ports, outputs], 1 -> MapAt[First, merge, {All, 2}]], upOutputPorts]
    ];
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

