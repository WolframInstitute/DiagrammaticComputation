BeginPackage["ProcessTheory`Diagram`Grid`", {"ProcessTheory`Port`", "ProcessTheory`Diagram`", "ProcessTheory`Utilities`", "ProcessTheory`Diagram`Surgery`"}];

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

Options[ColumnDiagram] := Join[{"PortOrderingFunction" -> Automatic, "Direction" -> Down}, Options[Diagram]]

ColumnDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Module[{
    func = OptionValue["PortFunction"],
    a, b, pa, pb,
    as, bs,
    aStyles, bStyles,
    aPorts, bPorts
},
    a = x["FlattenOutputs"];
    b = y["FlattenInputs"];
    as = a["OutputPorts"];
    bs = PortDual /@ b["InputPorts"];
    pa = Not /@ Through[as["NeutralQ"]];
    pb = Not /@ Through[bs["NeutralQ"]];
    as = Pick[as, pa];
    bs = Pick[bs, pb];
	aPorts = func /@ as;
	bPorts = func /@ bs;
    aStyles = a["PortStyles"];
    bStyles = b["PortStyles"];
    If[ ContainsNone[aPorts, bPorts],
        If[ aPorts === {} && bPorts === {},
            Return[DiagramComposition[b, a, FilterRules[{opts}, Options[DiagramComposition]], "PortArrows" -> {aStyles[[1]], bStyles[[2]]}]],
            Return[RowDiagram[{a, b}, FilterRules[{opts}, Options[RowDiagram]]]]
        ]
    ];
    aStyles = Pick[aStyles[[2]], pa];
    bStyles = Pick[bStyles[[1]], pb];
    Replace[SequenceAlignment[Reverse[aPorts], Reverse[bPorts], Method -> "Local"], {
        {left : {l_, {}} | {{}, l_} : {}, {__}, right : {r_, {}} | {{}, r_} : {}} /; ! ({l} =!= {} && {r} =!= {} && IntersectingQ[l, r]) :> (
            Which[
                MatchQ[left, {_, {}}],
                b = RowDiagram[{b, IdentityDiagram[Take[as, - Length[l]], "PortArrows" -> {Take[aStyles, - Length[l]]}]}]["Flatten", 1],
                MatchQ[left, {{}, _}],
                a = RowDiagram[{a, IdentityDiagram[Take[bs, - Length[l]], "PortArrows" -> {Take[bStyles, - Length[l]]}]}]["Flatten", 1]
            ];
            Which[
                MatchQ[right, {_, {}}],
                b = RowDiagram[{IdentityDiagram[Take[as, Length[r]], "PortArrows" -> {Take[aStyles, Length[r]]}], b}]["Flatten", 1],
                MatchQ[right, {{}, _}],
                a = RowDiagram[{IdentityDiagram[Take[bs, Length[r]], "PortArrows" -> {Take[bStyles, Length[r]]}], a}]["Flatten", 1]
            ]
        ),
        _ :> With[{inPos = FirstPositions[bPorts, aPorts], outPos = FirstPositions[aPorts, bPorts]}, {ins = Delete[bs, inPos], outs = Delete[as, outPos]},
            If[ins =!= {}, a = RowDiagram[{IdentityDiagram[ins, "PortArrows" -> {Delete[bStyles, inPos]}], a}]["Flatten", 1]];
            If[outs =!= {}, b = RowDiagram[{IdentityDiagram[outs, "PortArrows" -> {Delete[aStyles, outPos]}], b}]["Flatten", 1]]
        ]
    }
    ];
    as = a["OutputPorts"];
    bs = PortDual /@ b["InputPorts"];
    pa = Not /@ Through[as["NeutralQ"]];
    pb = Not /@ Through[bs["NeutralQ"]];
    as = Pick[as, pa];
    bs = Pick[bs, pb];
	aPorts = func /@ as;
	bPorts = func /@ bs;
    aStyles = a["PortStyles"];
    bStyles = b["PortStyles"];
	Which[
		aPorts === bPorts,
		DiagramComposition[b, a, FilterRules[{opts}, Options[DiagramComposition]], "PortArrows" -> {aStyles[[1]], bStyles[[2]]}],
		aPorts === Reverse[bPorts] && a["WireQ"],
        DiagramComposition[b, DiagramReverse[a], FilterRules[{opts}, Options[DiagramComposition]], "PortArrows" -> {Reverse[aStyles[[1]]], bStyles[[2]]}],
        aPorts === Reverse[bPorts] && b["WireQ"],
        DiagramComposition[DiagramReverse[b], a, FilterRules[{opts}, Options[DiagramComposition]], "PortArrows" -> {aStyles[[1]], Reverse[bStyles[[2]]]}],
		Sort[aPorts] === Sort[bPorts],
        With[{perm = FindPermutation[aPorts, bPorts]},
            DiagramComposition[
                b,
                PermutationDiagram[
                    as -> bs,
                    perm,
                    "PortArrows" -> MapAt[Permute[#, perm] &, {2}] @ Thread @ MapThread[
                        PadRight[#, 2, Replace[#, {} -> Automatic]] & @ DeleteCases[Automatic] @ Which[! #1["DualQ"] && #2["DualQ"], {#3, #3}, #1["DualQ"] && ! #2["DualQ"], {#4, #4}, True, {#3, #4}] &,
                        {as, bs, Pick[aStyles[[2]], pa], Permute[Pick[bStyles[[1]], pb], InversePermutation[perm]]}
                    ]
                ],
                a,
                FilterRules[{opts}, Options[DiagramComposition]],
                "PortArrows" -> {aStyles[[1]], bStyles[[2]]}
            ]
        ],
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

Options[RowDiagram] := Options[ColumnDiagram]
RowDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Block[{a = x["FlattenInputs", 1], b = y["FlattenOutputs", 1], aPorts, bPorts, ha, hb, aStyles, bStyles},
	aPorts = Through[a["InputPorts"]["Dual"]];
	bPorts = b["OutputPorts"];
    ha = decompositionHeight[a];
    hb = decompositionHeight[b];
    aStyles = a["PortStyles"];
    bStyles = b["PortStyles"];
    Diagram[
        Which[
            ha > hb,
            DiagramProduct[a, DiagramComposition[##, FilterRules[{opts}, Options[DiagramComposition]], "PortArrows" -> bStyles] & @@
                Append[ConstantArray[IdentityDiagram[bPorts, "PortArrows" -> {bStyles[[2]]}], ha - hb], b], FilterRules[{opts}, Options[DiagramProduct]]],
            ha < hb,
            DiagramProduct[DiagramComposition[##, FilterRules[{opts}, Options[DiagramComposition]], "PortArrows" -> aStyles] & @@
                Prepend[ConstantArray[IdentityDiagram[aPorts, "PortArrows" -> {aStyles[[1]]}], hb - ha], a], b, FilterRules[{opts}, Options[DiagramProduct]]],
            True,
            DiagramProduct[a, b, FilterRules[{opts}, Options[DiagramProduct]]]
        ]["Flatten", 1],
        "PortArrows" -> Join[aStyles, bStyles, 2]
    ]
]

RowDiagram[xs : {___Diagram}, opts : OptionsPattern[]] := Fold[RowDiagram[{##}, opts] &, xs]


setDiagram[diagram1_, diagram2_] := Diagram[diagram1, Function[Null, "Expression" :> ##, HoldAll] @@ diagram2["HoldExpression"], "PortFunction" -> diagram2["PortFunction"]]


Options[DiagramArrange] := Join[{"Network" -> True, "Arrange" -> True, "NetworkMethod" -> "Foliation", "AssignPorts" -> True, "Grid" -> True}, Options[ColumnDiagram]]

DiagramArrange[diagram_Diagram, opts : OptionsPattern[]] := If[(TrueQ[diagram["OptionValue"["Arrange"], opts]] || diagram["NetworkQ"]) && TrueQ[diagram["OptionValue"["Decompose"], opts]],
Replace[diagram["HoldExpression"], {
    HoldForm[Diagram[d_]] :> setDiagram[diagram, SingletonDiagram[DiagramArrange[d, opts], FilterRules[{opts, diagram["DiagramOptions"]}, Options[SingletonDiagram]]]],
    HoldForm[DiagramProduct[ds___]] :> setDiagram[diagram, RowDiagram[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[RowDiagram]]]],
    HoldForm[DiagramComposition[ds___]] :> setDiagram[diagram, ColumnDiagram[DiagramArrange[#, opts] & /@ Reverse[{ds}], FilterRules[{opts, diagram["DiagramOptions"]}, Options[ColumnDiagram]]]],
    HoldForm[DiagramSum[ds___]] :> setDiagram[diagram, DiagramSum[##, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramSum]]] & @@ (DiagramArrange[#, opts] & /@ {ds})],
    HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]],
        With[{g = DiagramsNetGraph[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, "RemoveCycles" -> True, "BinarySpiders" -> True, diagram["DiagramOptions"]}, Options[DiagramsNetGraph]], "UnarySpiders" -> False]},
            If[ TrueQ[OptionValue["AssignPorts"]], DiagramAssignPorts, Identity] @ setDiagram[
                diagram,
                SingletonDiagram @ DiagramComposition[##, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramComposition]]] & @@
                    Reverse @ Switch[OptionValue["NetworkMethod"],
                        "TopologicalSort", Diagram[#, "Center" -> Automatic] & /@ AnnotationValue[{g, TopologicalSort[g]}, "Diagram"],
                        "Stratify", RowDiagram[Diagram[#, "Center" -> Automatic] & /@ AnnotationValue[{g, Developer`FromPackedArray[#]}, "Diagram"]] & /@ ResourceFunction["VertexStratify"][g],
                        "Foliation", RowDiagram[Diagram[#, "Center" -> Automatic] & /@ AnnotationValue[{g, #}, "Diagram"]] & /@ First[ResourceFunction["GraphFoliations"][g, MaxItems -> 1]],
                        "RandomFoliation", RowDiagram[Diagram[#, "Center" -> Automatic] & /@ AnnotationValue[{g, #}, "Diagram"]] & /@ RandomChoice[ResourceFunction["GraphFoliations"][g]]
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


assignPorts[diagram_Diagram, ports : {inputPorts_, outputPorts_}] := With[{args = Sequence[
    If[inheritedQ[inputPorts], Inherited, MapThread[If[inheritedQ[#2], PortDual[#1], #2] &, {diagram["FlatInputPorts"], PadRight[inputPorts, diagram["FlatInputArity"], Inherited]}]],
    If[inheritedQ[outputPorts], Inherited, MapThread[If[inheritedQ[#2], #1, #2] &, {diagram["FlatOutputPorts"], PadRight[outputPorts, diagram["FlatOutputArity"], Inherited]}]],
    diagram["DiagramOptions"]
]
}
,
Replace[diagram["HoldExpression"], {
    HoldForm[Diagram[d_]] :> ({Diagram[SingletonDiagram[#1], args], #2} & @@ assignPorts[d, ports]),
	HoldForm[DiagramComposition[ds___, d_]] :> Block[{leftoverPorts, pos, restPos, padPorts, f = diagram["PortFunction"]},
		FoldList[List /* Replace[{{d1_, ps_}, d2_} :> With[{inputs = PortDual /@ d2["FlatInputPorts"], outputs = d1["FlatOutputPorts"]},
				pos = DeleteMissing @ FirstPositionsWithMissing[f /@ inputs, f /@ outputs];
				restPos = Complement[Range[Length[inputs]], Catenate[pos]];
				{leftoverPorts, padPorts} = TakeDrop[ps[[1]], UpTo[Length[restPos]]];
				assignPorts[d2, {Join[ReplacePart[inputs, Join[Thread[pos -> Inherited], Thread[Take[restPos, Length[leftoverPorts]] -> leftoverPorts]]], padPorts], Automatic}]
		]],
			assignPorts[d, {inputPorts, Inherited}],
	        Reverse[{ds}]
	    ] // (
		    {newInputs} |-> {Diagram[DiagramComposition @@ #[[All, 1]], args], {newInputs[[-1, 2, 1]], #[[-1, 2, 2]]}} & @
		    FoldList[List /* Replace[{{d1_, ps_}, d2_} :> With[{inputs = PortDual /@ d1["FlatInputPorts"], outputs = d2["FlatOutputPorts"]},
				pos = DeleteMissing @ FirstPositionsWithMissing[f /@ outputs, f /@ inputs];
				restPos = Complement[Range[Length[outputs]], Catenate[pos]];
				{leftoverPorts, padPorts} = TakeDrop[ps[[2]], UpTo[Length[restPos]]];
				assignPorts[d2, {Inherited, Join[ReplacePart[outputs, Join[Thread[pos -> Inherited], Thread[Take[restPos, Length[leftoverPorts]] -> leftoverPorts]]], padPorts]}]
			]],
				assignPorts[newInputs[[-1, 1]], {Inherited, outputPorts}],
		        Reverse[Most[newInputs][[All, 1]]]
		    ]
		)
	],
	HoldForm[DiagramProduct[ds___]] :> ({Diagram[(DiagramProduct @@ #[[1]])["Flatten"], args], #[[2]]} & @ Fold[{state, d} |-> MapAt[Append[state[[1]], #] &, assignPorts[d, state[[2]]], {1}], {{}, ports}, {ds}]),
	HoldForm[DiagramSum[ds___]] :> ({Diagram[DiagramSum @@ #[[All, 1]], args], {Intersection @@ #[[2, All, 1]], Intersection @@ #[[2, All, 2]]}} & @ (assignPorts[#, ports] & /@ {ds})),
	_ :> {
		Diagram[diagram, args]
		,
		{
			If[inheritedQ[inputPorts], {}, Drop[inputPorts, UpTo[diagram["FlatInputArity"]]]],
			If[inheritedQ[outputPorts], {}, Drop[outputPorts, UpTo[diagram["FlatOutputArity"]]]]
		}
	}
}]
]

DiagramAssignPorts[d_Diagram, ports_] := First @ assignPorts[d, ports]

DiagramAssignPorts[d_Diagram] := DiagramAssignPorts[d, {PortDual /@ d["InputPorts"], d["OutputPorts"]}]


Options[DiagramDecompose] = {"Network" -> True, "Unary" -> False, "Decompose" -> True, "Ports" -> False, "Diagram" -> False}

DiagramDecompose[diagram_Diagram ? DiagramQ, lvl : (_Integer ? NonNegative) | Infinity : Infinity, opts : OptionsPattern[]] := If[TrueQ[diagram["OptionValue"["Decompose"], opts]] && lvl > 0,
    Replace[diagram["HoldExpression"], {
        HoldForm[Diagram[d_]] :> {DiagramDecompose[d, lvl - 1, opts]},
        HoldForm[DiagramProduct[ds___]] :> (DiagramDecompose[#, lvl - 1, opts] & /@ CircleTimes[ds]),
        HoldForm[DiagramComposition[ds___]] :> (DiagramDecompose[#, lvl - 1, opts] & /@ CircleDot[ds]),
        HoldForm[DiagramSum[ds___]] :> (DiagramDecompose[#, lvl - 1, opts] & /@ CirclePlus[ds]),
        HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]], DiagramDecompose[#, lvl - 1, opts] & /@ {ds}, diagram],
        If[ TrueQ[OptionValue["Unary"]],
            Splice @ {
                HoldForm[DiagramFlip[d_]] :> Transpose[DiagramDecompose[d, lvl - 1, opts], FindPermutation[Join[#1 + Range[#2], Range[#1]]] & @@ {diagram["OutputArity"], diagram["InputArity"]}],
                HoldForm[DiagramReverse[d_]] :> Transpose[DiagramDecompose[d, lvl - 1, opts], FindPermutation[Join[Reverse[Range[#1]], Reverse[#1 + Range[#2]]]] & @@ {diagram["OutputArity"], diagram["InputArity"]}],
                HoldForm[DiagramDual[d_]] :> SuperStar[DiagramDecompose[d, lvl - 1, opts]]
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
    d_Diagram :> Replace[prop, {Automatic :> Max[d["MaxGridArity"], 1], _ :> d[prop]}],
    (CircleTimes | CirclePlus)[ds___] :> Total[gridWidth[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Max[gridWidth[#, prop] & /@ {ds}],
    (Transpose | SuperStar)[d_, ___] :> gridWidth[d, prop],
    ({x_} | x_ -> _) :> gridWidth[x, prop],
    _ -> 1
}]

decompositionHeight[d_Diagram, args___] := gridHeight[DiagramDecompose[d], args]

gridHeight[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic -> 1, _ :> Replace[d[prop], Except[_Integer] -> 1]}],
    (CircleTimes | CirclePlus)[ds___] :> Max[gridHeight[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Total[gridHeight[#, prop] & /@ {ds}],
    (Transpose | SuperStar)[d_, ___] :> gridHeight[d, prop],
    ({x_} | x_ -> _) :> gridHeight[x, prop],
    _ -> 1
}]

circuitArrange[diagram_Diagram -> d_, pos_, {_, autoHeight_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0] := Block[{
    arity = diagram["MaxGridArity"], inputOrder, outputOrder, min, max,
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

gridArrange[diagram_Diagram -> d_, pos_, {autoWidth_, autoHeight_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0, _] := Block[{
    arity = diagram["MaxGridArity"],
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
        "Height" -> h,
        "Shape" -> Automatic
    ], "Item"];
    Diagram[diagram,
        "Center" -> Replace[diagram["OptionValue"["Center"]], {Automatic -> center, Offset[shift_] :> center + shift}],
        "Width" -> Replace[diagram["OptionValue"["Width"]], Automatic :> If[MatchQ[diagram["OptionValue"["Shape"]], "Circle"] || arity <= 1, 1, ratio * w]],
        "Height" -> Replace[diagram["OptionValue"["Height"]], Automatic :> Max[h - dy, 1]]
    ]
]

gridArrange[grid : (head : CircleTimes | CirclePlus)[ds___] -> d_, pos_, {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_, upHead_] := Block[{widths, relativeWidths, newHeight, positions},
    widths = gridWidth /@ {ds};
    relativeWidths = If[width =!= Automatic, width * widths / Total[widths], widths];
    newHeight = Replace[height, Automatic :> gridHeight[grid, "OptionValue"["Height"]] + dy * gridHeight[grid]];
    relativeWidths = FoldPairList[With[{x = Floor[#1 + #2]}, {x, #2 - x}] &, 0, relativeWidths];
    If[width =!= Automatic, relativeWidths[[-1]] = width - Total[Most[relativeWidths]]];
    positions = Prepend[Accumulate[relativeWidths * (1 + dx)], 0];
    With[{w = Total[relativeWidths] * (1 + dx), h = newHeight},
        Sow[pos -> Diagram[d,
            "Center" -> RotationTransform[angle, corner][corner + {w, h} / 2],
            "Width" -> Replace[d["OptionValue"["Width"]], Automatic -> w],
            "Height" -> Replace[d["OptionValue"["Height"]], Automatic -> h],
            "Background" -> Transparent,
            If[head =!= upHead =!= None, "Shape" -> Directive[EdgeForm[Dotted]], {}]
        ],
            "Row"
        ]
    ];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, Append[pos, i], {relativeWidths[[i]], newHeight}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {positions[[i]], 0}, angle, head]] &, grid]
]

gridArrange[grid : CircleDot[ds___] -> d_, pos_, {width_, height_}, {dx_, dy_}, corner : {xMin_, yMin_}, angle_, _] := Block[{heights, newWidth, positions},
    heights = gridHeight[#, "OptionValue"["Height"]] + gridHeight[#] * dy & /@ {ds};
    If[height =!= Automatic, heights = height * heights / Total[heights]];
    newWidth = Replace[width, Automatic :> gridWidth[grid]];
    positions = Prepend[Accumulate[heights], 0];
    With[{w = newWidth * (1 + dx), h = Total[heights]},
        Sow[pos -> Diagram[d,
            "Center" -> RotationTransform[angle, corner][corner + {w, h} / 2],
            "Width" -> Replace[d["OptionValue"["Width"]], Automatic -> w],
            "Height" -> Replace[d["OptionValue"["Height"]], Automatic -> h],
            "Background" -> Transparent
        ],
            "Column"
        ]
    ];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, Append[pos, i], {newWidth, heights[[i]]}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {0, positions[[i]]}, angle, CircleDot]] &, grid]
]

gridArrange[HoldPattern[SuperStar[d_]] -> diag_, args___] := gridArrange[CircleTimes[d] -> diag, args]

gridArrange[HoldPattern[Transpose[d_, perm___]] -> diag_, args___] := (Sow[{perm}, "Transpose"]; gridArrange[CircleTimes[d] -> diag, args])

gridArrange[ds_List -> d_, args___] := If[Length[ds] == 1,
    gridArrange[CircleTimes[ds[[1]]] -> d, args],
    gridArrange[DiagramNetwork @@ ds -> d, args]
]

gridArrange[grid_, gapSizes_, angle_] := gridArrange[grid, {}, {Automatic, Automatic}, gapSizes, {0, 0}, angle, None]


gridOutputPositions[_Diagram, pos_] := {pos}
gridOutputPositions[(CircleTimes | List)[ds___], pos_] := Catenate[MapIndexed[gridOutputPositions[#1, Join[pos, #2]] &, {ds}]]
gridOutputPositions[_CirclePlus, _] := {}
gridOutputPositions[CircleDot[d_, ___], pos_] := gridOutputPositions[d, Append[pos, 1]]
gridOutputPositions[(Transpose | SuperStar)[d_, ___], pos_] := gridOutputPositions[d, pos]
gridOutputPositions[grid_ -> _, pos_] := gridOutputPositions[grid, Append[pos, 1]]
gridOutputPositions[grid_] := gridOutputPositions[grid, {}]

gridInputPositions[_Diagram, pos_] := {pos}
gridInputPositions[(CircleTimes | List)[ds___], pos_] := Catenate[MapIndexed[gridInputPositions[#1, Join[pos, #2]] &, {ds}]]
gridInputPositions[_CirclePlus, _] := {}
gridInputPositions[CircleDot[ds___, d_], pos_] := gridInputPositions[d, Append[pos, Length[{ds}] + 1]]
gridInputPositions[(Transpose | SuperStar)[d_, ___], pos_] := gridInputPositions[d, pos]
gridInputPositions[grid_ -> _, pos_] := gridInputPositions[grid, Append[pos, 1]]
gridInputPositions[grid_] := gridInputPositions[grid, {}]

GridInputPorts[d_Diagram] := If[d["NodeQ"], d["TopPorts"], GridInputPorts[If[d["NetworkQ"], d["Arrange"], d]["Decompose", "Unary" -> True]]]
GridInputPorts[grid_] := Catenate[Extract[grid, gridInputPositions[grid], #["TopPorts"] &]]

GridOutputPorts[d_Diagram] := If[d["NodeQ"], d["BottomPorts"], GridOutputPorts[If[d["NetworkQ"], d["Arrange"], d]["Decompose", "Unary" -> True]]]
GridOutputPorts[grid_] := Catenate[Extract[grid, gridOutputPositions[grid], #["BottomPorts"] &]]

Options[DiagramGrid] = Join[{
    "HorizontalGapSize" -> 1,
    "VerticalGapSize" -> 1,
    "Rotate" -> 0,
    "Wires" -> True,
    "WireArrows" -> True,
    "WireLabels" -> True,
    "WireLabelFunction" -> Automatic,
    "Frames" -> Automatic,
    Spacings -> 1.6,
    Dividers -> None,
    Alignment -> Automatic
}, Options[DiagramArrange], Options[DiagramDecompose], Options[DiagramGraphics], Options[Graphics]
]
DiagramGrid[diagram_Diagram ? DiagramQ, opts : OptionsPattern[]] := Block[{
    grid, unlabeledGrid,
    width, height, items, rows, columns, transposes,
    outputPositions, inputPositions, positions,
    vGapSize = diagram["OptionValue"["VerticalGapSize"], opts],
    hGapSize = diagram["OptionValue"["HorizontalGapSize"], opts],
    angle = Replace[diagram["OptionValue"["Rotate"], opts], {Left -> - Pi / 2, Right -> Pi / 2, Top | True | Up -> Pi, None | False | Bottom | Down -> 0}],
    spacing = diagram["OptionValue"[Spacings], opts],
    wiresQ = TrueQ[diagram["OptionValue"["Wires"], opts]],
    wireLabelFunction = Replace[diagram["OptionValue"["WireLabelFunction"], opts], {Automatic | True -> (#3 &), None | False -> ("" &)}],
    diagramOptions = FilterRules[{opts}, Except[Options[Graphics], Options[DiagramGraphics]]],
    portFunction = diagram["PortFunction"],
    wireArrows = diagram["OptionValue"["WireArrows"], opts],
    wireLabels = diagram["OptionValue"["WireLabels"], opts],
    frames = diagram["OptionValue"["Frames"], opts],
    alignment = diagram["OptionValue"[Alignment], opts],
    dividers
},
    grid = DiagramDecompose[DiagramArrange[diagram, FilterRules[{opts}, Options[DiagramArrange]]], "Diagram" -> True, "Unary" -> True, FilterRules[{opts}, Options[DiagramDecompose]]];
    width = gridWidth[grid];
    height = gridHeight[grid];

    grid = grid /. d_Diagram :> Diagram[d,
        "Angle" -> d["OptionValue"["Angle"]] + angle,
        "Spacing" -> spacing,
        Alignment -> Replace[d["OptionValue"[Alignment]], Automatic -> alignment],
        "PortOrderingFunction" -> Replace[d["OptionValue"["PortOrderingFunction"]], Automatic :> diagram["OptionValue"["PortOrderingFunction"], opts]]
    ];

    (* TODO: do something with transpositions *)
    {items, rows, columns, transposes} = Lookup[Reap[grid = gridArrange[grid, {hGapSize, vGapSize}, angle], _, Rule][[2]], {"Item", "Row", "Column", "Transpose"}];

    outputPositions = gridOutputPositions[grid];
    inputPositions = gridInputPositions[grid];
    positions = Position[grid, _Diagram, All];

    unlabeledGrid = grid //
        MapAt[Diagram[#, "PortLabelFunction" -> (If[#3 === Top && ! #1["NeutralQ"], None, Placed[Inherited, {- 2 / 3, 1}]] &), "PortArrowFunction" -> (Nothing &), "PortLabels" -> None] &, Complement[positions, outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabelFunction" -> (If[#3 === Top && ! #1["NeutralQ"], None, Inherited] &), "PortArrowFunction" -> (If[#3 === Top && ! #1["NeutralQ"], Nothing, Automatic] &), "PortLabels" -> {None, Inherited}] &, Complement[outputPositions, inputPositions]] //
        MapAt[Diagram[#, "PortLabelFunction" -> (If[#3 === Top && ! #1["NeutralQ"], Inherited, Placed[Inherited, {- 2 / 3, 1}]] &), "PortArrowFunction" -> (If[#3 === Bottom && ! #1["NeutralQ"], Nothing, Automatic] &), "PortLabels" -> {Inherited, None}] &, Complement[inputPositions, outputPositions]];
    
    dividers = {
        FaceForm[None], EdgeForm[Directive[Thin, Black]],
        Switch[diagram["OptionValue"[Dividers], opts],
            All | Automatic, #["Graphics", "Background" -> Transparent, "LabelFunction" -> ("" &), "PortArrows" -> None, "PortLabels" -> None][[1]] & /@ items[[All, 2]],
            True, #["Graphics", "Background" -> Transparent, "LabelFunction" -> ("" &), "PortArrows" -> None, "PortLabels" -> None][[1]] & /@ Catenate[{rows, columns} /. _Missing -> Nothing][[All, 2]],
            _, Nothing
        ]
    };

    Graphics[
        Switch[frames,
            All | Automatic,
            With[{subDiagrams = #[[1]] -> Diagram[#[[2]],
                    "LabelFunction" -> ("" &),
                    "PortLabels" -> Placed[Automatic, {0, 0}],
                    "Width" -> Min[1, 0.95 ^ (Length[#[[1]]] / 2)] #[[2]]["OptionValue"["Width"]],
                    "Height" -> If[#[[1]] === {}, 1.1, Min[1, 0.85 ^ (Length[#[[1]]] / 2)]] #[[2]]["OptionValue"["Height"]]
                ]["Flatten"] & /@ If[
                    frames === Automatic,
                    DeleteCases[
                        (pos_ -> d_Diagram) /; With[{portFunction = d["PortFunction"]},
                            ! (pos === {} && d["NeutralArity"] > 0) &&
                            portFunction /@ d["Flat"["TopPorts", True]] === Catenate[Extract[grid, {pos}, portFunction /@ PortDual /@ GridInputPorts[#] &]] &&
                            portFunction /@ d["Flat"["BottomPorts"]] === Catenate[Extract[grid, {pos}, portFunction /@ GridOutputPorts[#] &]]
                        ]
                    ], Identity
                ] @ Replace[Catenate[{rows, columns} /. _Missing -> Nothing], {} -> items]
            },
            {subDiagramLevels = KeyDrop[None] @ GroupBy[subDiagrams, If[# === {}, None, Most[#]] & @* First]},
                {
                    (pos |-> Extract[unlabeledGrid,
                        {pos},
                       Diagram[#, "DiagramOptions" -> Join[
                                diagramOptions,
                                If[ AnyTrue[subDiagrams[[All, 1]], Take[pos, UpTo[Length[#]]] === # &],
                                    {"PortArrowFunction" -> Function[{PointSize[0.003], Point[#2[[1]]]}], "PortLabels" -> Placed[Automatic, {0.1, .5}]},
                                    {}
                                ],
                                #["DiagramOptions"]
                            ]
                        ]["Graphics"][[1]] &
                    ]) /@ positions,
                    If[ wiresQ, {
                        gridFrameWires[grid, {}, subDiagrams,
                            With[{d = Lookup[subDiagrams, Key[{}]]}, If[MissingQ[d], {}, makeInputRules[d, portFunction, True]]],
                            portFunction,
                            "WireArrows" -> wireArrows, "WireLabels" -> wireLabels, "WireLabelFunction" -> wireLabelFunction, "GapSize" -> vGapSize
                        ]
                    },
                        Nothing
                    ],
                    gridNetworkWires[grid, Lookup[subDiagrams, Key[{}]], portFunction, "WireArrows" -> wireArrows, "WireLabels" -> wireLabels, "WireLabelFunction" -> wireLabelFunction, "GapSize" -> hGapSize],
                    #[[2]]["Graphics",
                        "PortArrowFunction" -> Function[{EdgeForm[LightGray], FaceForm[Directive[Opacity[1], White]], Disk[#2[[1]], Offset[10]]}]
                    ][[1]] & /@ subDiagrams,
                    dividers
                }
            ],
            _,
            {
                Cases[unlabeledGrid,
                    d_Diagram :> Diagram[d, "PortArrows" -> None, "DiagramOptions" -> Join[diagramOptions, d["DiagramOptions"]]]["Graphics"][[1]],
                    All
                ],
                If[wiresQ, gridWires[grid, {}, portFunction, "WireArrows" -> wireArrows, "WireLabels" -> wireLabels, "WireLabelFunction" -> wireLabelFunction, "GapSize" -> vGapSize], Nothing],
                gridNetworkWires[grid, Missing[], portFunction, "WireArrows" -> wireArrows, "WireLabels" -> wireLabels, "WireLabelFunction" -> wireLabelFunction, "GapSize" -> hGapSize],
                dividers
            }
        ],
        FilterRules[{opts}, Options[Graphics]],
        FormatType -> StandardForm,
        BaseStyle -> {
            GraphicsHighlightColor -> Automatic
        }
    ]
]


wireGraphics[opts___][{outPort_, out_, outStyle_, outLabel_}, {inPort_, in_, inStyle_, inLabel_}] := With[{
    inDual = inPort["DualQ"],
    outDual = outPort["DualQ"],
    wireArrows = OptionValue[{opts}, "WireArrows"],
    wireLabels = OptionValue[{opts}, "WireLabels"],
    wireLabelFunction = OptionValue[{opts}, "WireLabelFunction"],
    gapSize = OptionValue[{opts}, "GapSize"]
},
    If[
        inStyle === outStyle || inStyle === Automatic || outStyle === Automatic,
        With[{style = Replace[outStyle, Automatic :> Replace[inStyle, Automatic -> {}]]},
            If[
                MatchQ[style, None],
                {}
                ,
                With[{arrowheads = Arrowheads[
                        With[{arrowSize = Replace[wireArrows, {False | None -> 0, True -> Small}], from = If[outDual, -1, 1], to = If[inDual, -1, 1]},
                            If[ from == - to,
                                {{from * arrowSize, .5}},
                                {{from * arrowSize, .3}, {to * arrowSize, .7}}
                            ]
                        ]
                    ]
                },
                    If[ MatchQ[style, _Function],
                        {arrowheads, style[#, "Grid"]} &,
                        {arrowheads, style, Arrow @ BSplineCurve @ #} &
                    ]
                ] @ With[{p = out[[1]] + gapSize (out[[2]] - out[[1]]), q = in[[1]] + gapSize (in[[2]] - in[[1]])},
                    If[
                        Dot[p - q, out[[1]] - in[[1]]] > 0,
                        {out[[1]], p, q, in[[1]]},
                        {out[[1]], in[[1]]}
                    ]
                ]
            ]
        ]
        ,
        With[{
            arrowSize = Replace[wireArrows, {False | None -> 0, True -> Small}],
            from = If[outDual, -1, 1], to = If[inDual, -1, 1],
            p = out[[1]] + gapSize (out[[2]] - out[[1]]), q = in[[1]] + gapSize (in[[2]] - in[[1]])
        },
            {
                If[ outStyle === None,
                    {},
                    With[{arrowheads = Arrowheads[{{from * arrowSize, .5}}]},
                        If[MatchQ[outStyle, _Function], {arrowheads, outStyle[#, "Grid"]} &, {arrowheads, outStyle, Arrow @ BSplineCurve @ #} &] @ {out[[1]], p, (in[[1]] + out[[1]]) / 2}
                    ]
                ]
                ,
                If[ inStyle === None,
                    {},
                    With[{arrowheads = Arrowheads[{{to * arrowSize, .7}}]},
                        If[MatchQ[inStyle, _Function], {arrowheads, inStyle[#, "Grid"]} &, {arrowheads, inStyle, Arrow @ BSplineCurve @ #} &] @  {(in[[1]] + out[[1]]) / 2, q, in[[1]]}
                    ]
                ]
            }
        ]
    ] // Append[
        With[{label = Replace[Replace[inLabel, {Automatic -> outLabel, _ -> inLabel}], {Placed[Automatic | True, _] | Automatic | True -> outPort, Placed[l_, _] :> l}]},
            If[ MatchQ[wireLabels, None | False] || MatchQ[label, None | False], Nothing,
                Text[ClickToCopy[wireLabelFunction[out, in, label]], (out[[1]] + in[[1]]) / 2 + 0.1 RotationTransform[Replace[wireLabels, Automatic | True -> Pi / 2]] @ Normalize[out[[1]] - in[[1]]]],
                Nothing
            ]
        ]
    ]
]


makeRules[keys_, ports_, arrows_, styles_, labels_, dualQ_] :=
    Thread[
        keys -> Thread[{
            If[dualQ, Map[PortDual], Identity] @ ports,
            If[dualQ, {#1, #1 + (#1 - #2)} & @@@ # &, Identity] @ arrows,
            styles,
            labels
        }]
    ]

makeRules[keys_, ports_, arrows_, styles_, labels_, dualQ_, pick_] := makeRules[Pick[keys, pick], Pick[ports, pick], Pick[arrows, pick], Pick[styles, pick], Pick[labels, pick], dualQ]

makeInputRules[diagram_, portFunction_, dualQ_ : False, flatSumQ_ : False] := With[{ports = diagram["InputPorts"]},
    If[flatSumQ, flattenSumRules, Identity] @ flattenProductRules @
        makeRules[portFunction /@ PortDual /@ ports, ports, diagram["PortArrows"][[1]], diagram["PortStyles"][[1]], diagram["PortLabels"][[1]], dualQ, Not /@ Through[ports["NeutralQ"]]]
]

makeOutputRules[diagram_, portFunction_, dualQ_ : False, flatSumQ_ : False] := With[{ports = diagram["OutputPorts"]},
     If[flatSumQ, flattenSumRules, Identity] @ flattenProductRules @
        makeRules[portFunction /@ ports, ports, diagram["PortArrows"][[2]], diagram["PortStyles"][[2]], diagram["PortLabels"][[2]], dualQ, Not /@ Through[ports["NeutralQ"]]]
]

makeNeutralRules[diagram_, portFunction_, dualQ_ : False, flatSumQ_ : False] := With[
    {inputPorts = diagram["InputPorts"], outputPorts = diagram["OutputPorts"]},
    {inputPick = #["NeutralQ"] & /@ inputPorts, outputPick = #["NeutralQ"] & /@ outputPorts},

    If[flatSumQ, flattenSumRules, Identity] @ flattenProductRules @ makeRules[
        portFunction /@ Join[PortDual /@ Pick[inputPorts, inputPick], Pick[outputPorts, outputPick]],
        Join[Pick[inputPorts, inputPick], Pick[outputPorts, outputPick]],
        Catenate @ MapThread[Pick, {diagram["PortArrows"], {inputPick, outputPick}}],
        Catenate @ MapThread[Pick, {diagram["PortStyles"], {inputPick, outputPick}}],
        Catenate @ MapThread[Pick, {diagram["PortLabels"], {inputPick, outputPick}}],
        dualQ
    ]
]

flattenProductRules[rules_] := Replace[rules, {
    (HoldForm[CircleTimes[zs___]] -> {p_, ps___}) :> Splice[Map[# -> {p, ps} &, List @@ HoldForm /@ (FlattenAt[#, Position[#, _CircleTimes]] & @ Hold[zs])]],
    (HoldForm[CirclePlus[zs___]] -> {p_, ps___}) :> HoldForm[CirclePlus[zs]] -> {p, ps},
    (HoldForm[Superscript[x_, y_]] -> {p_, ps___}) :> Splice[Map[# -> {p, ps} &, HoldForm /@ Unevaluated[{SuperStar[x], y}]]]
}, 1]

flattenSumRules[rules_] := Replace[rules, {
    (HoldForm[CirclePlus[zs___]] -> {p_, ps___}) :> Splice[Map[# -> {p, ps} &,
        List @@ HoldForm /@ Flatten[Replace[Hold[zs], CircleTimes[xs__] :> Hold[xs], 1], 1,Hold]
    ]]
}, 1]

mergeRules[xs_, ys_] := Catenate @ KeyValueMap[{k, v} |->
    k -> # & /@ Thread[PadRight[v, {Automatic, Min[Length /@ v]}]],
    Select[Merge[KeyUnion[GroupBy[#, First, Map[Last]] & /@ {xs, ys}], Identity], MatchQ[{_List, _List}]]
]


gridWires[CirclePlus[ds___], args___] := gridWires[#, args] & /@ {ds}

gridWires[(Transpose | SuperStar)[d_, ___], args___] := gridWires[d, args]

gridWires[CircleTimes[ds___], ports_, portFunction_, opts___] :=
    Fold[
        With[
            {inputs = Join @@ Extract[#2, gridInputPositions[#2], makeInputRules[#, portFunction] &]},
            {merge = mergeRules[#1[[2]], inputs]},
            {
                Join[#1[[1]], wireGraphics[opts] @@@ Values[merge], gridWires[#2, {}, portFunction, opts]],
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
    inputs = Join @@ Extract[d, inputPos, makeInputRules[#, portFunction] &];
    outputs = Join @@ Extract[d, outputPos, makeOutputRules[#, portFunction] &];
    merge = mergeRules[ports, inputs];
    
    Join[
        wireGraphics[opts] @@@ Values[merge],
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
            inputs = Join @@ Extract[subGrid, inputPos, makeInputRules[#, portFunction, False, False] &];
            outputs = Join @@ Extract[subGrid, outputPos, makeOutputRules[#, portFunction, False, False] &];
            mergeInput = mergeRules[makeInputRules[diagram, portFunction, True], inputs];
            mergeOutput = mergeRules[makeOutputRules[diagram, portFunction, True], outputs];
            
            wireGraphics[opts] @@@ Values[#] & /@ {mergeInput, mergeOutput}
        ]
    ] & /@ diagrams,
    2
]


gridFrameWires[(Transpose | SuperStar)[d_, ___], pos_, args___] := gridFrameWires[d, Append[pos, 1], args]

gridFrameWires[{d_} | d_Diagram, args___] := gridFrameWires[CircleTimes[d], args]

gridFrameWires[(head : CircleTimes | CirclePlus)[ds___], pos_, frameDiagrams_, initPorts_, defPortFunction_, opts___] := Block[{
    diagram = Lookup[frameDiagrams, Key[pos]], sumQ = head === CirclePlus, upInputs = None, upOutputs = None, inputs, outputs, merge = {}, ports = initPorts, portFunction = defPortFunction
},
    If[ ! MissingQ[diagram],
        portFunction = diagram["PortFunction"];
        upInputs = makeInputRules[diagram, portFunction, True, sumQ];
        upOutputs = makeOutputRules[diagram, portFunction, True, sumQ];
        merge = mergeRules[ports, upInputs];
        ports = upInputs
    ];
    Join[
        Fold[(
            diagram = Lookup[frameDiagrams, Key[Append[pos, #1[[3]]]]];
            If[ MissingQ[diagram],
                inputs = Join @@ Extract[#2, gridInputPositions[#2], makeInputRules[#, portFunction] &];
                outputs = Join @@ Extract[#2, gridOutputPositions[#2], makeOutputRules[#, portFunction] &];
                merge = mergeRules[#1[[2]], inputs]
                ,
                inputs = makeInputRules[diagram, portFunction, False, sumQ];
                outputs = makeOutputRules[diagram, portFunction, False, sumQ];
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
                    #1[[1]], wireGraphics[opts] @@@ Values[merge]
                    ,
                    If[ DiagramQ[#2], {},
                        gridFrameWires[#2, Append[pos, #1[[3]]], frameDiagrams, If[MissingQ[diagram], {}, makeInputRules[diagram, portFunction, True, sumQ]], portFunction, opts]
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

gridFrameWires[CircleDot[ds___, d_], pos_, frameDiagrams_, initPorts_, defPortFunction_, opts___] := Block[{
    inputPos = gridInputPositions[d],
    outputPos = gridOutputPositions[d],
    upOutputPorts, downInputPorts, downOutputPorts, inputs, outputs, merge = {}, merge1, merge2,
    diagramUp = Lookup[frameDiagrams, Key[pos]],
    diagramDown = Lookup[frameDiagrams, Key[Append[pos, Length[{ds}] + 1]]],
    ports = initPorts,
    portFunction = defPortFunction
},
    If[ MissingQ[diagramDown],
        inputs = Join @@ Extract[d, inputPos, makeInputRules[#, portFunction] &];
        outputs = Join @@ Extract[d, outputPos, makeOutputRules[#, portFunction] &];
        merge = mergeRules[ports, inputs];
        ports = Join[outputs, DeleteElements[ports, 1 -> MapAt[First, merge, {All, 2}]]]
        ,
        downInputPorts = makeInputRules[diagramDown, portFunction];
        downOutputPorts = makeOutputRules[diagramDown, portFunction, True];
        outputs = Catenate @ Map[
            With[{diagramUp = Lookup[frameDiagrams, Key[Join[pos, {Length[{ds}] + 1}, Most[#]]], First[Extract[d, {#}]]]},
                makeOutputRules[diagramUp, portFunction]
            ] &,
            outputPos
        ];
        merge1 = mergeRules[ports, downInputPorts];
        merge2 = mergeRules[outputs, downOutputPorts];
        merge = Join[merge1, {}];
        portFunction = diagramDown["PortFunction"];
        ports = Join[
            makeOutputRules[diagramDown, portFunction],
            DeleteElements[ports, 1 -> MapAt[First, merge1, {All, 2}]]
        ]
    ];
    portFunction = defPortFunction;
    If[ ! MissingQ[diagramUp] && Length[{ds}] == 0,
        portFunction = diagramUp["PortFunction"];
        upOutputPorts = makeOutputRules[diagramUp, portFunction, True];
        merge = Join[merge, mergeRules[Join[ports, outputs], upOutputPorts]];
        ports = Join[DeleteElements[Join[ports, outputs], 1 -> MapAt[First, merge, {All, 2}]], upOutputPorts]
    ];
    Join[
        wireGraphics[opts] @@@ Values[merge],
        gridFrameWires[d, Append[pos, Length[{ds}] + 1], frameDiagrams, {}, portFunction, opts],
        gridFrameWires[CircleDot[ds], pos, frameDiagrams, ports, portFunction, opts]
    ]
]


gridFrameWires[___] := {}


gridNetworkWires[grid_, frame_, portFunction_, opts___] := With[{
    rules = Join[
        Catenate @ Cases[grid, d_Diagram /; d["NodeQ"] :> makeNeutralRules[d, portFunction], All],
        If[MissingQ[frame], {}, makeNeutralRules[frame, portFunction, True]]
    ]
},
    wireGraphics[opts] @@@ Values @ Catenate[mergeRules[{#}, rules] & /@ rules]
]



End[];

EndPackage[];

