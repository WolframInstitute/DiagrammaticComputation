BeginPackage["Wolfram`DiagrammaticComputation`Diagram`Grid`", {"Wolfram`DiagrammaticComputation`Port`", "Wolfram`DiagrammaticComputation`Diagram`", "Wolfram`DiagrammaticComputation`Utilities`", "Wolfram`DiagrammaticComputation`Diagram`Surgery`"}];

ColumnDiagram
RowDiagram
DiagramGrid

DiagramArrange
DiagramDecompose

DiagramMatchPorts
DiagramAssignPorts

GridInputPorts
GridOutputPorts

DiagramGridWidth
DiagramGridHeight
DiagramGridWidthHeight

DiagramGridTree

Begin["Wolfram`DiagrammaticComputation`Diagram`Grid`Private`"];

{$Black, $White} = If[$VersionNumber >= 14.3, {LightDarkSwitched[Black, White], LightDarkSwitched[White, Black]}, {Black, White}]


(* compose vertically preserving grid structure *)

identityDiagrams[ports_, styles_] := Splice @ MapThread[IdentityDiagram[#1, "PortArrows" -> {#2}] &, {ports, styles}]

permuteRow[a_Diagram, aPorts_List, bPorts_List, i : 1 | -1, rowSortQ : _ ? BooleanQ : False] :=
    Which[
        a["Head"] === DiagramProduct,
            With[{row = a["SubDiagrams"]}, {len = Length[row], arities = Through[row[Switch[i, 1, "OutputArity", -1, "InputArity"]]]},
                Replace[permuteRow[row, TakeList[aPorts, arities], bPorts, i, rowSortQ],
                    {changedQ_, newRow_, newPorts_} :> {
                        changedQ,
                        If[! changedQ, a, DiagramProduct[newRow, FilterRules[a["DiagramOptions"], Except["PortArrows" | "PortLabels"]]]],
                        newPorts
                    }
                ]
            ],
        a["Head"] === DiagramComposition,
            With[{as = a["SubDiagrams"], f = a["PortFunction"], opts = FilterRules[a["DiagramOptions"], Except["PortArrows" | "PortLabels"]]},
                With[{changedQ = Or @@ #[[All, 1]]}, {changedQ, If[changedQ, ColumnDiagram[Switch[i, 1, Reverse[#[[All, 2]]], -1, #[[All, 2]]], opts], a], #[[1, 3]]}] & @ FoldPairList[
                    With[{new = permuteRow[#2, f /@ Switch[i, 1, #2["OutputPorts"], -1, PortDual /@ #2["InputPorts"]], #1, i, rowSortQ]},
                        {
                            new,
                            f /@ Switch[i, 1, PortDual /@ new[[2]]["InputPorts"], -1, new[[2]]["OutputPorts"]]
                        }
                    ] &,
                    bPorts,
                    Switch[i, 1, as, -1, Reverse[as]]
                ]
            ],
        True,
            With[{
                perm = If[
                    Length[aPorts] <= 9 && MatchQ[a["OptionValue"["FloatingPorts"]], True | Switch[i, 1, {_, True}, -1, {True, _}]],
                    FindPermutation[
                        aPorts,
                        First @ MaximalBy[
                            Permutations[aPorts],
                            - DamerauLevenshteinDistance[#, bPorts] &,
                            1
                        ]
                    ],
                    Cycles[{}]
                ]
            },
                If[ perm === Cycles[{}],
                    {False, a, aPorts},
                    {True, a[Switch[i, 1, "PermuteOutput", -1, "PermuteInput"], perm], Permute[aPorts, perm]}
                ]
            ]
    ]

permuteRow[row : {__Diagram}, rowPorts_List, ports_List, i : 1 | -1, rowSortQ : _ ? BooleanQ : False] := With[{
    padPorts = MapThread[Replace[#1, Missing[] -> #2] &, {Switch[i, 1, PadRight, -1, PadLeft][ports, Total[Length /@ rowPorts], Missing[]], Catenate[rowPorts]}]
},
    If[ ! rowSortQ || Length[rowPorts] > 9,
        {Or @@ #1, #2, Catenate[#3]} & @@ Thread @ MapThread[permuteRow[##, i, rowSortQ] &, {row, rowPorts, TakeList[padPorts, Length /@ rowPorts]}],
        With[{perm = FindPermutation[rowPorts, First @ MaximalBy[Permutations @ rowPorts, - DamerauLevenshteinDistance[Catenate[#], padPorts] &, 1]]},
            {perm =!= Cycles[{}] || Or @@ #1, #2, Catenate[#3]} & @@ Thread @ MapThread[permuteRow[##, i, rowSortQ] &, {Permute[row, perm], Permute[rowPorts, perm], TakeList[padPorts, Length /@ Permute[rowPorts, perm]]}]
        ]
    ]
]

PermutationDecompose[perm_List ? PermutationListQ] := Switch[Length[perm], 0, {}, 1, {perm}, _,
	Prepend[PermutationDecompose[PermutationList[InversePermutation @ FindPermutation[#2], Length[#2]]], #1] & @@ NestWhile[Apply[{Append[#1, First[#2]], Rest[#2]} &], TakeDrop[perm, 1], Apply[! PermutationListQ[#1] &]]
]

PermutationCompose[perms : {___ ? PermutationListQ}] := Fold[Join[#1, #2 + Length[#1]] &, {}, perms]

Options[ColumnDiagram] := Join[{"PortOrderingFunction" -> Automatic, "Direction" -> Down, "RowSort" -> False, "PassThrough" -> False, "PermutationDecompose" -> True}, Options[Diagram]]

ColumnDiagram[{x_Diagram ? DiagramQ, y_Diagram ? DiagramQ}, opts : OptionsPattern[]] := Module[{
    func = OptionValue["PortFunction"],
    a, b, pa, pb,
    as, bs,
    aStyles, bStyles,
    aPorts, bPorts,
    resetPortsA, resetPortsB,
    rowSortQ = TrueQ[OptionValue["RowSort"]]
},
    a = x["FlattenOutputs"];
    b = y["FlattenInputs"];
    resetPortsA[] := (
        as = a["OutputPorts"];
        pa = Not /@ Through[as["NeutralQ"]];
        as = Pick[as, pa];
        aPorts = func /@ as;
        aStyles = Pick[a["PortStyles"][[2]], pa];
    );
    resetPortsB[] := (
        bs = PortDual /@ b["InputPorts"];
        pb = Not /@ Through[bs["NeutralQ"]];
        bs = Pick[bs, pb];
        bPorts = func /@ bs;
        bStyles = Pick[b["PortStyles"][[1]], pb];
    );

    resetPortsA[];
    resetPortsB[];
    aStyles = a["PortStyles"];
    bStyles = b["PortStyles"];
    If[ ContainsNone[aPorts, bPorts],
        If[ aPorts === {} && bPorts === {},
            Return[DiagramRightComposition[a, b, "ColumnPorts" -> False, FilterRules[{opts}, Options[DiagramComposition]]]],
            Return[RowDiagram[{a, b}, FilterRules[{opts}, Options[RowDiagram]]]]
        ]
    ];

    If[ TrueQ[OptionValue["PassThrough"]],
        Return[Diagram[
            DiagramRightComposition[a, b, "ColumnPorts" -> False, FilterRules[{opts}, Options[DiagramComposition]]],
            Sequence @@ MapThread[Join, Prepend[{PortDual /@ a["InputPorts"], b["OutputPorts"]}] @ Cases[SequenceAlignment[bPorts, aPorts, Method -> "Local"], {__List}]]
        ]]
    ];

    aStyles = Pick[aStyles[[2]], pa];
    bStyles = Pick[bStyles[[1]], pb];
    
    Replace[SequenceAlignment[Reverse[aPorts], Reverse[bPorts], Method -> "Local"], {
        {left : {l_, {}} | {{}, l_} : {}, {__}, right : {r_, {}} | {{}, r_} : {}} /; ! ({l} =!= {} && {r} =!= {} && IntersectingQ[l, r]) :> (
            Which[
                MatchQ[left, {_, {}}],
                    b = RowDiagram[permuteRow[{b, identityDiagrams[Take[as, - Length[l]], Take[aStyles, - Length[l]]]}, Join[{bPorts}, List /@ Take[aPorts, - Length[l]]], aPorts, -1, rowSortQ][[2]]];
                    resetPortsB[]
                ,
                MatchQ[left, {{}, _}],
                    a = RowDiagram[permuteRow[{a, identityDiagrams[Take[bs, - Length[l]], Take[bStyles, - Length[l]]]}, Join[{aPorts}, List /@ Take[bPorts, - Length[l]]], bPorts, 1, rowSortQ][[2]]];
                    resetPortsA[]
            ];
            Which[
                MatchQ[right, {_, {}}],
                    b = RowDiagram[permuteRow[{identityDiagrams[Take[as, Length[r]], Take[aStyles, Length[r]]], b}, Join[List /@ Take[aPorts, Length[r]], {bPorts}], aPorts, -1, rowSortQ][[2]]];
                    resetPortsB[],
                MatchQ[right, {{}, _}],
                    a = RowDiagram[permuteRow[{identityDiagrams[Take[bs, Length[r]], Take[bStyles, Length[r]]], a}, Join[List /@ Take[bPorts, Length[r]], {aPorts}], bPorts, 1, rowSortQ][[2]]];
                    resetPortsA[]
            ]
        ),
        _ :> Block[{inPos, outPos, ins, outs},
            inPos = FirstPositions[bPorts, aPorts];
            ins = Delete[bs, inPos];
            If[ins =!= {}, a = RowDiagram[permuteRow[{identityDiagrams[ins, Delete[bStyles, inPos]], a}, Join[List /@ Delete[bPorts, inPos], {aPorts}], bPorts, 1, rowSortQ][[2]]]; resetPortsA[]];
            outPos = FirstPositions[aPorts, bPorts];
            outs = Delete[as, outPos];
            If[outs =!= {}, b = RowDiagram[permuteRow[{b, identityDiagrams[outs, Delete[aStyles, outPos]]}, Join[{bPorts}, List /@ Delete[aPorts, outPos]], aPorts, -1, rowSortQ][[2]]]; resetPortsB[]]
        ]
    }
    ];

    Replace[permuteRow[a, aPorts, bPorts, 1, rowSortQ], {True, newA_, _} :> (a = newA; resetPortsA[])];
    Replace[permuteRow[b, bPorts, aPorts, -1, rowSortQ], {True, newB_, _} :> (b = newB; resetPortsB[])];

    aStyles = a["PortStyles"];
    bStyles = b["PortStyles"];
	Which[
		aPorts === bPorts,
		DiagramComposition[Diagram[b, "PortArrows" -> MapAt[MapThread[If[#1 === Automatic, #2, #1] &, {#, aStyles[[2]]}] &, {1}] @ b["PortStyles"]], a, "ColumnPorts" -> False, FilterRules[{opts}, Options[DiagramComposition]]],
		aPorts === Reverse[bPorts] && a["WireQ"],
        DiagramComposition[Diagram[b, "PortArrows" -> MapAt[MapThread[If[#1 === Automatic, #2, #1] &, {#, Reverse @ aStyles[[2]]}] &, {1}] @ b["PortStyles"]], DiagramReverse[a], "ColumnPorts" -> False, FilterRules[{opts}, Options[DiagramComposition]]],
        aPorts === Reverse[bPorts] && b["WireQ"],
        DiagramComposition[DiagramReverse[b, "PortArrows" -> MapAt[MapThread[If[#1 === Automatic, #2, #1] &, {#, aStyles[[2]]}] &, Reverse /@ b["PortStyles"], {1}]], a, "ColumnPorts" -> False, FilterRules[{opts}, Options[DiagramComposition]]],
		Sort[aPorts] === Sort[bPorts],
        With[{perm = FindPermutation[aPorts, bPorts]},
            DiagramComposition[
                Diagram[b, "PortArrows" -> MapAt[MapThread[If[#1 === Automatic, #2, #1] &, {#, Permute[aStyles[[2]], perm]}] &, {1}] @ b["PortStyles"]],
                If[ TrueQ[OptionValue["PermutationDecompose"]],
                    With[{decomp = PermutationDecompose[PermutationList[perm, Length[as]]]}, {lens = Length /@ decomp},
                        DiagramProduct @ MapThread[{as, bs, aStyles, bStyles, perm} |->
                            PermutationDiagram[as -> bs, perm, "PortArrows" -> MapAt[Permute[#, perm] &, {2}] @ Thread @ MapThread[
                                PadRight[#, 2, Replace[#, {} -> Automatic]] & @ DeleteCases[Automatic] @ Which[! #1["DualQ"] && #2["DualQ"], {#3, #3, #4}, #1["DualQ"] && ! #2["DualQ"], {#4, #4, #3}, True, {#3, #4}] &,
                                {as, bs, aStyles, Permute[bStyles, InversePermutation[perm]]}
                            ]],
                            Append[TakeList[#, lens] & /@ {as, bs, Pick[aStyles[[2]], pa], Pick[bStyles[[1]], pb]}, PermutationCycles /@ decomp]
                        ]
                    ]
                    ,
                    PermutationDiagram[
                        as -> bs,
                        perm,
                        "PortArrows" -> MapAt[Permute[#, perm] &, {2}] @ Thread @ MapThread[
                            PadRight[#, 2, Replace[#, {} -> Automatic]] & @ DeleteCases[Automatic] @ Which[! #1["DualQ"] && #2["DualQ"], {#3, #3}, #1["DualQ"] && ! #2["DualQ"], {#4, #4}, True, {#3, #4}] &,
                            {as, bs, Pick[aStyles[[2]], pa], Permute[Pick[bStyles[[1]], pb], InversePermutation[perm]]}
                        ]
                    ]
                ],
                a,
                "ColumnPorts" -> False,
                FilterRules[{opts}, Options[DiagramComposition]]
            ]
        ],
		True,
		$Failed
	]
]

ColumnDiagram[{}, opts : OptionsPattern[]] := EmptyDiagram[opts]

ColumnDiagram[xs : {__Diagram}, opts : OptionsPattern[]] := If[
    MatchQ[OptionValue["Direction"], Up | Top]
    ,
    Fold[ColumnDiagram[{#2, #1}, opts] &, Reverse[xs]]
    ,
    Fold[ColumnDiagram[{##}, opts] &, xs]
]
    


(* compose horizontally preserving height *)

Options[RowDiagram] := Join[{"PadHeight" -> True}, Options[ColumnDiagram]]
RowDiagram[{x_Diagram, y_Diagram}, opts : OptionsPattern[]] := Block[{a, b, aPorts, bPorts, ha, hb, aStyles, bStyles},
    If[! TrueQ[OptionValue["PadHeight"]], Return[DiagramProduct[x, y, FilterRules[{opts}, Options[DiagramProduct]]]]];
    a = x["FlattenInputs", 1];
    b = y["FlattenOutputs", 1];
	aPorts = Through[a["InputPorts"]["Dual"]];
	bPorts = b["OutputPorts"];
    ha = DiagramGridHeight[a];
    hb = DiagramGridHeight[b];
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

RowDiagram[{}, opts : OptionsPattern[]] := EmptyDiagram[opts]

RowDiagram[xs : {__Diagram}, opts : OptionsPattern[]] := Fold[RowDiagram[{##}, opts] &, xs]


setDiagram[diagram1_, diagram2_, opts___] := Diagram[diagram1, Function[Null, "Expression" :> ##, HoldAll] @@ diagram2["HoldExpression"], "PortFunction" -> diagram2["PortFunction"], FilterRules[{opts}, Options[Diagram]]]


Options[DiagramArrange] := DeleteDuplicatesBy[First] @ Join[{"Network" -> True, "Arrange" -> True, "NetworkMethod" -> "GridFoliation", "AssignPorts" -> False}, Options[RowDiagram], Options[ColumnDiagram], Options[DiagramsNetGraph]]

DiagramArrange[diagram_Diagram, opts : OptionsPattern[]] := Enclose @ If[
    (TrueQ[diagram["OptionValue"["Arrange"], opts]] || diagram["NetworkQ"]) && TrueQ[diagram["OptionValue"["Decompose"], opts]]
    ,
    Replace[diagram["HoldExpression"], {
        HoldForm[Diagram[d_]] :> setDiagram[diagram, SingletonDiagram[DiagramArrange[d, opts], FilterRules[{opts, diagram["DiagramOptions"]}, Options[SingletonDiagram]]], opts],
        HoldForm[DiagramProduct[ds___]] :> setDiagram[diagram, RowDiagram[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, diagram["DiagramOptions"]}, Options[RowDiagram]]], opts],
        HoldForm[DiagramComposition[ds___]] :> setDiagram[diagram, ColumnDiagram[DiagramArrange[#, opts] & /@ Reverse[{ds}], FilterRules[{opts, diagram["DiagramOptions"]}, Options[ColumnDiagram]]], opts],
        HoldForm[DiagramSum[ds___]] :> setDiagram[diagram, DiagramSum[##, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramSum]]] & @@ (DiagramArrange[#, opts] & /@ {ds}), opts],
        HoldForm[DiagramNetwork[ds___]] :> If[TrueQ[OptionValue["Network"]],
            With[{g = ConfirmBy[
                DiagramsNetGraph[DiagramArrange[#, opts] & /@ {ds}, FilterRules[{opts, "RemoveCycles" -> True, "BinarySpiders" -> Automatic, diagram["DiagramOptions"]}, Options[DiagramsNetGraph]], "UnarySpiders" -> False],
                AcyclicGraphQ
            ]},
                If[ TrueQ[OptionValue["AssignPorts"]], DiagramAssignPorts[#, diagram["GraphInputOutputPorts", True]] &, Identity] @
                    Diagram[#, FilterRules[{opts, diagram["DiagramOptions"], "RowSort" -> True}, Options[Diagram]]] & @
                        Switch[OptionValue["NetworkMethod"],
                            "TopologicalSort", RightComposition @@ (Diagram[#, "Center" -> Automatic] & /@ AnnotationValue[{g, TopologicalSort[g]}, "Diagram"]),
                            "Stratify", RightComposition @@ (CircleTimes @@ (Diagram[#, "Center" -> Automatic] & /@ AnnotationValue[{g, Developer`FromPackedArray[#]}, "Diagram"]) & /@ ResourceFunction["VertexStratify"][g]),
                            "Foliation", RightComposition @@ (CircleTimes @@ (Diagram[#, "Center" -> Automatic] & /@ AnnotationValue[{g, #}, "Diagram"]) & /@ First[ResourceFunction["GraphFoliations"][g, MaxItems -> 1, Direction -> Top]]),
                            "RandomFoliation", RightComposition @@ (CircleTimes @@ (Diagram[#, "Center" -> Automatic] & /@ AnnotationValue[{g, #}, "Diagram"]) & /@ RandomChoice[ResourceFunction["GraphFoliations"][g, "IncludePermutations" -> True, Direction -> Top]]),
                            "GridFoliation", With[{ig = IndexGraph[g]},
                                GridFoliation[ig] /. v_Integer :> Diagram[AnnotationValue[{ig, v}, "Diagram"], "Center" -> Automatic]
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


assignPorts[diagram_Diagram, ports : {inputPorts_, outputPorts_}] := Enclose @ With[{args = Sequence[
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
    HoldForm[DiagramNetwork[ds___]] :> Block[{f = diagram["PortFunction"], portDual, dualQ, inputs, outputs, in, out, rules},
        portDual = Replace[{(h : Annotation | Style | Labeled)[x_, args___] :> h[portDual[x], args], p_ :> PortDual[p]}];
        dualQ = Replace[{(h : Annotation | Style | Labeled)[x_, ___] :> dualQ[x], p_Port :> p["DualQ"]}];
        {inputs, outputs} = diagram["InputOutputPorts", True];
        {in, out} = {
			If[inheritedQ[inputPorts], inputs, Take[inputPorts, UpTo[Length[inputs]]]],
			If[inheritedQ[outputPorts], outputs, Take[outputPorts, UpTo[Length[outputs]]]]
		};
        rules = Association[
            Thread[Take[f /@ inputs, UpTo[Length[in]]] -> portDual /@ Take[in, UpTo[Length[inputs]]]],
            Thread[Take[f /@ outputs, UpTo[Length[out]]] -> Take[out, UpTo[Length[outputs]]]]
        ];
        {
            Diagram[
                DiagramNetwork[
                    assignPorts[#, {
                        Map[p |-> Lookup[rules, f[p], p, If[p["DualQ"] == dualQ[#], #, portDual[#]] &], PortDual /@ #["InputPorts"]],
                        Map[p |-> Lookup[rules, f[p], p, If[p["DualQ"] == dualQ[#], #, portDual[#]] &], #["OutputPorts"]]
                    }][[1]] & /@ {ds}
                ],
                args
            ],
            {
                Drop[in, UpTo[Length[inputs]]],
                Drop[out, UpTo[Length[outputs]]]
            }
        }
    ],
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

DiagramAssignPorts[d_Diagram, in_, out_] := DiagramAssignPorts[d, {in, out}]

DiagramAssignPorts[d_Diagram, in_ -> out_] := DiagramAssignPorts[d, {in, out}]

DiagramAssignPorts[d_Diagram, ports_] := Enclose @ First @ Confirm @ assignPorts[d, ports]

DiagramAssignPorts[d_Diagram] := DiagramAssignPorts[d, {PortDual /@ d["InputPorts"], d["OutputPorts"]}]


Options[DiagramDecompose] = {"Network" -> True, "Unary" -> False, "Decompose" -> True, "Ports" -> False, "Diagram" -> False}

DiagramDecompose[diagram_Diagram ? DiagramQ, lvl : (_Integer ? NonNegative) | Infinity : Infinity, opts : OptionsPattern[]] := If[TrueQ[diagram["OptionValue"["Decompose"], opts]] && lvl > 0,
    Replace[diagram["HoldExpression"], {
        HoldForm[Diagram[d_]] :> CircleTimes[DiagramDecompose[d, lvl - 1, opts]],
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


DiagramGridWidth[d_Diagram, args___] := gridWidth[DiagramDecompose[d], args]

gridWidth[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic :> Max[d["MaxGridArity"], 1], _ :> d[prop]}],
    (CircleTimes | CirclePlus)[ds___] :> Total[gridWidth[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Max[gridWidth[#, prop] & /@ {ds}],
    (Transpose | SuperStar)[d_, ___] :> gridWidth[d, prop],
    ({x_} | x_ -> _) :> gridWidth[x, prop],
    _ -> 1
}]

DiagramGridHeight[d_Diagram, args___] := gridHeight[DiagramDecompose[d], args]

gridHeight[expr_, prop_ : Automatic] := Replace[expr, {
    d_Diagram :> Replace[prop, {Automatic -> 1, _ :> Replace[d[prop], Except[_Integer] -> 1]}],
    (CircleTimes | CirclePlus)[ds___] :> Max[gridHeight[#, prop] & /@ {ds}],
    CircleDot[ds___] :> Total[gridHeight[#, prop] & /@ {ds}],
    (Transpose | SuperStar)[d_, ___] :> gridHeight[d, prop],
    ({x_} | x_ -> _) :> gridHeight[x, prop],
    _ -> 1
}]

DiagramGridWidthHeight[d_Diagram, args___] := With[{grid = DiagramDecompose[d]}, {gridWidth[grid, args], gridHeight[grid, args]}]

circuitArrange[diagram_Diagram -> d_, pos_, {autoWidth_, autoHeight_}, {dx_, dy_}, corner_ : {0, 0}, angle_ : 0] := Block[{
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
            Placed[Automatic, {{#, h / 2}, {#, h / 2 + 1 / 4}}] & /@ (- w / 2 + inputOrder - min + 1 / 2),
            Placed[Automatic, {{#, - h / 2}, {#, - h / 2 - 1 / 4}}] & /@ (- w / 2 + outputOrder - min + 1 / 2) 
        },
        "Center" -> Replace[diagram["OptionValue"["Center"]], {Automatic -> center, Offset[shift_] :> center + shift}]
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
        "Width" -> Replace[diagram["OptionValue"["Width"]], Automatic :> If[MatchQ[diagram["OptionValue"["Shape"]], "Circle"] || arity <= 1, 1, ratio * w]]
        (* ,
        "Height" -> Replace[diagram["OptionValue"["Height"]], Automatic :> Max[h - dy, 1]] *)
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
        Sow[pos -> If[d === None, EmptyDiagram[], Diagram[d,
            "Center" -> RotationTransform[angle, corner][corner + {w, h} / 2],
            "Width" -> Replace[d["OptionValue"["Width"]], Automatic -> w],
            "Height" -> Replace[d["OptionValue"["Height"]], Automatic -> h],
            "Style" -> None,
            If[head =!= upHead =!= None, "Shape" -> Directive[EdgeForm[Dashing[{Small, Tiny}]]], {}]
        ]],
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
            "Style" -> None
        ],
            "Column"
        ]
    ];
    MapIndexed[With[{i = #2[[1]]}, gridArrange[#1, Append[pos, i], {newWidth, heights[[i]]}, {dx, dy}, {xMin, yMin} + RotationTransform[angle] @ {0, positions[[i]]}, angle, CircleDot]] &, grid]
]

gridArrange[HoldPattern[SuperStar[d_]] -> diag_, args___] := gridArrange[CircleTimes[d] -> diag, args]

gridArrange[HoldPattern[Transpose[d_, perm___]] -> diag_, args___] := (Sow[{perm}, "Transpose"]; gridArrange[If[diag === None, d, CircleTimes[d] -> diag], args])

gridArrange[ds_List -> d_, args___] := If[Length[ds] == 1,
    gridArrange[CircleTimes[ds[[1]]] -> d, args],
    gridArrange[DiagramNetwork @@ ds -> d, args]
]

gridArrange[grid_, gapSizes_, angle_] := gridArrange[grid, {}, {Automatic, Automatic}, gapSizes, {0, 0}, angle, None]


gridOutputPositions[_Diagram, pos_] := {pos}
gridOutputPositions[(CircleTimes | List)[ds___], pos_] := Catenate[MapIndexed[gridOutputPositions[#1, Join[pos, #2]] &, {ds}]]
gridOutputPositions[_CirclePlus, _] := {}
gridOutputPositions[CircleDot[d_, ___], pos_] := gridOutputPositions[d, Append[pos, 1]]
gridOutputPositions[(Transpose | SuperStar)[d_, ___], pos_] := gridOutputPositions[d, Append[pos, 1]]
gridOutputPositions[grid_ -> _, pos_] := gridOutputPositions[grid, Append[pos, 1]]
gridOutputPositions[grid_] := gridOutputPositions[grid, {}]

gridInputPositions[_Diagram, pos_] := {pos}
gridInputPositions[(CircleTimes | List)[ds___], pos_] := Catenate[MapIndexed[gridInputPositions[#1, Join[pos, #2]] &, {ds}]]
gridInputPositions[_CirclePlus, _] := {}
gridInputPositions[CircleDot[ds___, d_], pos_] := gridInputPositions[d, Append[pos, Length[{ds}] + 1]]
gridInputPositions[(Transpose | SuperStar)[d_, ___], pos_] := gridInputPositions[d, Append[pos, 1]]
gridInputPositions[grid_ -> _, pos_] := gridInputPositions[grid, Append[pos, 1]]
gridInputPositions[grid_] := gridInputPositions[grid, {}]

GridInputPorts[d_Diagram] := If[d["SingletonNodeQ"], d["TopPorts"], GridInputPorts[If[d["NetworkQ"], d["Arrange"], d]["Decompose", "Unary" -> True]]]
GridInputPorts[grid_] := Catenate[Extract[grid, gridInputPositions[grid], #["TopPorts"] &]]

GridOutputPorts[d_Diagram] := If[d["SingletonNodeQ"], d["BottomPorts"], GridOutputPorts[If[d["NetworkQ"], d["Arrange"], d]["Decompose", "Unary" -> True]]]
GridOutputPorts[grid_] := Catenate[Extract[grid, gridOutputPositions[grid], #["BottomPorts"] &]]

Options[DiagramGrid] = DeleteDuplicatesBy[First] @ Join[{
    "HorizontalGapSize" -> 1,
    "VerticalGapSize" -> 1,
    "Rotate" -> 0,
    "Wires" -> True,
    "WireArrows" -> True,
    "WireLabels" -> True,
    "WireLabelFunction" -> Automatic,
    "Frames" -> Automatic,
    "SmoothWires" -> False,
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
    plotInteractivity = Replace[OptionValue[PlotInteractivity], Automatic -> True],
    dividers
},
    grid = DiagramDecompose[DiagramArrange[diagram, FilterRules[{opts, diagram["DiagramOptions"]}, Options[DiagramArrange]]], "Diagram" -> True, "Unary" -> False, FilterRules[{opts}, Options[DiagramDecompose]]];
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
        FaceForm[None], EdgeForm[Directive[Thin, $Black]],
        Switch[diagram["OptionValue"[Dividers], opts],
            All | Automatic, #["Graphics", "Shape" -> Automatic, PlotInteractivity -> plotInteractivity, "Style" -> None, "LabelFunction" -> ("" &), "PortArrows" -> None, "PortLabels" -> None][[1]] & /@ items[[All, 2]],
            True, #["Graphics", "Shape" -> Automatic, PlotInteractivity -> plotInteractivity, "Style" -> None, "LabelFunction" -> ("" &), "PortArrows" -> None, "PortLabels" -> None][[1]] & /@ Catenate[{rows, columns} /. _Missing -> Nothing][[All, 2]],
            _, Nothing
        ]
    };

    If[TrueQ[OptionValue["SmoothWires"]], SmoothGraphicsCurves, Identity] @ Graphics[
        Switch[frames,
            All | Automatic,
            With[{subDiagrams = #[[1]] -> Diagram[#[[2]],
                    "LabelFunction" -> ("" &),
                    "PortLabels" -> {Placed[Inherited, {0, 0}]},
                    "PortArrowFunction" -> (Nothing &),
                    "Width" -> Min[1, 0.95 ^ (Length[#[[1]]] / 2)] #[[2]]["OptionValue"["Width"]],
                    "Height" -> If[#[[1]] === {}, 1.1, Min[1, 0.85 ^ (Length[#[[1]]] / 2)]] #[[2]]["OptionValue"["Height"]],
                    "Style" -> Directive[EdgeForm[$Black], FaceForm[None]]
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
                                With[{
                                        parentDiagrams = Select[subDiagrams, Take[pos, UpTo[Length[#[[1]]]]] === #[[1]] &]
                                    },
                                    If[ parentDiagrams === {},
                                        {},
                                        With[
                                        {
                                            ports = MapThread[Join, {portFunction /@ PortDual /@ #["InputPorts"], portFunction /@ #["OutputPorts"]} & /@ parentDiagrams[[All, 2]]]
                                        },
                                            (opt |-> opt -> {
                                                Map[If[MemberQ[ports[[1]], #], None, Inherited] &, portFunction /@ PortDual /@ #["InputPorts"]],
                                                Map[If[MemberQ[ports[[2]], #], None, Inherited] &, portFunction /@ #["OutputPorts"]]
                                            }) /@ {"PortArrows", "PortLabels"}
                                        ]
                                    ]
                                ],
                                #["DiagramOptions"]
                            ]
                        ]["Graphics", PlotInteractivity -> plotInteractivity][[1]] &
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
                        PlotInteractivity -> plotInteractivity,
                        "PortsFirst" -> False,
                        "PortLabelFunction" -> Function[Framed[Wolfram`DiagrammaticComputation`Diagram`Private`$DefaultPortLabelFunction[##], Background -> $White, FrameStyle -> LightGray]]
                    ][[1]] & /@ subDiagrams,
                    dividers
                }
            ],
            _,
            {
                Cases[unlabeledGrid,
                    d_Diagram :> Diagram[d, "DiagramOptions" -> Join[diagramOptions, d["DiagramOptions"]]]["Graphics", PlotInteractivity -> plotInteractivity][[1]],
                    All
                ],
                {
                    Haloing[],
                    If[wiresQ, gridWires[grid, {}, portFunction, "WireArrows" -> wireArrows, "WireLabels" -> wireLabels, "WireLabelFunction" -> wireLabelFunction, "GapSize" -> vGapSize], Nothing],
                    gridNetworkWires[grid, Missing[], portFunction, "WireArrows" -> wireArrows, "WireLabels" -> wireLabels, "WireLabelFunction" -> wireLabelFunction, "GapSize" -> hGapSize]
                },
                dividers
            }
        ],
        FilterRules[{opts, diagram["DiagramOptions"]}, Options[Graphics]],
        FormatType -> StandardForm
    ]
]


wireGraphics[opts___][{outPort_, out_, outStyle_, outLabel_, ___}, {inPort_, in_, inStyle_, inLabel_, ___}] := With[{
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
                                {{arrowSize, .5}},
                                {{from * arrowSize, .3}, {to * arrowSize, .7}}
                            ]
                        ]
                    ]
                },
                    If[ MatchQ[style, _Function],
                        {arrowheads, style[#, "Grid"]} &,
                        {arrowheads, Replace[style, Placed[x_, _] :> x], Arrow @ BSplineCurve @ If[outDual && outDual == ! inDual, Reverse[#], #]} &
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
                        If[MatchQ[outStyle, _Function], {arrowheads, outStyle[#, "Grid"]} &, {arrowheads, Replace[outStyle, Placed[x_, _] :> x], Arrow @ BSplineCurve @ If[outDual, Reverse[#], #]} &] @ {out[[1]], p, (in[[1]] + out[[1]]) / 2}
                    ]
                ]
                ,
                If[ inStyle === None,
                    {},
                    With[{arrowheads = Arrowheads[{{- to * arrowSize, .5}}]},
                        If[MatchQ[inStyle, _Function], {arrowheads, inStyle[#, "Grid"]} &, {arrowheads, Replace[inStyle, Placed[x_, _] :> x], Arrow @ BSplineCurve @ If[! inDual, Reverse[#], #]} &] @  {(in[[1]] + out[[1]]) / 2, q, in[[1]]}
                    ]
                ]
            }
        ]
    ] // Append[
        With[{
            label = Replace[Replace[inLabel, {Automatic -> outLabel, _ -> inLabel}], {Placed[Automatic | True, _] | Automatic | True -> outPort["Name"], Placed[l_, _] :> l}],
            wirePos = (out[[1]] + in[[1]]) / 2 + 0.1 RotationTransform[Replace[wireLabels, Automatic | True -> Pi / 2]] @ Normalize[out[[1]] - in[[1]]]
        },
            With[{wireLabel = Replace[wireLabelFunction[out, in, label], {Placed[l_, x_] :> {l, x}, l_ :> {l, wirePos}}]},
                If[ MatchQ[wireLabels, None | False] || MatchQ[wireLabel[[1]], None | False] || MatchQ[wireLabel[[2]], None],
                    Nothing,
                    Text[ClickToCopy[Replace[wireLabel[[1]], Automatic | True -> label]], Replace[wireLabel[[2]], {Automatic -> wirePos, Offset[offset_] :> wirePos + offset}]]
                ]
            ]
        ]
    ]
]


makeRules[keys_, ports_, arrows_, styles_, labels_, type_, dualQ_] :=
    Thread[
        keys -> Thread[{
            If[dualQ, Map[PortDual], Identity] @ ports,
            If[dualQ, {#1, #1 + (#1 - #2)} & @@@ # &, Identity] @ arrows,
            styles,
            labels,
            {type, #} & /@ Range[Length[keys]]
        }]
    ]

makeRules[keys_, ports_, arrows_, styles_, labels_, dualQ_, type_, pick_] := makeRules[Pick[keys, pick], Pick[ports, pick], Pick[arrows, pick], Pick[styles, pick], Pick[labels, pick], type, dualQ]

makeInputRules[diagram_, portFunction_, dualQ_ : False, flatSumQ_ : False] := With[{ports = diagram["InputPorts"]},
    If[flatSumQ, flattenSumRules, Identity] @ flattenProductRules @
        makeRules[portFunction /@ PortDual /@ ports, ports, diagram["PortArrows"][[1]], diagram["PortStyles"][[1]], diagram["PortLabels"][[1]], dualQ, 1, Not /@ Through[ports["NeutralQ"]]]
]

makeOutputRules[diagram_, portFunction_, dualQ_ : False, flatSumQ_ : False] := With[{ports = diagram["OutputPorts"]},
    If[flatSumQ, flattenSumRules, Identity] @ flattenProductRules @
        makeRules[portFunction /@ ports, ports, diagram["PortArrows"][[2]], diagram["PortStyles"][[2]], diagram["PortLabels"][[2]], dualQ, 2, Not /@ Through[ports["NeutralQ"]]]
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
        0,
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
            Sow[merge, "Rules"];
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
    
    Sow[merge, "Rules"];
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
            
            wireGraphics[opts] @@@ Values[Sow[#, "Rules"]] & /@ {mergeInput, mergeOutput}
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
        ports = upInputs
    ];
    Fold[With[{subPos = Append[pos, #1[[3]]]},
        diagram = Lookup[frameDiagrams, Key[subPos]];
        If[ MissingQ[diagram],
            inputs = Join @@ Extract[#2, gridInputPositions[#2], makeInputRules[#, portFunction] &];
            outputs = Join @@ Extract[#2, gridOutputPositions[#2], makeOutputRules[#, portFunction] &]
            ,
            inputs = makeInputRules[diagram, portFunction, False, sumQ];
            outputs = makeOutputRules[diagram, portFunction, False, sumQ]
        ];
        merge = mergeRules[#1[[2]], inputs];
        If[ upOutputs =!= None,
            With[{mergeOutput = mergeRules[upOutputs, outputs]},
                merge = Join[merge, mergeOutput];
                upOutputs = DeleteElements[upOutputs, 1 -> MapAt[First, mergeOutput, {All, 2}]]
            ]   
        ];
        Sow[subPos -> merge, "Rules"];
        {
            Join[
                #1[[1]], wireGraphics[opts] @@@ Values[merge]
                ,
                If[ DiagramQ[#2], {},
                    gridFrameWires[#2, subPos, frameDiagrams, If[MissingQ[diagram], {}, makeInputRules[diagram, portFunction, True, sumQ]], portFunction, opts]
                ]
            ],
            DeleteElements[#1[[2]], 1 -> MapAt[First, merge, {All, 2}]],
            #1[[3]] + 1
        }
    ] &,
        {{}, ports, 1},
        {ds}
    ][[1]]
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
        merge = Join[merge, mergeRules[ports, upOutputPorts]];
        ports = Join[DeleteElements[ports, 1 -> MapAt[First, merge, {All, 2}]], upOutputPorts]
    ];
    Sow[pos -> merge, "Rules"];
    Join[
        wireGraphics[opts] @@@ Values[merge],
        gridFrameWires[d, Append[pos, Length[{ds}] + 1], frameDiagrams, {}, portFunction, opts],
        gridFrameWires[CircleDot[ds], pos, frameDiagrams, ports, portFunction, opts]
    ]
]


gridFrameWires[___] := {}


gridNetworkWires[grid_, frame_, portFunction_, opts___] := With[{
    rules = Join[
        Catenate @ Cases[grid, d_Diagram /; d["SingletonNodeQ"] :> makeNeutralRules[d, portFunction], All],
        If[MissingQ[frame], {}, makeNeutralRules[frame, portFunction, True]]
    ]
},
    Sow[rules, "Rules"];
    wireGraphics[opts] @@@ Values @ Catenate[mergeRules[{#}, rules] & /@ rules]
]


Options[DiagramGridTree] = Join[Options[DiagramGraphics], Options[NestTree]]

DiagramGridTree[diag_Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{
	diagramOptions = FilterRules[{opts}, Options[DiagramGraphics]]
},
	NestTree[
		Replace[{_Diagram -> {}, Verbatim[Transpose][expr_, _] :> {expr}, expr_ :> List @@ expr}],
		DiagramDecompose[diag, "Unary" -> True],
		Infinity,
		Replace[{d_Diagram :> d, Verbatim[Transpose][_, perm_] :> perm, expr_ :> Head[expr]}]
		,
		FilterRules[{opts}, Options[NestTree]],
		TreeElementLabel -> {TreeCases[CircleTimes] -> "\[CircleTimes]", TreeCases[CircleDot] -> "\[CircleDot]", TreeCases[List] -> "\[SmallCircle]", TreeCases[SuperStar] -> "*", TreeCases[_Cycles] -> "T"},
		TreeElementLabelFunction -> {TreeCases[_Diagram] -> Function[#["Graphics", diagramOptions, "PortArrows" -> Directive[Haloing[0], Arrowheads[0]], "PortLabels" -> None, ImageSize -> {20, 30}]]},
		TreeElementStyle -> {TreeCases[_Diagram] -> EdgeForm[StandardBlue]}
	]
]


End[];

EndPackage[];

