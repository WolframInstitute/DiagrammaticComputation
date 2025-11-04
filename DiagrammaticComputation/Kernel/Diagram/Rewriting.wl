BeginPackage["Wolfram`DiagrammaticComputation`Diagram`Rewriting`", {
    "Wolfram`DiagrammaticComputation`Port`",
    "Wolfram`DiagrammaticComputation`Diagram`",
    "Wolfram`DiagrammaticComputation`Utilities`",
    "Wolfram`DiagrammaticComputation`Diagram`Surgery`",
    "Wolfram`DiagrammaticComputation`Diagram`Grid`",
    "WolframInstitute`Hypergraph`"
}]

DiagramHypergraph
DiagramHypergraphRule

DiagramReplaceList
DiagramReplace

DiagramExpressionReplace

RemoveDiagramRule
DiagramRule

EraserDiagram

CommutationRule
EraserRule
AnnihilationRule
DuplicateAnnihilationRule
EraserAnnihilationRule
DuplicateEraserRule

DiagramCopySplit


$LambdaInteractionRules = <|
	"BetaReduce" -> AnnihilationRule[Subscript["\[Lambda]", _], "\[Application]", {SuperStar[var], body}, {SuperStar[arg], app}],
	"Dup" -> CommutationRule[{x1, SuperStar[x2]}, {y1, y2}],
	"DualDup" -> CommutationRule[{x1, SuperStar[x2]}, {y1, y2}, "Dual" -> True, "Bend" -> True],
	"DupReduce" -> DuplicateAnnihilationRule[{x1, x2}, {y1, y2}, "Bend" -> True],
	"DupSwapReduce" -> DuplicateAnnihilationRule[{x1, x2}, {y1, y2}, "Bend" -> True, "Reverse" -> True],
	"Erase" -> EraserRule[{SuperStar[x], y}],
	"EraseReduce" -> EraserAnnihilationRule[],
	"EraseDup" -> DuplicateEraserRule[x, y]
|>

Begin["`Private`"]


Options[DiagramHypergraph] = Join[{"Pattern" -> False}, Options[Hypergraph]]


patternLabelArities[d_Diagram] := Total /@ Replace[
	d["PortLabels"],
	{
		_BlankSequence | _BlankNullSequence | _Repeated | _RepeatedNull | Verbatim[Pattern][_, _BlankSequence | _BlankNullSequence] -> Infinity,
		_ -> 1
	},
	{2}
]

DiagramHyperedge[d_Diagram, f_, pattQ : _ ? BooleanQ] := With[{floatPorts = d["OptionValue"["FloatingPorts"]], n = d["InputArity"], m = d["OutputArity"]}, {
	perm = FindPermutation[Range[n + m], Join[n + Range[m], Range[n]]]
},
	Annotation[
		labeledVertices[d, f],
		EdgeLabels -> ((d["OptionValue"["Shape"]] -> Underoverscript[d["Label"], #2, #1]) -> Through[Catenate[d["InputOutputPorts"]]["DualQ"]] & @@
			If[pattQ, {_, _}, Replace[patternLabelArities[d], Infinity -> _, 1]]),
		"EdgeSymmetry" -> Switch[floatPorts,
			True, "Unordered",
			False, {Cycles[{}], perm},
			{True, False}, Join[
				GroupElements[PermutationGroup[Cycles[{#}] & /@ Subsets[Range[n], {2}]]],
				PermutationProduct[perm, #] & /@ GroupElements[PermutationGroup[Cycles[{#}] & /@ Subsets[m + Range[n], {2}]]]
			],
			{False, True}, Join[
				GroupElements[PermutationGroup[Cycles[{#}] & /@ Subsets[n + Range[m], {2}]]],
				PermutationProduct[perm, #] & /@ GroupElements[PermutationGroup[Cycles[{#}] & /@ Subsets[Range[m], {2}]]]
			]
		]
	]
]

DiagramHypergraphRule[src_Diagram -> tgt_Diagram, opts : OptionsPattern[]] :=
	HypergraphRule[DiagramHypergraph[src, "Pattern" -> True], DiagramHypergraph[tgt], opts]

labeledVertices[d_Diagram, f_] := MapThread[
	Labeled[f[#1], Replace[#2, {Automatic :> (Replace[#1["Name"], Labeled[l_, __] :> l]), False -> None}]] &,
	{Catenate @ d["InputOutputPorts", True], Catenate @ d["PortLabels"], Catenate @ d["PortStyles"]}
]

labeledVertices[d_Diagram] := With[{f = d["PortFunction"]},
	Catenate[labeledVertices[#, f] & /@ DiagramSubdiagrams[d, {1}]]
]

DiagramHypergraph[ds : {___Diagram}, f_, vs_List, opts : OptionsPattern[]] := Enclose @ ConfirmBy[
	Hypergraph[
		vs,
		DiagramHyperedge[#, f, TrueQ[OptionValue["Pattern"]]] & /@ Select[ds, #["Arity"] > 0 &],
		"EdgeSymmetry" -> "Ordered",
		FilterRules[{opts}, Options[Hypergraph]]
	],
	HypergraphQ
]

DiagramHypergraph[d_Diagram, opts : OptionsPattern[]] := With[{net = SimplifyDiagram[ToDiagramNetwork[d]]}, {f = net["PortFunction"]},
	DiagramHypergraph[
		DiagramSubdiagrams[net, {1}],
		f,
		labeledVertices[net],
		opts
	]
]

MatchDiagrams[
	srcDiagrams : {___Diagram},
	tgtDiagrams : {___Diagram},
	match : KeyValuePattern[{"Hypergraph" -> hg_Hypergraph, "MatchEdgePositions" -> pos_, "NewEdges" -> newEdges_, "Bindings" -> bindings_, "EdgeArities" -> arities_}]
] :=
	If[
		EdgeCount[hg] == 0
		,
		{EmptyDiagram[]}
		,
		With[{
			holdBindings = Normal @ KeyMap[HoldForm, HoldForm /@ Association[bindings]],
			optionRules = Append[_ -> {}] @ Thread[Through[#["Label"]] -> Through[#["DiagramOptions"]]] & @ Extract[srcDiagrams, pos]
		},
			MapThread[
				With[{expr = Replace[#3, ((_ -> Underoverscript[HoldForm[x_], ___]) -> _) | x_ :> x]},
					Diagram[
						DiagramExpressionReplace[#1, _ :> expr],
						Sequence @@ MapThread[
							MapThread[If[#1, PortDual, Port][#2] &, {PadRight[#1, Length[#2], #1], #2}] &,
							{Map[#["DualQ"] &, #1["InputOutputPorts", True], {2}], Replace[#3, ((_ -> Underoverscript[_, _, nInputs_]) -> _) :> TakeDrop[#2, Total[Take[#4, nInputs]]]]}
						],
						Replace[Replace[#1["Label"], holdBindings], optionRules]
					]
				] &,
				{tgtDiagrams, newEdges, Replace[newEdges, OptionValue[hg, EdgeLabels], 1], arities}
			]
		]
	]


Options[DiagramReplaceList] = Join[{"Return" -> Automatic, "IgnoreArity" -> True}, Options[Diagram]]

DiagramReplaceList[d_Diagram, src_Diagram -> tgt_Diagram, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := Enclose @ Block[{
	srcHg, tgtNet, tgtHg, tgtDiagrams, rule, net, diagrams, hg, nets,
	srcF = src["PortFunction"], tgtF = tgt["PortFunction"],
	matches,
	return = OptionValue["Return"],
	diagramOptions = FilterRules[{opts}, Options[Diagram]]
},
	srcHg = ConfirmBy[DiagramHypergraph[src, "Pattern" -> TrueQ[OptionValue["IgnoreArity"]]], HypergraphQ];
	tgtNet = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork @ tgt, DiagramQ];
	tgtDiagrams = DiagramSubdiagrams[tgtNet, {1}];
	tgtHg = ConfirmBy[With[{f = tgtNet["PortFunction"]}, DiagramHypergraph[tgtDiagrams, f, labeledVertices[tgtNet]]], HypergraphQ];
	rule = ConfirmBy[HypergraphRule[srcHg, tgtHg], HypergraphRuleQ];
	If[return === "Rule", Return[rule]];
	net = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork[d], DiagramQ];
	diagrams = DiagramSubdiagrams[net, {1}];
	hg = ConfirmBy[With[{f = net["PortFunction"]}, DiagramHypergraph[diagrams, f, labeledVertices[net]]], HypergraphQ];
	If[return === "Hypergraph", Return[hg]];
	matches = ConfirmMatch[rule[hg, "DistinctVertexLabels" -> False, "DistinctEdgeLabels" -> False, "SymmetryMethod" -> None], {___ ? AssociationQ}];
	If[return === "Matches", Return[matches]];
	matches = Take[matches, UpTo[n]];
	nets = Map[
		With[{
			newNet = SimplifyDiagram @ DiagramNetwork[Join[Delete[diagrams, #["MatchEdgePositions"]], MatchDiagrams[diagrams, tgtDiagrams, #]]],
			freeVertices = Complement[Union @@ EdgeList[#], VertexList[#]] & @ #["Hypergraph"]
		},
			If[freeVertices === {}, newNet, SingletonDiagram[newNet, freeVertices]]
		] &,
		matches
	];
	Diagram[#, Inherited, Inherited, FilterRules[{diagramOptions, d["DiagramOptions"]}, Except["PortArrows" | "PortLabels" | "PortFunction"]]] & /@ If[d["NetworkQ"], nets, DiagramArrange /@ nets]
]

DiagramReplaceList[d_Diagram, rules : {__Rule}, opts : OptionsPattern[]] := Switch[OptionValue["Return"],
	"Hypergraph",
	DiagramHypergraph[d],
	_,
	DiagramReplaceList[d, #, opts] & /@ rules
]

DiagramReplaceList[rules_][d_Diagram, opts : OptionsPattern[]] := DiagramReplaceList[d, rules, opts]


DiagramReplace[d_Diagram, rules_List, opts : OptionsPattern[]] := First[FoldWhile[DiagramReplaceList[d, #2, 1, opts] &, {}, rules, # === {} &], d]

DiagramReplace[d_Diagram, rule_, opts : OptionsPattern[]] := First[DiagramReplaceList[d, rule, 1, opts], d]

DiagramReplace[rule_][d_Diagram, opts : OptionsPattern[]] := DiagramReplace[d, rule, opts]


DiagramExpressionReplace[d_Diagram, rules_] :=
	DiagramMap[
		Diagram[#, "Expression" :> ## & @@ ReplaceAt[#["HoldExpression"], rules, {1}]] &,
		d
	]


RemoveDiagramRule[d_Diagram] :=
	DiagramRule[d,
		SingletonDiagram[
			EmptyDiagram[], ##,
			FilterRules[AbsoluteOptions[d], {"PortArrows", "PortLabels", "FloatingPorts"}]
		] & @@ d["InputOutputPorts", True]
	]


DiagramRule[src_Diagram, tgt_Diagram] := Block[{
	srcInPorts = PortDual /@ src["InputPorts"],
	srcOutPorts = src["OutputPorts"],
	tgtInPorts = PortDual /@ tgt["InputPorts"],
	tgtOutPorts = tgt["OutputPorts"],
	labels
},
	labels = Symbol["\[FormalP]" <> ToString[#]] & /@
		Range[Max[Length[srcInPorts] + Length[srcOutPorts], Length[tgtInPorts] + Length[tgtOutPorts]]];

	DiagramAssignPorts[src,
		MapThread[Labeled[#1, Pattern[#2, _]] &, {srcInPorts, Take[labels, Length[srcInPorts]]}],
		MapThread[Labeled[#1, Pattern[#2, _]] &, {srcOutPorts, Take[Drop[labels, Length[srcInPorts]], Length[srcOutPorts]]}]
	] ->
	DiagramAssignPorts[tgt,
		MapThread[Labeled, {tgtInPorts, Take[labels, Length[tgtInPorts]]}],
		MapThread[Labeled, {tgtOutPorts, Take[Drop[labels, Length[tgtInPorts]], Length[tgtOutPorts]]}]
	]
]

DiagramRule[src_Diagram -> tgt_Diagram] := DiagramRule[src, tgt]


Options[DuplicateRule] = Options[EraserRule] = Options[DuplicateAnnihilateRule] = Options[Diagram];


makePattern[expr_] := With[{rules = {
		sym : Except[None, _Symbol] :> Pattern @@ Hold[sym, _],
		SuperStar[sym : Except[None, _Symbol]] :> SuperStar[Pattern @@ Hold[sym, _]],
		p_Port :> p["Apply", With[{name = #["HoldName"]}, If[MatchQ[name, HoldForm[_Symbol]], Pattern @@ Append[name, _], #]] &]
	}
},
	Replace[Unevaluated[expr], Append[rules, d_Diagram :> DiagramExpressionReplace[d, rules]]]
]

SetAttributes[makePattern, HoldFirst]


$CopyOptions = {
	"Shape" -> "RoundedTriangle",
	"Width" -> 1, "Height" -> 1,
	"Style" -> Hue[0.709, 0.445, 1],
	"ShowLabel" -> False,
	"FloatingPorts" -> {False, True}
}

$Port = (_Symbol | SuperStar[_Symbol])

Options[CommutationRule] = Join[{"Bend" -> False, "Dual" -> False}, Options[Diagram]]

CommutationRule[ins : {$Port ...}, outs : {$Port ...}, opts : OptionsPattern[]] :=
	CommutationRule[
		Diagram[\[FormalF], _, ins,
			FilterRules[{opts}, Options[Diagram]],
			"Shape" -> "RoundedTriangle", "Width" -> 1, "Height" -> 1, "FloatingPorts" -> {False, True}, "PortLabels" -> {None, Automatic}
		],
		CopyDiagram[_, outs, $CopyOptions, "PortLabels" -> {None, Automatic}],
		opts
	]

CommutationRule[d_Diagram, outPorts : {$Port ...}, opts : OptionsPattern[]] /; d["OutputArity"] == 1 := 
	CommutationRule[d, CopyDiagram[x, outs, "PortLabels" -> {None, Automatic}, FilterRules[{opts, $CopyOptions}, Optsion[Diagram]]], FilterRules[{opts}, Except[Options[Diagram]]]]

CommutationRule[d_Diagram, c_Diagram, opts : OptionsPattern[]] /; d["InputArity"] == c["InputArity"] == 1 := Block[{
	diag, copy,
	bendQ = TrueQ[OptionValue["Bend"]], dualQ = TrueQ[OptionValue["Dual"]],
	ins = d["OutputPorts"], outs = c["OutputPorts"],
	port = First[d["InputPorts"]],
	lhs, rhs,
	diagOpts = FilterRules[{opts, Alignment -> Center, ImageSize -> {Automatic, 192}}, Options[Diagram]]
},
	If[ dualQ,
		ins = PortDual /@ ins;
		outs = PortDual /@ outs;
		port = PortDual @ port
	];
	diag = DiagramDual[Diagram[makePattern @ d, PortDual[port], makePattern /@ ins], "Singleton" -> False];
	copy = Diagram[c, PortDual[port], makePattern /@ outs, "PortLabels" -> {None, Automatic}];
	lhs = ColumnDiagram[
		If[	bendQ,
			{CupDiagram[port], DiagramProduct[diag, copy]}
			,
			{diag = DiagramFlip[diag, "Singleton" -> False], copy}
		],
		diagOpts
	];
	rhs = ColumnDiagram[{
			DiagramProduct @ Map[p |-> Diagram[c, p, Port[p]["Apply", #] & /@ Range[Length[outs]], "PortLabels" -> {Automatic, None}], ins],
			DiagramProduct @ MapIndexed[{p, i} |-> Diagram[DiagramFlip[d], #["Apply", i[[1]]] & /@ ins, p, "PortLabels" -> {None, Automatic}], outs]
		},
		diagOpts
	];
	lhs -> rhs
]

EraserDiagram[p_, opts : OptionsPattern[]] := Diagram[None, p, {}, opts, "Shape" -> "Disk", "Width" -> 1 / 2, "Height" -> 1 / 2, "PortLabels" -> None, "LabelFunction" -> ("\[Epsilon]" &)]

EraserRule[ports : {$Port ...}, opts : OptionsPattern[]] := CommutationRule[
	EraserDiagram[\[FormalX]],
	Diagram[_, \[FormalX], ports, "Shape" -> "RoundedTriangle", "Width" -> 1, "Height" -> 1, "FloatingPorts" -> {False, True}],
	opts
]


Options[AnnihilationRule] = Join[{"Bend" -> False, "Reverse" -> False}, Options[Diagram]]

AnnihilationRule[d_Diagram, opts : OptionsPattern[]] /; d["InputArity"] > 0 := With[{ins = d["InputPorts"], outs = d["OutputPorts"]},
	AnnihilationRule[Diagram[d, _, PortDual /@ ins, "PortLabels" -> {False, True}], Diagram[d, _, outs, "PortLabels" -> {False, True}], opts]
]

AnnihilationRule[d1_Diagram, d2_Diagram, opts : OptionsPattern[]] /; d1["InputArity"] == d2["InputArity"] == 1 := Block[{
	ins = d1["OutputPorts"], outs = d2["OutputPorts"],
	port = First[d1["InputPorts"]],
	lhs, rhs,
	diagOpts = FilterRules[{opts, Alignment -> Center, ImageSize -> {Automatic, 192}}, Options[Diagram]]
},
	lhs = ColumnDiagram[
		If[	TrueQ[OptionValue["Bend"]],
			{CupDiagram[port], DiagramProduct[Diagram[makePattern @ d1, port, PortDual /@ makePattern /@ ins], Diagram[makePattern @ d2, PortDual[port], makePattern /@ outs]]},
			{DiagramDual[DiagramFlip[Diagram[makePattern @ d1, makePattern /@ ins], "Singleton" -> False], "Singleton" -> False], Diagram[makePattern @ d2, PortDual[port], makePattern /@ outs]}
		],
		diagOpts
	];
	
	rhs = DiagramProduct[
		MapThread[IdentityDiagram[#1 -> #2] &, {ins, If[TrueQ[OptionValue["Reverse"]], Reverse[outs], outs]}],
		diagOpts,
		AspectRatio -> 2
	];
	lhs -> rhs
]

AnnihilationRule[expr1_, expr2_, ins : {$Port ...}, outs : {$Port ...}, opts : OptionsPattern[]] /; Length[ins] == Length[outs] := With[{
	diagramOpts = FilterRules[{opts, "Shape" -> "RoundedTriangle", "Width" -> 1, "FloatingPorts" -> {False, True}, "PortLabels" -> {None, Automatic}}, Options[Diagram]]
},
	AnnihilationRule[Diagram[expr1, _, ins, diagramOpts], Diagram[expr2, _, outs, diagramOpts], FilterRules[{opts}, Except[Options[Diagram]]]]
]

DuplicateAnnihilationRule[ins : {$Port ...}, outs : {$Port ...}, opts : OptionsPattern[]] /; Length[ins] == Length[outs] :=
	AnnihilationRule["Copy", "Copy", ins, outs, opts, $CopyOptions]

EraserAnnihilationRule[opts : OptionsPattern[]] :=
	AnnihilationRule[EraserDiagram[\[FormalX]], EraserDiagram[SuperStar[\[FormalX]]], opts]

DuplicateEraserRule[in : $Port, out : $Port, opts : OptionsPattern[]] :=
	DiagramArrange @ DiagramNetwork[
		EraserDiagram[\[FormalX]],
		CopyDiagram[makePattern @ in, {\[FormalX], makePattern @ out}, "PortLabels" -> {Automatic, {None, Automatic}}, $CopyOptions],
		opts,
		ImageSize -> {Automatic, 192}
	] -> IdentityDiagram[in -> out, ImageSize -> {Automatic, 192}]


DiagramCopySplit[d_Diagram] := If[d["NetworkQ"], Identity, DiagramArrange][
	DiagramNetwork[
		Map[
			diag |->
			If[
				MatchQ[diag["Arities"], {1, i_} /; i > 2]
				,
				Splice @ FoldPairList[
					With[{outs = Replace[#2[[1]], None :> Unique["x"], 1]}, {
						Diagram[diag, #1, outs,
							"PortArrows" -> {Inherited, #2[[2]]},
							"PortLabels" -> {Inherited, #2[[3]]},
							"Shape" -> Replace[diag["OptionValue"["Shape"]], "Wires"[_] :> "Wires"[{{1, 2}, {1, 3}}]]],
						Last[outs]
					}] &,
					PortDual @ First @ diag["InputPorts"],
					Thread[{MapAt[None &, {;; -2, -1}] @ Partition[diag["OutputPorts"], 2, 1], Partition[diag["PortStyles"][[2]], 2, 1], Partition[diag["PortLabels"][[2]], 2, 1]}]
				]
				,
				diag
			],
			AnnotationValue[{#, VertexList[#]}, "Diagram"] & @ d["NetGraph", "UnarySpiders" -> False]
		],
		FilterRules[d["DiagramOptions"], Except["PortFunction"]]
	]
]


End[]

EndPackage[]

