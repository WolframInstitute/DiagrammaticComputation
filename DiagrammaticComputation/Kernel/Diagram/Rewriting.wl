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
DiagramNestReplace

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

PropagationRule

DiagramCopySplit



$LambdaInteractionRules = <|
	"BetaReduce" :> AnnihilationRule[Subscript["\[Lambda]", _], "\[Application]", {SuperStar[var], body}, {SuperStar[arg], app}],
	"DupReduce" :> DuplicateAnnihilationRule[{x1, x2}, {y1, y2}, "Bend" -> True],
	"DupSwapReduce" :> DuplicateAnnihilationRule[{x1, x2}, {y1, y2}, "Bend" -> True, "Reverse" -> True],
	"Dup" :> CommutationRule[{x1, SuperStar[x2]}, {y1, y2}],
	"DualDup" :> CommutationRule[{x1, SuperStar[x2]}, {y1, y2}, "Dual" -> True, "Bend" -> True],
	"Erase" :> EraserRule[{SuperStar[x], y}],
	"EraseReduce" :> EraserAnnihilationRule[],
	"EraseDup" :> DuplicateEraserRule[x, y]
|>

$LambdaCroissantBracketRules = <|
	"Annihilation" :> AnnihilationRule[Interpretation[i, _], Interpretation[i, _], {SuperStar[x1], x2}, {SuperStar[y1], y2}, "Polarized" -> False, "Floating" -> False],
	"Commutation" :> CommutationRule[Interpretation[i, _], Interpretation[j, _], {x1, SuperStar[x2]}, {y1, y2}, "ShowLabel" -> True, "Style" -> Automatic, "Polarized" -> False, "Floating" -> False] /; i =!= j,
	"CroissantIdentity" :> AnnihilationRule[Diagram[i, a, b, "Shape" -> "UpsideDownCroissant", "Height" -> 1 / 2, "Width" -> 1], "Polarized" -> False, "Floating" -> False],
	"BracketIdentity" :> AnnihilationRule[Diagram[i, a, b, "Shape" -> "UpsideDownBracket", "Height" -> 1 / 2, "Width" -> 1], "Polarized" -> False, "Floating" -> False],
	"CroissantPropagation" :> PropagationRule[a, {b, c}, # - 1 &, "Shape" -> "Croissant", "Polarized" -> False, "Floating" -> False],
	"BracketPropagation" :> PropagationRule[a, {b, c}, # + 1 &, "Shape" -> "Bracket", "Polarized" -> False, "Floating" -> False]
|>

$LambdaCroissantBracketPolarizedRules = <|
	"BetaReduce" :> AnnihilationRule[Interpretation[i, _], Interpretation[i, _], {SuperStar[var], body}, {SuperStar[arg], app}],
	"DupReduce" :> AnnihilationRule[Interpretation[i, _], Interpretation[i, _], {SuperStar[x1], x2}, {SuperStar[y1], SuperStar[y2]}],
	"Dup" :> CommutationRule[Interpretation[i, _], Interpretation[j, _], {x1, SuperStar[x2]}, {y1, y2}, "ShowLabel" -> True],
	"DupDup" :> CommutationRule[Interpretation[i, _], Interpretation[j, _], {x1, x2}, {y1, y2}, "ShowLabel" -> True, "Bend" -> True, $CopyOptions],
	"DualDup" :> CommutationRule[Interpretation[i, _], Interpretation[j, _], {x1, SuperStar[x2]}, {y1, y2}, "ShowLabel" -> True, "Bend" -> True],
	"CroissantIdentity" :> AnnihilationRule[Diagram[i, a, b, "Shape" -> "UpsideDownCroissant", "Height" -> 1 / 2, "Width" -> 1]],
	"BracketIdentity" :> AnnihilationRule[Diagram[i, a, b, "Shape" -> "UpsideDownBracket", "Height" -> 1 / 2, "Width" -> 1]],
	"CroissantPropagation" :> PropagationRule[a, {b, c}, # - 1 &, "Shape" -> "Croissant"],
	"DualCroissantPropagation" :> PropagationRule[a, {SuperStar[b], c}, # - 1 &, "Shape" -> "Croissant"],
	"BracketPropagation" :> PropagationRule[a, {b, c}, # + 1 &, "Shape" -> "Bracket"],
	"DualBracketPropagation" :> PropagationRule[a, {SuperStar[b], c}, # + 1 &, "Shape" -> "Bracket"]
|>

Begin["`Private`"]


Options[DiagramHypergraph] = Join[{"Pattern" -> False, "Symmetric" -> False}, Options[Hypergraph]]


patternLabelArities[d_Diagram] := Total /@ Replace[
	d["PortLabels"],
	{
		_BlankSequence | _BlankNullSequence | _Repeated | _RepeatedNull | Verbatim[Pattern][_, _BlankSequence | _BlankNullSequence] -> Infinity,
		_ -> 1
	},
	{2}
]

DiagramHyperedge[d_Diagram, f_, pattQ : _ ? BooleanQ, symmetricQ : _ ? BooleanQ] := With[{floatPorts = d["OptionValue"["FloatingPorts"]], n = d["InputArity"], m = d["OutputArity"]},
	Annotation[
		labeledVertices[d, f],
		EdgeLabels -> Rule[
			d["Node"]["OptionValue"["Shape"]] -> Underoverscript[d["Label"], #2, #1] & @@ If[pattQ, {_, _}, Replace[patternLabelArities[d], Infinity -> _, 1]],
			MapThread[
				If[pattQ && MatchQ[#2, False | (Style | Placed)[False, __]], _, #1["DualQ"]] &,
				{Catenate[d["InputOutputPorts"]], Catenate[d["PortStyles"]]}
			]
		],
		"EdgeSymmetry" -> If[symmetricQ,
			With[{perm = FindPermutation[Range[n + m], Join[n + Range[m], Range[n]]]},
				Switch[floatPorts,
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
			,
			Switch[floatPorts,
				True, "Unordered",
				False, {Cycles[{}]},
				{True, False},
					GroupElements[PermutationGroup[Cycles[{#}] & /@ Subsets[Range[n], {2}]]],
				{False, True},
					GroupElements[PermutationGroup[Cycles[{#}] & /@ Subsets[n + Range[m], {2}]]]
			]
		]
	]
]

DiagramHypergraphRule[src_Diagram -> tgt_Diagram, opts : OptionsPattern[]] :=
	DiagramHypergraphRule[(src -> tgt) /; True, opts]

DiagramHypergraphRule[Verbatim[Condition][src_Diagram -> tgt_Diagram, cond_], opts : OptionsPattern[]] :=
	HypergraphRule[DiagramHypergraph[src, "Pattern" -> True], DiagramHypergraph[tgt], Hold[cond], opts]

labeledVertices[d_Diagram, f_] := MapThread[
	Labeled[f[#1], Replace[#2, {Automatic :> (Replace[#1["Name"], Labeled[l_, __] :> l]), False -> None}]] &,
	{Catenate @ d["InputOutputPorts", True], Catenate @ d["PortLabels"]}
]

labeledVertices[d_Diagram] := With[{f = d["PortFunction"]},
	Catenate[labeledVertices[#, f] & /@ DiagramSubdiagrams[d, {1}]]
]

DiagramHypergraph[ds : {___Diagram}, f_, vs_List, opts : OptionsPattern[]] := Enclose @ ConfirmBy[
	Hypergraph[
		vs,
		DiagramHyperedge[#, f, TrueQ[OptionValue["Pattern"]], TrueQ[OptionValue["Symmetric"]]] & /@ Select[ds, #["Arity"] > 0 &],
		"EdgeSymmetry" -> "Ordered",
		FilterRules[{opts}, Options[Hypergraph]]
	],
	HypergraphQ
]

DiagramHypergraph[d_Diagram, opts : OptionsPattern[]] := With[{net = Sow[SimplifyDiagram[ToDiagramNetwork[d]], "Net"]}, {f = net["PortFunction"]},
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
	portFunction_,
	match : KeyValuePattern[{"Hypergraph" -> hg_Hypergraph, "NewEdges" -> newEdges_, "Bindings" -> bindings_, "EdgeArities" -> arities_}]
] :=
	If[
		EdgeCount[hg] == 0
		,
		{EmptyDiagram[]}
		,
		With[{
			holdBindings = Normal @ KeyMap[HoldForm, HoldForm /@ Association[bindings]],
			optionRules = Append[_ -> {}] @ Thread[Through[#["Label"]] -> Through[#["DiagramOptions"]]] & @ srcDiagrams,
			portMap = Catenate[Thread[portFunction /@ Catenate[#["InputOutputPorts", True]] -> Catenate[#["AnnotatedInputOutputPorts"]]] & /@ srcDiagrams]
		},
			MapThread[
				With[{expr = Replace[#3, ((_ -> Underoverscript[HoldForm[x_], ___]) -> _) | x_ :> x]},
					Diagram[
						DiagramExpressionReplace[#1, _ :> expr],
						Sequence @@ MapThread[
							MapThread[If[MissingQ[#2], If[#1, PortDual, Port][#2], #2] &, {PadRight[#1, Length[#2], #1], #2}] &,
							{Map[#["DualQ"] &, #1["InputOutputPorts", True], {2}], Replace[#3, ((_ -> Underoverscript[_, _, nInputs_]) -> _) :> TakeDrop[#2, Total[Take[#4, nInputs]]]]}
						],
						Replace[Replace[#1["Label"], holdBindings], optionRules]
					]
				] &,
				{tgtDiagrams, Map[Lookup[portMap, Key[#]] &, newEdges, {2}], Replace[newEdges, OptionValue[hg, EdgeLabels], 1], arities}
			]
		]
	]


Options[DiagramReplaceList] = Join[{"Return" -> Automatic, "IgnoreArity" -> True}, Options[Diagram]]

DiagramReplaceList[d_Diagram, src_Diagram -> tgt_Diagram, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] :=
	DiagramReplaceList[d, (src -> tgt) /; True, n, opts]

DiagramReplaceList[d_Diagram, rule : Verbatim[Condition][src_Diagram -> tgt_Diagram, cond_], n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := Enclose @ Block[{
	tgtNet, tgtDiagrams, hgRule, net, diagrams, hg, nets,
	matches,
	return = OptionValue["Return"],
	diagramOptions = FilterRules[{opts}, Options[Diagram]],
	portFunction
},
	{srcNet, tgtNet} = Reap[hgRule = DiagramHypergraphRule[rule], "Net"][[2, 1]];
	tgtDiagrams = DiagramSubdiagrams[tgtNet, {1}];
	If[return === "Rule", Return[hgRule]];
	net = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork[d], DiagramQ];
	diagrams = DiagramSubdiagrams[net, {1}];
	portFunction = net["PortFunction"];
	hg = ConfirmBy[DiagramHypergraph[d], HypergraphQ];
	If[return === "Hypergraph", Return[hg]];
	matches = ConfirmMatch[hgRule[hg, "DistinctVertexLabels" -> False, "SymmetryMethod" -> None], {___ ? AssociationQ}];
	If[return === "Matches", Return[matches]];
	matches = Take[matches, UpTo[n]];
	nets = Map[
		With[{
			newNet = SimplifyDiagram @ DiagramNetwork[Join[Delete[diagrams, #["MatchEdgePositions"]], MatchDiagrams[Extract[diagrams, #["MatchEdgePositions"]], tgtDiagrams, portFunction, #]], "BinarySpiders" -> False],
			freeVertices = Complement[Union @@ EdgeList[#], VertexList[#]] & @ #["Hypergraph"]
		},
			If[freeVertices === {}, newNet, SingletonDiagram[newNet, freeVertices]]
		] &,
		matches
	];
	Diagram[#, Inherited, Inherited, FilterRules[{diagramOptions, d["DiagramOptions"]}, Except["PortArrows" | "PortLabels" | "PortFunction"]]] & /@ If[d["NetworkQ"], nets, DiagramArrange /@ nets]
]

DiagramReplaceList[d_Diagram, rules : {(_Rule | Verbatim[Condition][_Rule, _]) ..}, opts : OptionsPattern[]] := Switch[OptionValue["Return"],
	"Hypergraph",
	DiagramHypergraph[d],
	_,
	DiagramReplaceList[d, #, opts] & /@ rules
]

DiagramReplaceList[rules_][d_Diagram, opts : OptionsPattern[]] := DiagramReplaceList[d, rules, opts]


DiagramReplace[d_Diagram, rules_List, opts : OptionsPattern[]] := First[FoldWhile[DiagramReplaceList[d, #2, 1, opts] &, {}, rules, # === {} &], d]

DiagramReplace[d_Diagram, rule_, opts : OptionsPattern[]] := First[DiagramReplaceList[d, rule, 1, opts], d]

DiagramReplace[rule_][d_Diagram, opts : OptionsPattern[]] := DiagramReplace[d, rule, opts]


removeHypergraphWires[match_] := Block[{
	hg, labels, pos, edges, rules
},
	hg = match["Hypergraph"];
	labels = AnnotationValue[hg, EdgeLabels][[All, 2]];
	pos = Position[labels, ("Wires"[{{_, _} ..}] -> _) -> _, {1}, Heads -> False];
	edges = Extract[EdgeList[hg], pos];
	rules = Sow[Catenate @ MapThread[Rule @@@ Partition[Extract[#1, List /@ Catenate[#2]], 2] &, {edges, Extract[labels, pos][[All, 1, 1, 1]]}], "VertexReplace"];
	pos = Lookup[PositionIndex[match["NewEdges"]], edges];
	<|
		match,
		"Hypergraph" -> VertexReplace[
			EdgeDelete[hg, edges],
			rules
		],
		"NewEdges" -> Replace[Delete[match["NewEdges"], pos], rules, {2}],
		"EdgeArities" -> Delete[match["EdgeArities"], pos]
	|>
]

DiagramNestReplace[d_Diagram, rules : {(_Rule | Verbatim[Condition][_Rule, _]) ..}, n_Integer, opts : OptionsPattern[]] := Enclose @ Block[{
	hg, hgRules,
	portFunction, net, srcNets, tgtNets,
	match, vertexRules, newDiagrams, pos,
	diagramOptions = FilterRules[{opts}, Options[Diagram]]
},
	net = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork[d], DiagramQ];
	{srcNets, tgtNets} = Transpose @ Partition[Reap[hgRules = DiagramHypergraphRule /@ rules, "Net"][[2, 1]], 2];
	portFunction = net["PortFunction"];
	diagrams = DiagramSubdiagrams[net, {1}];
	hg = ConfirmBy[DiagramHypergraph[diagrams, portFunction, labeledVertices[net]], HypergraphQ];
	Do[
		Do[
			vertexRules = Flatten @ Reap[match = removeHypergraphWires @ First[hgRules[[i]][hg, "DistinctVertexLabels" -> False, "DistinctEdgeLabels" -> False, "SymmetryMethod" -> None], Continue[]], "VertexReplace"][[2]];
			hg = match["Hypergraph"];
			pos = match["MatchEdgePositions"];
			newDiagrams = MatchDiagrams[Extract[diagrams, pos], Select[DiagramSubdiagrams[tgtNets[[i]], {1}], ! MatchQ[#["OptionValue"["Shape"]], "Wires"[{{_, _} ..}]] &], portFunction, match];
			diagrams = Insert[
				DiagramPortReplace[#, vertexRules, portFunction] & /@ Delete[diagrams, pos],
				Splice[newDiagrams],
				Min[pos, Length[diagrams] + 1]
			];
			Break[]
			,
			{i, Length[hgRules]}
		],
		n
	];
	net = With[{
		newNet = DiagramNetwork[diagrams, "BinarySpiders" -> False],
		freeVertices = If[match === None, {}, Complement[Union @@ EdgeList[#], VertexList[#]] & @ match["Hypergraph"]]
	},
		If[freeVertices === {}, newNet, SingletonDiagram[newNet, freeVertices]]
	];
	Diagram[#, Inherited, Inherited, FilterRules[{diagramOptions, d["DiagramOptions"]}, Except["PortArrows" | "PortLabels" | "PortFunction"]]] & @ If[d["NetworkQ"], net, DiagramArrange[net]]
]

DiagramExpressionReplace[d_Diagram, rules_] :=
	DiagramMap[
		Diagram[#, "Expression" :> ## & @@ ReplaceAt[#["HoldExpression"], rules, {1}]] &,
		d
	]

DiagramPortReplace[d_Diagram, portRules_, portFunction_] :=
	Diagram[d, Sequence @@ Map[#["Apply", Replace[portFunction[#], portRules] &] &, d["InputOutputPorts"], {2}]]


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
		Interpretation[sym_Symbol, tag_] :> Interpretation[Evaluate[Pattern @@ Hold[sym, _]], tag],
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

Options[CommutationRule] = Join[{"Bend" -> False, "Dual" -> False, "Polarized" -> True, "Floating" -> True}, Options[Diagram]]

CommutationRule[ins : {$Port ...}, outs : {$Port ...}, opts : OptionsPattern[]] := CommutationRule[\[FormalF], "Copy", ins, outs, opts]

CommutationRule[expr1_, expr2_, ins : {$Port ...}, outs : {$Port ...}, opts : OptionsPattern[]] :=
	CommutationRule[
		Diagram[expr1, _, ins,
			FilterRules[{opts}, Options[Diagram]],
			"Shape" -> "RoundedTriangle", "Width" -> 1, "Height" -> 1, "FloatingPorts" -> If[TrueQ[OptionValue["Floating"]], {False, True}, False], "PortLabels" -> {None, Automatic}
		],
		Diagram[expr2, _, outs, FilterRules[{opts, "FloatingPorts" -> If[TrueQ[OptionValue["Floating"]], {False, True}, False], $CopyOptions, "PortLabels" -> {None, Automatic}}, Options[Diagram]]],
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
	diagOpts = FilterRules[{opts, Alignment -> Center, ImageSize -> {Automatic, 192}}, Options[Diagram]],
	arrowOpts = If[TrueQ[OptionValue["Polarized"]], {}, {"PortArrows" -> False}]
},
	If[ dualQ,
		ins = PortDual /@ ins;
		outs = PortDual /@ outs;
		port = PortDual @ port
	];
	diag = DiagramDual[Diagram[makePattern @ d, PortDual[port], makePattern /@ ins], "Singleton" -> False, arrowOpts];
	copy = Diagram[makePattern @ c, PortDual[port], makePattern /@ outs, "PortLabels" -> {None, Automatic}, arrowOpts];
	lhs = ColumnDiagram[
		If[	bendQ,
			{CupDiagram[port, arrowOpts], DiagramProduct[diag, copy]}
			,
			{diag = DiagramFlip[diag, "Singleton" -> False], copy}
		],
		diagOpts, If[bendQ, "HorizontalGapSize" -> 0, {}]
	];
	rhs = ColumnDiagram[{
			DiagramProduct @ Map[p |-> Diagram[c, p, Port[p]["Apply", #] & /@ Range[Length[outs]], arrowOpts, "PortLabels" -> {Automatic, None}], ins],
			DiagramProduct @ MapIndexed[{p, i} |-> Diagram[DiagramFlip[d], #["Apply", i[[1]]] & /@ ins, p, arrowOpts, "PortLabels" -> {None, Automatic}], outs]
		},
		diagOpts
	];
	lhs -> rhs
]


Options[EraserDiagram] = Join[{"Polarized" -> True, "Floating" -> True}, Options[CommutationRule]]

EraserDiagram[p_, opts : OptionsPattern[]] := Diagram[None, p, {}, opts, "Shape" -> "Disk", "Width" -> 1 / 2, "Height" -> 1 / 2, "PortLabels" -> None, "LabelFunction" -> ("\[Epsilon]" &)]

EraserRule[ports : {$Port ...}, opts : OptionsPattern[]] := CommutationRule[
	EraserDiagram[\[FormalX], FilterRules[{opts}, Except[Options[Diagram]]]],
	Diagram[_, \[FormalX], ports, "Shape" -> "RoundedTriangle", "Width" -> 1, "Height" -> 1,
	FilterRules[{opts}, Options[CommutationRule]]]
]


Options[AnnihilationRule] = Join[{"Bend" -> False, "Reverse" -> False, "Polarized" -> True, "Floating" -> True}, Options[Diagram]]

AnnihilationRule[d_Diagram, opts : OptionsPattern[]] /; d["InputArity"] > 0 := With[{ins = d["InputPorts"], outs = d["OutputPorts"]},
	AnnihilationRule[Diagram[d, _, PortDual /@ ins, "PortLabels" -> {False, True}], Diagram[d, _, outs, "PortLabels" -> {False, True}], opts]
]

AnnihilationRule[d1_Diagram, d2_Diagram, opts : OptionsPattern[]] /; d1["InputArity"] == d2["InputArity"] == 1 := Block[{
	ins = d1["OutputPorts"], outs = d2["OutputPorts"],
	port = First[d1["InputPorts"]],
	lhs, rhs,
	bendQ = TrueQ[OptionValue["Bend"]],
	diagOpts = FilterRules[{opts, Alignment -> Center, ImageSize -> {Automatic, 192}}, Options[Diagram]],
	arrowOpts = If[TrueQ[OptionValue["Polarized"]], {}, {"PortArrows" -> False}]
},
	lhs = ColumnDiagram[
		If[	bendQ,
			{CupDiagram[port, arrowOpts], DiagramProduct[Diagram[makePattern @ d1, port, PortDual /@ makePattern /@ ins, arrowOpts], Diagram[makePattern @ d2, PortDual[port], makePattern /@ outs, arrowOpts]]},
			{DiagramDual[DiagramFlip[Diagram[makePattern @ d1, makePattern /@ ins], "Singleton" -> False], "Singleton" -> False, arrowOpts], Diagram[makePattern @ d2, PortDual[port], makePattern /@ outs, arrowOpts]}
		],
		diagOpts,
		If[bendQ, "HorizontalGapSize" -> 0, {}]
	];
	
	rhs = DiagramProduct[
		MapThread[IdentityDiagram[#1 -> #2, arrowOpts] &, {ins, If[TrueQ[OptionValue["Reverse"]], Reverse[outs], outs]}],
		diagOpts,
		AspectRatio -> 2
	];
	lhs -> rhs
]

AnnihilationRule[expr1_, expr2_, ins : {$Port ...}, outs : {$Port ...}, opts : OptionsPattern[]] /; Length[ins] == Length[outs] := With[{
	diagramOpts = FilterRules[{opts, "Shape" -> "RoundedTriangle", "Width" -> 1, "FloatingPorts" -> If[TrueQ[OptionValue["Floating"]], {False, True}, False], "PortLabels" -> {None, Automatic}}, Options[Diagram]]
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


Options[PropagationRule] = Join[{"Polarized" -> True, "Floating" -> True}, Options[Diagram]]

PropagationRule[a : $Port, bs : {$Port ...}, f_, opts : OptionsPattern[]] := Block[{lhs, rhs, arrowOpts = If[TrueQ[OptionValue["Polarized"]], {}, {"PortArrows" -> False}], floating = If[TrueQ[OptionValue["Floating"]], {False, True}, False]},
	lhs = DiagramArrange @ DiagramNetwork[
		Diagram[Interpretation[\[FormalI]_, itag_], makePattern @ a, 1, arrowOpts, opts, "Height" -> 1 / 2, "Width" -> 1, "PortLabels" -> {True, False}],
		Diagram[Interpretation[\[FormalJ]_, jtag_], 1, makePattern /@ bs, arrowOpts, "Shape" -> "RoundedTriangle", "Width" -> 1, "PortLabels" -> {False, True}, "FloatingPorts" -> floating],
		Alignment -> Center,
		ImageSize -> {Automatic, 192}
	];
	rhs = DiagramArrange @ DiagramNetwork[
		Prepend[
			MapIndexed[Diagram[Interpretation[\[FormalI], itag], #2 + 1, #1, arrowOpts, opts, "Height" -> 1 / 2, "Width" -> 1, "PortLabels" -> {False, True}] &, bs],
			Diagram[Interpretation[f[\[FormalJ]], jtag], a, 1 + Range[Length[bs]], arrowOpts, "Shape" -> "RoundedTriangle", "Width" -> 1, "PortLabels" -> {True, False}, "FloatingPorts" -> floating]
		],
		Alignment -> Center,
		ImageSize -> {Automatic, 192}
	];
	lhs -> rhs
]


DiagramCopySplit[d_Diagram] := If[d["NetworkQ"], Identity, DiagramArrange][
	DiagramNetwork[
		Map[
			diag |->
			Which[
				MatchQ[diag["Arities"], {1, i_} /; i > 2],
				Splice @ FoldPairList[
					With[{i = #1[[2]]}, {outs = Replace[#2[[1]], Missing[p_] :> p["Apply", Replace[#["HoldName"], {
							HoldForm[Interpretation[label_, tag_]] :> Interpretation[label, tag[i]],
							HoldForm[label_] :> Interpretation[label, i]
						}] &], 1]}, {
						Diagram[diag, #1[[1]], outs,
							"PortArrows" -> {Inherited, #2[[2]]},
							"PortLabels" -> {Inherited, #2[[3]]},
							"Shape" -> Replace[diag["OptionValue"["Shape"]], "Wires"[_] :> "Wires"[{{1, 2}, {1, 3}}]]],
						{Last[outs], i + 1}
					}] &,
					{PortDual @ First @ diag["InputPorts"], 1},
					Thread[{MapAt[Missing, {;; -2, -1}] @ Partition[diag["OutputPorts"], 2, 1], Partition[diag["PortStyles"][[2]], 2, 1], Partition[diag["PortLabels"][[2]], 2, 1]}]
				],
				MatchQ[diag["Arities"], {i_, 1} /; i > 2],
				Splice @ FoldPairList[
					With[{i = #1[[2]]}, {ins = Replace[#2[[1]], Missing[p_] :> p["Apply", Replace[#["HoldName"], {
							HoldForm[Interpretation[label_, tag_]] :> Interpretation[label, tag[i]],
							HoldForm[label_] :> Interpretation[label, i]
						}] &], 1]}, {
						Diagram[diag, ins, #1[[1]],
							"PortArrows" -> {#2[[2]], Inherited},
							"PortLabels" -> {#2[[3]], Inherited},
							"Shape" -> Replace[diag["OptionValue"["Shape"]], "Wires"[_] :> "Wires"[{{3, 1}, {3, 2}}]]],
						{Last[ins], i + 1}
					}] &,
					{First @ diag["OutputPorts"], 1},
					Thread[{MapAt[Missing, {;; -2, -1}] @ Partition[PortDual /@ diag["InputPorts"], 2, 1], Partition[diag["PortStyles"][[1]], 2, 1], Partition[diag["PortLabels"][[1]], 2, 1]}]
				],
				True,
				diag
			],
			AnnotationValue[{#, VertexList[#]}, "Diagram"] & @ d["NetGraph", "UnarySpiders" -> False, "SpiderMethod" -> 2]
		],
		FilterRules[d["DiagramOptions"], Except["PortFunction"]]
	]
]


End[]

EndPackage[]

