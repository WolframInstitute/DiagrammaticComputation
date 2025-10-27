BeginPackage["Wolfram`DiagrammaticComputation`Diagram`Rewriting`", {
    "Wolfram`DiagrammaticComputation`Port`",
    "Wolfram`DiagrammaticComputation`Diagram`",
    "Wolfram`DiagrammaticComputation`Utilities`",
    "Wolfram`DiagrammaticComputation`Diagram`Surgery`",
    "Wolfram`DiagrammaticComputation`Diagram`Grid`",
    "WolframInstitute`Hypergraph`"
}]

DiagramHypergraph

DiagramReplaceList

DiagramExpressionReplace

RemoveDiagramRule
DiagramRule
DuplicateRule


Begin["`Private`"]


Options[DiagramHypergraph] = Options[Hypergraph]


patternLabelArities[d_Diagram] := Total /@ Replace[
	d["PortLabels"],
	{
		_BlankSequence | _BlankNullSequence | Verbatim[Pattern][_, _BlankSequence | _BlankNullSequence] -> Infinity,
		_ -> 1
	},
	{2}
]

DiagramHyperedge[d_Diagram, f_] := Annotation[
	labeledVertices[d, f],
	EdgeLabels -> (Underoverscript[d["Label"], ##] & @@ (Replace[patternLabelArities[d], Infinity -> _, 1]))
]

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
		DiagramHyperedge[#, f] & /@ ds,
		"EdgeSymmetry" -> "Ordered",
		opts
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

MatchDiagrams[diagrams : {___Diagram}, match : KeyValuePattern[{"Hypergraph" -> hg_Hypergraph, "MatchEdgePositions" -> pos_, "NewEdges" -> newEdges_, "Bindings" -> bindings_, "EdgeArities" -> arities_}]] :=
	If[
		EdgeCount[hg] == 0
		,
		{EmptyDiagram[]}
		,
		MapThread[
			Diagram[#1,
				Sequence @@ MapThread[
					MapThread[If[#1, PortDual, Port][#2] &, {PadRight[#1, Length[#2], #1], #2}] &,
					{Map[#["DualQ"] &, #1["InputOutputPorts", True], {2}], Replace[#3, Underoverscript[_, nInputs_, _] :> TakeDrop[#2, Total[Take[#4, nInputs]]]]}
				],
				Replace[#3, Underoverscript[HoldForm[x_], ___] | x_ :> "Expression" :> x],
				"PortLabels" -> (#1["PortLabels"] /. bindings)
			] &,
			{diagrams, newEdges, Replace[newEdges, OptionValue[hg, EdgeLabels], 1], arities}
		]
	]


Options[DiagramReplaceList] = Join[{"Return" -> Automatic}, Options[Diagram]]

DiagramReplaceList[d_Diagram, src_Diagram -> tgt_Diagram, opts : OptionsPattern[]] := Enclose @ Block[{
	srcHg, tgtNet, tgtHg, tgtDiagrams, rule, net, diagrams, hg, nets,
	srcF = src["PortFunction"], tgtF = tgt["PortFunction"],
	matches,
	return = OptionValue["Return"],
	diagramOptions = FilterRules[{opts}, Options[Diagram]]
},
	srcHg = ConfirmBy[DiagramHypergraph[src], HypergraphQ];
	tgtNet = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork @ tgt, DiagramQ];
	tgtDiagrams = DiagramSubdiagrams[tgtNet, {1}];
	tgtHg = ConfirmBy[With[{f = tgtNet["PortFunction"]}, DiagramHypergraph[tgtDiagrams, f, labeledVertices[tgtNet]]], HypergraphQ];
	rule = ConfirmBy[HypergraphRule[srcHg, tgtHg], HypergraphRuleQ];
	If[return === "Rule", Return[rule]];
	net = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork[d], DiagramQ];
	diagrams = DiagramSubdiagrams[net, {1}];
	hg = ConfirmBy[With[{f = net["PortFunction"]}, DiagramHypergraph[diagrams, f, labeledVertices[net, f]]], HypergraphQ];
	If[return === "Hypergraph", Return[hg]];
	matches = ConfirmMatch[rule[hg, "DistinctVertexLabels" -> False, "DistinctEdgeLabels" -> False], {___ ? AssociationQ}];
	If[return === "Matches", Return[matches]];
	nets = Map[
		With[{
			newNet = SimplifyDiagram @ DiagramNetwork[Join[Delete[diagrams, #["MatchEdgePositions"]], MatchDiagrams[tgtDiagrams, #]]],
			freeVertices = Complement[Union @@ EdgeList[#], VertexList[#]] & @ #["Hypergraph"]
		},
			If[freeVertices === {}, newNet, SingletonDiagram[newNet, freeVertices]]
		] &,
		matches
	];
	Diagram[#, diagramOptions] & /@ If[nets === {}, {d}, Diagram[#, Inherited, Inherited, FilterRules[d["DiagramOptions"], Except["PortArrows" | "PortLabels" | "PortFunction"]]] & /@ If[d["NetworkQ"], nets, DiagramArrange /@ nets]]
]

DiagramReplaceList[d_Diagram, rules : {__Rule}, opts : OptionsPattern[]] := Fold[{ds, rule} |-> Catenate[DiagramReplaceList[#, rule, opts] & /@ ds], {d}, rules]


DiagramExpressionReplace[d_Diagram, rules_] :=
	DiagramMap[
		Diagram[#, "Expression" -> (#["Expression"] /. rules)] &,
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
		MapThread[Labeled[#1, Pattern[#2, _]] &, {srcOutPorts, Drop[labels, Length[srcInPorts]]}]
	] ->
	DiagramAssignPorts[tgt,
		MapThread[Labeled, {tgtInPorts, Take[labels, Length[tgtInPorts]]}],
		MapThread[Labeled, {tgtOutPorts, Drop[labels, Length[tgtInPorts]]}]
	]
]

DiagramRule[src_Diagram -> tgt_Diagram] := DiagramRule[src, tgt]


Options[DuplicateRule] = Options[CopyDiagram];

patternPort[expr : _Symbol | SuperStar[_Symbol]] :=
	Replace[expr, {sym_Symbol :> Pattern @@ {sym, _}, SuperStar[sym_Symbol] :> SuperStar[Pattern @@ {sym, _}]}]

DuplicateRule[ins : {(_Symbol | SuperStar[_Symbol]) ..}, outs : {(_Symbol | SuperStar[_Symbol]) ..}, opts : OptionsPattern[]] := Block[{
	copyOpts = {"Shape" -> "Triangle", "Width" -> 1, "Style" -> Hue[0.709, 0.445, 1], opts}, lhs, rhs
},
	lhs = DiagramRightComposition[
		Diagram[\[FormalF]_, patternPort /@ ins, \[FormalX], "PortLabels" -> {Automatic, None}],
		CopyDiagram[\[FormalX], patternPort /@ outs, copyOpts],
		Alignment -> Center
	];
	rhs = DiagramRightComposition[
		DiagramProduct @ Map[p |-> CopyDiagram[p, Port[p]["Apply", #] & /@ Range[Length[outs]], copyOpts, "PortLabels" -> {Automatic, None}, "FloatingPorts" -> False], ins],
		DiagramProduct @ MapIndexed[{p, i} |-> Diagram[\[FormalF], Port[#]["Apply", i[[1]]] & /@ ins, p, "PortLabels" -> {None, Automatic}], outs]
	];
	lhs -> rhs
]

End[]

EndPackage[]

