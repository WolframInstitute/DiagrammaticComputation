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
DiagramReplace

DiagramExpressionReplace

RemoveDiagramRule
DiagramRule

DuplicateRule
EraserRule
AnnihilateRule
DuplicateAnnihilateRule

DiagramCopySplit



Begin["`Private`"]


Options[DiagramHypergraph] = Join[{"Pattern" -> False}, Options[Hypergraph]]


patternLabelArities[d_Diagram] := Total /@ Replace[
	d["PortLabels"],
	{
		_BlankSequence | _BlankNullSequence | Verbatim[Pattern][_, _BlankSequence | _BlankNullSequence] -> Infinity,
		_ -> 1
	},
	{2}
]

DiagramHyperedge[d_Diagram, f_, pattQ : _ ? BooleanQ] := With[{unordered = pattQ && TrueQ[d["OptionValue"["FloatingPorts"]]]},
	Annotation[
		labeledVertices[d, f],
		EdgeLabels -> (Underoverscript[d["Label"], #2, #1] & @@ If[unordered, {_, _}, Replace[patternLabelArities[d], Infinity -> _, 1]]),
		"EdgeSymmetry" -> If[unordered, "Unordered", "Ordered"]
	]
]

labeledVertices[d_Diagram, f_] := MapThread[
	Labeled[f[#1], {Replace[#2, {Automatic :> (Replace[#1["Name"], Labeled[l_, __] :> l]), False -> None}], #["DualQ"]}] &,
	{Catenate @ d["InputOutputPorts", True], Catenate @ d["PortLabels"], Catenate @ d["PortStyles"]}
]

labeledVertices[d_Diagram] := With[{f = d["PortFunction"]},
	Catenate[labeledVertices[#, f] & /@ DiagramSubdiagrams[d, {1}]]
]

DiagramHypergraph[ds : {___Diagram}, f_, vs_List, opts : OptionsPattern[]] := Enclose @ ConfirmBy[
	Hypergraph[
		vs,
		DiagramHyperedge[#, f, TrueQ[OptionValue["Pattern"]]] & /@ ds,
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
			holdBindings = Append[_ -> Missing[]] @ Normal @ KeyMap[HoldForm, HoldForm /@ Association[bindings]],
			optionRules = Append[_ -> {}] @ Thread[Through[srcDiagrams["HoldExpression"]] -> Through[srcDiagrams["DiagramOptions"]]]
		},
			MapThread[
				Diagram[#1,
					Sequence @@ MapThread[
						MapThread[If[#1, PortDual, Port][#2] &, {PadRight[#1, Length[#2], #1], #2}] &,
						{Map[#["DualQ"] &, #1["InputOutputPorts", True], {2}], Replace[#3, Underoverscript[_, _, nInputs_] :> TakeDrop[#2, Total[Take[#4, nInputs]]]]}
					],
					Replace[#3, Underoverscript[HoldForm[x_], ___] | x_ :> "Expression" :> x],
					"PortLabels" -> (#1["PortLabels"] /. bindings),
					Replace[Replace[#1["HoldExpression"], holdBindings], optionRules]
				] &,
				{tgtDiagrams, newEdges, Replace[newEdges, OptionValue[hg, EdgeLabels], 1], arities}
			]
		]
	]


Options[DiagramReplaceList] = Join[{"Return" -> Automatic}, Options[Diagram]]

DiagramReplaceList[d_Diagram, src_Diagram -> tgt_Diagram, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := Enclose @ Block[{
	srcHg, tgtNet, tgtHg, tgtDiagrams, rule, net, diagrams, hg, nets,
	srcF = src["PortFunction"], tgtF = tgt["PortFunction"],
	matches,
	return = OptionValue["Return"],
	diagramOptions = FilterRules[{opts}, Options[Diagram]]
},
	srcHg = ConfirmBy[DiagramHypergraph[src, "Pattern" -> True], HypergraphQ];
	tgtNet = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork @ tgt, DiagramQ];
	tgtDiagrams = DiagramSubdiagrams[tgtNet, {1}];
	tgtHg = ConfirmBy[With[{f = tgtNet["PortFunction"]}, DiagramHypergraph[tgtDiagrams, f, labeledVertices[tgtNet]]], HypergraphQ];
	rule = ConfirmBy[HypergraphRule[srcHg, tgtHg], HypergraphRuleQ];
	If[return === "Rule", Return[rule]];
	net = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork[d], DiagramQ];
	diagrams = DiagramSubdiagrams[net, {1}];
	hg = ConfirmBy[With[{f = net["PortFunction"]}, DiagramHypergraph[diagrams, f, labeledVertices[net, f]]], HypergraphQ];
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


DiagramReplace[d_Diagram, rules_List, opts : OptionsPattern[]] := First[FoldWhile[DiagramReplaceList[d, #2, 1, opts] &, {}, rules, # === {} &], d]

DiagramReplace[d_Diagram, rule_, opts : OptionsPattern[]] := First[DiagramReplaceList[d, rule, 1, opts], d]

DiagramReplace[rule_][d_Diagram] := DiagramReplace[d, rule]


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


Options[DuplicateRule] = Options[EraserRule] = Options[DuplicateAnnihilateRule] = Options[Diagram];

patternPort[expr : _Symbol | SuperStar[_Symbol]] :=
	Replace[expr, {sym_Symbol :> Pattern @@ {sym, _}, SuperStar[sym_Symbol] :> SuperStar[Pattern @@ {sym, _}]}]

DuplicateRule[ins : {(_Symbol | SuperStar[_Symbol]) ...}, outs : {(_Symbol | SuperStar[_Symbol]) ...}, opts : OptionsPattern[]] := Block[{
	copyOpts = {opts, "Shape" -> "Triangle", "Width" -> 1, "Style" -> Hue[0.709, 0.445, 1]},
	nodeOpts = {"Shape" -> "UpsideDownTriangle", "Width" -> 1},
	lhs, rhs
},
	lhs = DiagramRightComposition[
		Diagram[\[FormalF]_, patternPort /@ ins, \[FormalX], "PortLabels" -> {Automatic, None}, nodeOpts],
		CopyDiagram[\[FormalX], patternPort /@ outs, copyOpts],
		Alignment -> Center
	];
	rhs = DiagramRightComposition[
		DiagramProduct @ Map[p |-> CopyDiagram[p, Port[p]["Apply", #] & /@ Range[Length[outs]], copyOpts, "PortLabels" -> {Automatic, None}], ins],
		DiagramProduct @ MapIndexed[{p, i} |-> Diagram[\[FormalF], Port[#]["Apply", i[[1]]] & /@ ins, p, "PortLabels" -> {None, Automatic}, nodeOpts], outs]
	];
	lhs -> rhs
]

EraserRule[ports : {(_Symbol | SuperStar[_Symbol]) ...}, opts : OptionsPattern[]] := DuplicateRule[ports, {}, "Expression" :> None, "Style" -> Automatic]


Options[AnnihilateRule] = Join[{"Bend" -> False}, Options[Diagram]]

AnnihilateRule[expr1_, expr2_, ins : {(_Symbol | SuperStar[_Symbol]) ...}, outs : {(_Symbol | SuperStar[_Symbol]) ...}, opts : OptionsPattern[]] /; Length[ins] == Length[outs] := Block[{
	diagramOpts = FilterRules[{opts, "Width" -> 1, "PortLabels" -> {None, Automatic}}, Options[Diagram]],
	d, lhs, rhs
},
	d = Diagram[expr1, SuperStar[_], patternPort /@ ins, diagramOpts];
	lhs = DiagramArrange @ DiagramNetwork[
		If[	TrueQ[OptionValue["Bend"]], d, DiagramFlip[d]],
		Diagram[expr2, _, patternPort /@ outs, diagramOpts],
		Alignment -> Center
	];
	rhs = DiagramProduct[MapThread[IdentityDiagram[PortDual[#1] -> #2] &, {ins, outs}]];
	lhs -> rhs	
]

DuplicateAnnihilateRule[ins : {(_Symbol | SuperStar[_Symbol]) ...}, outs : {(_Symbol | SuperStar[_Symbol]) ...}, opts : OptionsPattern[]] /; Length[ins] == Length[outs] :=
	AnnihilateRule["Copy", "Copy", ins, outs, opts, "Shape" -> "Triangle", "Style" -> Hue[0.709, 0.445, 1], "ShowLabel" -> False, "FloatingPorts" -> True]


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

