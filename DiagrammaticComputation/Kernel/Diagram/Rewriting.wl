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


Begin["`Private`"]


Options[DiagramHypergraph] = Options[Hypergraph]

DiagramHyperedge[d_Diagram, f_] := Annotation[f /@ Catenate @ d["InputOutputPorts", True], EdgeLabels -> Underoverscript[d["HoldExpression"], d["OutputArity"], d["InputArity"]]]

Options[DiagramHypergraph] = Options[Hypergraph];

DiagramHypergraph[ds : {___Diagram}, f_, vs_List, opts : OptionsPattern[]] := Enclose @ Block[{
	hg = ConfirmBy[Hypergraph[vs, DiagramHyperedge[#, f] & /@ ds, "EdgeSymmetry" -> "Ordered", opts], HypergraphQ],
	edges
},
	edges = EdgeList[hg];
	EdgeDelete[hg, Extract[edges, Position[AnnotationValue[hg, EdgeLabels], _ -> Underoverscript[HoldForm[None], _, _]]]]
]

DiagramHypergraph[d_Diagram, opts : OptionsPattern[]] := With[{net = SimplifyDiagram[ToDiagramNetwork[d]]}, {f = net["PortFunction"]},
	DiagramHypergraph[DiagramSubdiagrams[net, {1}], f, f /@ net["Ports", True], opts]
]


ConformVertices[h1_Hypergraph, h2_Hypergraph] := Block[{vs1 = VertexList[h1], vs2 = VertexList[h2], targetEdges, targetLabels, vertexRules},
	targetEdges = EdgeList[h1];
	targetLabels = Values @ AnnotationValue[h1, EdgeLabels];
	vertexRules = Catenate @ MapThread[
		Catch[Thread[Extract[targetEdges, FirstPosition[targetLabels, #2, Throw[Nothing]]] -> (#1 /. Verbatim[Pattern][sym_Symbol, _] :> sym)]] &,
		{EdgeList[h2], Values @ AnnotationValue[h2, EdgeLabels]}
	];
	vertexRules = Join[Catch[# -> FirstCase[vs2, Replace[#, HoldForm[Labeled[p_, __]] :> HoldForm[Labeled[p, __]]], Throw[Nothing]]] & /@ vs1, vertexRules];
	VertexReplace[h1, Join[vertexRules, Thread[Take[vs1, UpTo[Length[vs2]]] -> Take[vs2, UpTo[Length[vs1]]]], vertexRules]]
]


DiagramHypergraphRule[d1_Diagram, d2_Diagram] := With[{h1 = DiagramHypergraph[d1], h2 = DiagramHypergraph[d2]},
	HypergraphRule[h1, ConformVertices[h2, h1]]
]


MatchDiagrams[diagrams : {___Diagram}, match : KeyValuePattern[{"Hypergraph" -> hg_Hypergraph, "NewEdges" -> newEdges_}]] :=
If[ EdgeCount[hg] == 0,
	{SpiderDiagram[VertexList[hg]]}
	,
	MapThread[
		Diagram[#1,
			"Expression" -> Replace[#3, Underoverscript[x_, ___] :> x],
			Thread[
				{"InputPorts", "OutputPorts"} ->
				TakeDrop[
					MapThread[
						If[#1["DualQ"], PortDual, Port][#2] &,
						{Catenate @ #1["InputOutputPorts", False], #2}
					],
					#1["InputArity"]
				]
			]
		] &,
		{diagrams, newEdges, Replace[newEdges, OptionValue[hg, EdgeLabels], 1]}
	]
]


Options[DiagramReplaceList] = Options[Diagram]

DiagramReplaceList[d_Diagram, src_Diagram -> tgt_Diagram, opts : OptionsPattern[]] := Enclose @ Block[{
	srcHg, tgtNet, tgtHg, tgtDiagrams, rule, net, diagrams, hg, nets,
	srcF = src["PortFunction"], tgtF = tgt["PortFunction"]
},
	srcHg = ConfirmBy[DiagramHypergraph[src], HypergraphQ];
	tgtNet = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork @ tgt, DiagramQ];
	tgtDiagrams = DiagramSubdiagrams[tgtNet, {1}];
	tgtHg = ConfirmBy[With[{f = tgtNet["PortFunction"]}, DiagramHypergraph[tgtDiagrams, f, f /@ tgtNet["Ports", True]]], HypergraphQ];
	rule = ConfirmBy[HypergraphRule[srcHg, ConformVertices[tgtHg, srcHg]], HypergraphRuleQ];
	net = ConfirmBy[SimplifyDiagram @ ToDiagramNetwork[d], DiagramQ];
	diagrams = DiagramSubdiagrams[net, {1}];
	hg = ConfirmBy[With[{f = net["PortFunction"]}, DiagramHypergraph[diagrams, f, f /@ net["Ports", True]]], HypergraphQ];
	nets = Map[
		DiagramNetwork[Join[Delete[diagrams, #["MatchEdgePositions"]], MatchDiagrams[Select[tgtDiagrams, ! MatchQ[#["HoldExpression"], HoldForm[None]] &], #]]] &,
		ConfirmMatch[rule[hg], {___ ? AssociationQ}]
	];
	
	Diagram[#, opts] & /@ If[nets === {}, {d}, Diagram[#, Inherited, Inherited, FilterRules[d["DiagramOptions"], Except["PortArrows"]]] & /@ If[d["NetworkQ"], nets, DiagramArrange /@ nets]]
]

DiagramReplaceList[d_Diagram, rules : {__Rule}, opts : OptionsPattern[]] := Fold[{ds, rule} |-> Catenate[DiagramReplaceList[#, rule, opts] & /@ ds], {d}, rules]


End[]

EndPackage[]

