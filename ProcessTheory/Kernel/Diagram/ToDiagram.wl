BeginPackage["ProcessTheory`Diagram`ToDiagram`", {"ProcessTheory`Port`"}];

ToDiagram

Begin["ProcessTheory`Diagram`ToDiagram`Private`"];


ToDiagram[g_Graph, opts : OptionsPattern[GraphDiagram]] := GraphDiagram[g, opts]
ToDiagram[hg : {___List} | _WolframInstitute`Hypergraph`Hypergraph, opts : OptionsPattern[HypergraphDiagram]] := HypergraphDiagram[hg, opts]
ToDiagram[ng_NetGraph, opts : OptionsPattern[NetGraphDiagram]] := NetGraphDiagram[NetFlatten[ng], opts]
ToDiagram[sm : HoldPattern[_SystemModel], opts : OptionsPattern[SystemModelDiagram]] := SystemModelDiagram[sm, {}, opts]
ToDiagram[qc_Wolfram`QuantumFramework`QuantumCircuitOperator, opts : OptionsPattern[QuantumCircuitDiagram]] := QuantumCircuitDiagram[qc, opts]
ToDiagram[expr_, opts : OptionsPattern[LambdaDiagram]] := LambdaDiagram[expr, opts]


Options[GraphDiagram] = Options[DiagramNetwork];
GraphDiagram[g_Graph, opts : OptionsPattern[]] := 
	DiagramNetwork[##, opts] & @@ (Diagram[#, EdgeList[g, _[_, #, ___]], EdgeList[g, _[#, __]]] & /@ VertexList[g])


Options[HypergraphDiagram] = Options[DiagramNetwork];
HypergraphDiagram[hg : {___List}, opts : OptionsPattern[]] :=
	DiagramNetwork[##, opts] & @@ MapIndexed[Diagram[#2[[1]], #1, "Shape" -> "Circle"] &, hg]
HypergraphDiagram[hg_WolframInstitute`Hypergraph`Hypergraph, opts : OptionsPattern[]] :=
	DiagramNetwork[##, opts] & @@ MapIndexed[Diagram[If[#1[[2]] === None, #2[[1]], #1[[2]]], Replace[#1[[1]], (e_ -> _) :> e], "Shape" -> "Circle"] &, Lookup[AbsoluteOptions[hg], EdgeLabels]]


Options[NetGraphDiagram] = Options[DiagramNetwork];
NetGraphDiagram[ng_NetGraph, opts : OptionsPattern[]] := Block[{
	layers = Information[ng, "Layers"],
	freeOutputPorts, freeInputPorts, outputPorts, inputPorts,
	edges, rules,
	diagrams
},
	freeOutputPorts = First /@ PositionIndex @ Information[ng, "OutputPortNames"];
	freeInputPorts = First /@ PositionIndex @ Information[ng, "InputPortNames"];
	outputPorts = First /@ PositionIndex[Information[#, "OutputPortNames"]] & /@ layers;
	inputPorts = First /@ PositionIndex[Information[#, "InputPortNames"]] & /@ layers;
	edges = NeuralNetworks`NetGraphEdges[ng] /. {
		NetPort[port_] /; KeyExistsQ[freeOutputPorts, port] :> Length[layers] + Length[freeInputPorts] + Lookup[freeOutputPorts, port],
		NetPort[port_] /; KeyExistsQ[freeInputPorts, port] :> Length[layers] + Lookup[freeInputPorts, port],
		NetPort[{x_, port_String}] :> Block[{key = Key[{x}], outputQ},
			layer = Lookup[layers, key];
			outputQ = KeyExistsQ[Lookup[outputPorts, key], port];
			{x, If[outputQ, 2, 1], Lookup[If[outputQ, Lookup[outputPorts, key], Lookup[inputPorts, key]], port, 2]}
		]
	};
	edges = Replace[edges, {
		(idx1 : _Integer | _String -> idx2 : _Integer | _String) :> {idx1, 2, 1} -> {idx2, 1, 1},
		(idx : _Integer | _String  -> port_List) :> {idx, 2, 1} -> port,
		(port_ -> idx : _Integer | _String) :> port -> {idx, 1, 1}
	}, 1];
	rules = Reverse /@ edges;
	
	diagrams = MapIndexed[With[{i = #2[[1, 1, 1]]},
		Diagram[
			Interpretation[Replace[#, _[assoc_,___] :> Graphics @ NeuralNetworks`Private`GetPanelIcon[assoc]], #],
			MapIndexed[Interpretation @@ {Replace[{i, 1, #2[[1]]}, rules], Construct @@ #1} &, Normal @ Information[#, "InputPorts"]],
			MapIndexed[Interpretation @@ {{i, 2, #2[[1]]}, Construct @@ #1} &, Normal @ Information[#, "OutputPorts"]]
		]] &,
		layers
	];
	DiagramNetwork[##, opts] & @@ diagrams
]


Options[SystemModelDiagram] = Options[DiagramNetwork];
SystemModelDiagram[sm : HoldPattern[_SystemModel], path_, opts : OptionsPattern[]] := Block[{name = sm[[1]], components, connections, parameters, transforms},
	{components, connections, parameters, transforms} = Quiet @ Check[sm /@ {"Components", "Connections", "ParameterNames", "Diagram"}, {{}, {}, {}, {}}, SystemModel::nomod];
	connections = Rule @@@ Map[StringSplit[#, "."] &, connections, {2}];
	parameters = HoldForm[Evaluate[Information[#, "Identifier"]]] & /@ parameters;
	transforms = Cases[
		transforms,
		Annotation[Tooltip[{Rotate[Scale[Translate[_, tr_], scale__], rot__], ___}, c_], _] :>
			c -> {{rot}, {scale}, tr},
		All
	];
	If[ components === {},
		Port[Interpretation[Last[path], path], name],
		With[{assoc = Association @ Map[Apply[#1 -> SystemModelDiagram[#2, Append[path, #1]] &], components]},
			If[ AllTrue[assoc, PortQ],
				With[{ports = <|True -> {}, False -> {}, GroupBy[Values[assoc], MemberQ[parameters, #["Name"]] &]|>}, Diagram[Interpretation[Show[sm["Thumbnail"], ImageSize -> 16], sm["ModelName"]], ports[True], ports[False]]],
				If[Length[assoc] == 1, #, DiagramNetwork[##,
					opts,
					"PortFunction" -> With[{c = Replace[connections, (lhs_ -> rhs_) :> Append[lhs, x___] -> Append[rhs, x], 1]},
						Replace[#["Expression"], Interpretation[_, p_] | PortDual[Interpretation[_, p_]] :> HoldForm[Evaluate @ Replace[p, c]]] &
					],
					"LabelFunction" -> Function[Evaluate[ClickToCopy[Show[sm["Thumbnail"], ImageSize -> 32], #["View"]]]],
					"ShowWireLabels" -> False,
					"Orientation" -> None,
					PlotLabel -> name
				]] & @@ KeyValueMap[
					Diagram[
						If[DiagramQ[#2], #2, If[MemberQ[parameters, #2["Name"]], Diagram[#2, #2, {}, "Shape" -> "Triangle"], Diagram[#2, #2, "Shape" -> "UpsideDownTriangle"]]],
						"Width" -> 20,
						"Height" -> 20,
						"Angle" -> Lookup[transforms, #1, 0, #[[1, 1]] &],
						"Center" ->  Lookup[transforms, #1, {0, 0}, #[[3]] &]
					] &,
					assoc
				]
			]
		]
	]
]


LambdaDiagrams[Interpretation["\[Lambda]", tag_][body_][arg_], depth_] := Block[{bodyDiagram, argDiagram = DiagramNetwork @@ LambdaDiagrams[arg, depth], out},
	out = argDiagram["OutputPorts"][[1]];
	bodyDiagram = DiagramNetwork @@ LambdaDiagrams[body /. Interpretation[v_Integer, tag] :> Interpretation[v, Evaluate @ out], depth + 1];
	Join[
		{
			Diagram["\[Lambda]", \[FormalX][tag], tag, "Shape" -> "Circle"],
			Diagram["\[Application]", {bodyDiagram["OutputPorts"][[1]], out}, \[FormalX][tag], "Shape" -> "Triangle"]
		},
		bodyDiagram["SubDiagrams"], argDiagram["SubDiagrams"]
	]
] 
LambdaDiagrams[Interpretation["\[Lambda]", tag_][body_], depth_] := With[{bodyDiagrams = LambdaDiagrams[body, depth]}, Join[{Diagram["\[Lambda]", \[FormalX][tag], tag, "Shape" -> "Circle"]}, bodyDiagrams]]
LambdaDiagrams[Interpretation[_Integer, f_][Interpretation[_Integer, x_]], _] := {Diagram["\[Application]", {f, x}, Unique["x"], "Shape" -> "Triangle"]}
LambdaDiagrams[Interpretation[_Integer, tag : _Port | _Symbol][arg_], depth_] := With[{argDiagram = DiagramNetwork @@ LambdaDiagrams[arg, depth]},
	Join[{Diagram["\[Application]", {tag, argDiagram["OutputPorts"][[1]]}, Unique["x"], "Shape" -> "Triangle"]}, argDiagram["SubDiagrams"]]
]
LambdaDiagrams[Interpretation[v_Integer, tag : _Port | _Symbol], _] := With[{port = Port[tag]}, {Diagram["", port, \[FormalO][port["Name"]], "Shape" -> "Circle"]}]
LambdaDiagrams[i_Interpretation[_Integer, _], _] := {}
LambdaDiagrams[f_[xs___], depth_] := Block[{fDiagram, xDiagrams = DiagramNetwork @@ LambdaDiagrams[#, depth] & /@ {xs}, out},
	out = Catenate[Through[xDiagrams["OutputPorts"]]];
	fDiagram = DiagramNetwork @@ LambdaDiagrams[f /. Interpretation[_Integer, var_Integer] :> Interpretation[var, Evaluate @ out], depth];
	Join[fDiagram["SubDiagrams"], {Diagram["\[Application]", Join[fDiagram["OutputPorts"], out], Unique["x"], "Shape" -> "Triangle"]},
		Catenate[Through[xDiagrams["SubDiagrams"]]]]
]
LambdaDiagrams[x_, _] := {Diagram[x, Unique["x"], "Shape" -> "UpsideDownTriangle"]}


ToDiagram::missing = "Lambda package is not loaded. Please install the package with \!\(\*TemplateBox[List[StyleBox[TagBox[RowBox[List[\"PacletInstall\", \
\"[\", \
\"\\\"Wolfram/Lambda\\\"\", \"]\"]], HoldForm], \"Hyperlink\", \
Rule[StripOnInput, False]], RowBox[List[\"PacletInstall\", \"[\", \
\"\\\"Wolfram/Lambda\\\"\", \"]\"]]], \"ClickToCopy2\"]\)";

Options[LambdaDiagram] = Options[DiagramNetwork];
LambdaDiagram[expr_, depth_Integer : 0, opts : OptionsPattern[]] := Module[{lambdaIdx = 1},
	Quiet[Check[Needs["Wolfram`Lambda`"], Message[ToDiagram::missing]; Return[$Failed]], {Get::noopen, Needs::nocont}];
	DiagramNetwork[##, opts, "ShowPortLabels" -> False, "PortLabels" -> False, "ShowWireLabels" -> False] & @@ 
		Map[
			If[#["Name"] === HoldForm["\[Lambda]"], Diagram[#, "Expression" -> Style["\[Lambda]", 16, Bold, ColorData[109][lambdaIdx++]]], #] &,
			LambdaDiagrams[Wolfram`Lambda`TagLambda[expr], depth]
		]
]



QuantumCircuitDiagram[qc_Wolfram`QuantumFramework`QuantumCircuitOperator, opts : OptionsPattern[]] := With[{d = DiagramComposition[##, "PortFunction" -> (#["HoldExpression"] &)] & @@ (
	Diagram[
		Interpretation[#["CircuitDiagram", "WireLabels" -> None, "ShowEmptyWires" -> False, "ShowGateLabels" -> False, "ShowMeasurementWire" -> False, ImageSize -> 16], #],
		KeyValueMap[Interpretation[#2, #1] &, #["OutputOrderDimensions"]],
		KeyValueMap[Interpretation[#2, #1] &, #["InputOrderDimensions"]]
	] & /@ Reverse[qc["Sort"]["NormalOperators"]])
},
	Diagram[d, "OutputPorts" -> SortBy[d["OutputPorts"], #["Name"] &], "InputPorts" -> SortBy[d["InputPorts"], #["Name"] &]]
]


End[];

EndPackage[];