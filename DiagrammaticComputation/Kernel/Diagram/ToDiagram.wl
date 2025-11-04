BeginPackage["Wolfram`DiagrammaticComputation`Diagram`ToDiagram`", {"Wolfram`DiagrammaticComputation`Utilities`", "Wolfram`DiagrammaticComputation`Port`", "Wolfram`DiagrammaticComputation`Diagram`", "Wolfram`DiagrammaticComputation`Diagram`Grid`"}];

ToDiagram

Begin["Wolfram`DiagrammaticComputation`Diagram`ToDiagram`Private`"];


ToDiagram[g_Graph, opts : OptionsPattern[GraphDiagram]] := GraphDiagram[g, opts]
ToDiagram[t_Tree, opts : OptionsPattern[TreeDiagram]] := TreeDiagram[t, opts]
ToDiagram[hg : {___List} | _WolframInstitute`Hypergraph`Hypergraph, opts : OptionsPattern[HypergraphDiagram]] := HypergraphDiagram[hg, opts]
ToDiagram[ng : HoldPattern[_NetGraph], opts : OptionsPattern[NetGraphDiagram]] := NetGraphDiagram[NetFlatten[ng], opts]
ToDiagram[sm : HoldPattern[_SystemModel], opts : OptionsPattern[SystemModelDiagram]] := SystemModelDiagram[sm, {}, opts]
ToDiagram[qc_Wolfram`QuantumFramework`QuantumCircuitOperator, opts : OptionsPattern[QuantumCircuitDiagram]] := QuantumCircuitDiagram[qc, opts]
ToDiagram[perm_Cycles, opts : OptionsPattern[Diagram]] := With[{inputs = Range[PermutationLength[perm]]}, PermutationDiagram[inputs -> Permute[inputs, perm], perm, opts]]
ToDiagram[expr_, opts : OptionsPattern[LambdaDiagram]] := LambdaDiagram[expr, opts]


Options[GraphDiagram] = Options[DiagramNetwork];
GraphDiagram[g_Graph, opts : OptionsPattern[]] := 
	DiagramNetwork[##, opts] & @@ (Diagram[#, EdgeList[g, _[_, #, ___]], EdgeList[g, _[#, __]]] & /@ VertexList[g])


Options[treeDiagram] = Options[Tree];
treeDiagram[t_Tree, pos_List, opts : OptionsPattern[]] := Block[{data = TreeData[t], children = Replace[TreeChildren[t], None -> {}], diagram},
	If[	children === {}
		,
		Diagram[data, {pos}, {}]
		,
		diagram = DiagramProduct @@ MapIndexed[treeDiagram[#1, Join[pos, #2], opts] &, children];
		DiagramComposition[diagram, Diagram[data, {pos}, PortDual /@ diagram["FlatInputPorts"]], opts]
	]
]

Options[TreeDiagram] = Options[treeDiagram];
TreeDiagram[t_Tree, opts : OptionsPattern[]] := treeDiagram[t, {}, opts]


Options[HypergraphDiagram] = Options[DiagramNetwork];
HypergraphDiagram[hg : {___List}, opts : OptionsPattern[]] :=
	DiagramNetwork[##, opts] & @@ MapIndexed[Diagram[#2[[1]], #1, "Shape" -> "Circle"] &, hg]
HypergraphDiagram[hg_WolframInstitute`Hypergraph`Hypergraph, opts : OptionsPattern[]] :=
	DiagramNetwork[##, opts] & @@ MapIndexed[Diagram[If[#1[[2]] === None, #2[[1]], #1[[2]]], Replace[#1[[1]], (e_ -> _) :> e], "Shape" -> "Circle"] &, Lookup[AbsoluteOptions[hg], EdgeLabels]]


Options[NetGraphDiagram] = Options[DiagramNetwork];
NetGraphDiagram[ng : HoldPattern[_NetGraph], opts : OptionsPattern[]] := Block[{
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
			MapIndexed[Interpretation @@ {Construct @@ #1, Replace[{i, 1, #2[[1]]}, rules]} &, Normal @ Information[#, "InputPorts"]],
			MapIndexed[Interpretation @@ {Construct @@ #1, {i, 2, #2[[1]]}} &, Normal @ Information[#, "OutputPorts"]]
		]] &,
		layers
	];
	DiagramNetwork[##, "PortFunction" -> (#["Apply", HoldForm[Evaluate[#["Expression"][[2]]]] &] &), opts] & @@ diagrams
]


Options[SystemModelDiagram] = Options[DiagramNetwork];
SystemModelDiagram[sm : HoldPattern[_SystemModel], path_, opts : OptionsPattern[]] := Block[{name = sm[[1]], components, connections, parameters, transforms},
	{components, connections, parameters, transforms} = Quiet @ Check[sm /@ {"Components", "Connections", "ParameterNames", "Diagram"}, {{}, {}, {}, {}}, SystemModel::nomod];
	connections = Rule @@@ Map[StringSplit[#, "."] &, connections, {2}];
	parameters = Information[#, "Identifier"] & /@ parameters;
	transforms = Cases[
		transforms,
		Annotation[Tooltip[{Rotate[Scale[Translate[_, tr_], scale__], rot__], ___}, c_], _] :>
			c -> {{rot}, {scale}, tr},
		All
	];
	If[ components === {},
		Port[Interpretation[Evaluate[Last[path]], path], name],
		With[{assoc = Association @ Map[Apply[#1 -> SystemModelDiagram[#2, Append[path, #1]] &], components]},
			If[ AllTrue[assoc, PortQ],
				With[{ports = <|True -> {}, False -> {}, GroupBy[Values[assoc], MemberQ[parameters, #["Name"]] &]|>}, Diagram[Interpretation[Show[sm["Thumbnail"], ImageSize -> 16], sm["ModelName"]], ports[True], ports[False]]],
				DiagramNetwork[##,
					opts,
					"PortFunction" -> With[{c = Replace[connections, (lhs_ -> rhs_) :> (Append[lhs, x___] -> Append[rhs, x]), 1]},
						#["Apply", Replace[#["HoldName"], HoldForm[Interpretation[_, p_]] :> HoldForm[Evaluate @ Replace[p, c]]] &] &
					],
					"LabelFunction" -> Function[Evaluate[ClickToCopy[Show[sm["Thumbnail"], ImageSize -> 32], #["View"]]]],
					"ShowWireLabels" -> False,
					"Orientation" -> None,
					PlotLabel -> name
				] & @@ KeyValueMap[
					Diagram[
						If[DiagramQ[#2], #2, If[MemberQ[parameters, #2["Name"]], Diagram[#2, #2, {}, "Shape" -> "Triangle"], Diagram[#2, #2, "Shape" -> "UpsideDownTriangle"]]],
						"Angle" -> Lookup[transforms, #1, 0, #[[1, 1]] &],
						"Center" ->  Lookup[transforms, #1, {0, 0}, #[[3]] &]
					] &,
					assoc
				]
			]
		]
	]
]

lambdaDiagram[tag_, port_, level_ : None] := Diagram[
	If[level === None, Subscript["\[Lambda]", tag], Interpretation[level, Subscript["\[Lambda]", tag]]],
	{PortDual[Interpretation[Evaluate[If[level === None, tag, tag[level]]], \[FormalX]]], port},
	Subscript["\[Lambda]", tag],
	"Shape" -> "RoundRectangle",
	"Style" -> Lookup[Lookup[Options[Wolfram`Lambda`LambdaTree], ColorRules], "Lambda"],
	"LabelStyle" -> Directive[FontWeight -> Bold, Black],
	"PortLabels" -> None,
	"Width" -> 1 / GoldenRatio, "Height" -> 1
]

applicationDiagram[f_, xs_List, level_ : None] := With[{fPort = Port[f], ports = Port /@ xs},
	Diagram[
		If[level === None, "\[Application]", Interpretation[level, "\[Application]"]],
		Append[ports, fPort],
		Interpretation @@ {fPort["Name"] @@ Through[ports["Name"]], Unique["app"]},
		"Shape" -> "Disk",
		"Style" -> Lookup[Lookup[Options[Wolfram`Lambda`LambdaTree], ColorRules], "Application"],
		"LabelStyle" -> Directive[FontWeight -> Bold, Black],
		"ShowLabel" -> level =!= None,
		"PortLabels" -> None,
		"Width" -> 1 / 2, "Height" -> 1 / 2
	]
]

varDiagram[tag_] := CupDiagram[{PortDual[Interpretation[tag, \[FormalX][tag]]], tag}, "PortLabels" -> None]

eraserDiagram[tag_] := Diagram[None, PortDual[Interpretation[tag, \[FormalX][tag]]], "Shape" -> "Disk", "Width" -> 1 / 2, "Height" -> 1 / 2, "PortLabels" -> None]


Options[LambdaDiagrams] = Options[LambdaGridDiagram] = {"AddCroissantBrackets" -> False}

rootPort[d_Diagram] := First[d["OutputPorts"]]

auxPorts[d_Diagram] := Complement[d["OutputPorts"], d["GraphOutputPorts"]]

LambdaDiagrams[Interpretation["\[Lambda]", var_][body_], depth_, level_, opts : OptionsPattern[]] := Block[{
	bodyDiagram = DiagramNetwork @ LambdaDiagrams[body, depth + 1, level, opts],
	tag = HoldForm[var],
	lvl = If[TrueQ[OptionValue["AddCroissantBrackets"]], level, None]
},
	Join[
		{
			lambdaDiagram[tag, rootPort[bodyDiagram], lvl]
		},
		bodyDiagram["SubDiagrams"]
	]
]

LambdaDiagrams[Interpretation[_Integer | _HoldForm, var_], _, level_, OptionsPattern[]] := With[{tag = HoldForm[var]},
	If[	TrueQ[OptionValue["AddCroissantBrackets"]],
		Diagram[level, PortDual[tag[level]], PortDual[Interpretation[tag[level], \[FormalX]]], "Shape" -> "Croissant", "Width" -> 1, "Height" -> 1 / 2, "LabelStyle" -> Directive[FontWeight -> Bold, Black]],
		IdentityDiagram[PortDual[tag[level]] -> PortDual[Interpretation[tag, \[FormalX]]]]
	]
]

LambdaDiagrams[f_[xs___], depth_, level_, opts : OptionsPattern[]] := Block[{
	fDiagram, xDiagrams
},
	fDiagram = DiagramNetwork @ LambdaDiagrams[f, depth, level, opts];
	xDiagrams = DiagramNetwork @ LambdaDiagrams[#, depth, level + 1, opts] & /@ {xs};
	Join[
		{applicationDiagram[rootPort[fDiagram], rootPort /@ xDiagrams, If[TrueQ[OptionValue["AddCroissantBrackets"]], level, None]]},
		fDiagram["SubDiagrams"],
		Catenate[Through[xDiagrams["SubDiagrams"]]],
		If[	TrueQ[OptionValue["AddCroissantBrackets"]],
			Map[
				Diagram[
					level,
					#, #["Apply", Replace[#["HoldName"], HoldForm[Interpretation[label_[_], tag_]] :> Interpretation[label[level], tag]] &],
					"Shape" -> "Bracket", "Width" -> 1, "Height" -> 1 / 2, "LabelStyle" -> Directive[FontWeight -> Bold]
				] &,
				Catenate[Through[xDiagrams["InputPorts"]]]
			],
			{}
		]
	]
]
LambdaDiagrams[Null | None, _, _, OptionsPattern[]] := {Diagram[None, Interpretation["*", Evaluate[Unique[]]], "Shape" -> "Disk", "Width" -> 1 / 2, "Height" -> 1 / 2, "ShowLabel" -> False]}
LambdaDiagrams[x_, _, _, OptionsPattern[]] := {Diagram[Unevaluated[x], Interpretation[x, Evaluate[Unique[]]], "Shape" -> "Disk", "Width" -> 1 / 2, "Height" -> 1 / 2]}


ToDiagram::missing = "Lambda package is not loaded. Please install the package with \!\(\*TemplateBox[List[StyleBox[TagBox[RowBox[List[\"PacletInstall\", \
\"[\", \
\"\\\"Wolfram/Lambda\\\"\", \"]\"]], HoldForm], \"Hyperlink\", \
Rule[StripOnInput, False]], RowBox[List[\"PacletInstall\", \"[\", \
\"\\\"Wolfram/Lambda\\\"\", \"]\"]]], \"ClickToCopy2\"]\)";

Options[LambdaDiagram] := Join[{"AddErasers" -> False, "Colored" -> False}, Options[LambdaDiagrams], Options[Wolfram`Lambda`LambdaTree, ColorFunction], Options[DiagramNetwork]];
LambdaDiagram[expr_, depth_Integer : 0, level_Integer : 0, opts : OptionsPattern[]] := Block[{net, lambdaIdx = 1, coloredQ = TrueQ[OptionValue["Colored"]], colorFunction},
	Quiet[Check[Needs["Wolfram`Lambda`"], Message[ToDiagram::missing]; Return[$Failed]], {Get::noopen, Needs::nocont}];
	colorFunction = OptionValue[ColorFunction];
	net = SimplifyDiagram @ DiagramNetwork @ Map[
		Switch[#["HoldExpression"],
			HoldForm[Style[Subscript["\[Lambda]", _], __]],
			Diagram[#, If[coloredQ, "Style" -> colorFunction[lambdaIdx++], {}]],
			_,
			#
		] &,
		LambdaDiagrams[Wolfram`Lambda`TagLambda[Wolfram`Lambda`UnscopedLambda[expr]], depth, level, FilterRules[{opts}, Options[LambdaDiagrams]]]
	];
	Diagram[
		If[ TrueQ[OptionValue["AddErasers"]],
			DiagramNetwork[Join[net["SubDiagrams"], Diagram[None, PortDual[#], "Shape" -> "Disk", "Width" -> 1 / 2, "Height" -> 1 / 2, "PortLabels" -> None] & /@ auxPorts[net]]],
			net
		],
		opts,
		"ShowPortLabels" -> False, "PortLabels" -> False, "ShowWireLabels" -> False
	]
]



QuantumCircuitDiagram[qc_Wolfram`QuantumFramework`QuantumCircuitOperator, opts : OptionsPattern[]] := With[{rules = Rule @@@ EdgeTags @ qc["TensorNetwork"]}, {
	d = DiagramComposition @@
		Reverse @ MapIndexed[{op, idx} |-> With[{i = idx[[1]], qo = Wolfram`QuantumFramework`QuantumOperator[op]},
			Diagram[
				Wolfram`QuantumFramework`QuantumOperator[qo, {Range[qo["OutputQudits"]], Range[qo["InputQudits"]]}]["CircuitDiagram", "WireLabels" -> None, "ShowWires" -> False, "ShowGateLabels" -> False, "ShowMeasurementWire" -> False, ImageSize -> 16],
				KeyValueMap[Interpretation[#1, Subscript[i, #1][#2]] &, qo["InputOrderDimensions"]],
				KeyValueMap[Interpretation[#1, Evaluate[Replace[Superscript[i, #1], rules][#2]]] &, qo["OutputOrderDimensions"]]
				(* "ShowLabel" -> False *)
				(* "PortArrows" -> Placed[Automatic, {0, 1}], *)
				(* "Outline" -> True,
				"Shape" -> 
					GeometricTransformation[
						First @ Wolfram`QuantumFramework`QuantumOperator[qo, {Range[qo["OutputQudits"]], Range[qo["InputQudits"]]}]["CircuitDiagram", "WireLabels" -> None, "ShowWires" -> False, "ShowGateLabels" -> False, "ShowMeasurementWire" -> False],
						ScalingTransform[{2, 2}] @* RotationTransform[Pi / 2] @* TranslationTransform[{-1, (1 + Max[qo["InputQudits"], qo["OutputQudits"]]) / 2}]
					] *)
			]
		],
			qc["Flatten"]["NormalOperators"]
		]
},
	Diagram[d, "OutputPorts" -> SortBy[d["OutputPorts"], #["Name"] &], "InputPorts" -> SortBy[d["InputPorts"], #["Name"] &],
		"PortOrderingFunction" -> Function[Replace[#["HoldName"], {HoldForm[Interpretation[_, (Subscript | Superscript)[_, order_][_]]] :> order + 1, _ -> 0}]]]
]


End[];

EndPackage[];