BeginPackage["ProcessTheory`Node`", {"ProcessTheory`Port`"}];

Node
NodeQ

NodeProduct
NodeSum
NodeCompose

NodeCombine
NodesFreePorts

NodesPortGraph
NodesGraph
NodesNetGraph

Begin["ProcessTheory`Node`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Node::usage = "Node[expr] represents a symbolic node with input and output nodes"

Options[Node] = {};

$NodeHiddenOptions = {"Expression" -> None, "OutputPorts" -> {}, "InputPorts" -> {}, "DiagramOptions" -> {}};

$NodeProperties = Join[Keys[Options[Node]],
    {"Properties", "HoldExpression", "ProductQ", "SumQ", "Ports", "Arity", "FlattenOutputs", "FlattenInputs", "Flatten", "View", "Symbol", "Shape", "Diagram"}
];


(* ::Subsection:: *)
(* Validation *)

nodeQ[HoldPattern[Node[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "OutputPorts" -> {___Port ? PortQ}, "InputPorts" -> {___Port ? PortQ}, "DiagramOptions" -> OptionsPattern[]}]]

nodeQ[___] := False


x_Node /; System`Private`HoldNotValidQ[x] && nodeQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

NodeQ[x_Node] := System`Private`HoldValidQ[x]

NodeQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

Node[CircleTimes[ns___], opts : OptionsPattern[]] := With[{nodes = Node /@ {ns}}, {node = NodeProduct @@ nodes},
    Node["Expression" :> NodeProduct[##], "OutputPorts" -> node["OutputPorts"], "InputPorts" -> node["InputPorts"], opts] & @@ nodes
]

Node[CirclePlus[ns___], opts : OptionsPattern[]] := With[{nodes = Node /@ {ns}}, {node = NodeSum @@ nodes},
    Node["Expression" :> NodeSum[##], "OutputPorts" -> node["OutputPorts"], "InputPorts" -> node["InputPorts"], opts] & @@ nodes
]

Node[CircleDot[ns___], opts : OptionsPattern[]] := With[{nodes = Node /@ {ns}}, {node = NodeCompose @@ nodes},
    Node["Expression" :> NodeCompose[##], "OutputPorts" -> node["OutputPorts"], "InputPorts" -> node["InputPorts"], opts] & @@ nodes
]

Node[expr : Except[_Association | _Node | OptionsPattern[]],
    outputs : {} | Except[OptionsPattern[], _List] : {},
    inputs : {} | Except[OptionsPattern[], _List] : {},
    opts : OptionsPattern[]
] :=
    Node[
        FilterRules[{
            "Expression" :> expr,
            "OutputPorts" -> Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[outputs]],
            "InputPorts" -> Comap[Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[inputs]], "Dual"],
            opts
        },
            Join[Options[Node], $NodeHiddenOptions, Options[NodeGraphics]]
        ]
    ]

Node[expr_, output : Except[_List], args___] := Node[Unevaluated[expr], Unevaluated[{output}], args]

Node[expr_, outputs_List, input : Except[_List | OptionsPattern[]], opts___] := Node[Unevaluated[expr], Unevaluated[outputs], Unevaluated[{input}], opts]

Node[expr_, output : Except[_List], input : Except[_List], opts___] := Node[Unevaluated[expr], Unevaluated[{output}], Unevaluated[{input}], opts]

Node[opts : OptionsPattern[]] := Node[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[NodeGraphics]], opts, Options[Node], $NodeHiddenOptions},
        Join[Options[Node], $NodeHiddenOptions]
    ]|>
]]


(* merge options *)

Node[n_ ? NodeQ, opts : OptionsPattern[]] := Node[Replace[Normal[Merge[{opts, n["Data"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* sum *)

NodeSum[ns___Node ? NodeQ, opts : OptionsPattern[]] := Node[
    opts,
    With[{expr = Unevaluated @@ CirclePlus @@@ Hold[Evaluate[Through[{ns}["HoldExpression"]]]]}, "Expression" :> expr],
    "OutputPorts" -> Replace[Through[{ns}["OutputPorts"]], {{} -> Port["0"], ps_ :> PortSum @@ ps}, 1],
    "InputPorts" -> Replace[Through[{ns}["InputPorts"]], {{} -> Port[SuperStar["0"]], ps_ :> PortSum @@ ps}, 1]
]

(* horizontal product *)

NodeProduct[ns___Node ? NodeQ, opts : OptionsPattern[]] := Node[
    opts,
    With[{expr = Unevaluated @@ CircleTimes @@@ Hold[Evaluate[Through[{ns}["HoldExpression"]]]]}, "Expression" :> expr],
    "OutputPorts" -> Replace[Through[{ns}["OutputPorts"]], {{} -> Port["1"], ps_ :> PortProduct @@ ps}, 1],
    "InputPorts" -> Replace[Through[{ns}["InputPorts"]], {{} -> Port[SuperStar["1"]], ps_ :> PortProduct @@ ps}, 1]
]


(* vertical product *)

collectPorts[ports_List] := If[ports === {}, {}, Fold[{Union[#2[[1]], Complement[#1[[1]], #2[[2]]]], Union[#1[[2]], Complement[#2[[2]], #1[[1]]]]} &, ports]]

NodeCompose[ns___Node ? NodeQ, opts : OptionsPattern[]] := With[{ports = collectPorts[{Through[#["OutputPorts"]["Expression"]], Through[#["InputPorts"]["Expression"]]} & /@ Through[{ns}["Flatten"]]]},
    Node[
        opts,
        With[{expr = Unevaluated @@ CircleDot @@@ Hold[Evaluate[Through[{ns}["HoldExpression"]]]]}, "Expression" :> expr],
        "OutputPorts" -> (Port /@ ports[[1]]),
        "InputPorts" -> (Port[#]["Dual"] & /@ ports[[2]])
    ]
]

NodeCombine[ns___Node ? NodeQ, opts : OptionsPattern[]] := Node[
    opts,
    With[{expr = Unevaluated @@ Composition @@@ Hold[Evaluate[Through[{ns}["HoldExpression"]]]]}, "Expression" :> expr],

    Block[{graph = NodesGraph[{ns}], nodes = Through[{ns}["Flatten"]], freeWires, edges},
        freeWires = Cases[Pick[VertexList[graph], VertexDegree[graph], 1], _HoldForm];
        edges = EdgeList[graph];
        {
            "OutputPorts" -> Cases[edges, DirectedEdge[{nodeId_, 1, portId_}, Alternatives @@ freeWires] :> nodes[[nodeId]]["OutputPorts"][[portId]]],
            "InputPorts" -> Cases[edges, DirectedEdge[Alternatives @@ freeWires, {nodeId_, 2, portId_}] :> nodes[[nodeId]]["InputPorts"][[portId]]["Dual"]]
        }
    ]
]


(* ::Subsection:: *)
(* Properties *)


(* dispatch properties *)

(p_Node ? NodeQ)[prop_, opts___] := NodeProp[p, prop, opts] 


(* property definitions *)

NodeProp[_, "Properties"] := Sort[$NodeProperties]

NodeProp[HoldPattern[Node[data_]], "Data"] := data

NodeProp[HoldPattern[Node[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

NodeProp[n_, "HoldExpression"] := Extract[n["Data"], "Expression", HoldForm]

NodeProp[n_, "ProductQ"] := MatchQ[n["HoldExpression"], HoldForm[_NodeProduct]]

NodeProp[n_, "SumQ"] := MatchQ[n["HoldExpression"], HoldForm[_NodeSum]]

NodeProp[n_, "ComposeQ"] := MatchQ[n["HoldExpression"], HoldForm[_NodeCompose]]

NodeProp[n_, "Ports"] := Join[n["OutputPorts"], n["InputPorts"]]

NodeProp[n_, "OutputArity"] := Length[n["OutputPorts"]]

NodeProp[n_, "InputArity"] := Length[n["InputPorts"]]

NodeProp[n_, "Arity"] := Length[n["Ports"]]

NodeProp[n_, "FlattenOutputs"] := Node[n, "OutputPorts" -> Catenate[Through[n["OutputPorts"]["ProductList"]]]]

NodeProp[n_, "FlattenInputs"] := Node[n, "InputPorts" -> Catenate[Through[n["InputPorts"]["ProductList"]]]]

NodeProp[n_, "Flatten"] := n["FlattenOutputs"]["FlattenInputs"]

NodeProp[n_, "View"] := With[{
    expr = n["HoldExpression"],
    outputs = Through[n["OutputPorts"]["Label"]],
    inputs = Through[Through[n["InputPorts"]["Dual"]]["Label"]]
},
    Defer[Node[expr, outputs, inputs]] //. HoldForm[x_] :> x
]

NodeProp[n_, "Symbol"] := Switch[n["Arity"], 1, VectorSymbol, 2, MatrixSymbol, _, ArraySymbol][n["HoldExpression"], n["Ports"]]

NodeProp[n_, "Diagram", opts___] := NodeGraphics[n, opts]

NodeProp[n_, "Shape", opts___] := Replace[
    OptionValue[{opts, n["DiagramOptions"], Options[NodeGraphics]}, "Shape"],
    {
        Automatic -> Rectangle[{- 1 / 2, - 1 / 2}, {1 / 2 , 1 / 2}, RoundingRadius -> {{Left, Top} -> .2}],
        "Triangle" -> Polygon[{{- 1 / 2, - 1 / 2}, {0, 1 / 2}, {1 / 2, - 1 / 2}}]
    }
]

NodeProp[_, prop_] := Missing[prop]


(* ::Subsection:: *)
(* Formatting *)

Options[NodeGraphics] = Join[{"Shape" -> Automatic}, Options[Graphics]];

NodeGraphics[node_ ? NodeQ, opts : OptionsPattern[]] := Graphics[{
    EdgeForm[Black], FaceForm[Transparent], 
    node["Shape", opts],
    Text[ClickToCopy[node["HoldExpression"], node["View"]]],
    Arrowheads[Small],
    With[{xs = node["OutputPorts"]},
        MapThread[{
            Arrow[If[#2["DualQ"], Reverse, Identity] @ {{- 1 / 2 + #, 1 / 2}, {- 1 / 2 + #,  .75}}],
            Text[ClickToCopy[#2, #2["View"]], {- 1 / 2 + #,  1}]
        } &,
            {Range[0, 1, 1 / (Length[xs] + 1)][[2 ;; -2]], xs}
        ]
    ],
    With[{xs = node["InputPorts"]},
        MapThread[{
            Arrow[If[#2["DualQ"], Reverse, Identity] @ {{- 1 / 2 + #, - 1 / 2}, {- 1 / 2 + #, - .75}}],
            Text[ClickToCopy[#2, #2["View"]], {- 1 / 2 + #, -1}]
        } &,
            {Range[0, 1, 1 / (Length[xs] + 1)][[2 ;; -2]], xs}
        ]
    ]
},
    FilterRules[{opts, node["DiagramOptions"]}, Options[Graphics]],
    ImageSize -> Tiny,
    FormatType -> StandardForm,
    BaseStyle -> {
        GraphicsHighlightColor -> Magenta
    }
]

Node /: MakeBoxes[node : Node[_Association] ? NodeQ, form_] := With[{boxes = ToBoxes[node["Diagram"], form]},
    InterpretationBox[boxes, node]
]

NodeProduct /: MakeBoxes[NodeProduct[ns___], form_] := With[{boxes = ToBoxes[CircleTimes[ns], form]}, InterpretationBox[boxes, NodeProduct[ns]]]

NodeSum /: MakeBoxes[NodeSum[ns___], form_] := With[{boxes = ToBoxes[CirclePlus[ns], form]}, InterpretationBox[boxes, NodeSum[ns]]]

NodeCompose /: MakeBoxes[NodeCompose[ns___], form_] := With[{boxes = ToBoxes[CircleDot[ns], form]}, InterpretationBox[boxes, NodeSum[ns]]]


(* ::Subsection:: *)
(* Functions *)


Options[NodesPortGraph] = Options[Graph];
NodesPortGraph[nodes : {___Node ? NodeQ}, opts : OptionsPattern[]] := GraphSum[##, FilterRules[{opts}, Options[Graph]], VertexLabels -> Automatic] & @@
    (With[{vs = Through[#["HoldExpression"]]}, Graph[vs, UndirectedEdge @@@ Subsets[vs, {2}]]] & /@ Through[nodes["Ports"]])


Options[NodesGraph] = Options[Graph];
NodesGraph[nodes : {___Node ? NodeQ}, opts : OptionsPattern[]] := Block[{
    ports = Thread[{Through[#["OutputPorts"]], Through[#["InputPorts"]]}] & @ Through[nodes["Flatten"]],
    graph, embedding
},
    graph = Graph[
        Join[
            MapIndexed[Annotation[#2[[1]], "Node" -> #1] &, nodes],
            Flatten[MapIndexed[Annotation[#2, "Port" -> #1] &, ports, {3}], 2]
        ],
        Flatten[
            MapIndexed[
                With[{node = #2[[1]], port = #2, wire = #1["Name"]},
                    Switch[port[[2]], 1, {DirectedEdge[node, port], DirectedEdge[port, wire]}, 2, {DirectedEdge[port, node], DirectedEdge[wire, port]}]
                ] &,
                ports,
                {3}
            ],
            3
        ],
        VertexLabels -> MapAt[Placed[#, Center] &, {All, 2}] @ Join[
            {_ -> Automatic},
            Thread[Range[Length[nodes]] -> Through[nodes["HoldExpression"]]],
            Flatten[MapIndexed[#2 -> #1["Label"] &, ports, {3}], 2]
        ],
        VertexSize -> {_ -> Medium, _Integer -> Large, {__Integer} -> Medium},
        VertexShapeFunction -> {_ -> "Diamond", _Integer -> "Square", {__Integer} -> "Circle"},
        VertexStyle -> Transparent,
        PerformanceGoal -> "Quality"
    ];
    embedding = AssociationThread[
        VertexList[graph],
        GraphEmbedding[
            EdgeAdd[graph,
                Catenate[DirectedEdge @@@ Partition[Reverse @ Catenate[#], 2, 1, 1] & /@ MapAt[Reverse, MapIndexed[#2 &, ports, {3}], {All, 2}]],
                FilterRules[{opts}, {VertexCoordinates, GraphLayout}]
            ]
        ]
    ];
    embedding = <|
        embedding,
        If[Catenate[#] === {}, Nothing, With[{nodeCenter = Lookup[embedding, Catenate[#][[1, 1]]]},
            Thread[# -> SortBy[Lookup[embedding, #], ArcTan @@ (# - nodeCenter) &]] & /@ #
        ]] & /@ MapIndexed[#2 &, ports, {3}]
    |>;
    Graph[
        graph,
        FilterRules[{opts}, Options[Graph]],
        VertexCoordinates -> Normal[embedding]
    ]
]


Options[NodesNetGraph] = Join[{"ShowPortLabels" -> True, "ShowWireLabels" -> True, "Scale" -> Automatic}, Options[NodeGraphics], Options[Graph]];
NodesNetGraph[nodes : {___Node ? NodeQ}, opts : OptionsPattern[]] := NodesNetGraph[NodesGraph[nodes], opts]
NodesNetGraph[graph_Graph, opts : OptionsPattern[]] := Block[{
	nodeVertices = VertexList[graph, _Integer], spiderVertices, vertices, edges,
	nodes, outDegrees, inDegrees,
	embedding, orientations,
	scale = Replace[OptionValue["Scale"], Automatic -> .75], rad = .2,
	portLabelsQ = TrueQ[OptionValue["ShowPortLabels"]],
	wireLabelsQ = TrueQ[OptionValue["ShowWireLabels"]]
},
	nodes = Through[AnnotationValue[{graph, nodeVertices}, "Node"]["Flatten"]];
	If[Length[nodes] == 0, Return[Graphics[FilterRules[Join[{opts}, Options[graph]], Options[Graphics]]]]];
	embedding = AssociationThread[VertexList[graph], GraphEmbedding[graph]];
	If[EdgeCount[graph] == 0 && VertexCount[graph] > 1, embedding = ScalingTransform[{1, .5} / Max[#2 - #1 & @@@ CoordinateBounds[embedding]], Mean[embedding]][embedding]];
	orientations = Map[
        Normalize[Lookup[#, 1] - Lookup[#, 2]] &,
		Values @ <|
            # -> <|1 -> {0, 1 / 2}, 2 -> {0, - 1 / 2}|> & /@ Range[Length[nodes]],
            GroupBy[VertexList[graph, {__Integer}], First, Mean /@ GroupBy[#, #[[2]] &, Lookup[embedding, #] &] &]
        |>
	];
	{outDegrees, inDegrees} = AssociationThread[VertexList[graph] -> #] & /@ Through[{VertexOutDegree, VertexInDegree}[graph]];
	spiderVertices = VertexList[graph, _HoldForm];
	spiderVertices = Pick[spiderVertices, VertexDegree[graph, #] & /@ spiderVertices, d_ /; d > 2];
	spiderVertices = First[Reap[
		edges = Map[v |->
			Block[{in = VertexInComponent[graph, v, {1}], out = VertexOutComponent[graph, v, {1}], ports},
				ports = Join[out, in];
				If[ Length[in] + Length[out] == 2,
					DirectedEdge[ports[[1, 1]], ports[[2, 1]], {{ports[[1, 2]], If[ports[[1, 2]] == 1, outDegrees, inDegrees][ports[[1, 1]]], ports[[1, 3]]}, v, {ports[[2, 2]], If[ports[[2, 2]] == 1, outDegrees, inDegrees][ports[[2, 1]]], ports[[2, 3]]}}],
					Sow[v]; Splice[
						If[#[[2]] == 1, DirectedEdge[#[[1]], v, {#[[2]], Lookup[outDegrees, #[[1]]], #[[3]]}], DirectedEdge[#[[1]], v, {#[[2]], Lookup[inDegrees, #[[1]]], #[[3]]}]] & /@ ports
					]
				]
			],
			VertexList[graph, _HoldForm]
		]
	][[2]], {}];
	vertices = Join[nodeVertices, spiderVertices];
	Graph[
		vertices,
		edges,
		FilterRules[{opts}, Options[Graph]],
		VertexCoordinates -> Thread[vertices -> Lookup[embedding, vertices]],
		VertexShapeFunction -> Join[
			Thread[nodeVertices ->
				MapThread[{node, orientation} |-> With[{
						shape = node["Shape", opts],
						labels = Join[
							{Text[ClickToCopy[node["HoldExpression"], RawBoxes @ ToBoxes[node["View"], StandardForm]], {0, 0}]},
							If[ portLabelsQ,
								Join[
									MapIndexed[Text[ClickToCopy[#1["HoldExpression"], RawBoxes @ ToBoxes[#1["View"], StandardForm]], {- 1 / 2 + #2[[1]] / (node["OutputArity"] + 1) + .1, 1.25 / 2}] &, node["OutputPorts"]],
									MapIndexed[Text[ClickToCopy[#1["HoldExpression"], RawBoxes @ ToBoxes[#1["View"], StandardForm]], {- 1 / 2 + #2[[1]] / (node["InputArity"] + 1) + .1, - 1.25 / 2}] &, node["InputPorts"]]
								],
								{}
							]
						],
						transform = RotationTransform[{{0, 1}, orientation}] @* ScalingTransform[scale {1, 1}]
					},
						Function[{
							Black, FaceForm[None],
							GeometricTransformation[{shape}, TranslationTransform[#1] @* transform],
							SubsetMap[TranslationTransform[#1] @* transform, labels, {All, 2}]
						}]
					],
					{Through[nodes["Flatten"]], orientations}
				]
			],
			Thread[spiderVertices -> With[{radius = rad scale}, Function[Circle[#1, radius]]]]
		],
		EdgeShapeFunction -> Replace[edges, {
				edge : DirectedEdge[v_Integer, w_Integer, {{i : 1 | 2, n_Integer, p_Integer}, x_, {j : 1 | 2, m_Integer, q_Integer}}] :> edge -> Block[{
					point1, point2, normal1, normal2, orientation1 = orientations[[v]], orientation2 = orientations[[w]], wireCoords = Lookup[embedding, x],
                    port1 = nodes[[v]][Replace[i, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[p]],
                    port2 = nodes[[w]][Replace[j, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[q]]
				},
					If[ i == 1,
						point1 = {- 1 / 2 + p / (n + 1),   1 / 2} scale;
						normal1 = {0, 1} scale
						,
						point1 = {- 1 / 2 + p / (n + 1), - 1 / 2} scale;
						normal1 = - {0, 1} scale
					];
					point1 = RotationTransform[{{0, 1}, orientation1}] @ point1;
					normal1 = RotationTransform[{{0, 1}, orientation1}] @ normal1;
					If[ j == 1,
						point2 = {- 1 / 2 + q / (m + 1),   1 / 2} scale;
						normal2 = {0, 1} scale
						,
						point2 = {- 1 / 2 + q / (m + 1), - 1 / 2} scale;
						normal2 = - {0, 1} scale
					];
					point2 = RotationTransform[{{0, 1}, orientation2}] @ point2;
					normal2 = RotationTransform[{{0, 1}, orientation2}] @ normal2;
					With[{a = VectorSymbol["p", 2], b = VectorSymbol["q", 2]},
						Function[Evaluate @ {
							Arrowheads[With[{size = 0.01}, {
                                If[port1["DualQ"], {- size, .3}, {size, .3}],
                                If[port2["DualQ"], {size, .7}, {- size, .7}]
                            }
                            ]],
							Arrow @ BSplineCurve[{a + point1, a + point1 + normal1, b + point2 + normal2, b + point2}],
							If[wireLabelsQ, Text[Style[ClickToCopy[x, x], Black], (a + point1 + normal1 + b + point2 + normal2) / 2 + .1 normal1], Nothing]
						}] /. {a :> #[[1]], b :> #[[-1]]}
					]
				],
				edge : DirectedEdge[v_Integer, _, {i : 1 | 2, n_Integer, p_Integer}] :> edge -> Block[{
					point, normal, orientation = orientations[[v]], portCoords = Lookup[embedding, Key[{v, i, p}]],
                    port = nodes[[v]][Replace[i, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[p]]
				},
					If[ i == 1,
						point = {- 1 / 2 + p / (n + 1),   1 / 2} scale;
						normal = {0, 1} scale
						,
						point = {- 1 / 2 + p / (n + 1), - 1 / 2} scale;
						normal = - {0, 1} scale
					];
					point = RotationTransform[{{0, 1}, orientation}] @ point;
					normal = RotationTransform[{{0, 1}, orientation}] @ normal;

					With[{a = VectorSymbol["p", 2], b = VectorSymbol["q", 2]},
						Function[Evaluate @ {
							Arrowheads[With[{size = 0.01}, If[port["DualQ"], {{-size, .5}}, {{size, .5}}]]],
							Arrow @ BSplineCurve[{a + point, a + point + normal, b + scale Normalize[portCoords - b], b + rad scale Normalize[portCoords - b]}]
						}] /. {a :> #[[1]], b :> #[[-1]]}
					]
				],
				_ -> Nothing
			},
			1
		],
		VertexLabels -> _HoldForm -> Placed[Automatic, Center],
		BaseStyle -> {FormatType -> StandardForm}
	]
]


NodesFreePorts[nodes : {___Node ? NodeQ}] := Keys @ Select[CountsBy[Catenate[Through[Through[nodes["Flatten"]]["Ports"]]], #["HoldExpression"] &], EqualTo[1]]


End[];

EndPackage[];