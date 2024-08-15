BeginPackage["ProcessTheory`Diagram`", {"ProcessTheory`Utilities`", "ProcessTheory`Port`"}];

Diagram
DiagramQ

DiagramDual
DiagramFlip
DiagramReverse

DiagramProduct
DiagramSum
DiagramComposition
DiagramNetwork

DiagramsFreePorts
DiagramsPortGraph
DiagramsGraph
DiagramsNetGraph

Begin["ProcessTheory`Diagram`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Diagram::usage = "Diagram[expr] represents a symbolic diagram with input and output ports"

Options[Diagram] = {};

$DiagramHiddenOptions = {"Expression" -> None, "OutputPorts" -> {}, "InputPorts" -> {}, "DiagramOptions" -> {}};

$DiagramProperties = Join[Keys[Options[Diagram]],
    {"Properties", "HoldExpression", "ProductQ", "SumQ", "Ports", "Arity", "FlattenOutputs", "FlattenInputs", "Flatten", "View", "Symbol", "Shape", "Diagram"}
];


(* ::Subsection:: *)
(* Validation *)

diagramQ[HoldPattern[Diagram[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "OutputPorts" -> {___Port ? PortQ}, "InputPorts" -> {___Port ? PortQ}, "DiagramOptions" -> OptionsPattern[]}]]

diagramQ[___] := False


x_Diagram /; System`Private`HoldNotValidQ[x] && diagramQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

DiagramQ[x_Diagram] := System`Private`HoldValidQ[x]

DiagramQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

Diagram[SuperStar[d_], opts : OptionsPattern[]] :=
    With[{diagram = DiagramDual[#]}, Diagram["Expression" :> DiagramDual[#], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts]] & @ Diagram[d]

Diagram[OverBar[d_], opts : OptionsPattern[]] :=
    With[{diagram = DiagramFlip[#]}, Diagram["Expression" :> DiagramFlip[#], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts]] & @ Diagram[d]

Diagram[OverTilde[d_], opts : OptionsPattern[]] :=
    With[{diagram = DiagramReverse[#]}, Diagram["Expression" :> DiagramReverse[#], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts]] & @ Diagram[d]

Diagram[CircleTimes[ds___], opts : OptionsPattern[]] := With[{diagrams = Diagram /@ {ds}}, {diagram = DiagramProduct @@ diagrams},
    Diagram["Expression" :> DiagramProduct[##], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts] & @@ diagrams
]

Diagram[CirclePlus[ds___], opts : OptionsPattern[]] := With[{diagrams = Diagram /@ {ds}}, {diagram = DiagramSum @@ diagrams},
    Diagram["Expression" :> DiagramSum[##], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts] & @@ diagrams
]

Diagram[CircleDot[ds___], opts : OptionsPattern[]] := With[{diagrams = Diagram /@ {ds}}, {diagram = DiagramComposition @@ diagrams},
    Diagram["Expression" :> DiagramComposition[##], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts] & @@ diagrams
]

Diagram[ds : Except[OptionsPattern[], _List], opts : OptionsPattern[]] := With[{diagrams = Diagram /@ ds}, {diagram = DiagramNetwork @@ diagrams},
    Diagram["Expression" :> DiagramNetwork[##], "OutputPorts" -> diagram["OutputPorts"], "InputPorts" -> diagram["InputPorts"], opts] & @@ diagrams
]

Diagram[expr : Except[_Association | _Diagram | OptionsPattern[]],
    outputs : {} | Except[OptionsPattern[], _List] : {},
    inputs : {} | Except[OptionsPattern[], _List] : {},
    opts : OptionsPattern[]
] :=
    Diagram[
        FilterRules[{
            "Expression" :> expr,
            "OutputPorts" -> Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[outputs]],
            "InputPorts" -> Comap[Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[inputs]], "Dual"],
            opts
        },
            Join[Options[Diagram], $DiagramHiddenOptions, Options[DiagramGraphics]]
        ]
    ]

Diagram[expr_, output : Except[_List], args___] := Diagram[Unevaluated[expr], Unevaluated[{output}], args]

Diagram[expr_, outputs_List, input : Except[_List | OptionsPattern[]], opts___] := Diagram[Unevaluated[expr], Unevaluated[outputs], Unevaluated[{input}], opts]

Diagram[expr_, output : Except[_List], input : Except[_List], opts___] := Diagram[Unevaluated[expr], Unevaluated[{output}], Unevaluated[{input}], opts]

Diagram[opts : OptionsPattern[]] := Diagram[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[DiagramGraphics]], opts, Options[Diagram], $DiagramHiddenOptions},
        Join[Options[Diagram], $DiagramHiddenOptions]
    ]|>
]]


(* overwrite ports *)

Diagram[d_ ? DiagramQ,
    outputs : Inherited | {} | Except[OptionsPattern[], _List] : Inherited,
    inputs : Inherited | {} | Except[OptionsPattern[], _List] : Inherited,
    opts : OptionsPattern[]
] := Diagram[Unevaluated @@ d["HoldExpression"], Replace[outputs, Inherited :> d["OutputPorrts"]], Replace[inputs, Inherited :> d["InputPorrts"]], opts]


(* merge options *)

Diagram[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[Replace[Normal[Merge[{opts, d["Data"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* ::Subsubsection:: *)
(* Unary ops *)

DiagramDual[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramDual[d],
    "OutputPorts" -> Through[d["OutputPorts"]["Dual"]],
    "InputPorts" -> Through[d["InputPorts"]["Dual"]]
]

DiagramFlip[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramFlip[d],
    "Shape" -> GeometricTransformation[d["Shape"], ReflectionTransform[{0, 1}]],
    "OutputPorts" -> d["InputPorts"],
    "InputPorts" -> d["OutputPorts"]
]

DiagramReverse[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramReverse[d],
    "Shape" -> GeometricTransformation[d["Shape"], ReflectionTransform[{1, 0}]],
    "OutputPorts" -> Reverse[Through[d["OutputPorts"]["Reverse"]]],
    "InputPorts" -> Reverse[Through[d["InputPorts"]["Reverse"]]]
]


(* ::Subsubsection:: *)
(* Binary ops *)

(* sum *)

DiagramSum[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramSum[ds],
    "OutputPorts" -> Replace[Through[{ds}["OutputPorts"]], {{} -> Port["0"], ps_ :> PortSum @@ ps}, 1],
    "InputPorts" -> Replace[Through[{ds}["InputPorts"]], {{} -> Port[SuperStar["0"]], ps_ :> PortSum @@ ps}, 1]
]

(* horizontal product *)

DiagramProduct[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramProduct[ds],
    "OutputPorts" -> Replace[Through[{ds}["OutputPorts"]], {{} -> Port["1"], ps_ :> PortProduct @@ ps}, 1],
    "InputPorts" -> Replace[Through[{ds}["InputPorts"]], {{} -> Port[SuperStar["1"]], ps_ :> PortProduct @@ ps}, 1]
]


(* vertical product *)

collectPorts[ports_List] := If[ports === {}, {}, Fold[{Union[#2[[1]], Complement[#1[[1]], #2[[2]]]], Union[#1[[2]], Complement[#2[[2]], #1[[1]]]]} &, ports]]

DiagramComposition[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{ports = collectPorts[{Through[#["OutputPorts"]["Expression"]], Through[#["InputPorts"]["Expression"]]} & /@ Through[{ds}["Flatten"]]]},
    Diagram[
        opts,
        "Expression" :> DiagramComposition[ds],
        "OutputPorts" -> (Port /@ ports[[1]]),
        "InputPorts" -> (Port[#]["Dual"] & /@ ports[[2]])
    ]
]

DiagramNetwork[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    opts,
    "Expression" :> DiagramNetwork[ds],

    Block[{graph = DiagramsGraph[{ds}], diagrams = Through[{ds}["Flatten"]], freeWires, edges},
        freeWires = Cases[Pick[VertexList[graph], VertexDegree[graph], 1], _HoldForm];
        edges = EdgeList[graph];
        {
            "OutputPorts" -> Cases[edges, DirectedEdge[{diagramId_, 1, portId_}, Alternatives @@ freeWires] :> diagrams[[diagramId]]["OutputPorts"][[portId]]],
            "InputPorts" -> Cases[edges, DirectedEdge[Alternatives @@ freeWires, {diagramId_, 2, portId_}] :> diagrams[[diagramId]]["InputPorts"][[portId]]["Dual"]]
        }
    ]
]


(* ::Subsection:: *)
(* Properties *)


(* dispatch properties *)

(p_Diagram ? DiagramQ)[prop_, opts___] := DiagramProp[p, prop, opts] 


(* property definitions *)

DiagramProp[_, "Properties"] := Sort[$DiagramProperties]

DiagramProp[HoldPattern[Diagram[data_]], "Data"] := data

DiagramProp[HoldPattern[Diagram[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

DiagramProp[d_, "HoldExpression"] := Extract[d["Data"], "Expression", HoldForm]

DiagramProp[d_, "ProductQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramProduct]]

DiagramProp[d_, "SumQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramSum]]

DiagramProp[d_, "CompositionQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramComposition]]

DiagramProp[d_, "Ports"] := Join[d["OutputPorts"], d["InputPorts"]]

DiagramProp[d_, "OutputArity"] := Length[d["OutputPorts"]]

DiagramProp[d_, "InputArity"] := Length[d["InputPorts"]]

DiagramProp[d_, "Arity"] := Length[d["Ports"]]

DiagramProp[d_, "FlattenOutputs"] := Diagram[d, "OutputPorts" -> Catenate[Through[d["OutputPorts"]["ProductList"]]]]

DiagramProp[d_, "FlattenInputs"] := Diagram[d, "InputPorts" -> Catenate[Through[d["InputPorts"]["ProductList"]]]]

DiagramProp[d_, "Flatten"] := d["FlattenOutputs"]["FlattenInputs"]

DiagramProp[d_, "View"] := With[{
    expr = Replace[d["HoldExpression"],
        HoldForm[(head : DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[ds___]] :>
            head @@@ HoldForm[Evaluate[Flatten[Defer @@ (Function[Null, If[DiagramQ[#], #["View"], Defer[#]], HoldFirst] /@ Unevaluated[{ds}])]]]
    ],
    outputs = Through[d["OutputPorts"]["Label"]],
    inputs = Through[Through[d["InputPorts"]["Dual"]]["Label"]]
},
    Function[Null, Defer[Diagram[#, outputs, inputs]] //. HoldForm[x_] :> x, HoldFirst] @@ expr
]

DiagramProp[d_, "Symbol"] := Switch[n["Arity"], 1, VectorSymbol, 2, MatrixSymbol, _, ArraySymbol][d["HoldExpression"], d["Ports"]]

DiagramProp[d_, "Diagram", opts___] := DiagramGraphics[d, opts]

DiagramProp[d_, "Shape", opts___] := Replace[
    OptionValue[{opts, d["DiagramOptions"], Options[DiagramGraphics]}, "Shape"],
    {
        Automatic -> Rectangle[{- 1 / 2, - 1 / 2}, {1 / 2 , 1 / 2}, RoundingRadius -> {{Left, Top} -> .2}],
        "Triangle" -> Polygon[{{- 1 / 2, - 1 / 2}, {0, 1 / 2}, {1 / 2, - 1 / 2}}]
    }
]

DiagramProp[_, prop_] := Missing[prop]


(* ::Subsection:: *)
(* Formatting *)

Options[DiagramGraphics] = Join[{"Shape" -> Automatic}, Options[Graphics]];

DiagramGraphics[diagram_ ? DiagramQ, opts : OptionsPattern[]] := Graphics[{
    EdgeForm[Black], FaceForm[Transparent], 
    diagram["Shape", opts],
    Text[ClickToCopy[diagram["HoldExpression"] //. d_Diagram ? DiagramQ :> RuleCondition[d["HoldExpression"]], diagram["View"]]],
    Arrowheads[Small],
    With[{xs = diagram["OutputPorts"]},
        MapThread[{
            Arrow[If[#2["DualQ"], Reverse, Identity] @ {{- 1 / 2 + #, 1 / 2}, {- 1 / 2 + #,  .75}}],
            Text[ClickToCopy[#2, #2["View"]], {- 1 / 2 + #,  1}]
        } &,
            {Range[0, 1, 1 / (Length[xs] + 1)][[2 ;; -2]], xs}
        ]
    ],
    With[{xs = diagram["InputPorts"]},
        MapThread[{
            Arrow[If[#2["DualQ"], Reverse, Identity] @ {{- 1 / 2 + #, - 1 / 2}, {- 1 / 2 + #, - .75}}],
            Text[ClickToCopy[#2, #2["View"]], {- 1 / 2 + #, -1}]
        } &,
            {Range[0, 1, 1 / (Length[xs] + 1)][[2 ;; -2]], xs}
        ]
    ]
},
    FilterRules[{opts, diagram["DiagramOptions"]}, Options[Graphics]],
    ImageSize -> Tiny,
    FormatType -> StandardForm,
    BaseStyle -> {
        GraphicsHighlightColor -> Magenta
    }
]

Diagram /: MakeBoxes[diagram : Diagram[_Association] ? DiagramQ, form_] := With[{boxes = ToBoxes[diagram["Diagram"], form]},
    InterpretationBox[boxes, diagram]
]

DiagramDual /: MakeBoxes[DiagramDual[d_], form_] := With[{boxes = ToBoxes[SuperStar[d], form]}, InterpretationBox[boxes, DiagramDual[d]]]

DiagramFlip /: MakeBoxes[DiagramFlip[d_], form_] := With[{boxes = ToBoxes[OverBar[d], form]}, InterpretationBox[boxes, DiagramFlip[d]]]

DiagramReverse /: MakeBoxes[DiagramReverse[d_], form_] := With[{boxes = ToBoxes[Overscript[d, RawBoxes["\[LongLeftRightArrow]"]], form]}, InterpretationBox[boxes, DiagramReverse[d]]]

DiagramProduct /: MakeBoxes[DiagramProduct[ds___], form_] := With[{boxes = ToBoxes[CircleTimes[ds], form]}, InterpretationBox[boxes, DiagramProduct[ds]]]

DiagramSum /: MakeBoxes[DiagramSum[ds___], form_] := With[{boxes = ToBoxes[CirclePlus[ds], form]}, InterpretationBox[boxes, DiagramSum[ds]]]

DiagramComposition /: MakeBoxes[DiagramComposition[ds___], form_] := With[{boxes = ToBoxes[CircleDot[ds], form]}, InterpretationBox[boxes, DiagramComposition[ds]]]

DiagramNetwork /: MakeBoxes[DiagramNetwork[ds___], form_] := With[{boxes = ToBoxes[DiagramsNetGraph[{ds}], form]}, InterpretationBox[boxes, DiagramNetwork[ds]]]


(* ::Subsection:: *)
(* Functions *)


Options[DiagramsPortGraph] = Options[Graph];
DiagramsPortGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := GraphSum[##, FilterRules[{opts}, Options[Graph]], VertexLabels -> Automatic] & @@
    (With[{vs = Through[#["HoldExpression"]]}, Graph[vs, UndirectedEdge @@@ Subsets[vs, {2}]]] & /@ Through[diagrams["Ports"]])


Options[DiagramsGraph] = Options[Graph];
DiagramsGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := Block[{
    ports = Thread[{Through[#["OutputPorts"]], Through[#["InputPorts"]]}] & @ Through[diagrams["Flatten"]],
    graph, embedding
},
    graph = Graph[
        Join[
            MapIndexed[Annotation[#2[[1]], "Diagram" -> #1] &, diagrams],
            Flatten[MapIndexed[Annotation[#2, "Port" -> #1] &, ports, {3}], 2]
        ],
        Flatten[
            MapIndexed[
                With[{diagram = #2[[1]], port = #2, wire = #1["Name"]},
                    Switch[port[[2]], 1, {DirectedEdge[diagram, port], DirectedEdge[port, wire]}, 2, {DirectedEdge[port, diagram], DirectedEdge[wire, port]}]
                ] &,
                ports,
                {3}
            ],
            3
        ],
        VertexLabels -> MapAt[Placed[#, Center] &, {All, 2}] @ Join[
            {_ -> Automatic},
            Thread[Range[Length[diagrams]] -> Through[diagrams["HoldExpression"]]],
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
        If[Catenate[#] === {}, Nothing, With[{diagramCenter = Lookup[embedding, Catenate[#][[1, 1]]]},
            Thread[# -> SortBy[Lookup[embedding, #], ArcTan @@ (# - diagramCenter) &]] & /@ #
        ]] & /@ MapIndexed[#2 &, ports, {3}]
    |>;
    Graph[
        graph,
        FilterRules[{opts}, Options[Graph]],
        VertexCoordinates -> Normal[embedding]
    ]
]


Options[DiagramsNetGraph] = Join[{"ShowPortLabels" -> True, "ShowWireLabels" -> True, "Scale" -> Automatic}, Options[DiagramGraphics], Options[Graph]];
DiagramsNetGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := DiagramsNetGraph[DiagramsGraph[diagrams], opts]
DiagramsNetGraph[graph_Graph, opts : OptionsPattern[]] := Block[{
	diagramVertices = VertexList[graph, _Integer], spiderVertices, vertices, edges,
	diagrams, outDegrees, inDegrees,
	embedding, orientations,
	scale = Replace[OptionValue["Scale"], Automatic -> .75], rad = .2,
	portLabelsQ = TrueQ[OptionValue["ShowPortLabels"]],
	wireLabelsQ = TrueQ[OptionValue["ShowWireLabels"]]
},
	diagrams = Through[AnnotationValue[{graph, diagramVertices}, "Diagram"]["Flatten"]];
	If[Length[diagrams] == 0, Return[Graphics[FilterRules[Join[{opts}, Options[graph]], Options[Graphics]]]]];
	embedding = AssociationThread[VertexList[graph], GraphEmbedding[graph]];
	If[EdgeCount[graph] == 0 && VertexCount[graph] > 1, embedding = ScalingTransform[{1, .5} / Max[#2 - #1 & @@@ CoordinateBounds[embedding]], Mean[embedding]][embedding]];
	orientations = Map[
        Normalize[Lookup[#, 1] - Lookup[#, 2]] &,
		Values @ <|
            # -> <|1 -> {0, 1 / 2}, 2 -> {0, - 1 / 2}|> & /@ Range[Length[diagrams]],
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
	vertices = Join[diagramVertices, spiderVertices];
	Graph[
		vertices,
		edges,
		FilterRules[{opts}, Options[Graph]],
		VertexCoordinates -> Thread[vertices -> Lookup[embedding, vertices]],
		VertexShapeFunction -> Join[
			Thread[diagramVertices ->
				MapThread[{diagram, orientation} |-> With[{
						shape = diagram["Shape", opts],
						labels = Join[
							{Text[ClickToCopy[diagram["HoldExpression"], RawBoxes @ ToBoxes[diagram["View"], StandardForm]], {0, 0}]},
							If[ portLabelsQ,
								Join[
									MapIndexed[Text[ClickToCopy[#1["HoldExpression"], RawBoxes @ ToBoxes[#1["View"], StandardForm]], {- 1 / 2 + #2[[1]] / (diagram["OutputArity"] + 1) + .1, 1.25 / 2}] &, diagram["OutputPorts"]],
									MapIndexed[Text[ClickToCopy[#1["HoldExpression"], RawBoxes @ ToBoxes[#1["View"], StandardForm]], {- 1 / 2 + #2[[1]] / (diagram["InputArity"] + 1) + .1, - 1.25 / 2}] &, diagram["InputPorts"]]
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
					{Through[diagrams["Flatten"]], orientations}
				]
			],
			Thread[spiderVertices -> With[{radius = rad scale}, Function[Circle[#1, radius]]]]
		],
		EdgeShapeFunction -> Replace[edges, {
				edge : DirectedEdge[v_Integer, w_Integer, {{i : 1 | 2, n_Integer, p_Integer}, x_, {j : 1 | 2, m_Integer, q_Integer}}] :> edge -> Block[{
					point1, point2, normal1, normal2, orientation1 = orientations[[v]], orientation2 = orientations[[w]], wireCoords = Lookup[embedding, x],
                    port1 = diagrams[[v]][Replace[i, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[p]],
                    port2 = diagrams[[w]][Replace[j, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[q]]
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
                    port = diagrams[[v]][Replace[i, {1 -> "OutputPorts", 2 -> "InputPorts"}]][[p]]
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


DiagramsFreePorts[diagrams : {___Diagram ? DiagramQ}] := Keys @ Select[CountsBy[Catenate[Through[Through[diagrams["Flatten"]]["Ports"]]], #["HoldExpression"] &], EqualTo[1]]


End[];

EndPackage[];