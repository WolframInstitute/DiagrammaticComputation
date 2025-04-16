BeginPackage["ProcessTheory`Diagram`Feynman`", {"ProcessTheory`Diagram`"}];

TopologyGraphics
FeynArtsTopologyGraphics
TopologyGraph
TopologyGraphs
FeynmanDiagram
WigglyArcFunction

Begin["ProcessTheory`Diagram`Feynman`Private`"];


TopologyGraphics[top : _FeynArts`Topology[___] -> g_] := Block[ {v, p, s},
	(
		v = FeynArts`Graphics`VGraphics /@ FeynArts`Vertices[top] /. #1;
		p = Transpose[{List @@ top /. FeynArts`Vertex[e_, _] :> FeynArts`Vertex[e] /. #1, #2, #3}];
		s = #4
	) & @@ FeynArts`Graphics`FindShape[top, FeynArts`ShapeSources, Null];
	Level[{FeynArts`Graphics`PGraphics @@@ (p /. List @@ # /. FeynArts`Field[_] -> 0), v, {s}}, {2}, FeynArts`DiagramGraphics[]] /. {None -> 0, Forward -> 1, Backward -> -1} & /@
		(g /. (x : FeynArts`FeynmanGraph[___][__] -> FeynArts`Insertions[_][gr___]) :> Sequence[x, gr])
]

FeynArtsTopologyGraphics[top : _FeynArts`Topology[___] -> fields_] := FeynArts`Graphics`DoRender[][] @ FeynArts`FeynArtsGraphics[][{{#}}] & /@
    TopologyGraphics[top -> Replace[Cases[fields, _FeynArts`FeynmanGraph[___], All], {} -> {{}}]]
FeynArtsTopologyGraphics[top : _FeynArts`Topology[___]] := FeynArtsTopologyGraphics[Append[0] /@ top -> {{}}]
FeynArtsTopologyGraphics[top : _FeynArts`TopologyList | _FeynArts`TopologyList[___]] := Catenate[FeynArtsTopologyGraphics /@ List @@ top]

TopologyGraph[top : FeynArts`Topology[_][props___]] := Block[{vertices, edges, embedding = First @ FeynArts`Graphics`FindShape[top, FeynArts`ShapeSources, Null]},
	vertices = Union @ First[#, {}] & @ Reap[
		edges = Replace[
			{props}, prop : FeynArts`Propagator[type_][FeynArts`Vertex[d1_][v1_], FeynArts`Vertex[d2_][v2_], FeynArts`Field[f___] | f___] :> (
				If[ MatchQ[type, FeynArts`Incoming | FeynArts`Outgoing], DirectedEdge, UndirectedEdge][##, {type, f}] & @@
					{Sow[v1, "Vertex"], Sow[v2," Vertex"]}[[
						If[type === FeynArts`Outgoing, If[d1 < d2, {2, 1}, {1, 2}], If[d1 < d2, {1, 2}, {2, 1}]]
					]]
			),
			1
		],
		"Vertex"
	][[2]];
	Graph[
        vertices, edges,
        VertexCoordinates -> (embedding /. FeynArts`Vertex[_][v_] :> v)
    ]
]

Options[TopologyGraphs] = Join[{DirectedEdges -> False}, Options[Graph]];
TopologyGraphs[top : _FeynArts`TopologyList | _FeynArts`TopologyList[___], opts : OptionsPattern[]] := Catenate[TopologyGraphs[#, opts] & /@ List @@ top]
TopologyGraphs[topology_, opts : OptionsPattern[]] := Block[{graph, vertexIndex, edges, insertions, edgeHead = If[TrueQ[OptionValue[DirectedEdges]], DirectedEdge, UndirectedEdge]},
	Replace[topology, {
		(top : FeynArts`Topology[_][___] -> ins_) :> (
			graph = TopologyGraph[top];
			insertions = GroupBy[Cases[ins, FeynArts`FeynmanGraph[_, type_ == id_][rules___] :> type[id] -> KeyMap[First][Association[rules]], All, Heads -> True], First -> Last]
		),
		top : _FeynArts`Topology | FeynArts`Topology[_][___] :> (
			graph = TopologyGraph[top];
			insertions = <||>
		),
        _ :> Return[$Failed]
	}
	];
	vertexIndex = PositionIndex[TopologicalSort[DirectedGraph[SimpleGraph[graph], "Acyclic"]]];
	edges = Replace[EdgeList[graph], head_[v1_, v2_, tag___] :> (head[##, tag] & @@ Extract[Keys[vertexIndex], Sort[Lookup[vertexIndex, {v1, v2}]]]), 1];
	Map[
		insertion |-> Graph[
			Union @ Keys[vertexIndex],
			MapIndexed[Replace[#1, {_[v1_, v2_, {type_, field_}] :> edgeHead[v1, v2, Append[#2, Replace[field, insertion]]], _[v1_, v2_, {type_}] :> edgeHead[v1, v2, {type}]}] &, edges],
			VertexCoordinates -> Thread[VertexList[graph] -> GraphEmbedding[graph]],
            FilterRules[{opts}, Options[Graph]]
		],
		Replace[Catenate @ Values[insertions], {} -> {{}}]
	]
];

FeynmanDiagram[g_ ? GraphQ, opts___] := Block[{vertices, edges, vertexEmbedding, edgeEmbedding},
    vertices = VertexList[g];
    edges = Catenate[KeyValueMap[{edge, n} |-> (Insert[edge, #, {3, 1}] & /@ Range[n]), ResourceFunction["EdgeMultiplicity"][g]]];
    vertexEmbedding = Thread[vertices -> GraphEmbedding[g]];
	edgeEmbedding = First[Reap[GraphPlot[Graph[vertices, edges, VertexCoordinates -> vertexEmbedding, EdgeShapeFunction -> (Sow[#2 -> #1, "e"] &)]], "e"][[2]], {}];
    edgeEmbedding = #1 -> If[MatchQ[#1, _[x_, x_, ___]], BSplineCurve[#2], First @ GraphComputation`GraphElementData["Line"][#2, None]] & @@@ edgeEmbedding;
	DiagramNetwork[##,
        opts,
		"ShowWireLabels" -> True,
		"WireLabelFunction" -> (Placed[
            Replace[Quiet @ FeynArts`TheLabel[Replace[#3["Expression"], Interpretation[x_, _] :> x][[3, -1]]], {l_String :> MaTeX`MaTeX[l], _ -> ""}],
            Offset[{-.02, .05}]
        ] &),
		"Arrange" -> False,
		Alignment -> Center
	] & @@ MapThread[
		With[{inEdges = Cases[edges, _[_, #, ___]], outEdges = Cases[edges, _[#, __]]}, Diagram[#, inEdges, outEdges,
			"Shape" -> Switch[VertexDegree[g, #], 1, None, _, "Point"],
            "LabelFunction" -> ("" &),
			"LabelFunction" -> (Placed[#1["Expression"], {.1, - .1}] &),
			"PortArrows" -> {
                Automatic,
                MapIndexed[{edge, i} |-> With[{edgeShape = Lookup[edgeEmbedding, edge], emb = Lookup[vertexEmbedding, List @@ edge[[;; 2]]]}, {scale = Max[1, Norm[emb[[1]] - emb[[2]]]]},
                        WigglyArcFunction[
                            ToString[FeynArts`PropagatorType[edge[[3, -1]]]],
                            0,
                            Replace[FeynArts`PropagatorArrow[edge[[3, -1]]], {Forward -> -1, Backward -> 1, None -> 0}],
                            "Amplitude" -> If[#2 === "Net", 0.01, 0.005] scale,
                            "Frequency" -> If[#2 === "Net", 10, 30] / scale,
                            "TaperFraction" -> 0
                        ][If[#2 === "Net", edgeShape, BSplineCurve[#1]]] &
                    ],
                    outEdges
                ]
            },
			"Center" -> #2
		]
		] &,
		{vertices, Values[vertexEmbedding]}
	]
]

Options[WigglyArcFunction] = Options[ResourceFunction["WiggleLine"]];
WigglyArcFunction[shape_String : "Straight", k : _ ? NumericQ : 0, arrow : _ ? NumericQ : 0, opts : OptionsPattern[]] := Function @ Block[{curve = #},
	If[ MatchQ[curve, {{_ ? NumericQ, _ ? NumericQ} ..}],
		If[ k == 0,
            curve = BSplineCurve[curve]
            ,
            Block[{m = (curve[[1]] + curve[[-1]]) / 2, x = (curve[[-1]] - curve[[1]]) / 2, d, h, a, r, c},
                d = Norm[x];
                h = k d;
                a = Pi - 2 ArcCot[Abs[k]];
                r = Abs[h] + d Cot[a];
                c = m + RotationTransform[- Sign[h] Pi / 2][(r - Abs[h]) Normalize[x]];
                curve = ResourceFunction["SplineCircle"][c, r, Sign[h] x, {Pi / 2 - a, Pi / 2 + a}];
            ]
        ]
	];
	{
        If[arrow == 0, Nothing, Arrowheads[{{arrow Small, .5}}]],
        Switch[shape,
            "Straight" | "GhostDash" | "ScalarDash",
            {Replace[shape, {"GhostDash" -> Dashing[Small], "ScalarDash" -> Dashing[Medium], "Straight" -> Nothing}], curve},
            _,
            ResourceFunction["WiggleLine"][
                ResourceFunction["CurveToBSplineFunction"][MeshCoordinates @ RegionUnion @ MeshPrimitives[DiscretizeRegion[curve, MaxCellMeasure -> {"Length", .1}], 1], 2],
                opts,
                "Shape" -> Replace[shape, "Cycles" -> "Helix"]
            ]
        ]
    }
]

End[];

EndPackage[];