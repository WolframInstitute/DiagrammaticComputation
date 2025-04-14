BeginPackage["ProcessTheory`Diagram`Grid`", {"ProcessTheory`Diagram`"}];

TopologyGraphics
FeynArtsTopologyGraphics
TopologyGraph
TopologyGraphs
FeynmanDiagram
WigglyArcFunction

Begin["ProcessTheory`Diagram`Grid`Private`"];


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

TopologyGraph[FeynArts`Topology[_][props___]] := Block[{vertices, edges},
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
	Graph[vertices, edges, VertexLabels -> Automatic, EdgeLabels -> "EdgeTag", GraphLayout -> "SpringElectricalEmbedding"]
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
		)
	}
	];
	vertexIndex = PositionIndex[TopologicalSort[DirectedGraph[SimpleGraph[graph], "Acyclic"]]];
	edges = Replace[EdgeList[graph], head_[v1_, v2_, tag___] :> (head[##, tag] & @@ Extract[Keys[vertexIndex], Sort[Lookup[vertexIndex, {v1, v2}]]]), 1];
	Map[
		insertion |-> Graph[
			Keys[vertexIndex],
			MapIndexed[Replace[#1, {_[v1_, v2_, {type_, field_}] :> edgeHead[v1, v2, Append[#2, Replace[field, insertion]]], _[v1_, v2_, {type_}] :> edgeHead[v1, v2, type]}] &, edges],
			FilterRules[{opts}, Options[Graph]],
			VertexLabels -> Automatic, EdgeLabels -> "EdgeTag", GraphLayout -> "SpringElectricalEmbedding", ImageSize -> Large
		],
		Replace[Catenate @ Values[insertions], {} -> {{}}]
	]
];

FeynmanDiagram[g_] := Block[{graph, vertexEmbedding, edgeEmbedding},
	graph = Graph[g,
		VertexShapeFunction -> (Sow[#2 -> #1, "v"] &),
        EdgeShapeFunction -> (Sow[#2 -> #1, "e"] &)
	];
	{vertexEmbedding, edgeEmbedding} = First[#, {}] & /@ Reap[GraphPlot[graph], {"v", "e"}][[2]];
	DiagramNetwork[##,
		"ShowWireLabels" -> True,
		"WireLabelFunction" -> (MaTeX`MaTeX[FeynArts`TheLabel[Replace[#3["Expression"], Interpretation[x_, _] :> x][[3, -1]]]] &),
		"Arrange" -> False,
		Alignment -> Center,
		ImageSize -> Large
	] & @@ MapThread[
		With[{inEdges = EdgeList[graph, _[_, #, ___]], outEdges = EdgeList[graph, _[#, __]]}, Diagram[#, inEdges, outEdges,
			"Shape" -> Switch[VertexDegree[graph, #], 1, None, _, "Point"],
			"LabelFunction" -> ("" &),
			"PortArrows" -> {
                Automatic,
                MapIndexed[{edge, i} |-> With[{
                    line = WigglyArcFunction[ToString[FeynArts`PropagatorType[edge[[3, -1]]]]][Lookup[edgeEmbedding, edge]]
                },
                    (If[#2 === "Net", line, Arrow[BSplineCurve[#1]]] &)
                ],
                    outEdges
                ]
            },
			"Center" -> #2
		]
		] &,
		{VertexList[graph], Lookup[vertexEmbedding, VertexList[graph]]}
	]
]

Options[WigglyArcFunction] = Options[ResourceFunction["WiggleLine"]];
WigglyArcFunction[k : _ ? NumericQ : 0, shape_String : "Straight", opts : OptionsPattern[]] := Function @ Block[{points},
	If[ k == 0,
		points = #,
		Block[{m = (#[[1]] + #[[-1]]) / 2, x = (#[[-1]] - #[[1]]) / 2, d, h, a, r, c},
			d = Norm[x];
			h = k d;
			a = Pi - 2 ArcCot[Abs[k]];
			r = Abs[h] + d Cot[a];
			c = m + RotationTransform[- Sign[h] Pi / 2][(r - Abs[h]) Normalize[x]];
			points = MeshCoordinates @ RegionUnion @ MeshPrimitives[DiscretizeRegion @ ResourceFunction["SplineCircle"][c, r, Sign[h] x, {Pi / 2 - a, Pi / 2 + a}], 1];
			
		]
	];
	Switch[shape,
		"Straight" | "GhostDash" | "ScalarDash",
		{Replace[shape, {"GhostDash" -> Dashing[Small], "ScalarDash" -> Dashing[Medium], "Straight" -> Nothing}], Line[points]},
		_,
		ResourceFunction["WiggleLine"][points, opts, "Shape" -> Replace[shape, "Cycles" -> "Helix"]]
	]
]

End[];

EndPackage[];