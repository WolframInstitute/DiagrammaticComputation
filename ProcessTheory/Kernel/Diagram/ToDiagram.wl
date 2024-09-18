BeginPackage["ProcessTheory`Diagram`ToDiagram`"];

ToDiagram

Begin["ProcessTheory`Diagram`ToDiagram`Private`"];


ToDiagram[ng_NetGraph, opts : OptionsPattern[NetGraphDiagramNetwork]] := NetGraphDiagramNetwork[ng, opts]
ToDiagram[expr_, opts : OptionsPattern[LambdaDiagram]] := LambdaDiagram[expr, opts]


Options[NetGraphDiagramNetwork] = Options[DiagramNetwork];
NetGraphDiagramNetwork[ng_NetGraph, opts : OptionsPattern[]] := Block[{
	layers = Information[ng, "LayersList"],
	freeOutputPorts, freeInputPorts, outputPorts, inputPorts,
	edges, rules,
	diagrams
},
	freeOutputPorts = First /@ PositionIndex @ Information[ng, "OutputPortNames"];
	freeInputPorts = First /@ PositionIndex @ Information[ng, "InputPortNames"];
	outputPorts = First /@ PositionIndex[Information[#, "OutputPortNames"]] & /@ layers;
	inputPorts = First /@ PositionIndex[Information[#, "InputPortNames"]] & /@ layers;
	edges = NeuralNetworks`NetGraphEdges[ng] /. {
		NetPort[port_] /; KeyExistsQ[freeInputPorts, port] :> Length[layers] + Length[freeOutputPorts] + Lookup[freeInputPorts, port],
		NetPort[port_] /; KeyExistsQ[freeOutputPorts, port] :> Length[layers] + Lookup[freeOutputPorts, port],
		NetPort[{layerIdx_Integer, port_String}] :> Block[{
			layer = layers[[layerIdx]], outputQ
		},
			outputQ = KeyExistsQ[outputPorts[[layerIdx]], port];
			{layerIdx, If[outputQ, 1, 2], Lookup[If[outputQ, outputPorts[[layerIdx]], inputPorts[[layerIdx]]], port, 1]}
		]
	};
	edges = Replace[edges, {
		(idx1_Integer -> idx2_Integer) :> {idx1, 1, 1} -> {idx2, 2, 1},
		(idx_Integer -> port_) :> {idx, 1, 1} -> port,
		(port_ -> idx_Integer) :> port -> {idx, 2, 1}
	}, 1];
	rules = Reverse /@ edges;
	
	diagrams = MapIndexed[With[{i = #2[[1]]},
		Diagram[
			Interpretation[Replace[#, _[assoc_,___] :> Graphics @ NeuralNetworks`Private`GetPanelIcon[assoc]], #],
			MapIndexed[Interpretation @@ {{i, 1, #2[[1]]}, Construct @@ #1} &, Normal @ Information[#, "OutputPorts"]],
			MapIndexed[Interpretation @@ {Replace[{i, 2, #2[[1]]}, rules], Construct @@ #1} &, Normal @ Information[#, "InputPorts"]]
		]] &,
		layers
	];
	DiagramNetwork[##, opts] & @@ diagrams
]


LambdaDiagrams[Interpretation["\[Lambda]", tag_][body_][arg_], depth_] := Block[{bodyDiagram, argDiagram = DiagramNetwork @@ LambdaDiagrams[arg, depth], out},
	out = argDiagram["OutputPorts"][[1]];
	bodyDiagram = DiagramNetwork @@ LambdaDiagrams[body /. Interpretation[v_Integer, tag] :> Interpretation[v, Evaluate @ out], depth + 1];
	Join[
		{
			Diagram["\[Lambda]", tag, \[FormalX][tag], "Shape" -> "Circle"],
			Diagram["\[Application]", \[FormalX][tag], {bodyDiagram["OutputPorts"][[1]], out}, "Shape" -> "Triangle"]
		},
		bodyDiagram["SubDiagrams"], argDiagram["SubDiagrams"]
	]
] 
LambdaDiagrams[Interpretation["\[Lambda]", tag_][body_], depth_] := With[{bodyDiagrams = LambdaDiagrams[body, depth]}, Join[{Diagram["\[Lambda]", tag, \[FormalX][tag], "Shape" -> "Circle"]}, bodyDiagrams]]
LambdaDiagrams[Interpretation[_Integer, f_][Interpretation[_Integer, x_]], _] :=  {Diagram["\[Application]", Unique["x"], {f, x}, "Shape" -> "Triangle"]}
LambdaDiagrams[Interpretation[_Integer, tag : _Port | _Symbol][arg_], depth_] :=  With[{argDiagram = DiagramNetwork @@ LambdaDiagrams[arg, depth]},
	{Diagram["\[Application]", Unique["x"], {tag, argDiagram["OutputPorts"][[1]]}, "Shape" -> "Triangle"], argDiagram}
]
LambdaDiagrams[Interpretation[v_Integer, tag : _Port | _Symbol], _] := With[{port = Port[tag]}, {Diagram["", \[FormalO][port["Name"]], port, "Shape" -> "Wire"]}]
LambdaDiagrams[i_Interpretation[_Integer, _], _] := {}
LambdaDiagrams[f_[x_], depth_] := Block[{fDiagram, xDiagram = DiagramNetwork @@ LambdaDiagrams[x, depth], out},
	out = xDiagram["OutputPorts"][[1]];
	fDiagram = DiagramNetwork @@ LambdaDiagrams[f /. Interpretation[_Integer, var_Integer] :> Interpretation[var, Evaluate @ out], depth];
	Join[fDiagram["SubDiagrams"], {Diagram["\[Application]", Unique["x"], {fDiagram["OutputPorts"][[1]], out}, "Shape" -> "Triangle"]}, xDiagram["SubDiagrams"]]
]
LambdaDiagrams[x_, _] := {Diagram[x, Unique["x"], "Shape" -> "UpsideDownTriangle"]}


LambdaDiagram::missing = "Lambda package is not loaded. Please install the package with PacletInstall[\"Wolfram/Lambda\"]";

Options[NetGraphDiagramNetwork] = Options[DiagramNetwork];
LambdaDiagram[expr_, depth_Integer : 0, opts : OptionsPattern[]] := Module[{lambdaIdx = 1},
	Check[Needs["Wolfram`Lambda`"], Message[LambdaDiagram::missing]; Return[$Failed]];
	DiagramNetwork[##, opts, "ShowPortLabels" -> False, "PortLabels" -> False, "ShowWireLabels" -> False] & @@ 
		Map[
			If[#["Name"] === HoldForm["\[Lambda]"], Diagram[#, "Expression" -> Style["\[Lambda]", 16, Bold, ColorData[109][lambdaIdx++]]], #] &,
			LambdaDiagrams[Wolfram`Lambda`TagLambda[expr], depth]
		]
]


End[];

EndPackage[];