BeginPackage["ProcessTheory`Diagram`ToDiagram`"];

ToDiagram

Begin["ProcessTheory`Diagram`ToDiagram`Private`"];


ToDiagram[ng_NetGraph, opts : OptionsPattern[NetGraphDiagramNetwork]] := NetGraphDiagramNetwork[ng, opts]


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


End[];

EndPackage[];