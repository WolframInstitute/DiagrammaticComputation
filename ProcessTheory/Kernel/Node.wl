BeginPackage["ProcessTheory`Node`", {"ProcessTheory`Port`"}];

Node
NodeQ

NodeProduct
NodeCompose

NodesFreePorts

NodesPortGraph
NodesGraph

Begin["ProcessTheory`Node`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Node::usage = "Node[expr] represents a symbolic node with input and output nodes"

Options[Node] = {};

$NodeHiddenOptions = {"Expression" -> None, "OutputPorts" -> {}, "InputPorts" -> {}, "DiagramOptions" -> {}};

$NodeProperties = Join[Keys[Options[Node]], {"Properties", "HoldExpression", "Ports", "Arity", "FlattenOutputs", "FlattenInputs", "Flatten"}];


(* ::Subsection:: *)
(* Validation *)

nodeQ[HoldPattern[Node[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "OutputPorts" -> {___Port ? PortQ}, "InputPorts" -> {___Port ? PortQ}, "DiagramOptions" -> OptionsPattern[]}]]

nodeQ[___] := False


x_Node /; System`Private`HoldNotValidQ[x] && nodeQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

NodeQ[x_Node] := System`Private`HoldValidQ[x]

NodeQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

Node[expr : Except[_Association | _Node | OptionsPattern[]], outputs : {} | Except[OptionsPattern[], _List] : {}, inputs : {} | Except[OptionsPattern[], _List] : {}, opts : OptionsPattern[]] :=
    Node[FilterRules[{"Expression" :> expr, "OutputPorts" -> Port /@ outputs, "InputPorts" -> Comap[Port /@ inputs, "Dual"], opts}, Join[Options[Node], $NodeHiddenOptions, Options[NodeDiagram]]]]

Node[opts : OptionsPattern[]] := Node[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[NodeDiagram]], opts, Options[Node], $NodeHiddenOptions},
        Join[Options[Node], $NodeHiddenOptions]
    ]|>
]]


(* merge options *)

Node[n_ ? NodeQ, opts : OptionsPattern[]] := Node[Replace[Normal[Merge[{opts, n["Data"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* horizontal product *)

NodeProduct[ns___Node ? NodeQ, opts : OptionsPattern[]] := Node[
    opts,
    With[{expr = Unevaluated @@ CircleTimes @@@ Hold[Evaluate[Through[{ns}["HoldExpression"]]]]}, "Expression" :> expr],
    "OutputPorts" -> Replace[CircleTimes @@@ Through[{ns}["OutputPorts"]], CircleTimes[] -> Port[1], 1],
    "InputPorts" -> Replace[CircleTimes @@@ Through[{ns}["InputPorts"]], CircleTimes[] -> Port[SuperStar[1]], 1]
]


(* vertical product *)

NodeCompose[ns___Node ? NodeQ, opts : OptionsPattern[]] := Node[
    opts,
    With[{expr = Unevaluated @@ Composition @@@ Hold[Evaluate[Through[{ns}["HoldExpression"]]]]}, "Expression" :> expr],

    Block[{graph = NodesGraph[{ns}], nodes = Through[{ns}["Flatten"]], freeWires, edges},
        freeWires = Cases[Pick[VertexList[graph], VertexDegree[graph], 1], _HoldForm];
        edges = EdgeList[graph];
        {
            "OutputPorts" -> Cases[edges, DirectedEdge[{nodeId_, 1, portId_}, Alternatives @@ freeWires] :> nodes[[nodeId]]["OutputPorts"][[portId]]],
            "InputPorts" -> Cases[edges, DirectedEdge[Alternatives @@ freeWires, {nodeId_, 2, portId_}] :> nodes[[nodeId]]["InputPorts"][[portId]]]
        }
    ]
]


(* ::Subsection:: *)
(* Properties *)


(* dispatch properties *)

(p_Node ? NodeQ)[prop_] := NodeProp[p, prop] 


(* property definitions *)

NodeProp[_, "Properties"] := Sort[$NodeProperties]

NodeProp[HoldPattern[Node[data_]], "Data"] := data

NodeProp[HoldPattern[Node[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

NodeProp[n_, "HoldExpression"] := Extract[n["Data"], "Expression", HoldForm]

NodeProp[n_, "Ports"] := Join[n["OutputPorts"], n["InputPorts"]]

NodeProp[n_, "OutputArity"] := Length[n["OutputPorts"]]

NodeProp[n_, "InputArity"] := Length[n["InputPorts"]]

NodeProp[n_, "Arity"] := Length[n["Ports"]]

NodeProp[n_, "FlattenOutputs"] := Node[n, "OutputPorts" -> Flatten[Through[n["OutputPorts"]["PortList"]]]]

NodeProp[n_, "FlattenInputs"] := Node[n, "InputPorts" -> Flatten[Through[n["InputPorts"]["PortList"]]]]

NodeProp[n_, "Flatten"] := n["FlattenOutputs"]["FlattenInputs"]

NodeProp[n_, "View"] := With[{
    expr = n["HoldExpression"],
    outputs = Through[n["OutputPorts"]["Label"]],
    inputs = Through[Through[n["InputPorts"]["Dual"]]["Label"]]
},
    Defer[Node[expr, outputs, inputs]] //. HoldForm[x_] :> x
]

NodeProp[n_, "Symbol"] := Switch[n["Arity"], 1, VectorSymbol, 2, MatrixSymbol, _, ArraySymbol][n["HoldExpression"], n["Ports"]]

NodeProp[n_, "Diagram", opts___] := NodeDiagram[n, opts]

NodeProp[_, prop_] := Missing[prop]


(* ::Subsection:: *)
(* Formatting *)

Options[NodeDiagram] = Options[Graphics];

NodeDiagram[node_ ? NodeQ, opts : OptionsPattern[]] := Graphics[{
    EdgeForm[Black], FaceForm[Transparent], 
    Rectangle[],
    Text[ClickToCopy[node["HoldExpression"], node["View"]], {1/2, 1/2}],
    Arrowheads[Small],
    With[{xs = node["OutputPorts"]},
        MapThread[{Arrow[If[#2["DualQ"], Reverse, Identity] @ {{#, 1}, {#,  1.3}}], Text[ClickToCopy[#2, #2["View"]], {#,  1.5}]} &, {Range[0, 1, 1 / (Length[xs] + 1)][[2 ;; -2]], xs}]
    ],
    With[{xs = node["InputPorts"]},
        MapThread[{Arrow[If[#2["DualQ"], Reverse, Identity] @ {{#, 0}, {#, -0.3}}], Text[ClickToCopy[#2, #2["View"]], {#, -0.5}]} &, {Range[0, 1, 1 / (Length[xs] + 1)][[2 ;; -2]], xs}]
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


(* ::Subsection:: *)
(* Functions *)


Options[NodesPortGraph] = Options[Graph];
NodesPortGraph[nodes : {___Node ? NodeQ}, opts : OptionsPattern[]] := GraphSum[##, FilterRules[{opts}, Options[Graph]], VertexLabels -> Automatic] & @@
    (With[{vs = Through[#["HoldExpression"]]}, Graph[vs, UndirectedEdge @@@ Subsets[vs, {2}]]] & /@ Through[nodes["Ports"]])


Options[NodesGraph] = Options[Graph];
NodesGraph[nodes : {___Node ? NodeQ}, opts : OptionsPattern[]] := Block[{
    ports = Thread[{Through[#["OutputPorts"]], Through[#["InputPorts"]]}] & @ Through[nodes["Flatten"]]
},
    Graph[
        Join[
            MapIndexed[Annotation[#2[[1]], "Node" -> #1] &, nodes],
            Flatten[MapIndexed[Annotation[#2, "Port" -> #1] &, ports, {3}], 2]
        ],
        Flatten[
            MapIndexed[
                With[{node = #2[[1]], port = #2, wire = #1["HoldExpression"]},
                    Switch[port[[2]], 1, {DirectedEdge[node, port], DirectedEdge[port, wire]}, 2, {DirectedEdge[port, node], DirectedEdge[wire, port]}]
                ] &,
                ports,
                {3}
            ],
            3
        ],
        FilterRules[{opts}, Options[Graph]],
        VertexLabels -> MapAt[Placed[#, Center] &, {All, 2}] @ Join[
            {_ -> Automatic},
            Thread[Range[Length[nodes]] -> Through[nodes["HoldExpression"]]],
            Flatten[MapIndexed[#2 -> #1["Label"] &, ports, {3}], 2]
        ],
        VertexSize -> {_ -> Small, _Integer -> Large, {__Integer} -> Medium},
        VertexShapeFunction -> _Integer -> "Square",
        PerformanceGoal -> "Quality"
    ]
]

NodesFreePorts[nodes : {___Node ? NodeQ}] := Keys @ Select[CountsBy[Catenate[Through[Through[nodes["Flatten"]]["Ports"]]], #["HoldExpression"] &], EqualTo[1]]


End[];

EndPackage[];