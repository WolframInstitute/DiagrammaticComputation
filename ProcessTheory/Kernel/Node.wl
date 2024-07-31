BeginPackage["ProcessTheory`Node`", {"ProcessTheory`Port`"}];

Node
NodeProduct
NodeQ

Begin["ProcessTheory`Node`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Node::usage = "Node[expr] represents a symbolic node with input and output nodes"

Options[Node] = {};

$NodeHiddenOptions = {"Expression" -> None, "Outputs" -> {}, "Inputs" -> {}, "DiagramOptions" -> {}};

$NodeProperties = Join[Keys[Options[Node]], {"Properties", "HoldExpression", "FlattenOutputs", "FlattenInputs", "Flatten"}];


(* ::Subsection:: *)
(* Validation *)

nodeQ[HoldPattern[Node[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "Outputs" -> {___Port ? PortQ}, "Inputs" -> {___Port ? PortQ}, "DiagramOptions" -> OptionsPattern[]}]]

nodeQ[___] := False


x_Node /; System`Private`HoldNotValidQ[x] && nodeQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

NodeQ[x_Node] := System`Private`HoldValidQ[x]

NodeQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

Node[expr : Except[_Association | _Node | OptionsPattern[]], outputs : Except[OptionsPattern[], _List] : {}, inputs : Except[OptionsPattern[], _List] : {}, opts : OptionsPattern[]] :=
    Node[FilterRules[{"Expression" :> expr, "Outputs" -> Port /@ outputs, "Inputs" -> Port /@ inputs, opts}, Join[Options[Node], $NodeHiddenOptions, Options[NodeDiagram]]]]

Node[opts : OptionsPattern[]] := Node[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[NodeDiagram]], opts, Options[Node], $NodeHiddenOptions},
        Join[Options[Node], $NodeHiddenOptions]
    ]|>
]]


(* merge options *)

Node[n_ ? NodeQ, opts : OptionsPattern[]] := Node[Normal[Merge[{opts, n["Data"]}, First]]]


(* horizontal product *)

NodeProduct[ns___Node ? NodeQ, opts : OptionsPattern[]] := Node[
    opts,
    With[{expr = Unevaluated @@ CircleTimes @@@ Hold[Evaluate[Through[{ns}["HoldExpression"]]]]}, "Expression" :> expr],
    "Outputs" -> CircleTimes @@@ Through[{ns}["Outputs"]],
    "Inputs" -> CircleTimes @@@ Through[{ns}["Inputs"]]
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

NodeProp[n_, "FlattenOutputs"] := Node[n, "Outputs" -> Catenate[Through[n["Outputs"]["PortList"]]]]

NodeProp[n_, "FlattenInputs"] := Node[n, "Inputs" -> Catenate[Through[n["Inputs"]["PortList"]]]]

NodeProp[n_, "Flatten"] := n["FlattenOutputs"]["FlattenInputs"]

NodeProp[n_, "Diagram", opts___] := NodeDiagram[n, opts]


(* ::Subsection:: *)
(* Formatting *)

Options[NodeDiagram] = Options[Graphics];

NodeDiagram[node_, opts : OptionsPattern[]] := Graphics[{
    EdgeForm[Black], FaceForm[Transparent], 
    Rectangle[],
    Text[node["Expression"], {1/2, 1/2}],
    With[{xs = node["Outputs"]},
        MapThread[{Line[{{#, 1}, {#,  1.3}}], Text[#2, {#,  1.5}]} &, {Range[0, 1, 1 / (Length[xs] + 1)][[2 ;; -2]], xs}]
    ],
    With[{xs = node["Inputs"]},
        MapThread[{Line[{{#, 0}, {#, -0.3}}], Text[#2, {#, -0.5}]} &, {Range[0, 1, 1 / (Length[xs] + 1)][[2 ;; -2]], xs}]
    ]
},
    FilterRules[{opts, node["DiagramOptions"]}, Options[Graphics]],
    ImageSize -> Tiny,
    BaseStyle -> {
        GraphicsHighlightColor -> Magenta
    }
]

Node /: MakeBoxes[node_Node /; NodeQ[node], form_] := With[{boxes = ToBoxes[node["Diagram"], form]},
    InterpretationBox[boxes, node]
]


End[];

EndPackage[];