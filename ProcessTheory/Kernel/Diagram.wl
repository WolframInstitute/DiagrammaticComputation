BeginPackage["ProcessTheory`Diagram`", {"ProcessTheory`Port`", "ProcessTheory`Node`"}];

NodeDiagram
NodeDiagramQ

Begin["ProcessTheory`Diagram`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Options[NodeDiagram] = {};

$NodeDiagramHiddenOptions = {"Nodes" -> {}, "DiagramOptions" -> {}};

$NodeDiagramProperties = Join[Keys[Options[NodeDiagram]], {"Properties", "FreePorts", "PortGraph", "Graph", "Diagram"}];


(* ::Subsection:: *)
(* Validation *)

NodeDiagramQ[HoldPattern[NodeDiagram[data_Association]]] := MatchQ[data, KeyValuePattern[{"Nodes" -> _List, "DiagramOptions" -> OptionsPattern[]}]]

NodeDiagramQ[___] := False


x_NodeDiagram /; System`Private`HoldNotValidQ[x] && NodeDiagramQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

NodeDiagramQ[x_NodeDiagram] := System`Private`HoldValidQ[x]

NodeDiagramQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

NodeDiagram[nodes : Except[_Association | _NodeDiagram | OptionsPattern[]], opts : OptionsPattern[]] :=
    NodeDiagram[FilterRules[{"Nodes" -> Node /@ Developer`ToList[nodes], opts}, Join[Options[NodeDiagram], $NodeDiagramHiddenOptions, Options[NodesNetGraph]]]]

NodeDiagram[opts : OptionsPattern[]] := NodeDiagram[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[NodesNetGraph]], opts, Options[NodeDiagram], $NodeDiagramHiddenOptions},
        Join[Options[NodeDiagram], $NodeDiagramHiddenOptions]
    ]|>
]]


(* ::Subsection:: *)
(* Properties *)


(* dispatch properties *)

(d_NodeDiagram ? NodeDiagramQ)[prop_, opts___] := NodeDiagramProp[d, prop, opts] 


(* property definitions *)

NodeDiagramProp[_, "Properties"] := Sort[$NodeDiagramProperties]

NodeDiagramProp[HoldPattern[NodeDiagram[data_]], "Data"] := data

NodeDiagramProp[HoldPattern[NodeDiagram[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

NodeDiagramProp[d_, "FreePorts"] := NodesFreePorts[d["Nodes"]]

NodeDiagramProp[d_, "PortGraph", opts___] := NodesPortGraph[d["Nodes"], opts]

NodeDiagramProp[d_, "Graph", opts___] := NodesGraph[d["Nodes"], opts]

NodeDiagramProp[d_, "Diagram", opts___] := NodesNetGraph[d["Nodes"], opts, d["DiagramOptions"]]


(* ::Subsection:: *)
(* Formatting *)

NodeDiagram /: MakeBoxes[diag_NodeDiagram /; NodeDiagramQ[diag], form_] := With[{
    boxes = ToBoxes[diag["Diagram", BaseStyle -> {GraphicsHighlightColor -> Magenta}], form]
},
    InterpretationBox[boxes, diag]
]


End[];

EndPackage[];