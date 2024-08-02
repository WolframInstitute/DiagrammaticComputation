BeginPackage["ProcessTheory`Diagram`", {"ProcessTheory`Port`", "ProcessTheory`Node`"}];

ProcessDiagram
ProcessDiagramQ

Begin["ProcessTheory`Diagram`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Options[ProcessDiagram] = {};

$ProcessDiagramHiddenOptions = {"Nodes" -> {}, "DiagramOptions" -> {}};

$ProcessDiagramProperties = Join[Keys[Options[ProcessDiagram]], {"Properties", "FreePorts", "PortGraph", "Graph", "Diagram"}];


(* ::Subsection:: *)
(* Validation *)

processDiagramQ[HoldPattern[ProcessDiagram[data_Association]]] := MatchQ[data, KeyValuePattern[{"Nodes" -> _List, "DiagramOptions" -> OptionsPattern[]}]]

processDiagramQ[___] := False


x_ProcessDiagram /; System`Private`HoldNotValidQ[x] && processDiagramQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

ProcessDiagramQ[x_ProcessDiagram] := System`Private`HoldValidQ[x]

ProcessDiagramQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

ProcessDiagram[nodes : Except[_Association | _ProcessDiagram | OptionsPattern[]], opts : OptionsPattern[]] :=
    ProcessDiagram[FilterRules[{"Nodes" -> Node /@ Developer`ToList[nodes], opts}, Join[Options[ProcessDiagram], $ProcessDiagramHiddenOptions, Options[NodesNetGraph]]]]

ProcessDiagram[opts : OptionsPattern[]] := ProcessDiagram[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[NodesNetGraph]], opts, Options[ProcessDiagram], $ProcessDiagramHiddenOptions},
        Join[Options[ProcessDiagram], $ProcessDiagramHiddenOptions]
    ]|>
]]


(* ::Subsection:: *)
(* Properties *)


(* dispatch properties *)

(d_ProcessDiagram ? ProcessDiagramQ)[prop_, opts___] := ProcessDiagramProp[d, prop, opts] 


(* property definitions *)

ProcessDiagramProp[_, "Properties"] := Sort[$ProcessDiagramProperties]

ProcessDiagramProp[HoldPattern[ProcessDiagram[data_]], "Data"] := data

ProcessDiagramProp[HoldPattern[ProcessDiagram[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

ProcessDiagramProp[d_, "FreePorts"] := NodesFreePorts[d["Nodes"]]

ProcessDiagramProp[d_, "PortGraph", opts___] := NodesPortGraph[d["Nodes"], opts]

ProcessDiagramProp[d_, "Graph", opts___] := NodesGraph[d["Nodes"], opts]

ProcessDiagramProp[d_, "Diagram", opts___] := NodesNetGraph[d["Nodes"], opts, d["DiagramOptions"]]


(* ::Subsection:: *)
(* Formatting *)

ProcessDiagram /: MakeBoxes[diag_ProcessDiagram /; ProcessDiagramQ[diag], form_] := With[{
    boxes = ToBoxes[diag["Diagram", BaseStyle -> {GraphicsHighlightColor -> Magenta}], form]
},
    InterpretationBox[boxes, diag]
]


End[];

EndPackage[];