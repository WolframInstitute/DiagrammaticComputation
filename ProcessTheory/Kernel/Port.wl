BeginPackage["ProcessTheory`Port`"];

Port
PortQ

PortProduct


Begin["ProcessTheory`Port`Private`"];


(* ::Section:: *)
(* Definitions *)

Port::usage = "Port[expr] represents a symbolic port for node inputs and outputs"

Options[Port] = {"DualQ" -> False, "Type" -> \[FormalCapitalT]};

$PortHiddenOptions = {"Expression" -> "1"}

$PortProperties = Join[Keys[Options[Port]], {"Properties", "Data", "HoldExpression", "Types", "Arity", "Label", "View", "Dual"}];


(* ::Section:: *)
(* Validation *)

portQ[HoldPattern[Port[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "DualQ" -> _ ? BooleanQ, "Type" -> _}]]

portQ[___] := False


x_Port /; System`Private`HoldNotValidQ[x] && portQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

PortQ[x_Port] := System`Private`HoldValidQ[x]

PortQ[___] := False


(* ::Section:: *)
(* Constructors *)


(* empty/unit *)

Port[(Power | Superscript | Overscript)[port_, 0], ___] := emptyPort[port]

Port[1 | CircleTimes[], ___] := emptyPort["1"]

emptyPort[p_] := Port[p, "Type" -> CircleTimes[]]


(* exponential *)

Port[(Power | Superscript | Overscript)[p_, n_Integer ? NonNegative], opts : OptionsPattern[]] := With[{port = Port[Unevaluated[p], opts]}, Port[port, "Type" -> Superscript[port["Type"], n]]]


(* product *)

Port[CircleTimes[ps__], opts : OptionsPattern[]] := PortProduct @@ Map[Function[Null, Port[Unevaluated[#], opts], HoldFirst], Unevaluated[{ps}]]

PortProduct[ps___Port ? PortQ] := If[AllTrue[{ps}, #["DualQ"] &],
    Port["Expression" -> Through[{ps}["Dual"]], "DualQ" -> True, "Type" -> CircleTimes @@ Through[{ps}["Type"]]],
    Port["Expression" -> {ps}, "Type" -> CircleTimes @@ Through[{ps}["Type"]]]
]


(* conjugation *)

Port[SuperStar[p_], opts : OptionsPattern[]] := SuperStar[Port[Unevaluated[p], opts]]

Port /: SuperStar[p_Port ? PortQ] := p["Dual"]


(* merge options *)

Port[p_ ? PortQ, opts : OptionsPattern[]] := Port[Replace[Normal[Merge[{opts, p["Data"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* data constructor *)

Port[expr : Except[_Association | _Port | OptionsPattern[]], opts : OptionsPattern[]] := Port[FilterRules[{"Expression" :> expr, opts}, Join[Options[Port], $PortHiddenOptions]]]

Port[expr : Except[_Association], type : Except[OptionsPattern[]], opts : OptionsPattern[]] := Port[expr, "Type" -> type, opts]

Port[opts : OptionsPattern[]] := Port[KeySort[<|DeleteDuplicatesBy[First] @ FilterRules[{opts, Options[Port], $PortHiddenOptions}, Join[Options[Port], $PortHiddenOptions]]|>]]


(* ::Section:: *)
(* Properties *)


(* dispatch properties *)

(p_Port ? PortQ)[prop_, opts___] := PortProp[p, prop, opts] 


(* property definitions *)

PortProp[_, "Properties"] := Sort[$PortProperties]

PortProp[HoldPattern[Port[data_]], "Data"] := data

PortProp[HoldPattern[Port[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

PortProp[p_, "HoldExpression"] := Extract[p["Data"], "Expression", HoldForm]

PortProp[p_, "Options"] := Normal[KeyDrop[p["Data"], "Expression"]]

PortProp[p_, "Types"] := Through[Flatten[p["PortList"]]["Type"]]

PortProp[p_, "Arity"] := Length[p["Types"]]

PortProp[p_, "Label"] := ReplaceAll[
    ReplaceAll[p["PortList"], q_Port :> If[q["DualQ"], SuperStar, Identity][q["HoldExpression"]]] /. List -> CircleTimes,
    {
        CircleTimes[x_, y_] /; x === SuperStar[y] :> OverHat[x],
        CircleTimes[x_, y_] /; SuperStar[x] ===y :> OverHat[y],
        CircleTimes[x_] :> x,
        CircleTimes[] -> "1"
    }
]

PortProp[p_, "View"] := With[{
    label = p["Label"]
},
    Defer[Port[label]] /. HoldForm[x_] :> x
]

PortProp[p_, "Dual"] := Port[p, "DualQ" -> ! p["DualQ"]]

PortProp[_, prop_] := Missing[prop]


(* internal properties *)

PortProp[p_, "ProductQ"] := MatchQ[p["HoldExpression"], HoldForm[{___Port ? PortQ}]]

PortProp[p_, "PortList"] := If[p["ProductQ"],
    If[p["DualQ"], ReplaceAll[q_Port :> q["Dual"]], Identity] @ Through[p["Expression"]["PortList"]],
    p
]


(* ::Section:: *)
(* Formatting *)

Port /: MakeBoxes[p : Port[_Association] ? PortQ, form_] := With[{
    boxes = ToBoxes[p["Label"], form],
    tooltip = ToBoxes[p["Type"] /. {CircleTimes[] -> "1", CircleTimes[x_] :> x}, form]
},
    InterpretationBox[
        boxes,
        p,
        Tooltip -> tooltip
    ]
]



End[];

EndPackage[];