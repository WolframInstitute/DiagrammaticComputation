BeginPackage["ProcessTheory`Port`"];

Port
PortQ


Begin["ProcessTheory`Port`Private`"];


(* ::Section:: *)
(* Definitions *)

Port::usage = "Port[expr] represents a symbolic port for node inputs and outputs"

Options[Port] = {"DualQ" -> False, "Type" -> \[FormalCapitalT]};

$PortHiddenOptions = {"Expression" -> "1"}

$PortProperties = Join[Keys[Options[Port]], {"Properties", "Data", "HoldExpression", "Types", "Arity", "Label"}];


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

Port[CircleTimes[ps__], opts : OptionsPattern[]] := CircleTimes @@ Map[Function[Null, Port[Unevaluated[#], opts], HoldFirst], Unevaluated[{ps}]]

Port /: CircleTimes[ps___Port ? PortQ] := Port["Expression" -> {ps}, "Type" -> CircleTimes @@ Through[{ps}["Type"]]]


(* conjugation *)

Port[SuperStar[p_], opts : OptionsPattern[]] := SuperStar[Port[Unevaluated[p], opts]]

Port /: SuperStar[p_Port ? PortQ] := p["Dual"]


(* merge options *)

Port[p_ ? PortQ, opts : OptionsPattern[]] := Port[Normal[Merge[{opts, p["Data"]}, First]]]


(* data constructor *)

Port[expr : Except[_Association | _Port | OptionsPattern[]], opts : OptionsPattern[]] := Port[FilterRules[{"Expression" :> expr, opts}, Join[Options[Port], $PortHiddenOptions]]]

Port[opts : OptionsPattern[]] := Port[KeySort[<|DeleteDuplicatesBy[First] @ FilterRules[{opts, Options[Port], $PortHiddenOptions}, Join[Options[Port], $PortHiddenOptions]]|>]]


(* ::Section:: *)
(* Properties *)


(* dispatch properties *)

(p_Port ? PortQ)[prop_] := PortProp[p, prop] 


(* property definitions *)

PortProp[_, "Properties"] := Sort[$PortProperties]

PortProp[HoldPattern[Port[data_]], "Data"] := data

PortProp[HoldPattern[Port[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

PortProp[p_, "HoldExpression"] := Extract[p["Data"], "Expression", HoldForm]

PortProp[p_, "Options"] := Normal[KeyDrop[p["Data"], "Expression"]]

PortProp[p_, "Types"] := Through[p["PortList"]["Type"]]

PortProp[p_, "Arity"] := Length[p["Types"]]

PortProp[p_, "Label"] := Replace[
    CircleTimes @@ Map[If[#["DualQ"], SuperStar, Identity][#["HoldExpression"]] &, p["PortList"]],
    {
        CircleTimes[x_, y_] /; x === SuperStar[y] :> OverHat[x],
        CircleTimes[x_, y_] /; SuperStar[x] ===y :> OverHat[y],
        CircleTimes[x_] :> x,
        CircleTimes[] -> "1"
    }
]

PortProp[p_, "Dual"] := Port[p, "DualQ" -> ! p["DualQ"]]


(* internal properties *)

PortProp[p_, "ProductQ"] := MatchQ[p["HoldExpression"], HoldForm[{___Port ? PortQ}]]

PortProp[p_, "PortList"] := If[p["ProductQ"],
    If[p["DualQ"], OperatorApplied[Comap]["Dual"], Identity] @ Catenate[Through[p["Expression"]["PortList"]]],
    {p}
]


(* ::Section:: *)
(* Formatting *)

Port /: MakeBoxes[p_Port /; PortQ[p], form_] := With[{
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