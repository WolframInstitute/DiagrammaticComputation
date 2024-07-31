(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


System`Private`NewContextPath[{"System`", "ProcessTheory`"}];

ProcessTheory`PortDump`$exported = {
	System`Port,
	System`PortQ
};

Unprotect /@ ProcessTheory`PortDump`$exported;
ClearAll /@ ProcessTheory`PortDump`$exported;

Begin["ProcessTheory`PortDump`"];


(* ::Section:: *)
(*Definitions*)


Options[Port] = {"Dimensions" -> {}, "DualQ" -> False, "Field" -> None}


(** Validation **)

PortQ[p_Port] := System`Private`HoldValidQ[p]

PortQ[___] := False

portQ[Port[data_Association]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "Dimensions" -> {___Integer}, "DualQ" -> _ ? BooleanQ, "Field" -> _}]]

portQ[___] := False

p_Port /; System`Private`HoldNotValidQ[p] && portQ[Unevaluated[p]] := System`Private`HoldSetValid[p]


(** Constructors **)

(* empty/unit *)

Port[(Power | Superscript | Overscript)[port_, 0], ___] := emptyPort[port]

Port[1 | CircleTimes[], ___] := emptyPort["1"]

emptyPort[t_] := Port[t, "Dimensions" -> {}, "Field" -> CircleTimes[]]


(* exponential *)

Port[(Power | Superscript | Overscript)[p_, n_Integer ? NonNegative], opts : OptionsPattern[]] := Port[Unevaluated[p], "Dimensions" -> {n}, opts]


(* product *)

Port[CircleTimes[ps__], opts : OptionsPattern[]] := CircleTimes @@ Map[Function[Null, Port[Unevaluated[#], opts], HoldFirst], Unevaluated[{ps}]]

Port /: CircleTimes[ps___Port ? PortQ] := Port["Expression" -> {ps}, "Dimensions" -> Catenate[Through[{ps}["Dimensions"]]]]


(* conjugation *)

Port[SuperStar[p_], opts : OptionsPattern[]] := SuperStar[Port[Unevaluated[p], opts]]

Port /: SuperStar[p_Port ? PortQ] := p["Dual"]


(* merge options *)

Port[p_ ? PortQ, opts___] := With[{expr = Unevaluated @@ p["HoldExpression"]},
    Port[expr, Normal[Merge[{opts, p["Options"]}, First]]]
]


(* data constructor *)

Port[expr : Except[_Association | _Port | OptionsPattern[]], opts : OptionsPattern[]] := Port[KeySort[<|"Expression" :> expr, FilterRules[{Options[Port], opts}, Options[Port]]|>]]

Port[opts : OptionsPattern[]] := Port[KeySort[<|"Expression" -> "1", FilterRules[{Options[Port], opts}, Append["Expression"] @ Options[Port]]|>]]



(** Properties **)

$PortProperties = Join[Keys[Options[Port]], {"Properties", "Data", "HoldExpression", "Dimension", "Arity", "Label"}]


(* dispatch properties *)

(p_Port ? PortQ)[prop_] := PortProp[p, prop] 


(* property definitions *)

PortProp[_, "Properties"] := Sort[$PortProperties]

PortProp[HoldPattern[Port[data_]], "Data"] := data

PortProp[HoldPattern[Port[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

PortProp[p_, "HoldExpression"] := Extract[p["Data"], "Expression", HoldForm]

PortProp[p_, "Options"] := Normal[KeyDrop[p["Data"], "Expression"]]

PortProp[p_, "Dimension"] := Times @@ p["Dimensions"]

PortProp[p_, "Arity"] := Length[Catenate[Through[p["PortList"]["Dimensions"]]]]

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

PortProp[p_, "Fields"] := Through[p["PortList"]["Field"]]

PortProp[p_, "ProductQ"] := MatchQ[p["HoldExpression"], HoldForm[{___Port ? PortQ}]]

PortProp[p_, "PortList"] := If[p["ProductQ"],
    If[p["DualQ"], OperatorApplied[Comap]["Dual"], Identity] @ Catenate[Through[p["Expression"]["PortList"]]],
    {p}
]



(** Formatting **)

Port /: MakeBoxes[p_Port /; PortQ[Unevaluated[p]], form_] := With[{
    boxes = ToBoxes[p["Label"], form],
    tooltip = With[{fields = Replace[p["Fields"], None -> \[FormalCapitalA], 1], dims = p["Dimensions"]},
        If[ Length[fields] == Length[dims] && Length[dims] > 1,
            ToBoxes[CircleTimes @@ MapThread[Superscript, {fields, dims}] /. CircleTimes[] -> 1, form],
            ToBoxes[Superscript[First[fields], Times @@ dims], form]
        ]
    ]
},
    InterpretationBox[
        boxes,
        p,
        Tooltip -> tooltip
    ]
]


(* ::Section::Closed:: *)
(*Package Footer*)


End[]; (* ProcessTheory`PortDump` *)

System`Private`RestoreContextPath[];

ProcessTheory`PortDump`$exported
