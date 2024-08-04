BeginPackage["ProcessTheory`Port`"];

Port
PortQ

PortDual
PortProduct
PortSum


Begin["ProcessTheory`Port`Private`"];


(* ::Section:: *)
(* Definitions *)

Port::usage = "Port[expr] represents a symbolic port for node inputs and outputs"

Options[Port] = {"Type" -> \[FormalCapitalT]};

$PortHiddenOptions = {"Expression" -> "1"}

$PortProperties = Join[Keys[Options[Port]], {"Properties", "Data", "HoldExpression", "Name", "Types", "Arity", "Label", "View", "Dual"}];


(* ::Section:: *)
(* Validation *)

portQ[HoldPattern[Port[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "Type" -> _}]]

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

Port[0 | CirclePlus[], ___] := Port["0", "Type" -> CirclePlus[]]


(* exponential *)

Port[(Power | Superscript | Overscript)[p_, n_Integer ? NonNegative], opts : OptionsPattern[]] := With[{port = Port[Unevaluated[p], opts]}, Port[port, "Type" -> Superscript[port["Type"], n]]]


(* product *)

Port[CircleTimes[ps__], opts : OptionsPattern[]] := PortProduct @@ Map[Function[Null, Port[Unevaluated[#], opts], HoldFirst], Unevaluated[{ps}]]

PortProduct[ps___Port ? PortQ] := If[AllTrue[{ps}, #["DualQ"] &],
    Port["Expression" :> PortDual[PortProduct[##]], "Type" -> CircleTimes @@ Through[{ps}["Type"]]] & @@ Through[{ps}["Dual"]],
    Port["Expression" :> PortProduct[ps], "Type" -> CircleTimes @@ Through[{ps}["Type"]]]
]


(* sum *)

Port[CirclePlus[ps__], opts : OptionsPattern[]] := PortSum @@ Map[Function[Null, Port[Unevaluated[#], opts], HoldFirst], Unevaluated[{ps}]]

PortSum[ps___Port ? PortQ] := If[AllTrue[{ps}, #["DualQ"] &],
    Port["Expression" :> PortDual[PortSum[ps]], "Type" -> CirclePlus @@ Through[{ps}["Type"]]] & @@ Through[{ps}["Dual"]],
    Port["Expression" :> PortSum[ps], "Type" -> CirclePlus @@ Through[{ps}["Type"]]]
]


(* conjugation *)

Port[SuperStar[p_], opts : OptionsPattern[]] := PortDual[Port[Unevaluated[p], opts]]

PortDual[p_Port ? PortQ] := Function[Null, Port["Expression" :> #, "Type" -> Replace[p["Type"], {SuperStar[x_] :> x, x_ :> SuperStar[x]}]], HoldFirst] @@
    Replace[p["HoldExpression"], {HoldForm[PortDual[q_]] :> HoldForm[q], HoldForm[q_] :> HoldForm[PortDual[q]]}]


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

PortProp[p_, "Name"] := Replace[p["HoldExpression"], HoldForm[PortDual[q_]] :> HoldForm[q]]

PortProp[p_, "Options"] := Normal[KeyDrop[p["Data"], "Expression"]]

PortProp[p_, "Types"] := Through[Flatten[p["PortTree"]]["Type"]]

PortProp[p_, "Arity"] := Length[p["Types"]]

PortProp[p_, "Label"] := ReplaceAll[
    ReplaceAll[p["PortTree"], q_Port :> q["HoldExpression"]],
    {
        CircleTimes[x_, y_] /; x === SuperStar[y] :> OverHat[x],
        CircleTimes[x_, y_] /; SuperStar[x] === y :> OverHat[y],
        (CircleTimes | CirclePlus)[x_] :> x,
        CircleTimes[] -> "1",
        CirclePlus[] -> "0"
    }
]

PortProp[p_, "View"] := With[{
    label = p["Label"]
},
    Defer[Port[label]] /. HoldForm[x_] :> x
]

PortProp[p_, "Dual"] := PortDual[p]

PortProp[_, prop_] := Missing[prop]


(* internal properties *)

PortProp[p_, "DualQ"] := MatchQ[p["HoldExpression"], HoldForm[_PortDual]]

PortProp[p_, "ProductQ"] := MatchQ[p["HoldExpression"], HoldForm[_PortProduct]]

PortProp[p_, "SumQ"] := MatchQ[p["HoldExpression"], HoldForm[_PortSum]]

PortProp[p_, "PortTree"] :=
    Replace[p["HoldExpression"], {
        HoldForm[PortDual[q_]] :> SuperStar[Port[q]["PortTree"]],
        HoldForm[PortProduct[ps___]] :> CircleTimes @@ Through[{ps}["PortTree"]],
        HoldForm[PortSum[ps___]] :> CirclePlus @@ Through[{ps}["PortTree"]],
        _ :> p
    }]

PortProp[p_, "ProductList"] := Replace[p["HoldExpression"], {
    HoldForm[PortProduct[ps___]] :> Catenate[Through[{ps}["ProductList"]]],
    _ :> {p}
}]

PortProp[p_, "SumList"] := Replace[p["HoldExpression"], {
    HoldForm[PortSum[ps___]] :> Catenate[Through[{ps}["SumList"]]],
    _ :> {p}
}]



(* ::Section:: *)
(* Formatting *)

Port /: MakeBoxes[p : Port[_Association] ? PortQ, form_] := With[{
    boxes = ToBoxes[p["Label"], form],
    tooltip = ToBoxes[p["Type"] /. {CircleTimes[] -> "1", CircleTimes[x_] :> x, CirclePlus[] -> "0", CirclePlus[x_] :> x}, form]
},
    InterpretationBox[
        boxes,
        p,
        Tooltip -> tooltip
    ]
]

PortDual /: MakeBoxes[PortDual[p_], form_] := With[{boxes = ToBoxes[SuperStar[p], form]}, InterpretationBox[boxes, PortDual[p]]]

PortProduct /: MakeBoxes[PortProduct[ps___], form_] := With[{boxes = ToBoxes[CircleTimes[ps], form]}, InterpretationBox[boxes, PortProduct[ps]]]

PortSum /: MakeBoxes[PortSum[ps___], form_] := With[{boxes = ToBoxes[CirclePlus[ps], form]}, InterpretationBox[boxes, PortSum[ps]]]



End[];

EndPackage[];