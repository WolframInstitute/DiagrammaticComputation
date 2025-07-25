BeginPackage["Wolfram`DiagrammaticComputation`Port`", {"Wolfram`DiagrammaticComputation`Utilities`"}];

Port
PortQ
EmptyPortQ
ZeroPortQ

PortDual
PortMinus
PortNeutral
PortProduct
PortSum
PortPower


Begin["Wolfram`DiagrammaticComputation`Port`Private`"];


(* ::Section:: *)
(* Definitions *)

Port::usage = "Port[expr] represents a symbolic port for diagram inputs and outputs"

$DefaultPortType = \[FormalCapitalT]

Options[Port] = {"Type" -> $DefaultPortType, "NeutralQ" -> False};

$PortHiddenOptions = {"Expression" -> "1"}

$PortProperties = Join[Keys[Options[Port]], {"Properties", "Data", "HoldExpression", "Name", "Types", "Arity", "Label", "View", "Dual", "Neutral", "Reverse"}];


(* ::Section:: *)
(* Validation *)

portQ[HoldPattern[Port[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "Type" -> _, "NeutralQ" -> _ ? BooleanQ}]]

portQ[___] := False


x_Port /; System`Private`HoldNotValidQ[x] && portQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

PortQ[x_Port] := System`Private`HoldValidQ[x]

PortQ[___] := False


(* ::Section:: *)
(* Constructors *)


(* empty/unit *)

Port[(Power | Superscript | Overscript)[port_, 0], ___] := emptyPort[port]

Port["1" | CircleTimes[], ___] := emptyPort["1"]

emptyPort[p_] := Port["Expression" :> p, "Type" -> CircleTimes[]]

emptyTypeQ[CircleTimes[]] := True
emptyTypeQ[(SuperStar | OverBar)[t_]] := emptyTypeQ[t]
emptyTypeQ[Superscript[t_, _]] := emptyTypeQ[t]
emptyTypeQ[_] := False

EmptyPortQ[p_Port ? PortQ] := emptyTypeQ[p["Type"]]

Port["0" | CirclePlus[], ___] := Port["Expression" :> "0", "Type" -> CirclePlus[]]

zeroTypeQ[CirclePlus[]] := True
zeroTypeQ[(SuperStar | OverBar)[t_]] := zeroTypeQ[t]
zeroTypeQ[Superscript[t_, _]] := zeroTypeQ[t]
zeroTypeQ[_] := False

ZeroPortQ[p_Port ? PortQ] := zeroTypeQ[p["Type"]]


(* exponential *)

Port[(Power | Superscript | Overscript)[p_, n_Integer], opts : OptionsPattern[]] :=
    PortProduct @@ ConstantArray[If[n >= 0, Port, PortDual][Unevaluated[p], opts], Abs[n]]


(* product *)

Port[CircleTimes[ps__], opts : OptionsPattern[]] := PortProduct @@ Map[Function[Null, Port[Unevaluated[#], opts], HoldFirst], Unevaluated[{ps}]]

PortProduct[p_Port ? PortQ] := p

PortProduct[ps___Port ? PortQ] := If[Length[{ps}] > 0 && AllTrue[{ps}, #["DualQ"] &],
    Port["Expression" :> PortDual[PortProduct[##]], "Type" -> CircleTimes @@ Through[{ps}["Type"]]] & @@ Through[{ps}["Dual"]],
    Port["Expression" :> PortProduct[ps], "Type" -> CircleTimes @@ Through[{ps}["Type"]]]
]


(* multiplication *)

Port[Times[n_Integer, p_] | Times[p_, n_Integer], opts : OptionsPattern[]] :=
    PortSum @@ ConstantArray[If[n >= 0, Port, PortMinus][Unevaluated[p], opts], Abs[n]]


(* sum *)

Port[CirclePlus[ps__], opts : OptionsPattern[]] := PortSum @@ Map[Function[Null, Port[Unevaluated[#], opts], HoldFirst], Unevaluated[{ps}]]

PortSum[p_Port ? PortQ] := p

PortSum[ps___Port ? PortQ] := If[Length[{ps}] > 0 && AllTrue[{ps}, #["MinusQ"] &],
    Port["Expression" :> PortMinus[PortSum[##]], "Type" -> CirclePlus @@ Through[{ps}["Type"]]] & @@ Through[{ps}["Minus"]],
    Port["Expression" :> PortSum[ps], "Type" -> CirclePlus @@ Through[{ps}["Type"]]]
]


(* power *)

Port[(Superscript | Power)[p_, q_], opts : OptionsPattern[]] := PortPower[Port[Unevaluated[p], opts], Port[Unevaluated[q], opts]]

PortPower[p_Port ? PortQ, q_Port ? PortQ] := Port["Expression" :> PortPower[p, q], "Type" -> Superscript[p["Type"], q["Type"]]]


(* conjugation/inverse *)

Port[SuperStar[p_], opts : OptionsPattern[]] := PortDual[Port[Unevaluated[p], opts]]

PortDual[p_Port ? PortQ] := 
    Function[Null, Port[p, "Expression" :> #, "Type" -> Replace[p["Type"], {SuperStar[x_] :> x, x_ :> SuperStar[x]}]], HoldFirst] @@
        Replace[p["HoldExpression"], {HoldForm[PortDual[q_]] :> HoldForm[q], HoldForm[q_] :> HoldForm[PortDual[q]]}]

PortDual[expr_] := PortDual[Port[Unevaluated[expr]]]


(* negation *)

Port[OverBar[p_], opts : OptionsPattern[]] := PortMinus[Port[Unevaluated[p], opts]]

PortMinus[p_Port ? PortQ] :=
    Function[Null, Port[p, "Expression" :> #, "Type" -> Replace[p["Type"], {OverBar[x_] :> x, x_ :> OverBar[x]}]], HoldFirst] @@
        Replace[p["HoldExpression"], {HoldForm[PortMinus[q_]] :> HoldForm[q], HoldForm[q_] :> HoldForm[PortMinus[q]]}]

PortMinus[expr_] := PortMinus[Port[Unevaluated[expr]]]


(* neutral *)

Port[OverTilde[p_], opts : OptionsPattern[]] := PortNeutral[Port[Unevaluated[p], opts]]

PortNeutral[p_Port ? PortQ] := Port[p, Function[Null, "Expression" :> ##, HoldFirst] @@ Replace[p["HoldExpression"], {
        HoldForm[(h : PortProduct | PortSum | PortDual | PortMinus)[ps___]] :> (HoldForm[h[##]] & @@ (PortNeutral /@ {ps}))
    }],
    "NeutralQ" -> ! p["NeutralQ"]
]

PortNeutral[expr_] := PortNeutral[Port[Unevaluated[expr]]]


(* merge options *)

Port[p_Port ? PortQ, opts : OptionsPattern[]] := Port[Replace[Normal[Merge[{opts, p["Data"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* data constructor *)

Port[expr : Except[_Association | _Port | OptionsPattern[]], opts : OptionsPattern[]] := Port[FilterRules[{"Expression" :> expr, opts}, Join[Options[Port], $PortHiddenOptions]]]

Port[expr : Except[_Association], type : Except[OptionsPattern[]], opts : OptionsPattern[]] := Port[Port[Unevaluated[expr]], "Type" -> type, opts]

Port[opts : OptionsPattern[]] := Port[KeySort[<|DeleteDuplicatesBy[First] @ FilterRules[{opts, Options[Port], $PortHiddenOptions}, Join[Options[Port], $PortHiddenOptions]]|>]]

Port[{}] := Port["Expression" :> {}]

(* ::Section:: *)
(* Properties *)


(* dispatch properties *)

(p_Port ? PortQ)[prop_, opts___] := PortProp[p, prop, opts] 


(* property definitions *)

PortProp[_, "Properties"] := Sort[$PortProperties]

PortProp[HoldPattern[Port[data_]], "Data"] := data

PortProp[HoldPattern[Port[data_Association]], prop_] /; KeyExistsQ[data, prop] := Lookup[data, prop]

PortProp[p_, "HoldExpression"] := Extract[p["Data"], "Expression", HoldForm]

PortProp[p_, "HoldName"] := Replace[p["HoldExpression"], HoldForm[PortDual[x_] | x_] :> HoldForm[x]]

PortProp[p_, "Name"] := Replace[p["HoldName"], HoldForm[Interpretation[HoldForm[x_] | x_, _] | x_] :> x]

PortProp[p_, "Options"] := Normal[KeyDrop[p["Data"], "Expression"]]

PortProp[p_, "Types"] := Through[Flatten[p["PortTree"]]["Type"]]

PortProp[p_, "Arity"] := Length[p["Types"]]

PortProp[p_, "Label"] := ReplaceAll[
    ReplaceAll[p["PortTree"], q_Port :> If[q["NeutralQ"], OverTilde, Identity] @ q["HoldExpression"]],
    {
        CircleTimes[x_, y_] /; x === SuperStar[y] :> OverHat[x],
        CircleTimes[x_, y_] /; SuperStar[x] === y :> OverHat[y],
        (CircleTimes | CirclePlus)[x_] :> x,
        CircleTimes[] -> "1",
        CirclePlus[] -> "0"
    }
]

PortProp[p_, "View"] := With[{
    label = p["Label"], type = p["Type"]
},
    If[type === $DefaultPortType, Defer[Port[label]], Defer[Port[label, type]]] //. HoldForm[x_] :> x
]

PortProp[p_, "Dual"] := PortDual[p]

PortProp[p_, "Minus"] := PortMinus[p]

PortProp[p_, "Neutral"] := PortNeutral[p]

PortProp[p_, "Reverse"] := Port[reverseTree[p["PortTree"]], reverseTree[p["Type"]]]


(* internal properties *)

PortProp[p_, "DualQ"] := MatchQ[p["HoldExpression"], HoldForm[_PortDual]]

PortProp[p_, "MinusQ"] := MatchQ[p["HoldExpression"], HoldForm[_PortMinus]]

PortProp[p_, "ProductQ"] := MatchQ[p["HoldExpression"], HoldForm[_PortProduct]]

PortProp[p_, "SumQ"] := MatchQ[p["HoldExpression"], HoldForm[_PortSum]]

PortProp[p_, "PowerQ"] := MatchQ[p["HoldExpression"], HoldForm[_PortPower]]

PortProp[p_, "PortTree" | "Decompose"] :=
    Replace[p["HoldExpression"], {
        HoldForm[PortDual[q_]] :> SuperStar[Port[Unevaluated[q], "NeutralQ" -> p["NeutralQ"]]["PortTree"]],
        HoldForm[PortMinus[q_]] :> OverBar[Port[Unevaluated[q], "NeutralQ" -> p["NeutralQ"]]["PortTree"]],
        HoldForm[PortProduct[ps___]] :> CircleTimes @@ Through[{ps}["PortTree"]],
        HoldForm[PortSum[ps___]] :> CirclePlus @@ Through[{ps}["PortTree"]],
        HoldForm[PortPower[x_, y_]] :> Superscript[x["PortTree"], y["PortTree"]],
        _ :> p
    }]

PortProp[p_, "ProductList", lvl : (_Integer ? NonNegative) | Infinity : Infinity] := If[lvl > 0, Replace[p["HoldExpression"], {
    HoldForm[PortProduct[ps___]] :> Catenate[Through[{ps}["ProductList", lvl - 1]]],
    HoldForm[PortPower[x_, y_]] :> Join[PortDual /@ x["ProductList", lvl - 1], y["ProductList", lvl - 1]],
    HoldForm[PortDual[(PortProduct | PortPower)[ps___]]] :> Through[Catenate[Through[{ps}["ProductList", lvl - 1]]]["Dual"]],
    _ :> {p}
}],
    {p}
]

PortProp[p_, "SumList", lvl : (_Integer ? NonNegative) | Infinity : Infinity] :=  If[lvl > 0, Replace[p["HoldExpression"], {
    HoldForm[PortSum[ps___]] :> PortSum @@@ Through[{ps}["SumList", lvl - 1]],
    HoldForm[PortMinus[PortSum[ps___]]] :> Through[(PortSum @@@ Through[{ps}["SumList", lvl - 1]])["Minus"]],
    _ :> {p}
}],
    {p}
]

PortProp[p_, "Apply", f_] := p["PortTree"] /. port_Port :> f[port]


PortProp[_, prop_, ___] := Missing[prop]



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

PortMinus /: MakeBoxes[PortMinus[p_], form_] := With[{boxes = ToBoxes[OverBar[p], form]}, InterpretationBox[boxes, PortMinus[p]]]

PortProduct /: MakeBoxes[PortProduct[ps___], form_] := With[{boxes = ToBoxes[CircleTimes[ps], form]}, InterpretationBox[boxes, PortProduct[ps]]]

PortSum /: MakeBoxes[PortSum[ps___], form_] := With[{boxes = ToBoxes[CirclePlus[ps], form]}, InterpretationBox[boxes, PortSum[ps]]]

PortPower /: MakeBoxes[PortPower[p_, q_], form_] := With[{boxes = ToBoxes[Superscript[p, q], form]}, InterpretationBox[boxes, PortPower[p, q]]]



End[];

EndPackage[];