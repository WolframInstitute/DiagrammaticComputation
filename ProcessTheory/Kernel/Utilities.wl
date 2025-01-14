BeginPackage["ProcessTheory`Utilities`"];


fillAutomatic
reverseTree

idDiagram
piDiagram

tag


Begin["ProcessTheory`Utilities`Private`"];


fillAutomatic[expr_, arities_List, def_ : Inherited] := MapThread[
    {list, arity} |-> 
        Replace[
            Replace[Replace[list, x : Except[_List] :> ConstantArray[x, arity]], Automatic -> def, 1] //
                PadRight[#, arity, {Replace[def, Inherited -> SelectFirst[Reverse[#], # =!= Inherited &, Automatic]]}] &,
            Inherited -> Automatic,
            1
        ],
    {
        PadRight[
            Replace[expr, x : Except[_List] :> ConstantArray[x, Length[arities]]],
            Length[arities],
            {{def}}
        ],
        arities
    }
]


reverseTree[tree_] := Replace[Unevaluated[tree], {
    SuperStar[x_] :> SuperStar[reverseTree[x]],
    (head : CircleTimes | CirclePlus)[xs___] :> head @@ Reverse[reverseTree /@ {xs}]
}]


makePorts[xs_List] := Function[Null, Port[Unevaluated[##]], HoldAll] @@@ Flatten @* HoldForm /@ Replace[xs, SuperStar[HoldForm[x_]] :> HoldForm[SuperStar[x]], 1]

idDiagram[xs_List, opts___] := With[{ports = makePorts[xs]},
    Diagram[Interpretation["1", Identity], ports, ports, opts, "Shape" -> "Wires"[Thread[{Range[Length[xs]], Length[xs] + Range[Length[xs]]}]], "ShowLabel" -> False, "PortFunction" -> (#["HoldExpression"] &)]
]
    
piDiagram[inputs_List, outputs_List, opts___] := With[{len = Min[Length[inputs], Length[outputs]]}, {perm = FindPermutation[Take[inputs, len], Take[outputs, len]]},
    Diagram[Interpretation["\[Pi]", perm], makePorts[inputs], makePorts[outputs], opts, "Shape" -> "Wires"[Thread[{Range[len], Length[inputs] + Permute[Range[len], InversePermutation[perm]]}]], "ShowLabel" -> False]
]

tag[expr_, tag_] := Replace[expr, {
    HoldForm[Interpretation[x_, y_]] | Interpretation[x_, y_] :> Interpretation[x, y -> tag],
    HoldForm[x_] | x_ :> Interpretation[x, tag]
}]


End[];

EndPackage[];