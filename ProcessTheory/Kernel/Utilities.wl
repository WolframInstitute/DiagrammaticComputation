BeginPackage["ProcessTheory`Utilities`", {"ProcessTheory`Port`"}];


fillAutomatic
reverseTree

idDiagram
piDiagram

tag


Begin["ProcessTheory`Utilities`Private`"];


fillAutomatic[expr_, arities_List, def_ : Automatic] := MapThread[
    PadRight[Replace[Replace[#1, x : Except[_List] :> ConstantArray[x, #2]], Automatic -> def, 1], #2, {def}] &,
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

idDiagram[xs_List] := With[{ports = makePorts[xs]},
    Diagram["1", ports, ports, "Shape" -> "CrossWires", "ShowLabel" -> False]
]
    
piDiagram[outputs_List, inputs_List] := Diagram["\[Pi]", makePorts[outputs], makePorts[inputs], "Shape" -> "CrossWires", "ShowLabel" -> False]


tag[expr_, tag_] := Replace[expr, {
    HoldForm[Interpretation[x_, y_]] | Interpretation[x_, y_] :> Interpretation[x, y -> tag],
    HoldForm[x_] | x_ :> Interpretation[x, tag]
}]


End[];

EndPackage[];