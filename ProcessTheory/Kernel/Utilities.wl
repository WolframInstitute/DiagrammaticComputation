BeginPackage["ProcessTheory`Utilities`"];


fillAutomatic
reverseTree


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


End[];

EndPackage[];