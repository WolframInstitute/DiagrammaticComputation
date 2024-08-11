BeginPackage["ProcessTheory`Utilities`"];


reverseTree


Begin["ProcessTheory`Utilities`Private`"];

reverseTree[tree_] := Replace[Unevaluated[tree], {
    SuperStar[x_] :> SuperStar[reverseTree[x]],
    (head : CircleTimes | CirclePlus)[xs___] :> head @@ Reverse[reverseTree /@ {xs}]
}]


End[];

EndPackage[];