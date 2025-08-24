BeginPackage["Wolfram`DiagrammaticComputation`Utilities`"];


fillAutomatic
reverseTree

getName
tag
untag
InterpretationForm

collectPorts
collectPortsListBy

inheritedQ

FirstPositions
FirstPositionsWithMissing


Begin["Wolfram`DiagrammaticComputation`Utilities`Private`"];


fillAutomatic[expr_, arities_List, def_ : Inherited] := MapThread[
    {list, arity} |-> 
        Replace[
            Replace[Replace[list, x : Except[_List] :> ConstantArray[x, arity]], Automatic -> def, 1] //
                PadRight[#, arity, {Replace[def, Inherited :> SelectFirst[Reverse[#], # =!= Inherited &, Automatic]]}] &,
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

getName[expr_] := Replace[Unevaluated[expr], {
    SuperStar[x_] :> x
}]

tag[expr_, t_] := Replace[Unevaluated[expr], {
    HoldForm[Interpretation[Interpretation[x_, y_], z_]] | Interpretation[Interpretation[x_, y_], z_] :> tag[HoldForm[Interpretation[x, y -> z]], t],
    HoldForm[Interpretation[x_, y_]] | Interpretation[x_, y_] :> Interpretation[x, y -> t],
    HoldForm[SuperStar[x_]] | SuperStar[x_] :> SuperStar[tag[Unevaluated[x], t]],
    HoldForm[x_] | x_ :> Interpretation[x, t]
}]

untag[expr_] := Replace[Unevaluated[expr], {
    HoldForm[Interpretation[x_, tag_ -> _]] :> HoldForm[Interpretation[x, tag]],
    HoldForm[SuperStar[Interpretation[x_, tag_ -> _]]] :> HoldForm[SuperStar[Interpretation[x, tag]]],
    HoldForm[Interpretation[x_, _]] :> HoldForm[x],
    HoldForm[SuperStar[Interpretation[x_, _]]] :> HoldForm[SuperStar[x]]
}]


InterpretationForm[Interpretation[i_Interpretation, _]] := InterpretationForm[i]
InterpretationForm[HoldForm[x_]] := HoldForm[Evaluate[InterpretationForm[Unevaluated[x]]]]
InterpretationForm[x_] := x


collectPorts[ports_List] := If[ports === {}, {},
    Fold[
        {
            Join[DeleteElements[#1[[1]], 1 -> #2[[2]]], #2[[1]]],
            Join[#1[[2]], DeleteElements[#2[[2]], 1 -> #1[[1]]]]
        } &,
        ports
    ]
]

collectPortsListBy[ports_List, f_] := If[ports === {}, {},
    FoldList[List /* Replace[{{out1_, in1_}, {out2_, in2_}} :>
        With[{fout1 = f /@ out1, fin2 = f /@ in2},
            {
                Join[Delete[out1, FirstPositions[fout1, fin2]], out2],
                Join[in1, Delete[in2, FirstPositions[fin2, fout1]]]
            }
        ]
    ],
        ports
    ]
]


inheritedQ = MatchQ[Automatic | Inherited]


(* WFR candidates *)

FirstPositions[list1_ ? ListQ, list2_ ? ListQ] := Block[{list = list2, result = {}, i = 1, pos},
    Do[
        If[list === {}, Break[]];
        pos = FirstPosition[list, value, None, {1}, Heads -> False];
        If[pos =!= None, AppendTo[result, {i}]; list //= Delete[pos]];
        i++
        ,
        {value, list1}
    ];
    result
]

FirstPositionsWithMissing[list1_ ? ListQ, list2_ ? ListQ] := Block[{
    list = list2, result = ConstantArray[Missing["NotFound"], Length[list2]], idx = Range[Length[list2]], i = 1, pos
},
    Do[
        If[list === {}, Break[]];
        pos = FirstPosition[list, value, None, {1}, Heads -> False];
        If[pos =!= None, result[[Extract[idx, pos]]] = {i}; list //= Delete[pos]; idx //= Delete[pos]];
        i++
        ,
        {value, list1}
    ];
    result
]


End[];

EndPackage[];