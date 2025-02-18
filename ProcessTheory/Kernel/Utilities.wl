BeginPackage["ProcessTheory`Utilities`"];


fillAutomatic
reverseTree

makePorts

tag

collectPorts
collectPortsListBy

inheritedQ

FirstPositions
FirstPositionsWithMissing


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


tag[expr_, t_] := Replace[expr, {
    HoldForm[Interpretation[x_, y_]] | Interpretation[x_, y_] :> Interpretation[x, y -> t],
    HoldForm[x_] | x_ :> Interpretation[x, t]
}]


collectPorts[ports_List] := If[ports === {}, {},
    Fold[
        {
            Join[#2[[1]], DeleteElements[#1[[1]], 1 -> #2[[2]]]],
            Join[DeleteElements[#2[[2]], 1 -> #1[[1]]], #1[[2]]]
        } &,
        ports
    ]
]

collectPortsListBy[ports_List, f_] := If[ports === {}, {},
    FoldList[List /* Replace[{{out1_, in1_}, {out2_, in2_}} :>
        With[{fout1 = f /@ out1, fin2 = f /@ in2},
            {
                Join[out2, Delete[out1, FirstPositions[fout1, fin2]]],
                Join[Delete[in2, FirstPositions[fin2, fout1]], in1]
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