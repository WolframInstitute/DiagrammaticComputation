BeginPackage["Wolfram`DiagrammaticComputation`Utilities`"];


fillAutomatic
reverseTree
reverseEdge

getName
tag
untag
InterpretationForm

collectPorts
collectPortsListBy

inheritedQ

FirstPositions
FirstPositionsWithMissing

SmoothGraphicsCurves

GridFoliation


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

reverseEdge[DirectedEdge[a_, b_, t_]] := DirectedEdge[b, a, Reverse[t]]

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
        With[{fout1 = f /@ out1, fin2 = f /@ in2}, {pos1 = FirstPositions[fout1, fin2], pos2 = FirstPositions[fin2, fout1]},
            {
                Join[Delete[out1, pos1], out2],
                Join[in1, Delete[in2, pos2]]
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


ConnectCurves[curves_, eps_ : 1*^-4] := Block[{g},
    g = RelationGraph[EuclideanDistance[#1[[-1]], #2[[1]]] < eps &, curves];
  
    Catenate[
        With[{sg = #, in = Pick[VertexList[#], VertexInDegree[#], 0], out = Pick[VertexList[#], VertexOutDegree[#], 0]}, 
            Apply[Join] @* MapAt[Rest, {2 ;;}] @* Map[Split /* Map[First]] /@ 
                Catenate @ Outer[First[FindPath[sg, ##], VertexList[sg]] &, in, out, 1]
        ] & /@ WeaklyConnectedGraphComponents[g]
    ]
]

SmoothPoints[points_, n : _ ? NumericQ : .5, m : _Integer?Positive : 5] /; 0 <= n <= 1 := With[
    {len = Length[points]}, {k = Round[n * (len - 2) + 1]},
    {if = Interpolation[Thread[{Subdivide[len - k], Prepend[First[points]] @ Append[Last[points]] @ MovingAverage[points, k][[2 ;; -2]]}], InterpolationOrder -> 2]},
    BSplineCurve[if /@ Subdivide[m]]
]

Options[SmoothGraphicsCurves] = Join[{
    "WireStyle" -> Directive[CapForm["Round"], AbsoluteThickness[1.5], Arrowheads[{{Medium, .6, Graphics[Polygon[{{-1/2, 1/4}, {1/2, 0}, {-1/2, -1/4}}]]}}]]},
    Options[Graphics]
]

SmoothGraphicsCurves[g_, n : _ ? NumericQ : .1, m : _Integer ? Positive : 4, opts : OptionsPattern[]] /; 0 <= n <= 1 := Block[{h, curves},
    curves = First[Reap[h = g /. BSplineCurve[ps_] :> (Sow[ps]; {})][[2]], {}];
    Show[Graphics[{OptionValue["WireStyle"], Arrow @ SmoothPoints[#, n, m]} & /@ ConnectCurves[curves]], h, FilterRules[{opts}, Options[Graphics]]]
]


GridFoliation[g_Graph] /; DirectedGraphQ[g] && AcyclicGraphQ[g] := With[{sources = Pick[VertexList[g], VertexInDegree[g], 0]},
	Switch[Length[sources],
		0,
			Identity,
		1,
			RightComposition[First[sources], GridFoliation[VertexDelete[g, sources]]],
		_,
			Block[{cones = VertexOutComponent[g, #] & /@ sources, layer},
				layer = Map[First[WeaklyConnectedGraphComponents[Subgraph[g, #], #]] &, UniqueElements[cones]];
				RightComposition[
					(If[Length[layer] == 1, First[#], CircleTimes @@ #] &) @ (OptimalFoliation /@ layer),
					GridFoliation[Subgraph[g, Complement[Union @@ cones, Union @@ VertexList /@ layer]]]
				]
			]
	]
]


End[];

EndPackage[];