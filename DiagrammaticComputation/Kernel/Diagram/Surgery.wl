BeginPackage["Wolfram`DiagrammaticComputation`Diagram`Surgery`", {"Wolfram`DiagrammaticComputation`Diagram`", "Wolfram`DiagrammaticComputation`Utilities`"}];

DiagramSubdiagrams
DiagramPositions
DiagramPattern
DiagramCases
DiagramPosition
DiagramMap
DiagramMapAt


Begin["Wolfram`DiagrammaticComputation`Diagram`Surgery`Private`"];


DiagramPositions[d_Diagram, lvl : (_Integer ? NonNegative) | Infinity : Infinity] := With[{subDiagrams = d["SubDiagrams"]},
    If[ lvl > 0 && Length[subDiagrams] > 0,
        Join @@ Prepend[<|{} -> d|>] @ MapIndexed[{diag, idx} |-> KeyMap[Join[idx, #] &, DiagramPositions[diag, lvl - 1]], subDiagrams],
        <|{} -> d|>
    ]
]

DiagramPositions[d_Diagram, levels : {_Integer, _Integer}] := With[
    {pos = DiagramPositions[d, If[AllTrue[levels, NonNegative], Max[levels], Infinity]]},
    {maxLevel = Max[Length /@ Keys[pos]]},
    {bounds = If[# < 0, Max[maxLevel + # + 1, 0], #] & /@ levels}
    ,
    KeySelect[pos, Between[Length[#], bounds] &]
]

DiagramPositions[d_Diagram, {lvl_Integer}] := DiagramPositions[d, {lvl, lvl}]

DiagramPositions[d_Diagram, lvl_Integer] := DiagramPositions[d, {1, lvl}]


DiagramSubdiagrams[d_Diagram, lvl : _Integer | {_Integer} | {_Integer, _Integer} | Infinity : Infinity] := Values @ DiagramPositions[d, lvl]


DiagramPattern[expr_] := DiagramPattern[expr, {___}, {___}]
DiagramPattern[expr_, out_] := DiagramPattern[expr, {___}, out]
DiagramPattern[expr_, in : Except[_List], out_, opts___] := DiagramPattern[expr, {in}, out, opts]
DiagramPattern[expr_, in_, out : Except[_List], opts___] := DiagramPattern[expr, in, {out}, opts]
DiagramPattern[expr_, in_, out_] := DiagramPattern[expr, in, out, ___]

DiagramCases[d_Diagram, patt_] :=
	Cases[
		Hold[Evaluate[{#["HoldExpression"], Through[#["InputPorts"]["Name"]], Through[#["OutputPorts"]["Name"]], #["DiagramOptions"], #} & /@ DiagramSubdiagrams[d]]] /. HoldForm[x_] :> x,
		Replace[patt, {
			HoldPattern[DiagramPattern[expr_, in_, out_, opts___]] :> {expr, in, out, {opts}, diag_} :> diag,
			HoldPattern[(head : Rule | RuleDelayed)[DiagramPattern[expr_, in_List, out_List, opts___], rhs_]] :> head[{expr, in, out, {opts}, _}, rhs],
            HoldPattern[(head : Rule | RuleDelayed)[lhs_, rhs_]] :> head[{lhs, __}, rhs],
            _ :> {patt, ___, diag_} :> diag
		}],
		{2}
	]

DiagramCases[d_Diagram] := DiagramCases[d, _]


DiagramPosition[d_Diagram, patt_, lvl : (_Integer ? NonNegative) | Infinity : Infinity] :=
	Keys @ Select[
		DiagramPositions[d, lvl],
		MatchQ[
            Replace[patt, {
                HoldPattern[DiagramPattern[expr_, in_, out_, opts___]] :> HoldPattern[diag_Diagram /;
                    MatchQ[Hold[Evaluate[{diag["HoldExpression"], Through[diag["InputPorts"]["Name"]], Through[diag["OutputPorts"]["Name"]], diag["DiagramOptions"]}]] /. HoldForm[x_] :> x, Hold[{expr, in, out, {opts}}]]
                ]
		    }]
        ]
	]

DiagramPosition[d_Diagram] := DiagramPosition[d, _Diagram]


DiagramMap[f_, d_Diagram, lvl : (_Integer ? NonNegative) | Infinity : Infinity] := Enclose @ ConfirmBy[
    If[ lvl > 0,
        Replace[d["HoldExpression"], {
            _[(head : $DiagramHeadPattern)[ds___]] :> Diagram[d, "Expression" :> head[##] & @@ Map[DiagramMap[f, #, lvl - 1] &, {ds}]],
            _ :> Diagram[f[d]]
        }]
        ,
        Diagram[f[d]]
    ],
    DiagramQ
]


DiagramMapAt[f_, d_Diagram, pos : {{___Integer} ...}, curPos_ : {}] := Enclose @ 
    ConfirmBy[
        If[ d["Head"] === Null,
            If[MemberQ[pos, curPos], Diagram[f[d, curPos]], d],
            If[MemberQ[pos, curPos], Diagram[f[#, curPos]] &, # &] @ Diagram[d["Head"] @@ MapIndexed[DiagramMapAt[f, #1, pos, Join[curPos, #2]] &, d["SubDiagrams"]], d["DiagramOptions"]]
        ],
        DiagramQ
    ]

DiagramMapAt[f_, d_Diagram, pos : {___Integer}] := DiagramMapAt[f, d, {pos}]


End[]

EndPackage[]