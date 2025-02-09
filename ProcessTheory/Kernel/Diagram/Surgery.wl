BeginPackage["ProcessTheory`Diagram`Surgery`", {"ProcessTheory`Diagram`", "ProcessTheory`Utilities`"}];

DiagramSubdiagrams
DiagramPositions
DiagramPattern
DiagramCases
DiagramPosition
DiagramMap


Begin["ProcessTheory`Diagram`Surgery`Private`"];

DiagramSubdiagrams[d_Diagram] := Prepend[Catenate[DiagramSubdiagrams /@ d["SubDiagrams"]], d]

DiagramPositions[d_Diagram, lvl : (_Integer ? NonNegative) | Infinity : Infinity] := With[{subDiagrams = d["SubDiagrams"]},
    If[ lvl > 0 && Length[subDiagrams] > 0,
        Join @@ Prepend[<|{} -> d|>] @ MapIndexed[{diag, idx} |-> KeyMap[Join[idx, #] &, DiagramPositions[diag, lvl - 1]], subDiagrams],
        <|{} -> d|>
    ]
]

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


DiagramMap[f_, d_Diagram, lvl : (_Integer ? NonNegative) | Infinity : Infinity] := If[lvl > 0,
    Replace[d["HoldExpression"], {
        _[(head : $DiagramHeadPattern)[ds___]] :> Diagram[d, "Expression" :> head[##] & @@ Map[DiagramMap[f, #, lvl - 1] &, {ds}]],
        _ :> Diagram[f @@ d["HoldExpression"]]
    }]
    ,
    Diagram[f[d]]
]


End[]

EndPackage[]