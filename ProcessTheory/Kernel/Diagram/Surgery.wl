BeginPackage["ProcessTheory`Diagram`Surgery`", {"ProcessTheory`Diagram`", "ProcessTheory`Utilities`"}];

DiagramPattern
DiagramCases


Begin["ProcessTheory`Diagram`Surgery`Private`"];

DiagramSubdiagrams[d_Diagram] := Prepend[Catenate[DiagramSubdiagrams /@ d["SubDiagrams"]], d]

DiagramPattern[expr_] := DiagramPattern[expr, {}, {}]
DiagramPattern[expr_, out_] := DiagramPattern[expr, {}, out]
DiagramPattern[expr_, in : Except[_List], out_, opts___] := DiagramPattern[expr, {in}, out, opts]
DiagramPattern[expr_, in_, out : Except[_List], opts___] := DiagramPattern[expr, in, {out}, opts]
DiagramPattern[expr_, in_, out_] := DiagramPattern[expr, in, out, ___]

DiagramCases[d_Diagram, patt_] :=
	Cases[
		Hold[Evaluate[{#["HoldExpression"], Through[#["InputPorts"]["Name"]], Through[#["OutputPorts"]["Name"]], #["DiagramOptions"], #} & /@ DiagramSubdiagrams[d]]] /. HoldForm[x_] :> x,
		patt /. {
			HoldPattern[DiagramPattern[expr_, in_, out_, opts___]] :> {expr, in, out, {opts}, diag_} :> diag,
			HoldPattern[(head : Rule | RuleDelayed)[DiagramPattern[expr_, in_List, out_List, opts___], rhs_]] :> head[{expr, in, out, {opts}, _}, rhs]
		},
		{2}
	]

End[]

EndPackage[]