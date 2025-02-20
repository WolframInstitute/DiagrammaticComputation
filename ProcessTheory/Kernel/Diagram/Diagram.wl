BeginPackage["ProcessTheory`Diagram`", {"ProcessTheory`Utilities`", "ProcessTheory`Port`", "ProcessTheory`Diagram`Grid`"}];

Diagram
DiagramQ

DiagramDual
DiagramFlip
DiagramReverse

DiagramProduct
DiagramSum
DiagramComposition
DiagramNetwork
SingletonDiagram
IdentityDiagram
PermutationDiagram

DiagramGraphics
DiagramsFreePorts
DiagramsPortGraph
DiagramsGraph
DiagramsNetGraph

DiagramGraphSimplify
SimplifyDiagram

DiagramSplit
DiagramPermute

DiagramTensor
TensorDiagram
DiagramFunction

$DiagramHeadPattern
$DiagramDefaultGraphics


Begin["ProcessTheory`Diagram`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Diagram::usage = "Diagram[expr] represents a symbolic diagram with input and output ports"

Options[Diagram] := Sort @ DeleteDuplicatesBy[First] @ Join[Options[DiagramGraphics], Options[DiagramGrid], Options[DiagramsNetGraph]];

$DiagramHiddenOptions = {"Expression" -> None, "InputPorts" -> {}, "OutputPorts" -> {}, "DiagramOptions" -> {}};

$DiagramProperties = Sort @ {
    "Properties", "HoldExpression", "ProductQ", "SumQ", "CompositionQ", "NetworkQ", "SubDiagrams",
    "Ports", "PortArrows", "Arity", "FlattenOutputs", "FlattenInputs", "Flatten", "View", "Name", "Tensor", "Function", "Shape",
    "Diagram", "PortGraph", "Graph", "NetGraph", "Grid"
}

$DefaultPortFunction = Function[Replace[HoldForm[Evaluate[#["Apply", #["HoldName"] &]]], HoldForm[x_] :> x, Infinity]]

$DiagramDefaultGraphics = If[#["SingletonNodeQ"], #["Graphics"], #["Grid"]] &


(* ::Subsection:: *)
(* Validation *)

diagramQ[HoldPattern[Diagram[data_Association]]] := MatchQ[data, KeyValuePattern[{_["Expression", _], "OutputPorts" -> {___Port ? PortQ}, "InputPorts" -> {___Port ? PortQ}, "DiagramOptions" -> OptionsPattern[]}]]

diagramQ[___] := False


x_Diagram /; System`Private`HoldNotValidQ[x] && diagramQ[Unevaluated[x]] := (System`Private`HoldSetValid[x]; System`Private`HoldSetNoEntry[x])

DiagramQ[x_Diagram] := System`Private`HoldValidQ[x]

DiagramQ[___] := False


(* ::Subsection:: *)
(* Constructors *)

$DiagramGrid = _SuperStar | _OverBar | _OverTilde | _CircleTimes | _CirclePlus | _CircleDot | _List

Diagram[SuperStar[d_], opts : OptionsPattern[]] := DiagramDual[Diagram[d], opts]

Diagram[OverBar[d_], opts : OptionsPattern[]] := DiagramFlip[Diagram[d], opts]

Diagram[OverTilde[d_], opts : OptionsPattern[]] := DiagramReverse[Diagram[d], opts]

Diagram[CircleTimes[ds___], opts : OptionsPattern[]] := DiagramProduct[##, opts] & @@ (Diagram /@ {ds})

Diagram[CirclePlus[ds___], opts : OptionsPattern[]] := DiagramSum[##, opts] & @@ (Diagram /@ {ds})

Diagram[(CircleDot | Composition)[ds___], opts : OptionsPattern[]] := DiagramComposition[##, opts] & @@ (Diagram /@ {ds})

Diagram[HoldPattern[RightComposition[ds___]], opts : OptionsPattern[]] := DiagramComposition[##, opts] & @@ Reverse[Diagram /@ {ds}]

Diagram["Identity"[args___], opts : OptionsPattern[]] := IdentityDiagram[args, opts]

Diagram["Permutation"[args___], opts : OptionsPattern[]] := PermutationDiagram[args, opts]

Diagram[ds : Except[OptionsPattern[], _List], opts : OptionsPattern[]] := DiagramNetwork[##, opts] & @@ (Diagram /@ ds)

Diagram[grid : $DiagramGrid -> _, opts : OptionsPattern[]] := Diagram[grid, opts]


(* overwrite ports *)

inheritPorts[Inherited | Automatic, oldPorts_List] := oldPorts

inheritPorts[ports_List, oldPorts_List] := DeleteCases[Inherited] @ MapThread[If[inheritedQ[#1], #2, #1] &, {ports, PadRight[oldPorts, Length[ports], Inherited]}]

inheritPorts[port_, oldPorts_List] := inheritPorts[{port}, oldPorts]


Diagram[d_ ? DiagramQ, {}, {}, opts : OptionsPattern[]] := Diagram[Unevaluated @@ d["HoldExpression"], {}, {}, opts, d["DiagramOptions"]]

Diagram[d_ ? DiagramQ, inputs : Except[OptionsPattern[]], {}, opts : OptionsPattern[]] := Diagram[Unevaluated @@ d["HoldExpression"], inheritPorts[inputs, PortDual /@ d["InputPorts"]], {}, opts, d["DiagramOptions"]]

Diagram[d_ ? DiagramQ, {}, opts : OptionsPattern[]] := Diagram[d, Inherited, {}, opts]

Diagram[d_ ? DiagramQ, output : Except[OptionsPattern[]], opts : OptionsPattern[]] := Diagram[d, Inherited, output, opts]

Diagram[d_ ? DiagramQ, inputs_, outputs : Except[OptionsPattern[]], opts : OptionsPattern[]] :=
    Diagram[Unevaluated @@ d["HoldExpression"],
        inheritPorts[inputs, PortDual /@ d["InputPorts"]],
        inheritPorts[outputs, d["OutputPorts"]],
        opts, d["DiagramOptions"]
    ]

Diagram[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[d, Inherited, Inherited, opts]


(* default constructor *)

Diagram[expr : {} | Except[_Association | _Diagram | OptionsPattern[]],
    inputs_List,
    outputs_List,
    opts : OptionsPattern[]
] :=
    Diagram[    
        FilterRules[{
            opts,
            "Expression" :> expr,
            "OutputPorts" -> Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[outputs]],
            "InputPorts" -> Comap[Map[Function[p, Port[Unevaluated[p]], HoldFirst], Unevaluated[inputs]], "Dual"]
        },
            Join[Options[Diagram], $DiagramHiddenOptions, Options[DiagramGraphics], Options[DiagramsNetGraph], Options[DiagramGrid]]
        ]
    ]

Diagram[expr_, inputs_List, output : Except[_List | OptionsPattern[]], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], Unevaluated[inputs], Unevaluated[{output}], opts]

Diagram[expr_, input : Except[_List], outputs_List, opts : OptionsPattern[]] := Diagram[Unevaluated[expr], Unevaluated[{input}], Unevaluated[outputs], opts]

Diagram[expr_, input : Except[_List], output : Except[_List | OptionsPattern[]], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], Unevaluated[{input}], Unevaluated[{output}], opts]

Diagram[expr_, output : Except[_List | OptionsPattern[]], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], {}, Unevaluated[{output}], opts]

Diagram[expr_, outputs : Except[OptionsPattern[], _List], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], {}, Unevaluated[outputs], opts]

Diagram[expr : Except[_Association | _Diagram | OptionsPattern[]], opts : OptionsPattern[]] := Diagram[Unevaluated[expr], {}, {}, opts]


(* merge options *)

inheritExpresion[expr_, deps_List, def_ : Automatic] := With[{pos = Position[expr, Inherited]},
    ReplacePart[expr, DeleteCases[Catenate[(dep |->
        # -> If[# =!= {} && (Extract[expr, #] === Extract[dep, #] &[Append[Most[#], 0]]), ResourceFunction["LookupPart"][dep, Sequence @@ #, Automatic], Automatic] & /@ pos) /@ deps], _ -> Inherited]] /. Inherited -> def
]


mergeOptions[opts_List] := Normal @ GroupBy[opts, First,
    If[ MatchQ[#[[1, 1]], "PortArrows" | "PortLabels"],
        Map[
            With[{len = Max[Length /@ #, 1]}, inheritExpresion[#1, {##2}] & @@ (PadRight[#, len, #] & /@ #)] &,
            Thread[Developer`ToList /@ PadRight[Developer`ToList[#], 2, #] & /@ #[[All, 2]]]
        ]
        ,
        #[[1, 2]]
    ] &
]

Diagram[opts : OptionsPattern[]] := Diagram[KeySort[<|
    DeleteDuplicatesBy[First] @ FilterRules[
        {"DiagramOptions" -> mergeOptions @ FilterRules[{opts, Values[FilterRules[{opts}, "DiagramOptions"]]}, Options[Diagram]], opts, $DiagramHiddenOptions},
        Join[$DiagramHiddenOptions]
    ]|>
]]

Diagram[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[Replace[Normal[Merge[{opts, d["Data"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* ::Subsubsection:: *)
(* Unary ops *)

Options[DiagramDual] := Join[{"Singleton" -> True}, Options[Diagram]]

DiagramDual[d_ ? DiagramQ, opts : OptionsPattern[]] := If[d["DualQ"], First[d["SubDiagrams"]], Diagram[
    d,
    opts,
    Replace[d["HoldExpression"], {
        _[(head : (Diagram | DiagramSum | DiagramComposition | DiagramProduct | DiagramNetwork | DiagramReverse | DiagramFlip))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramDual[#, opts] & /@ {ds})),
        _[DiagramDual[x_]] :> "Expression" :> x,
        _ :> If[TrueQ[OptionValue["Singleton"]], "Expression" :> DiagramDual[d], Function[Null, "Expression" :> #, HoldAll] @@ d["HoldExpression"]]
    }],
    "OutputPorts" -> Through[d["OutputPorts"]["Dual"]],
    "InputPorts" -> Through[d["InputPorts"]["Dual"]],
    "DiagramOptions" -> d["DiagramOptions"]
]
]

Options[DiagramFlip] := Join[{"Singleton" -> True}, Options[Diagram]]

DiagramFlip[d_ ? DiagramQ, opts : OptionsPattern[]] := If[d["FlipQ"], First[d["SubDiagrams"]], Diagram[
    d,
    opts,
    Replace[d["HoldExpression"], {
        _[DiagramComposition[ds___]] :> ("Expression" :> DiagramComposition[##] & @@ Reverse[DiagramFlip[#, opts] & /@ {ds}]),
        _[(head : (Diagram | DiagramSum | DiagramProduct | DiagramNetwork | DiagramReverse | DiagramDual))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramFlip[#, opts] & /@ {ds})),
        _[DiagramFlip[x_]] :> "Expression" :> x,
        _ :> If[TrueQ[OptionValue["Singleton"]], "Expression" :> DiagramFlip[d], Function[Null, "Expression" :> #, HoldAll] @@ d["HoldExpression"]]
    }],
    "OutputPorts" -> d["InputPorts"],
    "InputPorts" -> d["OutputPorts"],
    "PortArrows" -> Reverse[fillAutomatic[d["OptionValue"["PortArrows"], opts], d["Arities"], True]],
    "PortLabels" -> Reverse[fillAutomatic[d["OptionValue"["PortLabels"], opts], d["Arities"], Automatic]],
    "DiagramOptions" -> d["DiagramOptions"]
]
]

Options[DiagramReverse] := Join[{"Singleton" -> True}, Options[Diagram]]

DiagramReverse[d_ ? DiagramQ, opts : OptionsPattern[]] := If[d["ReverseQ"], First[d["SubDiagrams"]], Diagram[
    d,
    opts,
    Replace[d["HoldExpression"], {
        _[DiagramProduct[ds___]] :> ("Expression" :> DiagramProduct[##] & @@ Reverse[DiagramReverse[#, opts] & /@ {ds}]),
        _[(head : (Diagram | DiagramSum | DiagramComposition | DiagramNetwork | DiagramFlip | DiagramDual))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramReverse[#, opts] & /@ {ds})),
        _[DiagramReverse[x_]] :> "Expression" :> x,
        _ :> If[TrueQ[OptionValue["Singleton"]], "Expression" :> DiagramReverse[d], Function[Null, "Expression" :> #, HoldAll] @@ d["HoldExpression"]]
    }],
    "OutputPorts" -> Reverse[Through[d["OutputPorts"]["Reverse"]]],
    "InputPorts" -> Reverse[Through[d["InputPorts"]["Reverse"]]],
    "PortArrows" -> (Reverse /@ fillAutomatic[d["OptionValue"["PortArrows"], opts], d["Arities"], True]),
    "PortLabels" -> (Reverse /@ fillAutomatic[d["OptionValue"["PortLabels"], opts], d["Arities"], Automatic]),
    "DiagramOptions" -> d["DiagramOptions"]
]
]


(* ::Subsubsection:: *)
(* Binary ops *)

(* sum *)


Options[DiagramSum] = Options[Diagram]

DiagramSum[d_Diagram, opts : OptionsPattern[]] := Diagram[d, opts]

DiagramSum[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{subDiagrams = If[#["SumQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}},
    Diagram[
        opts,
        "Expression" :> DiagramSum[##] & @@ subDiagrams,
        "OutputPorts" -> Replace[Through[{ds}["OutputPorts"]], {{} -> PortSum[], ps_ :> {PortSum @@ PortProduct @@@ ps}}],
        "InputPorts" -> Replace[Through[{ds}["InputPorts"]], {{} -> PortSum[]["Dual"], ps_ :> {PortDual[PortSum @@ PortDual /@ PortProduct @@@ ps]}}]
    ]
]

(* horizontal product *)

Options[DiagramProduct] = Options[Diagram]

DiagramProduct[d_Diagram, opts : OptionsPattern[]] := Diagram[d, opts]

DiagramProduct[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{subDiagrams = If[#["ProductQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}},
    Diagram[
        opts,
        "Expression" :> DiagramProduct[##] & @@ subDiagrams,
        "OutputPorts" -> Replace[Through[{ds}["OutputPorts"]], {{} -> PortProduct[], ps_ :> PortProduct @@ ps}, 1],
        "InputPorts" -> Replace[Through[{ds}["InputPorts"]], {{} -> PortProduct[]["Dual"], ps_ :> PortProduct @@ ps}, 1]
    ]
]

Options[SingletonDiagram] = Options[Diagram]

SingletonDiagram[diagram_Diagram, opts : OptionsPattern[]] := Diagram[diagram, "Expression" :> Diagram[diagram], opts]


Options[IdentityDiagram] = Options[PermutationDiagram] = Options[Diagram]

IdentityDiagram[xs_List, opts : OptionsPattern[]] := With[{ports = makePorts[xs]},
    Diagram[Interpretation["1", Identity], ports, ports, opts, "Shape" -> "Wires"[Thread[{Range[Length[xs]], Length[xs] + Range[Length[xs]]}]], "ShowLabel" -> False, "PortFunction" -> (#["HoldExpression"] &)]
]
    
PermutationDiagram[inputs_List -> outputs_List, ins_List -> outs_List, opts___] := Enclose @ With[
    {len = Min[Length[ins], Length[outs]]},
    {perm = ConfirmBy[FindPermutation[Take[ins, len], Take[outs, len]], PermutationCyclesQ]}
    ,
    PermutationDiagram[inputs, outputs, perm, opts, "Shape" -> "Wires"[Thread[{Range[len], Length[inputs] + Permute[Range[len], InversePermutation[perm]]}]]]
]

PermutationDiagram[outputs_List, opts___] := PermutationDiagram[Sort[outputs] -> outputs, opts]

PermutationDiagram[inputs_List -> outputs_List, opts___] := PermutationDiagram[inputs -> outputs, inputs -> outputs, opts]

PermutationDiagram[inputs_List -> outputs_List, perm_Cycles, opts___] := PermutationDiagram[inputs, outputs, perm, opts]

PermutationDiagram[inputs_List, perm_Cycles, opts___] := PermutationDiagram[inputs, Permute[inputs, perm], perm, opts]

PermutationDiagram[inputs_List, outputs_List, perm_Cycles, opts___] := With[{len = Min[Length[inputs], Length[outputs]]},
    Diagram[Interpretation["\[Pi]", perm], makePorts[inputs], makePorts[outputs], opts, "Shape" -> "Wires"[Thread[{Range[len], Length[inputs] + Permute[Range[len], InversePermutation[perm]]}]], "ShowLabel" -> False]
]

(* vertical product *)

Options[DiagramComposition] = Join[{"PortFunction" -> $DefaultPortFunction}, Options[Diagram]]

DiagramComposition[d_Diagram, opts : OptionsPattern[]] := Diagram[d, opts]

DiagramComposition[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{
    subDiagrams = If[#["CompositionQ"], Splice[#["SubDiagrams"]], #] & /@ {ds},
    func = OptionValue["PortFunction"]
}, {
    ports = Last @ collectPortsListBy[{#["OutputPorts"], PortDual /@ #["InputPorts"]} & /@ Through[Reverse[{ds}]["Flatten"]], func]
},
    Diagram[
        opts,
        "Expression" :> DiagramComposition[##] & @@ subDiagrams,
        "OutputPorts" -> ports[[1]],
        "InputPorts" -> PortDual /@ ports[[2]]
    ]
]


(* network of diagrams exposing free ports *)

Options[DiagramNetwork] := DeleteDuplicatesBy[First] @ Join[{"PortFunction" -> $DefaultPortFunction}, Options[Diagram], Options[DiagramsNetGraph]]
DiagramNetwork[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{
    subDiagrams = If[#["NetworkQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}
},
    Diagram[
        opts,
        "Expression" :> DiagramNetwork[ds],

        Sequence @@ Block[{graph = DiagramsGraph[subDiagrams, FilterRules[{opts}, Options[DiagramsGraph]]], diagrams = Through[subDiagrams["Flatten"]], freeWires, edges},
            freeWires = Cases[Pick[VertexList[graph], VertexDegree[graph], 1], _HoldForm];
            edges = EdgeList[graph];
            {
                "InputPorts" -> Cases[edges, DirectedEdge[Alternatives @@ freeWires, {diagramId_, 1, portId_}] :> diagrams[[diagramId]]["InputPorts"][[portId]]],
                "OutputPorts" -> Cases[edges, DirectedEdge[{diagramId_, 2, portId_}, Alternatives @@ freeWires] :> diagrams[[diagramId]]["OutputPorts"][[portId]]]
            }
        ]
    ]
]



(* ::Subsection:: *)
(* Properties *)


(* dispatch properties *)

(d_Diagram ? DiagramQ)[prop_, opts___] := DiagramProp[d, prop, opts] 


(* property definitions *)

DiagramProp[_, "Properties"] := Sort[$DiagramProperties]

DiagramProp[HoldPattern[Diagram[data_]], "Data"] := data

DiagramProp[d_, "InputPorts", neutralQ : _ ? BooleanQ : True] := If[neutralQ, d["Data"]["InputPorts"], Discard[d["Data"]["InputPorts"], #["NeutralQ"] &]]

DiagramProp[d_, "OutputPorts", neutralQ : _ ? BooleanQ : True] := If[neutralQ, d["Data"]["OutputPorts"], Discard[d["Data"]["OutputPorts"], #["NeutralQ"] &]]

DiagramProp[HoldPattern[Diagram[data_Association]], prop_] /; ! MemberQ[prop, $DiagramProperties] && KeyExistsQ[data, prop] := Lookup[data, prop]

DiagramProp[d_, "HoldExpression"] := Extract[d["Data"], "Expression", HoldForm]

collectUnaries[(head : DiagramDual | DiagramFlip | DiagramReverse)[d_Diagram]] := Prepend[collectUnaries[d["HoldExpression"]], head]
collectUnaries[HoldForm[d_]] := collectUnaries[Unevaluated[d]]
collectUnaries[_] := {}

DiagramProp[d_, "DualQ"] := OddQ[Count[collectUnaries[d["HoldExpression"]], DiagramDual]]

DiagramProp[d_, "FlipQ"] := OddQ[Count[collectUnaries[d["HoldExpression"]], DiagramFlip]]

DiagramProp[d_, "ReverseQ"] := OddQ[Count[collectUnaries[d["HoldExpression"]], DiagramReverse]]

DiagramProp[d_, "ProductQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramProduct]]

DiagramProp[d_, "SumQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramSum]]

DiagramProp[d_, "CompositionQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramComposition]]

DiagramProp[d_, "NetworkQ"] := MatchQ[d["HoldExpression"], HoldForm[_DiagramNetwork]]

$DiagramHeadPattern = Diagram | DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork

DiagramProp[d_, "NodeQ"] := ! MatchQ[d["Head"], $DiagramHeadPattern]

DiagramProp[d_, "SingletonNodeQ"] := d["NodeQ"] || MatchQ[d["HoldExpression"], HoldForm[Evaluate @ $DiagramHeadPattern[diag_Diagram]] /; diag["NodeQ"]]

DiagramProp[d_, "Dual", opts___] := DiagramDual[d, opts]

DiagramProp[d_, "Flip", opts___] := DiagramFlip[d, opts]

DiagramProp[d_, "Reverse", opts___] := DiagramReverse[d, opts]

DiagramProp[d_, "Head"] := Replace[d["HoldExpression"], {
    With[{headPatt = $DiagramHeadPattern}, HoldForm[(head : headPatt)[___]] :> head],
    _ -> Null
}]

DiagramProp[d_, "SubDiagrams"] := Replace[d["HoldExpression"], {
    With[{headPatt = $DiagramHeadPattern}, HoldForm[headPatt[ds___]] :> {ds}],
    _ -> {}
}]

DiagramProp[d_, "TopPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ d["InputPorts", False]

DiagramProp[d_, "BottomPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ d["OutputPorts", False]

DiagramProp[d_, "NeutralPorts", dualQ : _ ? BooleanQ : False] := Select[
    Join[d["OutputPorts", True], If[dualQ, PortDual, Identity] /@ d["InputPorts", True]],
    #["NeutralQ"] &
]

DiagramProp[d_, "LeftPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ Select[d["InputPorts", True], #["NeutralQ"] &]

DiagramProp[d_, "RightPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ Select[d["OutputPorts", True], #["NeutralQ"] &]

DiagramProp[d_, "Ports", dualQ : _ ? BooleanQ : False, neutralQ : _ ? BooleanQ : True] := Join[d["OutputPorts", neutralQ], If[dualQ, PortDual, Identity] /@ d["InputPorts", neutralQ]]

DiagramProp[d_, "OutputArity"] := Length[d["OutputPorts", True]]

DiagramProp[d_, "InputArity"] := Length[d["InputPorts", True]]

DiagramProp[d_, "TopArity"] := Length[d["TopPorts"]]

DiagramProp[d_, "BottomArity"] := Length[d["BottomPorts"]]

DiagramProp[d_, "LeftArity"] := Length[d["LeftPorts"]]

DiagramProp[d_, "RightArity"] := Length[d["RightPorts"]]

DiagramProp[d_, "NeutralArity"] := Length[d["NeutralPorts"]]

DiagramProp[d_, "Arity", neutralQ : _ ? BooleanQ : False] := Length[d["Ports", False, neutralQ]]

DiagramProp[d_, "Arities"] := {d["InputArity"], d["OutputArity"]}

DiagramProp[d_, "MaxArity"] := Max[d["OutputArity"], d["InputArity"]]

DiagramProp[d_, "MaxGridArity"] := Max[d["TopArity"], d["BottomArity"]]

DiagramProp[d_, "Flat"[params__], args___] := Catenate[Through[d[params]["ProductList", args]]]

DiagramProp[d_, "FlatInputPorts", args___] := d["Flat"["InputPorts"], args]

DiagramProp[d_, "FlatOutputPorts", args___] := d["Flat"["OutputPorts"], args]

DiagramProp[d_, "FlattenOutputs", args___] := Diagram[d, "OutputPorts" -> d["FlatOutputPorts", args], "PortArrows" -> ({#1, Catenate @ MapThread[ConstantArray[#2, Length[#1]] &, {Through[d["OutputPorts"]["ProductList", args]], #2}]} & @@ d["PortStyles"])]

DiagramProp[d_, "FlattenInputs", args___] := Diagram[d, "InputPorts" -> d["FlatInputPorts", args], "PortArrows" -> ({Catenate @ MapThread[ConstantArray[#2, Length[#1]] &, {Through[d["InputPorts"]["ProductList", args]], #1}], #2} & @@ d["PortStyles"])]

DiagramProp[d_, "FlatOutputArity", args___] := Length[d["FlatOutputPorts", args]]

DiagramProp[d_, "FlatInputArity", args___] := Length[d["FlatInputPorts", args]]

DiagramProp[d_, "Flatten", args___] := d["FlattenOutputs", args]["FlattenInputs", args]

DiagramProp[d_, "FlatPorts", args___] := Join[d["FlatOutputPorts", args], d["FlatInputPorts", args]]

DiagramProp[d_, "FlattenNetworks"] := If[d["NetworkQ"],
    Diagram[d, "Expression" :> DiagramNetwork[##] & @@ (If[#["NetworkQ"], Splice[#["SubDiagrams"]], #] & /@ Through[d["SubDiagrams"]["FlattenNetworks"]])],
    With[{ds = d["SubDiagrams"]}, If[ds === {}, d, Diagram[d, "Expression" -> d["Head"] @@ Through[ds["FlattenNetworks"]]]]]
]

DiagramProp[d_, "GridInputPorts"] := GridInputPorts[d]

DiagramProp[d_, "GridOutputPorts"] := GridOutputPorts[d]

DiagramProp[d_, "Split", n : _Integer | Infinity | - Infinity : Infinity, dualQ : _ ? BooleanQ : True] := Block[{
    m = If[n >= 0, n, Max[d["Arity"] + n, 0]], outputs, inputs, dual = If[dualQ, PortDual, Identity]
},
    outputs = TakeDrop[d["OutputPorts"], UpTo[m]];
    inputs = TakeDrop[d["InputPorts"], UpTo[Max[0, m - d["OutputArity"]]]];
    Diagram[d,
        "OutputPorts" -> Join[outputs[[1]], dual /@ inputs[[1]]],
        "InputPorts" -> Join[dual /@ outputs[[2]], inputs[[2]]]
    ]
]

DiagramProp[d_, "Permute", perm_, dualQ : _ ? BooleanQ : True] := Enclose @ With[
    {ports = d["Ports"], ordering = ConfirmBy[PermutationList[perm, d["Arity"]], ListQ], dual = If[dualQ, PortDual, Identity]},
    {newPorts = TakeDrop[MapIndexed[If[Xor[#1 <= d["OutputArity"], #2[[1]] <= d["OutputArity"]], dual, Identity][ports[[#1]]] &, ordering], d["OutputArity"]]},
    Diagram[d,
        "OutputPorts" -> newPorts[[1]],
        "InputPorts" -> newPorts[[2]]
    ]
]

DiagramProp[d_, "View"] := With[{
    holdExpr = Replace[d["HoldExpression"],
        HoldForm[(head : DiagramDual | DiagramFlip | DiagramReverse | DiagramProduct | DiagramSum | DiagramComposition | DiagramNetwork)[ds___]] :>
            head @@@ HoldForm[Evaluate[Flatten[Defer @@ (Function[Null, If[DiagramQ[#], #, Defer[#]], HoldFirst] /@ Unevaluated[{ds}])]]]
    ],
    outputs = Replace[Through[d["OutputPorts"]["View"]], {p : Except[HoldForm[_List | _Interpretation]]} :> p],
    inputs = Replace[Through[Through[d["InputPorts"]["Dual"]]["View"]], {p : Except[HoldForm[_List | _Interpretation]]} :> p],
    opts = d["DiagramOptions"]
},
    Function[expr, If[opts === {}, Defer[Diagram[expr, inputs, outputs]], Defer[Diagram[expr, inputs, outputs, ##]] & @@ opts] //. HoldForm[x_] :> x, HoldFirst] @@ holdExpr
]

DiagramProp[d_, "Name"] := Replace[
    d["HoldExpression"],

    HoldForm[(head : $DiagramHeadPattern)[ds___]] :>
        Replace[head, {
            Diagram -> Identity,
            DiagramDual -> SuperStar,
            DiagramFlip -> OverBar,
            DiagramReverse -> OverTilde,
            DiagramProduct -> CircleTimes,
            DiagramSum -> CirclePlus,
            DiagramComposition -> CircleDot,
            DiagramNetwork -> List
        }] @@@ HoldForm[Evaluate[Flatten[Defer @@ (Function[Null, If[DiagramQ[#], #["Name"], Defer[#]], HoldFirst] /@ Unevaluated[{ds}])]]]
]

DiagramProp[diagram_, "Decompose", args___] := DiagramDecompose[diagram, args]

DiagramProp[diagram_, "Tensor" | "ArraySymbol", opts : OptionsPattern[]] := DiagramTensor[diagram, FilterRules[{opts}, Options[DiagramTensor]]]

DiagramProp[diagram_, "Function", opts : OptionsPattern[]] := DiagramFunction[diagram, FilterRules[{opts}, Options[DiagramFunction]]]

DiagramProp[d_, "Diagram" | "Graphics", opts : OptionsPattern[]] := DiagramGraphics[d, FilterRules[{opts}, Options[DiagramGraphics]], BaseStyle -> {GraphicsHighlightColor -> Automatic}]

DiagramProp[d_, "Normal"] := If[d["NetworkQ"],
    With[{g = DiagramsNetGraph[d["SubDiagrams"], "BinarySpiders" -> All, "UnarySpiders" -> False, "RemoveCycles" -> True, FilterRules[d["DiagramOptions"], Options[DiagramsNetGraph]]]},
        DiagramComposition @@ AnnotationValue[{g, Reverse[TopologicalSort[g]]}, "Diagram"]
    ],
    d
]

DiagramProp[d_, "PortFunction"] := Lookup[d["DiagramOptions"], "PortFunction", $DefaultPortFunction]

DiagramProp[d_, "PortGraph", opts : OptionsPattern[]] := DiagramsPortGraph[d["SubDiagrams"], opts]

DiagramProp[d_, "Graph", opts : OptionsPattern[]] := DiagramsGraph[d["SubDiagrams"], opts, "PortFunction" -> d["PortFunction"]]

DiagramProp[d_, "Network", opts : OptionsPattern[]] := ToDiagramNetwork[d, FilterRules[{opts}, Options[ToDiagramNetwork]]]

DiagramProp[d_, "NetGraph", opts : OptionsPattern[]] := DiagramsNetGraph[d["Network"]["SubDiagrams"], FilterRules[{opts, d["DiagramOptions"]}, Options[DiagramsNetGraph]]]

DiagramProp[d_, "Arrange", opts : OptionsPattern[]] := DiagramArrange[d, opts]

DiagramProp[d_, "Grid", opts : OptionsPattern[]] := DiagramGrid[d, opts]

DiagramProp[d_, "OptionValue"[opt_], opts : OptionsPattern[]] := OptionValue[{opts, d["DiagramOptions"], Options[DiagramGraphics], Options[DiagramGrid], Options[DiagramsNetGraph]}, opt]

DiagramProp[d_, "WireQ"] := MatchQ[d["OptionValue"["Shape"]], "Wire" | "Wires" | "Wires"[_]]

DiagramProp[d_, "Shape", opts : OptionsPattern[]] := Enclose @ Block[{
    w = Replace[d["OptionValue"["Width"], opts], Automatic -> 1],
    h = Replace[d["OptionValue"["Height"], opts], Automatic -> 1],
    c = d["OptionValue"["Center"], opts],
    a = d["OptionValue"["Angle"], opts],
    func = d["OptionValue"["PortFunction"], opts],
    transform, primitives
},
    transform = GeometricTransformation[#, RotationTransform[a, c] @* If[d["FlipQ"], ReflectionTransform[{0, 1}, c], Identity] @* If[d["ReverseQ"], ReflectionTransform[{1, 0}, c], Identity]] &;
    primitives = Replace[
        d["OptionValue"["Shape"], opts],
        {
            None -> {},
            Automatic :> transform @ Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c],
            "RoundedRectangle" :> transform @ Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c, RoundingRadius -> {{Right, Bottom} -> .1 (w + h)}],
            "Triangle" :> transform @ Polygon[{{- w / 2, h / 2}, {0, - h / 2}, {w / 2, h / 2}} + Threaded[c]],
            "UpsideDownTriangle" :> transform @ Polygon[{{- w / 2, - h / 2}, {0, h / 2}, {w / 2, - h / 2}} + Threaded[c]],
            "Circle" :> transform @ Circle[c, {w, h} / 2],
            "CrossWires" :> With[{
                points = d["PortArrows", opts],
                inputs = PositionIndex[func /@ Through[d["InputPorts"]["Dual"]]],
                outputs = PositionIndex[func /@ d["OutputPorts"]]
            },
                Map[
                    ps |-> Outer[
                        BSplineCurve[{#1[[1]], 2 * #1[[1]] - #1[[2]], 2 * #2[[1]] - #2[[2]], #2[[1]]}] &,
                        ps[[2]],
                        ps[[1]],
                        1
                    ],
                    Values @ Merge[KeyUnion[{inputs, outputs}, {} &], Apply[{points[[1, #1]], points[[2, #2]]} &]]
                ]
            ],
            "Wires" :> With[{
                points = d["PortArrows", opts],
                inputs = PositionIndex[func /@ Through[d["InputPorts"]["Dual"]]],
                outputs = PositionIndex[func /@ d["OutputPorts"]]
            },
                Map[
                    ps |-> BSplineCurve[{ps[[1, 1]], 2 * ps[[1, 1]] - ps[[1, 2]], If[Length[ps] == 2, Nothing, c], 2 * #[[1]] - #[[2]], #[[1]]}] & /@ Rest[ps],
                    Values @ Merge[KeyUnion[{inputs, outputs}, {} &], Apply[Join[points[[1, #1]], points[[2, #2]]] &]]
                ]
            ],
            "Wires"[wires_] :> With[{
                ps = Catenate[d["PortArrows", opts]],
                styles = Catenate[d["PortStyles", opts]]
            },
                With[{p = ps[[First[#]]], style = Replace[SelectFirst[styles[[#]], # =!= Automatic &, Nothing], None -> Nothing]},
                    {style, BSplineCurve[{p[[1]], 2 * p[[1]] - p[[2]], 2 * #[[1]] - #[[2]], #[[1]]}] & /@ DeleteCases[None] @ ps[[Rest[#]]]}
                ] & /@ wires
            ],
            "Wire" :> With[{
                ps = Catenate[d["PortArrows", opts]]
            },
                BSplineCurve[{ps[[1, 1]], 2 * ps[[1, 1]] - ps[[1, 2]], c, 2 * #[[1]] - #[[2]], #[[1]]}] & /@ Rest[ps]
            ],
            shape_ :> transform @ GeometricTransformation[shape, TranslationTransform[c]]
        }
    ];
    If[ MatchQ[d["OptionValue"["Outline"], opts], Automatic | True],
        primitives = {primitives, EdgeForm[Directive[Dashed, Black]], FaceForm[None], transform[Rectangle[{c[[1]]- w / 2, c[[2]] - h / 2}, {c[[1]] + w / 2, c[[2]] + h / 2}]]},
        primitives
    ]
]

DiagramProp[d_, "PortArrows", opts : OptionsPattern[]] := Block[{
    w = Replace[d["OptionValue"["Width"], opts], Automatic -> 1],
    h = Replace[d["OptionValue"["Height"], opts], Automatic -> 1],
    c = d["OptionValue"["Center"], opts],
    a = d["OptionValue"["Angle"], opts],
    s = d["OptionValue"["Spacing"], opts],
    shape = d["OptionValue"["Shape"], opts],
    arities = {d["InputArity"], d["OutputArity"]},
    arrows = fillAutomatic[d["OptionValue"["PortArrows"], opts], arities, True],
    transform = RotationTransform[a, c],
    placeShift = <||>, placeArity, placeArrow
},
    placeArity = Counts @ Join[
        MapThread[Replace[#1, {Placed[_, p_] :> Replace[p, Automatic :> If[#2["NeutralQ"], Left, Top]], _ :> If[#2["NeutralQ"], Left, Top]}] &, {arrows[[1]], d["InputPorts"]}],
        MapThread[Replace[#1, {Placed[_, p_] :> Replace[p, Automatic :> If[#2["NeutralQ"], Right, Bottom]], _ :> If[#2["NeutralQ"], Right, Bottom]}] &, {arrows[[2]], d["OutputPorts"]}]
    ];
    placeArrow = Function @ With[{dx = s / (Lookup[placeArity, #1, 0] + 1)}, {x = Lookup[placeShift, #1, (1 - s) / 2 + dx]},
        placeShift = <|placeShift, #1 -> x + dx|>;
        Replace[#1, {
            Right :> {{w / 2, (1 / 2 - x) h}, {w / 2 + 1 / 4, (1 / 2 - x) h}},
            Left :> {{- w / 2, (1 / 2 - x) h}, {- w / 2 - 1 / 4, (1 / 2 - x) h}},
            Top | Up :> {{(- 1 / 2 + x) w, h / 2}, {(- 1 / 2 + x) w, h / 2 + 1 / 4}},
            Bottom | Down :> {{(- 1 / 2 + x) w, - h / 2}, {(- 1 / 2 + x) w, - h / 2 - 1 / 4}}
        }] + Threaded[c]
    ];
    {
         transform @ MapThread[
            Replace[#3, {
                Placed[_, p : Except[None]] :> placeArrow[Replace[p, Automatic :> If[#4["NeutralQ"], Left, Top]]],
                _ :> Replace[shape, {
                    "Circle" :> With[{p = {w Cos[#1], h Sin[#1]}}, {p / 2, p / 2 + Normalize[p] /4}] + Threaded[c],
                    _ :> placeArrow[If[#4["NeutralQ"], Left, Top]]
                }]
            }] &,
            {
                Range[Pi, 0, - Pi / (d["InputArity"] + 1)][[2 ;; -2]],
                Range[(1 - s) / 2, (s + 1) / 2, s / (d["InputArity"] + 1)][[2 ;; -2]],
                arrows[[1]],
                d["InputPorts"]
            }
        ]
        ,
        transform @ MapThread[
            Replace[#3, {
                Placed[_, p : Except[None]] :> placeArrow[Replace[p, Automatic :> If[#4["NeutralQ"], Right, Bottom]]],
                _ :> Replace[shape, {
                    "Circle" :> With[{p = {w Cos[#1], h Sin[#1]}}, {p / 2, p / 2 + Normalize[p] /4}] + Threaded[c],
                    _ :> placeArrow[If[#4["NeutralQ"], Right, Bottom]]
                }]
            }] &,
            {
                Range[Pi, 2 Pi, Pi / (d["OutputArity"] + 1)][[2 ;; -2]],
                Range[(1 - s) / 2, (s + 1) / 2, s / (d["OutputArity"] + 1)][[2 ;; -2]],
                arrows[[2]],
                d["OutputPorts"]
            }
        ]
    }
]

DiagramProp[d_, "FlatPortArrows", opts : OptionsPattern[]] := d["Flatten"]["PortArrows", opts]

DiagramProp[d_, "PortStyles", opts : OptionsPattern[]] :=
    Replace[fillAutomatic[d["OptionValue"["PortArrows"], opts], {d["InputArity"], d["OutputArity"]}, Automatic], Placed[x_, _] :> x, {2}]


DiagramProp[_, prop_] := Missing[prop]


(* ::Subsection:: *)
(* Formatting *)

$DefaultPortLabelFunction = Function[ClickToCopy[#2 /. Automatic :> If[#1["DualQ"], #1["Dual"], #1], #1["View"]]]

Options[DiagramGraphics] = Join[{
    "Shape" -> Automatic,
    "Center" -> {0, 0},
    "Width" -> Automatic,
    "Height" -> Automatic,
    "Angle" -> 0,
    "Spacing" -> 1.6,
    "ShowLabel" -> Automatic,
    "LabelFunction" -> Automatic,
    "PortArrows" -> Automatic,
    "PortLabels" -> Automatic,
    "PortArrowFunction" -> Automatic,
    "PortLabelFunction" -> Automatic,
    "Outline" -> None
}, Options[Graphics]];

DiagramGraphics[diagram_ ? DiagramQ, opts : OptionsPattern[]] := Enclose @ With[{
    points = diagram["PortArrows", opts],
    arities = {diagram["InputArity"], diagram["OutputArity"]}
}, {
    portArrows = diagram["PortStyles", opts],
    portLabels = fillAutomatic[diagram["OptionValue"["PortLabels"], opts], arities],
    labelFunction = diagram["OptionValue"["LabelFunction"], opts],
    portArrowFunction = Replace[diagram["OptionValue"["PortArrowFunction"], opts], Automatic -> (#2 &)],
    portLabelFunction = Replace[diagram["OptionValue"["PortLabelFunction"], opts], Automatic -> $DefaultPortLabelFunction]
}, Graphics[{
    EdgeForm[Black], FaceForm[None], 
    Confirm @ diagram["Shape", opts],
    Text[
        Replace[labelFunction,
            Automatic :> Function[ClickToCopy[
                If[ MatchQ[#["OptionValue"["ShowLabel"], opts], None | False],
                    "\t\t\t",
                    Replace[#["HoldExpression"], expr_ :> (expr //. d_Diagram ? DiagramQ :> RuleCondition[d["HoldExpression"]])]
                ],
                #["View"]
            ]]
        ] @ diagram,
        diagram["OptionValue"["Center"], opts]
    ],
    Arrowheads[Small],
    MapThread[{ports, ps, arrows, labels, dir} |->
        MapThread[{x, p, arrow, label} |-> {
            If[ MatchQ[arrow, None | False],
                Nothing,
                If[MatchQ[arrow, _Function], portArrowFunction[x, arrow[x, p], dir], {Replace[arrow, True | Automatic -> Nothing], portArrowFunction[x, Arrow[If[x["DualQ"], Reverse, Identity] @ p], dir]}]
            ],
            With[{
                labelExpr = Replace[label, Placed[e_, _] :> e],
                newLabel = Replace[label, {Placed[l_, pos_] :> Placed[Replace[portLabelFunction[x, l, dir], Placed[e_, _] :> e], pos], l_ :> portLabelFunction[x, l, dir]}]
            }, If[ MatchQ[labelExpr, None | False],
                Nothing,
                Replace[newLabel, Placed[l_, pos_] | l_ :> If[l === None, Nothing, Text[
                        l /. Inherited :> $DefaultPortLabelFunction[x, labelExpr, dir],
                        With[{v = (p[[-1]] - p[[1]]) 3 / 4, s = PadLeft[Flatten[Replace[{pos}, {{Right} -> {2, 0}, {Left} -> {- 2, 0}, {Top | Up} -> {0, 2}, {Bottom | Down} -> {0, - 2}, {Center} -> {0, 0}, {} -> {0, 2}}]], 2, 0]},
                            p[[1]] + s[[2]] * v + s[[1]] * RotationTransform[Replace[dir, {Top -> Pi / 2, Bottom -> - Pi / 2}]][v]
                        ]
                    ]]
                ]
            ]]
        },
           {ports, ps, arrows, labels}
        ],
        {{diagram["InputPorts"], diagram["OutputPorts"]}, points, portArrows, portLabels, {Top, Bottom}}
    ]
},
    FilterRules[{opts, diagram["DiagramOptions"]}, Options[Graphics]],
    FormatType -> StandardForm
]]

Diagram /: MakeBoxes[diagram : Diagram[_Association] ? DiagramQ, form_] := With[{boxes = ToBoxes[Show[
    If[diagram["NetworkQ"], diagram["NetGraph"], Replace[$DiagramDefaultGraphics, {"Grid" :> diagram["Grid"], f_Function :> f[diagram], _ :> diagram["Graphics"]}]], BaseStyle -> {GraphicsHighlightColor -> Magenta}], form]},
    InterpretationBox[boxes, diagram]
]

DiagramDual /: MakeBoxes[DiagramDual[d_], form_] := With[{boxes = ToBoxes[SuperStar[d], form]}, InterpretationBox[boxes, DiagramDual[d]]]

DiagramFlip /: MakeBoxes[DiagramFlip[d_], form_] := With[{boxes = ToBoxes[OverBar[d], form]}, InterpretationBox[boxes, DiagramFlip[d]]]

DiagramReverse /: MakeBoxes[DiagramReverse[d_], form_] := With[{boxes = ToBoxes[Overscript[d, RawBoxes["\[LongLeftRightArrow]"]], form]}, InterpretationBox[boxes, DiagramReverse[d]]]

DiagramProduct /: MakeBoxes[DiagramProduct[ds___], form_] := With[{boxes = ToBoxes[CircleTimes[ds], form]}, InterpretationBox[boxes, DiagramProduct[ds]]]

DiagramSum /: MakeBoxes[DiagramSum[ds___], form_] := With[{boxes = ToBoxes[CirclePlus[ds], form]}, InterpretationBox[boxes, DiagramSum[ds]]]

DiagramComposition /: MakeBoxes[DiagramComposition[ds___], form_] := With[{boxes = ToBoxes[CircleDot[ds], form]}, InterpretationBox[boxes, DiagramComposition[ds]]]

DiagramNetwork /: MakeBoxes[DiagramNetwork[ds___], form_] := With[{boxes = ToBoxes[{ds}, form]}, InterpretationBox[boxes, DiagramNetwork[ds]]]


(* ::Subsection:: *)
(* Functions *)


Options[DiagramsPortGraph] = Options[Graph];
DiagramsPortGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := GraphSum[##, FilterRules[{opts}, Options[Graph]], VertexLabels -> Automatic] & @@
    (With[{vs = Through[#["HoldExpression"]]}, Graph[vs, UndirectedEdge @@@ Subsets[vs, {2}]]] & /@ Through[diagrams["Ports"]])


DiagramGraphSimplify[g_ ? GraphQ] := Fold[
    {net, v} |-> Block[{d = AnnotationValue[{net, v}, "Diagram"], wires, out, in, ports},
        (wires = If[MatchQ[#, "Wires"[_]], First[#], {}]) & @ d["OptionValue"["Shape"]];
        If[wires === {}, Return[net, Block]];
        in = EdgeList[net, DirectedEdge[_, v]];
        out = EdgeList[net, DirectedEdge[v, _]];
        ports = Join[SortBy[in, #[[1, 3]] &], SortBy[out, #[[2, 3]] &]];
        VertexReplace[
            VertexDelete[
                net, 
                Append[v] @ Replace[ports, DirectedEdge[_, p_List] | DirectedEdge[p_List, _] :> p, 1]
            ],
            First @ Solve[Equal @@ Replace[
                    ports[[#]],
                    {
                        DirectedEdge[_, out_List] :> Splice @ EdgeList[net, DirectedEdge[out, _]][[All, 2]], 
                        DirectedEdge[in_List, _] :> Splice @ EdgeList[net, DirectedEdge[_, in]][[All, 1]]
                    }, 
                    1
                ] & /@ wires
			]
        ]
    ],
    g,
    VertexList[g, _Integer]
]

SimplifyDiagram[diag_ ? DiagramQ] := With[{portFunction = If[diag["NetworkQ"], diag["PortFunction"], #["HoldExpression"] &]}, {
	net = DiagramsNetGraph[
            diag["Network", "Arrange" -> False]["Graph", "Simplify" -> True, "PortFunction" -> portFunction],
            "PortFunction" -> portFunction, "UnarySpiders" -> False, "BinarySpiders" -> False
        ] //
        DiagramNetwork[##, "PortFunction" -> portFunction] & @@ AnnotationValue[{#, VertexList[#]}, "Diagram"] &
},
	If[diag["NetworkQ"], net, net["Arrange"]]
]


Options[DiagramsGraph] = Join[{"Simplify" -> False, "PortFunction" -> $DefaultPortFunction}, Options[Graph]];
DiagramsGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := Block[{
    ports = Thread[{Through[#["InputPorts"]["Dual"]] & /@ #, Through[#["OutputPorts"]]}] & @ Through[diagrams["Flatten"]], indexedPorts,
    portFunction = OptionValue["PortFunction"],
    graph, embedding
},
    graph = Graph[
        Join[
            MapIndexed[Annotation[#2[[1]], "Diagram" -> #1] &, diagrams],
            Flatten[MapIndexed[Annotation[#2, "Port" -> #1] &, ports, {3}], 2]
        ],
        Flatten[
            MapIndexed[
                With[{diagram = #2[[1]], port = #2, wire = portFunction[#1]},
                    Switch[port[[2]], 1, {DirectedEdge[port, diagram], DirectedEdge[wire, port]}, 2, {DirectedEdge[diagram, port], DirectedEdge[port, wire]}]
                ] &,
                ports,
                {3}
            ],
            3
        ],
        VertexLabels -> MapAt[Placed[#, Center] &, {All, 2}] @ Join[
            {_ -> Automatic},
            Thread[Range[Length[diagrams]] -> (#["Graphics", #["DiagramOptions"], "PortLabels" -> None, "PortArrows" -> None, "Shape" -> None] & /@ diagrams)],
            Flatten[MapIndexed[#2 -> #1["Label"] &, ports, {3}], 2]
        ],
        VertexSize -> {_ -> Medium, _Integer -> Large, {__Integer} -> Medium},
        VertexShapeFunction -> {_ -> "Diamond", _Integer -> "Square", {__Integer} -> "Circle"},
        VertexStyle -> Transparent,
        PerformanceGoal -> "Quality"
    ];
    indexedPorts = MapIndexed[#2 &, ports, {3}];
    If[ TrueQ[OptionValue["Simplify"]],
        graph = DiagramGraphSimplify[graph];
        indexedPorts = indexedPorts[[VertexList[graph, _Integer]]];
    ];
    embedding = AssociationThread[
        VertexList[graph],
        GraphEmbedding[
            EdgeAdd[graph,
                Catenate[DirectedEdge @@@ Partition[Reverse @ Catenate[#], 2, 1, 1] & /@ MapAt[Reverse, indexedPorts, {All, 2}]],
                FilterRules[{opts}, {VertexCoordinates, GraphLayout}]
            ]
        ]
    ];
    embedding = <|
        embedding,
        If[Catenate[#] === {}, Nothing, With[{diagramCenter = Lookup[embedding, Catenate[#][[1, 1]]]},
            Thread[# -> SortBy[Lookup[embedding, #], ArcTan @@ (# - diagramCenter) &]] & /@ #
        ]] & /@ indexedPorts
    |>;
    Graph[
        graph,
        FilterRules[{opts}, Options[Graph]],
        VertexCoordinates -> Normal[embedding]
    ]
]


RemoveDiagramsNetGraphCycles[inputNet_ ? DirectedGraphQ, opts : OptionsPattern[Graph]] := Enclose @ Block[{
    net = inputNet, diagrams, cycles, id, edge, cups = {}, caps = {}, cupDiagrams = {}, capDiagrams = {}, cup, cap
},
	diagrams = AssociationThread[VertexList[net], AnnotationValue[{inputNet, VertexList[net]}, "Diagram"]];
	id = Max[VertexList[net, _Integer], 0] + 1;

	While[
        Length[cycles = Join[FindCycle[net, Infinity, 1], FirstCase[EdgeList[net], e : _[x_, x_, ___] :> {{e}}, {}, {1}, Heads -> False]]] > 0,

		edge = cycles[[1, -1]];
		AppendTo[cups, cup = id++];
		AppendTo[caps, cap = id++];
		AppendTo[cupDiagrams, With[{port = Lookup[diagrams, edge[[2]]]["InputPorts"][[edge[[3, -1, 3]]]]},
            Diagram["\[DoubleStruckCapitalI]", {PortDual[port], port}, "Shape" -> "Wires"[{{1, 2}}], "ShowLabel" -> False]
        ]];
		AppendTo[capDiagrams, With[{port = Lookup[diagrams, edge[[1]]]["OutputPorts"][[edge[[3, 1, 3]]]]},
            Diagram["\[DoubleStruckCapitalI]", {port, PortDual[port]}, {}, "Shape" -> "Wires"[{{1, 2}}], "ShowLabel" -> False]
        ]];
		net = EdgeDelete[net, {edge}];
		net = VertexAdd[net, {cap, cup}];
        net = EdgeAdd[net, {
			DirectedEdge[cup, cap, {{2, 2, 1}, {1, 2, 1}}],
			DirectedEdge[cup, edge[[2]], {{2, 2, 2}, {1, edge[[3, -1, 2]], edge[[3, -1, 3]]}}],
			DirectedEdge[edge[[1]], cap, {{2, edge[[3, 1, 2]], edge[[3, 1, 3]]}, {1, 2, 2}}]
		}];
	];
	Graph[net, opts,
		AnnotationRules -> Join[
            Thread[cups -> List /@ Thread["Diagram" -> cupDiagrams]],
            Thread[caps -> List /@ Thread["Diagram" -> capDiagrams]]
        ]
	]
]

Options[DiagramsNetGraph] = Join[{
    "ShowPortLabels" -> False,
    "ShowWireLabels" -> True,
    "Scale" -> Automatic,
    "ArrowSize" -> Small, 
    "SpiderRadius" -> 0.2,
    "Orientation" -> Automatic,
    "UnarySpiders" -> True,
    "BinarySpiders" -> True,
    "RemoveCycles" -> False
}, Options[DiagramsGraph], Options[DiagramGraphics], Options[Graph]];
DiagramsNetGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] :=
    DiagramsNetGraph[
        DiagramsGraph[diagrams, FilterRules[{opts}, {GraphLayout, FilterRules[Options[DiagramsGraph], Except[Options[Graph]]]}]],
        FilterRules[{opts}, Except[GraphLayout]]
    ]
DiagramsNetGraph[graph_Graph, opts : OptionsPattern[]] := Block[{
	diagramVertices = VertexList[graph, _Integer], vertices, edges, netGraph,
    spiderVertices, spiderDiagrams,
	diagrams, outDegrees, inDegrees,
	embedding, orientations, orientation = OptionValue["Orientation"],
	scale = Replace[OptionValue["Scale"], Automatic -> .75],
    arrowSize = OptionValue["ArrowSize"],
    rad = OptionValue["SpiderRadius"],
	portLabelsQ = TrueQ[OptionValue["ShowPortLabels"]],
	wireLabelsQ = TrueQ[OptionValue["ShowWireLabels"]],
    unarySpiders = OptionValue["UnarySpiders"],
    binarySpiders = OptionValue["BinarySpiders"],
    portFunction = OptionValue["PortFunction"]
},
	diagrams = AssociationMap[AnnotationValue[{graph, #}, "Diagram"]["Flatten"] &, diagramVertices];
	If[Length[diagrams] == 0, Return[Graphics[FilterRules[Join[{opts}, Options[graph]], Options[Graphics]]]]];
	embedding = AssociationThread[VertexList[graph], GraphEmbedding[graph]];
	If[EdgeCount[graph] == 0 && VertexCount[graph] > 1, embedding = ScalingTransform[{1, .5} / Max[#2 - #1 & @@@ CoordinateBounds[embedding]], Mean[embedding]][embedding]];
	orientations = Switch[
        orientation,
        Automatic,
        Map[
            Normalize[Lookup[#, 1] - Lookup[#, 2]] &,
            Values @ <|
                # -> <|1 -> {0, 1 / 2}, 2 -> {0, - 1 / 2}|> & /@ diagramVertices,
                KeyValueMap[
                    With[{center = Lookup[embedding, #1]}, #1 -> <|<|1 -> center, 2 -> center|>, #2|>] &,
                    GroupBy[VertexList[graph, {__Integer}], First, Mean /@ GroupBy[#, #[[2]] &, Lookup[embedding, #] &] &]
                ]
            |>
        ],
        {_ ? NumericQ, _ ? NumericQ},
        ConstantArray[orientation, Length[diagramVertices]],
        _,
        ConstantArray[{0, 1}, Length[diagramVertices]]
    ];
    orientations = AssociationThread[diagramVertices, orientations];
	{outDegrees, inDegrees} = AssociationThread[VertexList[graph] -> #] & /@ Through[{VertexOutDegree, VertexInDegree}[graph]];
	{spiderVertices, spiderDiagrams} = Replace[{{} -> {{}, {}}, sow_List :> Thread[sow]}] @ First[Reap[
		edges = Sort @ Map[v |->
			Block[{in = Sort @ VertexInComponent[graph, v, {1}], out = Sort @ VertexOutComponent[graph, v, {1}], ports},
				ports = Join[in, out];
				If[ Length[ports] > 2 ||
                    Length[ports] == 1 && MatchQ[unarySpiders, True] ||
                    Length[ports] == 2 && (MatchQ[binarySpiders, All | Full] || MatchQ[binarySpiders, True] && SameQ @@ ports[[All, 2]])
                    ,
					Sow[{v,
                        Diagram[If[Length[ports] == 2, "\[DoubleStruckCapitalI]", v],
                            Port[tag[v, #]] & /@ in,
                            Port[tag[v, #]] & /@ out,
                            If[Length[ports] == 2, {"Shape" -> If[Length[ports] == 2, "Wires"[{{1, 2}}], "Wire"], "ShowLabel" -> False}, {"Shape" -> "Circle", "ShowLabel" -> wireLabelsQ}],
                            "PortArrows" -> {diagrams[#[[1]]]["PortStyles"][[2, #[[3]]]] & /@ in, diagrams[#[[1]]]["PortStyles"][[1, #[[3]]]] & /@ out}
                        ]
                    }];
                    Splice @ Catenate @ {
                        MapIndexed[DirectedEdge[#[[1]], v, {{2, Lookup[outDegrees, #[[1]]], #[[3]]}, {1, Length[in], #2[[1]]}}] &, in],
                        MapIndexed[DirectedEdge[v, #[[1]], {{2, Length[out], #2[[1]]}, {1, Lookup[inDegrees, #[[1]]], #[[3]]}}] &, out]
                    }
                    ,
					If[ Length[ports] < 2,
                        Nothing,
                        Block[{src, tgt, srcDegree, tgtDegree},
                            {src, tgt} = If[ ports[[1, 2]] == 1, {ports[[2]], ports[[1]]}, {ports[[1]], ports[[2]]}];
                            srcDegree = If[ src[[2]] == 1, inDegrees, outDegrees][src[[1]]];
                            tgtDegree = If[ tgt[[2]] == 1, inDegrees, outDegrees][tgt[[1]]];
                            DirectedEdge[src[[1]], tgt[[1]], {{src[[2]], srcDegree, src[[3]]}, v, {tgt[[2]], tgtDegree, tgt[[3]]}}]
                        ]
                    ]
				]
			],
			VertexList[graph, _HoldForm]
		]
	][[2]], {}];
	vertices = Join[diagramVertices, spiderVertices];
    netGraph = Graph[vertices, edges,
        AnnotationRules -> Join[
            Thread[diagramVertices -> List /@ Thread["Diagram" -> KeyValueMap[
                Diagram[#2,
                    "OutputPorts" -> MapThread[
                        FirstCase[edges,
                            DirectedEdge[#2[[1]], tgtIdx_, {{2, _, #2[[3]]}, _, {1, _, portIdx_}}] :> With[{tgt = diagrams[tgtIdx]["InputPorts"][[portIdx]]["Dual"]},
                                Port[tag[portFunction @ tgt, {tgtIdx, 1, portIdx}], "NeutralQ" -> tgt["NeutralQ"]]
                            ],
                            FirstCase[edges,
                                DirectedEdge[#2[[1]], tgtIdx_, {{2, _, #2[[3]]}, _, {2, _, portIdx_}}] :> With[{tgt = diagrams[tgtIdx]["OutputPorts"][[portIdx]]},
                                    Port[tag[portFunction @ tgt, {tgtIdx, 2, portIdx}], "NeutralQ" -> tgt["NeutralQ"]]
                                ],
                                Port[tag[portFunction @ #1, #2], "NeutralQ" -> #1["NeutralQ"]]
                            ]
                        ] &,
                        {#2["OutputPorts"], Thread[{#1, 2, Range[#2["OutputArity"]]}]}
                    ],
                    "InputPorts" -> MapThread[
                        FirstCase[edges,
                            DirectedEdge[#2[[1]], tgtIdx_, {{1, _, #2[[3]]}, _, {2, _, portIdx_}}] :> With[{tgt = diagrams[tgtIdx]["OutputPorts"][[portIdx]]},
                                Port[tag[portFunction @ tgt, {tgtIdx, 2, portIdx}], "NeutralQ" -> tgt["NeutralQ"]]
                            ],
                            FirstCase[edges,
                                DirectedEdge[#2[[1]], tgtIdx_, {{1, _, #2[[3]]}, _, {1, _, portIdx_}}] :> With[{tgt = diagrams[tgtIdx]["InputPorts"][[portIdx]]["Dual"]},
                                    Port[tag[portFunction @ tgt, {tgtIdx, 1, portIdx}],  "NeutralQ" -> tgt["NeutralQ"]]
                                ],
                                Port[tag[portFunction @ #1, #2],  "NeutralQ" -> #1["NeutralQ"]]
                            ]
                        ]["Dual"] &,
                        {Through[#2["InputPorts"]["Dual"]], Thread[{#1, 1, Range[#2["InputArity"]]}]}
                    ]
                ] &,
                diagrams
            ]]],
            Thread[spiderVertices -> List /@ Thread["Diagram" -> spiderDiagrams]]
        ]
    ];
    If[TrueQ[OptionValue["RemoveCycles"]], netGraph = RemoveDiagramsNetGraphCycles[netGraph]];
	Graph[
		netGraph,
		FilterRules[{opts}, Options[Graph]],
		VertexCoordinates -> Thread[vertices -> Join[Lookup[embedding, diagramVertices] + Through[Values[diagrams]["OptionValue"["Center"]]], Lookup[embedding, spiderVertices]]],
		VertexShapeFunction -> Join[
			Thread[diagramVertices ->
				MapThread[{diagram, orientation} |-> With[{
						shape = First @ diagram["Graphics", diagram["DiagramOptions"], "PortArrowFunction" -> (Nothing &), "PortLabels" -> If[portLabelsQ, Automatic, None], "LabelFunction" -> Function[If[#["NetworkQ"], #, #["HoldExpression"]]]],
						transform = RotationTransform[{{0, 1}, orientation}] @* ScalingTransform[scale {1, 1}]
					},
						Function[{
							Black, FaceForm[None],
							GeometricTransformation[shape, TranslationTransform[#1] @* transform]
						}]
					],
					{Values[diagrams], Values[orientations]}
				]
			],
			Thread[spiderVertices -> With[{radius = rad * scale}, Function[Circle[#1, radius]]]]
		],
		EdgeShapeFunction -> Replace[edges, {
				edge : DirectedEdge[v_Integer, w_Integer, {{i : 1 | 2, _Integer, p_Integer}, x_, {j : 1 | 2, _Integer, q_Integer}}] :> edge -> Block[{
					point1, point2, normal1, normal2, orientation1 = orientations[v], orientation2 = orientations[w], wireCoords = Lookup[embedding, x],
                    style1, style2,
                    diagram1 = diagrams[v], diagram2 = diagrams[w],
                    port1, port2,
                    points1, points2
				},
                    port1 = diagram1[Replace[i, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[p]];
                    port2 = diagram2[Replace[j, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[q]];
                    points1 = diagram1["PortArrows"][[i, p]];
                    points2 = diagram2["PortArrows"][[j, q]];
                    style1 = diagram1["PortStyles"][[i, p]];
                    style2 = diagram2["PortStyles"][[j, q]];
                    point1 = points1[[1]] * scale;
                    normal1 = (points1[[-1]] - points1[[1]]) * scale * 3;
                    point2 = points2[[1]] * scale;
                    normal2 = (points2[[-1]] - points2[[1]]) * scale * 3;
					point1 = RotationTransform[{{0, 1}, orientation1}] @ point1;
					normal1 = RotationTransform[{{0, 1}, orientation1}] @ normal1;
					point2 = RotationTransform[{{0, 1}, orientation2}] @ point2;
					normal2 = RotationTransform[{{0, 1}, orientation2}] @ normal2;
					With[{
                        a = VectorSymbol["p", 2], b = VectorSymbol["q", 2],
                        lindep = v == w && TrueQ[Quiet[Chop[Det[{normal1, normal2}]]] == 0]
                    },
						Function[Evaluate @ {If[style1 === style2 || style1 === Automatic || style2 === Automatic,
                            {
                                Arrowheads[{
                                    If[port1["DualQ"], {- arrowSize, .3}, {arrowSize, .3}],
                                    If[port2["DualQ"], {arrowSize, .7}, {- arrowSize, .7}]
                                }],
                                Replace[Replace[style1, Automatic :> Replace[style2, Automatic -> {}]], f_Function :> f[port1]],
                                Arrow @ BSplineCurve[{
                                    a + point1, a + point1 + normal1,
                                    If[lindep, (a + b) / 2 + 2 * RotationTransform[Pi / 2][normal1], Nothing],
                                    b + point2 + normal2, b + point2
                                }]
                            },
                            {
                                If[ style1 === None, {}, {
                                    Arrowheads[{
                                        If[port1["DualQ"], {- arrowSize, .5}, {arrowSize, .5}]
                                    }],
                                    style1,
                                    Arrow @ BSplineCurve[{
                                        a + point1, a + point1 + normal1,
                                        (a + b) / 2 + 2 * RotationTransform[Pi / 2][normal1],
                                        b + point2 + normal2, b + point2
                                    }]
                                }],
                                If[ style2 === None, {}, {
                                    Arrowheads[{
                                        If[port2["DualQ"], {arrowSize, .5}, {- arrowSize, .5}]
                                    }
                                    ],
                                    style2,
                                    Arrow @ BSplineCurve[{
                                        a + point1, a + point1 + normal1,
                                        (a + b) / 2 + 2 * RotationTransform[Pi / 2][normal1],
                                        b + point2 + normal2, b + point2
                                    }]
                                }]
                            }
                        ],
							If[ wireLabelsQ,
                                Text[
                                    Style[ClickToCopy[InterpretationForm[x], x], Black],
                                    If[ lindep,
                                        (a + b) / 2 + 1.25 RotationTransform[Pi / 2][normal1],
                                        (a + point1 + normal1 + b + point2 + normal2) / 2 + .1 normal1
                                    ]
                                ],
                                Nothing
                            ]
						}] /. {a :> #[[1]], b :> #[[-1]]}
					]
				],
				edge : DirectedEdge[v_Integer, _, {{i : 1 | 2, _Integer, p_Integer}, _}] | DirectedEdge[_, v_Integer, {_, {i : 1 | 2, _Integer, p_Integer}}] :> edge -> Block[{
					point, normal, orientation = orientations[v], portCoords = Lookup[embedding, Key[{v, i, p}]],
                    style = diagrams[v]["PortStyles"][[i, p]],
                    diagram = diagrams[v],
                    port, points
				},
                    port = diagram[Replace[i, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[p]];
                    points = diagram["PortArrows"][[i, p]];
                    point = points[[1]] * scale;
                    normal = (points[[-1]] - points[[1]]) * scale * 3;
					point = RotationTransform[{{0, 1}, orientation}] @ point;
					normal = RotationTransform[{{0, 1}, orientation}] @ normal;

					With[{a = VectorSymbol["p", 2], b = VectorSymbol["q", 2]},
						Function[Evaluate @ If[style === None, {}, {
							Arrowheads[If[port["DualQ"], {{-arrowSize, .5}}, {{arrowSize, .5}}]],
                            Replace[style, Automatic -> Nothing],
							Arrow @ BSplineCurve[{a + point, a + point + normal, b + scale Normalize[portCoords - b], b + rad scale Normalize[portCoords - b]}]
						}]] /. With[{s = If[IntegerQ[edge[[1]]], 1, -1]}, {a :> #[[s]], b :> #[[-s]]}]
					]
				],
				_ -> Nothing
			},
			1
		],
		VertexLabels -> (# -> If[wireLabelsQ, Placed[ClickToCopy[InterpretationForm[#], #], Center], None] & /@ spiderVertices),
		BaseStyle -> {FormatType -> StandardForm}
	]
]


DiagramsFreePorts[diagrams : {___Diagram ? DiagramQ}] := Keys @ Select[CountsBy[Catenate[Through[Through[diagrams["Flatten"]]["Ports"]]], #["HoldExpression"] &], EqualTo[1]]


Options[ToDiagramNetwork] = Options[toDiagramNetwork] = Join[{"Unique" -> True}, Options[DiagramNetwork]];

ToDiagramNetwork[d_Diagram, opts : OptionsPattern[]] := If[d["NetworkQ"],
    Diagram[d, Inherited, Inherited, FilterRules[{opts}, Options[Diagram]]]
    ,
    Diagram[d,
        "Expression" :> DiagramNetwork[##],
        "PortFunction" -> $DefaultPortFunction,
        FilterRules[{opts}, Options[Diagram]]
    ] & @@ toDiagramNetwork[If[TrueQ[OptionValue["Arrange"]], d["Arrange", opts], d]["Decompose", "Unary" -> True, "Diagram" -> True], {}, {}, FilterRules[{opts}, Options[toDiagramNetwork]]]
]

toDiagramNetwork[d_Diagram -> None, pos_, ports_, opts : OptionsPattern[]] := Block[{
    portFunction = OptionValue["PortFunction"],
    uniqueQ = TrueQ[OptionValue["Unique"]],
    mports = ports, port
}, {
	Diagram[d,
		"InputPorts" -> MapIndexed[If[#1["NeutralQ"], #1, With[{p = portFunction[PortDual[#1]]},
            PortDual @ If[ KeyExistsQ[mports, p],
                Sow[port = p -> Lookup[mports, p], "Port"];
                mports = DeleteElements[mports, 1 -> {port}];
                port[[2]]
                ,
                Interpretation[p, Evaluate @ If[uniqueQ, Join[pos, {1}, #2], pos]]
            ]]] &,
            d["FlatInputPorts"]
        ],
		"OutputPorts" -> MapIndexed[If[#1["NeutralQ"], #1, With[{p = portFunction[#1]}, If[#1["DualQ"], PortDual, Port] @ Interpretation[p, Evaluate @ If[uniqueQ, Join[pos, {2}, #2], pos]]]] &, d["FlatOutputPorts"]],
        FilterRules[{opts}, Options[Diagram]]
	]
}
]

toDiagramNetwork[CirclePlus[ds___] -> d_, pos_, ports_, opts : OptionsPattern[]] :=
    Catenate @ MapIndexed[toDiagramNetwork[#1, Join[pos, #2], ports, "Unique" -> True, "PortFunction" -> d["PortFunction"], opts] &, {ds}]

toDiagramNetwork[CircleTimes[ds___] -> d_, pos_, ports_, opts : OptionsPattern[]] :=
    Catenate @ FoldPairList[With[{net = Reap[toDiagramNetwork[#2, Append[pos, #1[[1]]], #1[[2]], "Unique" -> True, "PortFunction" -> d["PortFunction"], opts], "Port"]}, {net[[1]], {#1[[1]] + 1, DeleteElements[#1[[2]], 1 -> Catenate[net[[2]]]]}}] &, {1, ports}, {ds}]

toDiagramNetwork[CircleDot[ds__] -> d_, pos_, ports_, opts : OptionsPattern[]] := With[{portFunction = (Replace[$DefaultPortFunction[#], HoldForm[SuperStar[Interpretation[x_, _]] | Interpretation[x_, _]] :> HoldForm[x]] &)},
	Fold[
		{
            DiagramNetwork[##, "PortFunction" -> (#["HoldExpression"] &), FilterRules[{opts}, Options[DiagramNetwork]]] & @@
                Join[#1[[1]]["SubDiagrams"], toDiagramNetwork[#2, Append[pos, #1[[2]]], Join[portFunction[#] -> # & /@ #1[[1]]["FlatOutputPorts"], ports], "PortFunction" -> d["PortFunction"], "Unique" -> True, opts]],
            #1[[2]] - 1
        } &,
		{Diagram[], Length[{ds}]},
		Reverse[{ds}]
	][[1]]["SubDiagrams"]
]

toDiagramNetwork[{ds___} -> d_, pos_, ports_, opts : OptionsPattern[]] := Catenate[toDiagramNetwork[#, pos, ports, "Unique" -> False, "PortFunction" -> d["PortFunction"], opts] & /@ {ds}]

toDiagramNetwork[(Transpose | SuperStar)[diag_, ___] -> d_, pos_, ports_, opts : OptionsPattern[]] := toDiagramNetwork[diag, pos, ports, "Unique" -> True, "PortFunction" -> d["PortFunction"], opts]


portDimension[p_Port] := Replace[p["Type"], {SuperStar[Superscript[_, n_]] | Superscript[_, n_] :> n, _ :> p["Name"]}]


Options[diagramTensor] = {"Kronecker" -> False, "ArrayDot" -> True}

diagramTensor[diagram_Diagram, opts : OptionsPattern[]] := Replace[diagram["HoldExpression"], {
	HoldForm[Diagram[d_]] :> diagramTensor[d, opts]
    ,
	HoldForm[DiagramDual[d_]] :> Conjugate[diagramTensor[d, opts]]
	,
	HoldForm[DiagramFlip[d_]] :> ConjugateTranspose[diagramTensor[d, opts], FindPermutation[Catenate[Reverse @ TakeDrop[Range[diagram["Arity"]], diagram["OutputArity"]]]]]
	,
	HoldForm[DiagramReverse[d_]] :> Transpose[diagramTensor[d, opts], FindPermutation[Join[Reverse @ Range[diagram["OutputArity"]], Reverse[diagram["OutputArity"] + Range[diagram["InputArity"]]]]]]
	,
	HoldForm[DiagramComposition[ds___]] :> If[TrueQ[OptionValue["ArrayDot"]],
        Fold[ArrayDot[If[DiagramQ[#1], diagramTensor[#1, opts], #1], diagramTensor[#2, opts], #2["OutputArity"]] &, {ds}]
        ,
        Dot @@ (
            If[ #["OutputArity"] == #["InputArity"] == 1
                ,
                diagramTensor[#, opts]
                ,
                ArrayReshape[diagramTensor[#, opts], {Times @@ Through[#["OutputPorts"]["Name"]], Times @@ Through[#["InputPorts"]["Name"]]}]
            ] & /@ {ds}
	    )
    ]
	,
	HoldForm[DiagramProduct[ds___]] :> If[TrueQ[OptionValue["Kronecker"]],
        With[{
            tensors = If[ #["OutputArity"] == #["InputArity"] == 1
                ,
                diagramTensor[#, opts]
                ,
                ArrayReshape[diagramTensor[#, opts], {Times @@ Through[#["OutputPorts"]["Name"]], Times @@ Through[#["InputPorts"]["Name"]]}]
            ] & /@ {ds}
        }
        ,
            ArrayReshape[
                KroneckerProduct @@ tensors
                ,
                Join[Catenate[Through[#["OutputPorts"]["Name"]] & /@ {ds}], Catenate[Through[#["InputPorts"]["Name"]] & /@ {ds}]]
            ]
        ]
        ,
        With[{
            tensors = diagramTensor[#, opts] & /@ {ds}
        }
        ,
            If[ AllTrue[tensors, MatchQ[_MatrixSymbol]],
                KroneckerProduct @@ tensors,
                With[{indices = FoldPairList[With[{out = #2["OutputArity"], in = #2["InputArity"]}, {#1 + {Range[out], out + Range[in]}, #1 + out + in}] &, 0, {ds}]}, {perm = FindPermutation[Flatten[Thread[indices]]]},
                    If[perm === Cycles[{}], #, Transpose[#, perm]] &[TensorProduct @@ tensors]
                ]
            ]
        ]
    ]
	,
	HoldForm[DiagramSum[ds___]] :> Plus @@ (diagramTensor[#, opts] & /@ {ds})
	,
	HoldForm[DiagramNetwork[ds___]] :> Block[{
		portFunction = diagram["OptionValue"["PortFunction"]],
		freePorts, ports, contraction, permutation, tensor
	},
		freePorts = Join[portFunction /@ diagram["OutputPorts"], portFunction[#["Dual"]] & /@ diagram["InputPorts"]];
		ports = Catenate @ MapThread[Join, {Map[portFunction, Through[{ds}["OutputPorts"]], {2}], Map[portFunction[#["Dual"]] &, Through[{ds}["InputPorts"]], {2}]}];
		contraction = Values @ Select[PositionIndex[ports], Length[#] > 1 &];
		permutation = FindPermutation[Delete[ports, List /@ Catenate[contraction]], freePorts];
        tensor = TensorContract[
            TensorProduct @@ (diagramTensor[#, opts] & /@ {ds}),
            contraction
        ];
		If[permutation === Cycles[{}], tensor, Transpose[tensor, permutation]]
	]
	,
	_ :>
        Replace[diagram["Expression"], {
            "\[DoubleStruckCapitalI]" :> Enclose @ With[
                {wires = First @ ConfirmMatch[diagram["OptionValue"["Shape"]], "Wires"[_]]},
                {outputPorts = Join[diagram["InputPorts"], diagram["OutputPorts"]][[wires[[All, 2]]]]},
                {tensor = SymbolicIdentityArray[portDimension /@ outputPorts], perm = ConfirmBy[FindPermutation[portDimension /@ Join[outputPorts, outputPorts], portDimension /@ diagram["Ports"]], PermutationCyclesQ]}
                ,
                If[perm === Cycles[{}], tensor, Transpose[tensor, perm]]
            ],
            Interpretation["1", Identity] :> SymbolicIdentityArray[portDimension /@ diagram["OutputPorts"]],
            Interpretation["\[Pi]", perm_Cycles] :> Transpose[SymbolicIdentityArray[portDimension /@ diagram["OutputPorts"]], perm],
            Annotation[expr_, OptionsPattern[{"Domain" -> Sequence[], "Symmetry" -> Sequence[]}]] | expr_ :>
                Switch[diagram["Arity"], 1, VectorSymbol, 2, MatrixSymbol, _, ArraySymbol][expr, portDimension /@ diagram["Ports"], OptionValue["Domain"], OptionValue["Symmetry"]]
        }]
}]

Options[DiagramTensor] = Join[Options[diagramTensor] , Options[DiagramArrange]]

DiagramTensor[diagram_Diagram, opts : OptionsPattern[]] := diagramTensor[DiagramArrange[diagram, FilterRules[{opts}, Options[DiagramArrange]], "Network" -> False], FilterRules[{opts}, Options[diagramTensor]]]


DiagramSplit[diagram_Diagram /; diagram["NodeQ"], n : _Integer | Infinity | - Infinity : Infinity, dualQ : _ ? BooleanQ : True, ___] :=
    diagram["Split", n, dualQ]

DiagramSplit[diagram_Diagram, n : _Integer | Infinity | - Infinity : Infinity, dualQ : _ ? BooleanQ : True, flipQ : _ ? BooleanQ : False] := With[
    {d = diagram["Flatten"], dual = If[dualQ, Identity, PortDual]},
    {outs = d["OutputArity"], ins = d["InputArity"], m = If[n >= 0, Min[d["Arity"], n], Max[d["Arity"] + n, 0]]}
,
	Which[
		m < outs,
        With[{outputs = TakeDrop[d["OutputPorts"], UpTo[m]]},
            DiagramComposition[
                If[ flipQ,
                    Diagram["\[DoubleStruckCapitalI]", Join[d["OutputPorts"], dual /@ outputs[[2]]], outputs[[1]],
                        "Shape" -> "Wires"[Join[Thread[{Range[m], 2 outs - m + Range[m]}], Thread[{m + Range[outs - m], outs + Range[outs - m]}]]], "ShowLabel" -> False
                    ],
                    Diagram["\[DoubleStruckCapitalI]", Join[dual /@ outputs[[2]], d["OutputPorts"]], outputs[[1]],
                        "Shape" -> "Wires"[Join[Thread[{Range[outs - m], outs + Range[outs - m]}], Thread[{outs - m + Range[m], 2 outs - m + Range[m]}]]], "ShowLabel" -> False
                    ]
                ],
                d
            ]
        ],
		m > outs,
        With[{inputs = TakeDrop[Through[d["InputPorts"]["Dual"]], UpTo[m - outs]]},
		    DiagramComposition[
                d,
                If[ flipQ,
                    Diagram["\[DoubleStruckCapitalI]", inputs[[2]], Join[dual /@ inputs[[1]], Through[d["InputPorts"]["Dual"]]],
                        "Shape" -> "Wires"[Join[
                            Thread[{ins - (m - outs) + Range[m - outs], ins + Range[m - outs]}],
                            Thread[{Range[ins - (m - outs)], ins + (m - outs) + Range[ins - (m - outs)]}]
                        ]],
                        "ShowLabel" -> False
                    ],
                    Diagram["\[DoubleStruckCapitalI]", inputs[[2]], Join[Through[d["InputPorts"]["Dual"]], dual /@ inputs[[1]]],
                        "Shape" -> "Wires"[Join[
                            Thread[{Range[ins - (m - outs)], ins + Range[ins - (m - outs)]}],
                            Thread[{ins - (m - outs) + Range[m - outs], 2 ins - (m - outs) + Range[m - outs]}]
                        ]],
                        "ShowLabel" -> False
                    ]
                ]
            ]
        ],
		True,
		d
	]
]


DiagramPermute[diagram_, Cycles[{}], ___] := diagram

DiagramPermute[diagram_ /; diagram["NodeQ"], perm_, dualQ : _ ? BooleanQ : True] := diagram["Permute", perm, dualQ]

DiagramPermute[diagram_Diagram, perm_, dualQ : _ ? BooleanQ : True] := Enclose @ With[{d = diagram["Flatten"]}, {ports = d["Ports", dualQ], newDiagram = DiagramSplit[d, Infinity, dualQ]}, {newPorts = ConfirmBy[Permute[ports, perm], ListQ]},
	If[ ports === newPorts,
		newDiagram,
		DiagramComposition[PermutationDiagram[ports -> newPorts, perm], newDiagram]
	]
]


Options[TensorDiagram] = Options[Diagram]

splitPattern = _Integer | Infinity | -Infinity

TensorDiagram[HoldPattern[VectorSymbol[v_, d_, dom_ : None]], opts : OptionsPattern[]] :=
	Diagram[Annotation[v, "Domain" -> Replace[dom, None -> Sequence[]]], Port[v, Superscript[Replace[dom, None -> Reals], d]], opts]

TensorDiagram[HoldPattern[MatrixSymbol[a_, {m_, n_}, dom_ : None, sym_ : Sequence[]]], opts : OptionsPattern[]] :=
    Diagram[
        Annotation[a, "Domain" -> Replace[dom, None -> Sequence[]], "Symmetry" -> sym],
        Port[Subscript[a, 2], Superscript[Replace[dom, None -> Reals], n]], Port[Subscript[a, 1], Superscript[Replace[dom, None -> Reals], m]],
        opts
    ]

TensorDiagram[HoldPattern[ArraySymbol[a_, ns_List : {}, dom_ : None, sym_ : Sequence[]]], opts : OptionsPattern[]] :=
    Diagram[
        Annotation[a, "Domain" -> Replace[dom, None -> Sequence[]], "Symmetry" -> sym],
        MapIndexed[Port[Subscript[a, Sequence @@ #2], Superscript[Replace[dom, None -> Reals], #1]] &, ns],
        opts
    ]

TensorDiagram[HoldPattern[KroneckerProduct[ts___]], opts : OptionsPattern[]] := DiagramProduct @@ (TensorDiagram[#, opts] & /@ {ts})

TensorDiagram[HoldPattern[TensorProduct[ts___]], opts : OptionsPattern[]] := DiagramProduct @@ (DiagramSplit[TensorDiagram[#, opts], Infinity] & /@ {ts})

TensorDiagramDot[a_, b_, k_] := With[{x = DiagramSplit[a, -k, True, True], y = DiagramSplit[b, k, True, True]},
    DiagramComposition[x, DiagramAssignPorts[y, {Inherited, PortDual /@ x["InputPorts"]}]["Flatten"]]
]

TensorDiagram[HoldPattern[Dot[ts__]], opts : OptionsPattern[]] := Fold[TensorDiagramDot[##, 1] &, TensorDiagram[#, opts] & /@ {ts}]

TensorDiagram[HoldPattern[ArrayDot[a_, b_, k_]], opts : OptionsPattern[]] := TensorDiagramDot[TensorDiagram[a, opts], TensorDiagram[b, opts], k]

TensorDiagram[HoldPattern[Transpose[a_, perm_ : {1, 2}]], opts : OptionsPattern[]] := DiagramPermute[TensorDiagram[a, opts], perm]

TensorDiagram[SymbolicIdentityArray[ns_List], opts : OptionsPattern[]] := Diagram["\[DoubleStruckCapitalI]", Join[#, #] & @ (Interpretation[#, Evaluate[Unique["i"]]] & /@ ns), "Shape" -> "Wires"[Thread[{Range[#], # + Range[#]}] & @ Length[ns]], "ShowLabel" -> False]

TensorDiagram[TensorContract[x_, indices : {{_Integer, _Integer} ...}], opts : OptionsPattern[]] := With[{d = DiagramSplit[TensorDiagram[x, opts], Infinity]}, {perm = FindPermutation[Join[Catenate[indices], Complement[Range[d["OutputArity"]], Catenate[indices]]]]},
    DiagramComposition[RowDiagram[Diagram["\[DoubleStruckCapitalI]", d["OutputPorts"][[#]], {}, "Shape" -> "Wires"[{{1, 2}}], "ShowLabel" -> False] & /@ indices], PermutationDiagram[d["OutputPorts"] -> Permute[d["OutputPorts"], perm], perm], d]
]

TensorDiagram[scalar_, opts : OptionsPattern[]] := Diagram[scalar, {}, {}, FilterRules[{opts}, Options[Diagram]]]



$FunctionPortsType = "Association" | "List" | "Sequence"
$FunctionType = $FunctionPortsType -> $FunctionPortsType

Options[DiagramFunction] = {"Input" -> "Sequence", "Output" -> "List", "Parallel" -> False, "PortFunction" -> Function[#["Name"]]};
 
DiagramFunction[diagram_Diagram, opts : OptionsPattern[]] := Enclose @ Replace[diagram["HoldExpression"], {
	HoldForm[(Diagram | DiagramDual)[d_]] :> DiagramFunction[d, opts]
	,
	HoldForm[DiagramFlip[d_]] :> InverseFunction[DiagramFunction[d, opts]]
	,
	HoldForm[DiagramReverse[d_]] :> Reverse @* DiagramFunction[d, opts] @* Reverse
	,
	HoldForm[DiagramComposition[ds___]] :> Composition @@ (DiagramFunction[#, opts] & /@ {ds})
	,
	HoldForm[DiagramProduct[ds___]] :> With[{args = TakeList[Slot /@ Range[Total[#]], #] & @ Through[{ds}["InputArity"]]},
		Function @@ Switch[OptionValue["Input"], "List" | "Association", Map[Apply[Join]], "Sequence", Map[Apply[Sequence]]][
            If[ TrueQ[OptionValue["Parallel"]],
                WaitAll /@ List @@@
                    Hold @ Evaluate @ Flatten[Hold @@ MapThread[If[Length[#2] == 1, With[{x = #2[[1]]}, Hold[ParallelSubmit[#1[x]]]], Hold[ParallelSubmit[#1 @@ #2]]] &, #]] &,
                List @@@ Hold[Evaluate[Flatten[Hold @@ MapThread[If[Length[#2] == 1, With[{x = #2[[1]]}, Hold[#1[x]]], Hold[#1 @@ #2]] &, #]]]] &
            ] @ {DiagramFunction[#, "Parallel" -> False, opts] & /@ {ds}, args}
        ]
    ]
	,
	HoldForm[DiagramSum[ds___]] :> (DiagramFunction[#, opts] & /@ {ds})
	,
	_ :> Block[{f, type, defType, inputMap, outputMap, finalMap, inputPorts, outputPorts, portFunction = OptionValue["PortFunction"]},
        defType = ConfirmMatch[OptionValue["Input"] -> OptionValue["Output"], $FunctionType];
        {f, type} = Replace[
            diagram["HoldExpression"], {
                HoldForm[anno_Annotation] :> (
                    {
                        Lookup[#, "Function", diagram["HoldExpression"]],
                        Replace[Lookup[#, "Type"], Except[$FunctionType] -> defType]
                    } & @ Options[anno]
                ),
                HoldForm[Interpretation[_, Identity]] -> {Identity, "List" -> "List"},
                HoldForm[Interpretation[_, perm_Cycles]] :> {Permute[#, perm] &, "List" -> "List"},
                _ :> {diagram["HoldExpression"], defType}
            }
		];
        inputPorts = portFunction /@ Through[diagram["InputPorts"]["Dual"]];
        outputPorts = portFunction /@ diagram["OutputPorts"];
		{inputMap, outputMap, finalMap} = Replace[{
            {x_, x_, _} -> Identity,
            {"Association", "List", ports_} :>
                Function[Evaluate[Slot @* Key /@ ports]],
            {"List", "Association", ports_} :>
                Association @@@ Function[Evaluate[MapIndexed[{port, i} |-> port -> Indexed[#, i[[1]]], ports]]],
            {"Association", "Sequence", ports_} :>
                With[{slots = Slot @* Key /@ ports}, Function[Sequence @@ slots]],
            {"Sequence", "Association", ports_} :>
                Association @@@ Function[Evaluate[MapIndexed[{port, i} |-> port -> Slot[i[[1]]], ports]]],
            {"Sequence", "List", ports_} :>
                Function[Evaluate[Slot /@ Range[Length[ports]]]],
            {"List", "Sequence", ports_} :>
                With[{slots = Map[i |-> Indexed[#, i], Range[Length[ports]]]}, Function[Sequence @@ slots]]
        }] /@ {
            {defType[[1]], type[[1]], inputPorts},
            {type[[2]], defType[[2]], outputPorts},
            {defType[[2]], defType[[1]], outputPorts}
        };
        finalMap @* outputMap @* f @* inputMap
	]
}]


End[];

EndPackage[];