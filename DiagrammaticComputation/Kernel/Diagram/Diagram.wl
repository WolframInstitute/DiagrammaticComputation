BeginPackage["Wolfram`DiagrammaticComputation`Diagram`", {
    "Wolfram`DiagrammaticComputation`Utilities`",
    "Wolfram`DiagrammaticComputation`Port`",
    "Wolfram`DiagrammaticComputation`Diagram`Grid`",
    "Wolfram`DiagrammaticComputation`Diagram`Surgery`"
}];

Diagram
DiagramQ

DiagramDual
DiagramFlip
DiagramReverse

DiagramProduct
DiagramSum
DiagramComposition
DiagramRightComposition
DiagramNetwork
ToDiagramNetwork
SingletonDiagram
EmptyDiagram
CapDiagram
CupDiagram
IdentityDiagram
PermutationDiagram
SpiderDiagram
CopyDiagram

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


Begin["Wolfram`DiagrammaticComputation`Diagram`Private`"];


(* ::Subsection:: *)
(* Definitions *)

Diagram::usage = "Diagram[expr] represents a symbolic diagram with input and output ports"

Options[Diagram] := Sort @ DeleteDuplicatesBy[First] @ Join[{"FloatingPorts" -> False}, Options[DiagramGraphics], Options[DiagramGrid], Options[DiagramsNetGraph]];

$DiagramHiddenOptions = {"Expression" -> None, "InputPorts" -> {}, "OutputPorts" -> {}, "DiagramOptions" -> {}};

$DiagramProperties = Sort @ {
    "Properties", "HoldExpression", "ProductQ", "SumQ", "CompositionQ", "NetworkQ", "SubDiagrams",
    "Ports", "PortArrows", "Arity", "FlattenOutputs", "FlattenInputs", "Flatten", "View", "Name", "Tensor", "Function", "Shape",
    "Diagram", "PortGraph", "Graph", "NetGraph", "Grid"
}


$DefaultPortFunction = Function[Replace[HoldForm[Evaluate[#["Apply", #["HoldName"] &]]], HoldForm[x_] :> x, Infinity]]

$DefaultNetworkPortFunction = Function[Replace[#["HoldName"] , HoldForm[x_] :> x, Infinity]]

$DiagramDefaultGraphics = If[#["SingletonNodeQ"], #["Graphics"], #["Grid"]] &

$Gray = RGBColor[0.952941188969422, 0.9529411889694224, 0.9529411889694221]

{$Black, $White, $Gray} = If[$VersionNumber >= 14.3,
    {LightDarkSwitched[Black, White], LightDarkSwitched[White, Black], LightDarkSwitched[$Gray, StandardGray]}, {Black, White, $Gray}]

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

Diagram[d_ ? DiagramQ, {}] := d

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
        {{##}} -> ResourceFunction["LookupPart"][dep, Sequence[##], Automatic] & @@@ pos) /@ deps], _ -> Inherited]] /. Inherited -> def
]


mergeOptions[opts_List] := Normal @ GroupBy[opts, First,
    If[ MatchQ[#[[1, 1]], "PortArrows" | "PortLabels"],
        Map[
            With[{len = Max[If[ListQ[#], Length[#], 1] & /@ #, 1]}, inheritExpresion[#1, {##2}] & @@ (If[ListQ[#], PadRight[#, len, #], #] & /@ #)] &,
            Thread[PadRight[Developer`ToList[#], 2, #] & /@ #[[All, 2]]]
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

Diagram[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[Replace[Normal[Merge[{opts, d["AbsoluteData"]}, List]], head_[k_, {{v_, ___}}] :> head[k, v], 1]]


(* ::Subsubsection:: *)
(* Unary ops *)

Options[DiagramDual] := Join[{"Singleton" -> True}, Options[Diagram]]

DiagramDual[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    d,
    opts,
    Replace[d["HoldExpression"], {
        _[(head : (DiagramSum | DiagramComposition | DiagramProduct | DiagramNetwork))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramDual[#, opts] & /@ {ds})),
        _[DiagramDual[x_Diagram]] :> (Function[Null, "Expression" :> ##, HoldAll] @@ x["HoldExpression"]),
        _[DiagramDual[x_]] :> "Expression" :> x,
        _ :> If[TrueQ[OptionValue["Singleton"]], "Expression" :> DiagramDual[d], Function[Null, "Expression" :> #, HoldAll] @@ d["HoldExpression"]]
    }],
    If[ d["NetworkQ"],
        {
            "InputPorts" -> d["OutputPorts"],
            "OutputPorts" -> d["InputPorts"]
        },
        {
            "OutputPorts" -> Through[d["FlatOutputPorts"]["Dual"]],
            "InputPorts" -> Through[d["FlatInputPorts"]["Dual"]]
        }
    ],
     If[TrueQ[OptionValue["Singleton"]], "Shape" -> Automatic, {}],
    "DiagramOptions" -> d["DiagramOptions"]
]

Options[DiagramFlip] := Join[{"Singleton" -> True}, Options[Diagram]]

DiagramFlip[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    d,
    opts,
    Replace[d["HoldExpression"], {
        _[DiagramComposition[ds___]] :> ("Expression" :> DiagramComposition[##] & @@ Reverse[DiagramFlip[#, opts] & /@ {ds}]),
        _[(head : (DiagramSum | DiagramProduct | DiagramNetwork))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramFlip[#, opts] & /@ {ds})),
        _[DiagramFlip[x_Diagram]] :> (Function[Null, "Expression" :> ##, HoldAll] @@ x["HoldExpression"]),
        _[DiagramFlip[x_]] :> "Expression" :> x,
        _ :> If[TrueQ[OptionValue["Singleton"]], "Expression" :> DiagramFlip[d], Function[Null, "Expression" :> #, HoldAll] @@ d["HoldExpression"]]
    }],
    If[ d["NetworkQ"],
        {
            "InputPorts" -> d["InputPorts"],
            "OutputPorts" -> d["OutputPorts"]
        },
        {
            "OutputPorts" -> d["FlatInputPorts"],
            "InputPorts" -> d["FlatOutputPorts"]
        }
    ],
    "PortArrows" -> Reverse[d["PortStyles", opts]],
    "PortLabels" -> Reverse[d["PortLabels", opts]],
    If[TrueQ[OptionValue["Singleton"]], "Shape" -> Automatic, {}],
    "DiagramOptions" -> d["DiagramOptions"]
]

Options[DiagramReverse] := Join[{"Singleton" -> True}, Options[Diagram]]

DiagramReverse[d_ ? DiagramQ, opts : OptionsPattern[]] := Diagram[
    d,
    opts,
    Replace[d["HoldExpression"], {
        _[DiagramProduct[ds___]] :> ("Expression" :> DiagramProduct[##] & @@ Reverse[DiagramReverse[#, opts] & /@ {ds}]),
        _[(head : (DiagramSum | DiagramComposition | DiagramNetwork))[ds___]] :>
            ("Expression" :> head[##] & @@ (DiagramReverse[#, opts] & /@ {ds})),
        _[DiagramReverse[x_Diagram]] :> (Function[Null, "Expression" :> ##, HoldAll] @@ x["HoldExpression"]),
        _[DiagramReverse[x_]] :> "Expression" :> x,
        _ :> If[TrueQ[OptionValue["Singleton"]], "Expression" :> DiagramReverse[d], Function[Null, "Expression" :> #, HoldAll] @@ d["HoldExpression"]]
    }],
    "OutputPorts" -> Reverse[Through[d["FlatOutputPorts"]["Reverse"]]],
    "InputPorts" -> Reverse[Through[d["FlatInputPorts"]["Reverse"]]],
    "PortArrows" -> (Reverse /@ d["PortStyles", opts]),
    "PortLabels" -> (Reverse /@ d["PortLabels", opts]),
    If[TrueQ[OptionValue["Singleton"]], "Shape" -> Automatic, {}],
    "DiagramOptions" -> d["DiagramOptions"]
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


Options[SingletonDiagram] = Options[EmptyDiagram] = Options[CupDiagram] = Options[CapDiagram] = Options[IdentityDiagram] = Options[PermutationDiagram] = Options[SpiderDiagram] = Options[CopyDiagram] = Options[Diagram]

SingletonDiagram[diagram_Diagram, opts : OptionsPattern[]] := Diagram[diagram, "Expression" :> Diagram[diagram], opts]


makePorts[xs_List] := Function[Null, Port[Unevaluated[##]], HoldAll] @@@ Flatten @* HoldForm /@ Replace[xs, SuperStar[HoldForm[x_]] :> HoldForm[SuperStar[x]], 1]

EmptyDiagram[opts : opts : OptionsPattern[]] := Diagram[
    opts,
    "ShowLabel" -> False,
    "Shape" -> None
]

CupDiagram[{x_, y_}, opts : OptionsPattern[]] := Diagram["\[DoubleStruckCapitalI]", {}, {x, y}, opts, "Shape" -> "Wires"[{{1, 2}}], "ShowLabel" -> False]
CupDiagram[x_, opts : OptionsPattern[]] := CupDiagram[{x, PortDual[x]}, opts]

CapDiagram[{x_, y_}, opts : OptionsPattern[]] := Diagram["\[DoubleStruckCapitalI]", {x, y}, {}, opts, "Shape" -> "Wires"[{{1, 2}}], "ShowLabel" -> False]
CapDiagram[x_, opts : OptionsPattern[]] := CapDiagram[{x, PortDual[x]}, opts]



IdentityDiagram[xs_List -> ys_List, opts : OptionsPattern[]] /; Length[xs] == Length[ys] := With[{in = makePorts[xs], out = makePorts[ys]},
    Diagram[Interpretation["1", Identity], in, out, opts, "Shape" -> "Wires"[Thread[{Range[Length[xs]], Length[xs] + Range[Length[xs]]}]], "ShowLabel" -> False]
]

IdentityDiagram[xs_List, opts : OptionsPattern[]] := IdentityDiagram[xs -> xs, opts]

IdentityDiagram[x_ -> y_, opts : OptionsPattern[]] := IdentityDiagram[{x} -> {y}, opts]

IdentityDiagram[x_, opts : OptionsPattern[]] := IdentityDiagram[{x}, opts]


PermutationDiagram[inputs_List -> outputs_List, ins_List -> outs_List, opts : OptionsPattern[]] := Enclose @ With[
    {len = Min[Length[ins], Length[outs]]},
    {perm = ConfirmBy[FindPermutation[Take[ins, len], Take[outs, len]], PermutationCyclesQ]}
    ,
    PermutationDiagram[inputs, outputs, perm, opts, "Shape" -> "Wires"[Thread[{Range[len], Length[inputs] + Permute[Range[len], InversePermutation[perm]]}]]]
]

PermutationDiagram[outputs_List, opts : OptionsPattern[]] := PermutationDiagram[Sort[outputs] -> outputs, opts]

PermutationDiagram[inputs_List -> outputs_List, opts : OptionsPattern[]] := PermutationDiagram[inputs -> outputs, inputs -> outputs, opts]

PermutationDiagram[inputs_List -> outputs_List, perm_Cycles, opts : OptionsPattern[]] := PermutationDiagram[inputs, outputs, perm, opts]

PermutationDiagram[inputs_List, perm_Cycles, opts : OptionsPattern[]] := PermutationDiagram[inputs, Permute[inputs, perm], perm, opts]

PermutationDiagram[inputs_List, outputs_List, perm_Cycles, opts : OptionsPattern[]] := With[{len = Min[Length[inputs], Length[outputs]]},
    Diagram[Interpretation["\[Pi]", perm], makePorts[inputs], makePorts[outputs], opts, "Shape" -> "Wires"[Thread[{Range[len], Length[inputs] + Permute[Range[len], InversePermutation[perm]]}]], "ShowLabel" -> False]
]


SpiderDiagram[in_List, out_List, opts : OptionsPattern[]] := Diagram["",
    in, out,
    opts,
  	"ShowLabel" -> False,
  	"Shape" -> "Disk",
  	"Width" -> 1 / 2, "Height" -> 1 / 2,
    "FloatingPorts" -> True
]

SpiderDiagram[x : Except[_List], out_, OptionsPattern[]] := SpiderDiagram[{x}, out, opts]

SpiderDiagram[in_, y : Except[_List], OptionsPattern[]] := SpiderDiagram[in, {y}]

SpiderDiagram[x_] := SpiderDiagram[{}, {x}]


CopyDiagram[x_, xs : {__}, opts : OptionsPattern[]] := Diagram["Copy", x, xs, opts, "Shape" -> "Wires"[Thread[{1, Range[2, Length[xs] + 1]}]], "ShowLabel" -> False, "FloatingPorts" -> True]

CopyDiagram[xs : {x_, ___}, opts : OptionsPattern[]] := CopyDiagram[x, xs, opts]

CopyDiagram[x_, n_Integer ? Positive, opts : OptionsPattern[]] := CopyDiagram[x, ConstantArray[x, n], opts]

CopyDiagram[x_, opts : OptionsPattern[]] := CopyDiagram[x, {x, x}, opts]


(* vertical product *)

Options[DiagramComposition] := Join[{"PortFunction" -> $DefaultPortFunction}, Options[Diagram]]

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


Options[DiagramRightComposition] := Options[DiagramComposition]

DiagramRightComposition[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := DiagramComposition[##, opts] & @@ Reverse[{ds}]


(* network of diagrams exposing free ports *)

Options[DiagramNetwork] := DeleteDuplicatesBy[First] @ Join[{"PortFunction" -> $DefaultNetworkPortFunction}, Options[Diagram], Options[DiagramsNetGraph]]
DiagramNetwork[ds___Diagram ? DiagramQ, opts : OptionsPattern[]] := With[{
    subDiagrams = If[#["NetworkQ"], Splice[#["SubDiagrams"]], #] & /@ {ds}
},
    Diagram[
        opts,
        "Expression" :> DiagramNetwork[ds],

        Sequence @@ Block[{graph = DiagramsGraph[subDiagrams, FilterRules[{opts}, Options[DiagramsGraph]]], diagrams = Through[subDiagrams["Flatten"]], freeWires, edges},
            freeWires = Alternatives @@ Cases[Pick[VertexList[graph], VertexDegree[graph], 1], _HoldForm];
            edges = EdgeList[graph];
            Thread[{"InputPorts", "OutputPorts"} ->
                Lookup[GroupBy[Cases[edges, DirectedEdge[freeWires, {diagramId_, i_, portId_}] | DirectedEdge[{diagramId_, i_, portId_}, freeWires] :>
                    diagrams[[diagramId]]["InputOutputPorts"][[i]][[portId]]], #["DualQ"] &], {True, False}, {}]
            ]
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

DiagramProp[d_, "AbsoluteData"] := MapAt[
    Replace[#, {_[k : "PortArrows" | "PortLabels", v_] :> (k -> fillAutomatic[d["OptionValue"[k]], {d["InputArity"], d["OutputArity"]}, Automatic])}, 1] &,
    d["Data"],
    Key["DiagramOptions"]
]

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

DiagramProp[d_, "SingletonNodeQ"] := d["NodeQ"] || MatchQ[d["HoldExpression"], HoldForm[Evaluate @ $DiagramHeadPattern[diag_Diagram]] /; diag["SingletonNodeQ"]]

DiagramProp[d_, "Node"] := Replace[d["HoldExpression"], {HoldForm[Evaluate @ $DiagramHeadPattern[diag_Diagram]] :> diag["Node"], _ :> d}]

DiagramProp[d_, "Dual", opts___] := DiagramDual[d, opts]

DiagramProp[d_, "Flip", opts___] := DiagramFlip[d, opts]

DiagramProp[d_, "Reverse", opts___] := DiagramReverse[d, opts]

DiagramProp[d_, "Head"] := Replace[d["HoldExpression"], {
    With[{headPatt = $DiagramHeadPattern}, HoldForm[(head : headPatt)[___]] :> head],
    _ -> None
}]

DiagramProp[d_, "SubDiagrams"] := Replace[d["HoldExpression"], {
    With[{headPatt = $DiagramHeadPattern}, HoldForm[headPatt[ds___]] :> {ds}],
    _ -> {}
}]

DiagramProp[d_, "SubDiagrams", n : _Integer | Infinity : 1] := FixedPoint[Catenate @* Map[Replace[#["SubDiagrams"], {} :> {#}] &], {d}, n]

DiagramProp[d_, "TopPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ d["InputPorts", False]

DiagramProp[d_, "BottomPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ d["OutputPorts", False]

DiagramProp[d_, "NeutralPorts", dualQ : _ ? BooleanQ : False] := Select[
    Join[d["OutputPorts", True], If[dualQ, PortDual, Identity] /@ d["InputPorts", True]],
    #["NeutralQ"] &
]

DiagramProp[d_, "LeftPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ Select[d["InputPorts", True], #["NeutralQ"] &]

DiagramProp[d_, "RightPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ Select[d["OutputPorts", True], #["NeutralQ"] &]

DiagramProp[d_, "InputOutputPorts", dualQ : _ ? BooleanQ : False, neutralQ : _ ? BooleanQ : True] := {If[dualQ, PortDual, Identity] /@ d["InputPorts", neutralQ], d["OutputPorts", neutralQ]}

DiagramProp[d_, "Ports", dualQ : _ ? BooleanQ : False, neutralQ : _ ? BooleanQ : True] := Join[d["OutputPorts", neutralQ], If[dualQ, PortDual, Identity] /@ d["InputPorts", neutralQ]]

DiagramProp[d_, "GraphInputOutputPorts", dualQ : _ ? BooleanQ : False] := Block[{diagrams = d["SubDiagrams", Infinity], graph = d["Graph"], edges, freeWires},
    edges = EdgeList[graph];
    freeWires = Alternatives @@ Cases[Pick[VertexList[graph], VertexDegree[graph], 1], _HoldForm];
    {
        If[dualQ, PortDual, Identity] /@ Cases[edges, DirectedEdge[freeWires, {diagramId_, 1, portId_}] :> diagrams[[diagramId]]["InputPorts"][[portId]]],
        Cases[edges, DirectedEdge[{diagramId_, 2, portId_}, freeWires] :> diagrams[[diagramId]]["OutputPorts"][[portId]]]
    }
]

DiagramProp[d_, "GraphInputPorts", dualQ : _ ? BooleanQ : False] := d["GraphInputOutputPorts", dualQ][[1]]

DiagramProp[d_, "GraphOutputPorts", dualQ : _ ? BooleanQ : False] := If[dualQ, PortDual, Identity] /@ d["GraphInputOutputPorts", False][[2]]

DiagramProp[d_, "SubInputPorts", n : _Integer | Infinity : 1] := Flatten[Through[d["SubDiagrams", n]["InputPorts"]]]

DiagramProp[d_, "SubOutputPorts", n : _Integer | Infinity : 1] := Flatten[Through[d["SubDiagrams", n]["OutputPorts"]]]

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

flatPorts[xs_List, args___] := Discard[If[Length[#] == 1, First[#], PortSum @@ (PortProduct @@ Discard[flatPorts[{#}, args], EmptyPortQ] & /@ #)] & @ #["SumList"] & /@ Catenate[Through[xs["ProductList", args]]], EmptyPortQ]

DiagramProp[d_, "Flat"[params__], args___] := flatPorts[d[params], args]

DiagramProp[d_, "FlatInputPorts", args___] := d["Flat"["InputPorts"], args]

DiagramProp[d_, "FlatOutputPorts", args___] := d["Flat"["OutputPorts"], args]

DiagramProp[d_, "FlattenOutputs", args___] := With[{newPorts = d["FlatOutputPorts", args]},
    Diagram[d, "OutputPorts" -> newPorts, If[Length[newPorts] == d["OutputArity"], {}, "PortArrows" -> ({#1, Catenate @ MapThread[ConstantArray[#2, Length[#1]] &, {Through[d["OutputPorts"]["ProductList", args]], #2}]} & @@ d["PortStyles"])]]
]

DiagramProp[d_, "FlattenInputs", args___] :=  With[{newPorts = d["FlatInputPorts", args]},
    Diagram[d, "InputPorts" -> newPorts, If[Length[newPorts] == d["InputArity"], {}, "PortArrows" -> ({Catenate @ MapThread[ConstantArray[#2, Length[#1]] &, {Through[d["InputPorts"]["ProductList", args]], #1}], #2} & @@ d["PortStyles"])]]
]

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

DiagramProp[diagram_, "Label"] := Replace[diagram["HoldExpression"], expr_ :> (expr //. d_Diagram ? DiagramQ :> RuleCondition[d["HoldExpression"]])]

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

DiagramProp[d_, "PortFunction"] := Lookup[d["DiagramOptions"], "PortFunction", If[d["NetworkQ"], $DefaultNetworkPortFunction, $DefaultPortFunction]]

DiagramProp[d_, "PortGraph", opts : OptionsPattern[]] := DiagramsPortGraph[d["SubDiagrams"], opts]

DiagramProp[d_, "Graph", opts : OptionsPattern[]] := DiagramsGraph[d["SubDiagrams", Infinity], opts, "PortFunction" -> d["PortFunction"]]

DiagramProp[d_, "Network", opts : OptionsPattern[]] := ToDiagramNetwork[d, FilterRules[{opts}, Options[ToDiagramNetwork]]]

DiagramProp[d_, "NetGraph", opts : OptionsPattern[]] := DiagramsNetGraph[d["Network"]["SubDiagrams"], FilterRules[{opts, d["DiagramOptions"]}, Options[DiagramsNetGraph]]]

DiagramProp[d_, "Arrange", opts : OptionsPattern[]] := DiagramArrange[d, opts]

DiagramProp[d_, "Grid", opts : OptionsPattern[]] := DiagramGrid[d, opts]

DiagramProp[d_, "OptionValue"[opt_], opts : OptionsPattern[]] := OptionValue[{opts, d["DiagramOptions"], Options[DiagramGraphics], Options[DiagramGrid], Options[DiagramsNetGraph]}, opt]

DiagramProp[d_, "Center", opts : OptionsPattern[]] := Replace[d["OptionValue"["Center"], opts], Automatic -> {0, 0}]

DiagramProp[d_, "Width", opts : OptionsPattern[]] := Replace[d["OptionValue"["Width"], opts], Automatic :> If[d["SingletonNodeQ"], 1, DiagramGridWidth[d]]]

DiagramProp[d_, "Height", opts : OptionsPattern[]] := Replace[d["OptionValue"["Height"], opts], Automatic :> If[d["SingletonNodeQ"], 1, DiagramGridHeight[d]]]

DiagramProp[d_, "WireQ"] := MatchQ[d["OptionValue"["Shape"]], "Wire" | "Wires" | "Wires"[_]]

DiagramProp[d_, "Shape", opts : OptionsPattern[]] := Enclose @ Block[{
    w, h, c, a,
    func,
    transform, primitives,
    node = d["Node"]
},
    w = Replace[d["OptionValue"["Width"], opts], Automatic -> 1];
    h = Replace[d["OptionValue"["Height"], opts], Automatic -> 1];
    c = Replace[d["Center", opts], _Offset -> {0, 0}];
    a = d["OptionValue"["Angle"], opts];
    func = d["OptionValue"["PortFunction"], opts];
    transform = Evaluate[GeometricTransformation[#, RotationTransform[a, c] @* If[d["FlipQ"], ReflectionTransform[{0, 1}, c], Identity] @* If[d["ReverseQ"], ReflectionTransform[{1, 0}, c], Identity]]] &;
    primitives = Replace[
        node["OptionValue"["Shape"], opts],
        {
            None -> {},
            Automatic | dir_Directive :> {dir, transform @ Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c]},
            "RoundedRectangle" :> transform @ Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c, RoundingRadius -> {{Right, Bottom} -> .1 (w + h)}],
            "RoundRectangle" :> transform @ Rectangle[{- w / 2, - h / 2} + c, {w / 2 , h / 2} + c, RoundingRadius -> .1 (w + h)],
            "UpsideDownTriangle" :> transform @ Polygon[{{- w / 2, h / 2}, {0, - h / 2}, {w / 2, h / 2}} + Threaded[c]],
            "Triangle" :> transform @ Polygon[{{- w / 2, - h / 2}, {0, h / 2}, {w / 2, - h / 2}} + Threaded[c]],
            "Circle" :> transform @ Circle[c, {w, h} / 2],
            "Disk" :> transform @ Disk[c, {w, h} / 2],
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
                points = node["PortArrows", opts],
                inputs = PositionIndex[func /@ Through[node["InputPorts"]["Dual"]]],
                outputs = PositionIndex[func /@ node["OutputPorts"]]
            },
                Map[
                    ps |-> BSplineCurve[{ps[[1, 1]], 2 * ps[[1, 1]] - ps[[1, 2]], If[Length[ps] == 2, Nothing, c], 2 * #[[1]] - #[[2]], #[[1]]}] & /@ Rest[ps],
                    Values @ Merge[KeyUnion[{inputs, outputs}, {} &], Apply[Join[points[[1, #1]], points[[2, #2]]] &]]
                ]
            ],
            "Wires"[wires_] :> With[{
                ports = Join @@ node["InputOutputPorts"],
                ps = Catenate[node["PortArrows", opts, d["DiagramOptions"]]],
                styles = Catenate[node["PortStyles", opts, d["DiagramOptions"]]]
            },
                With[{p = ps[[First[#]]], style = Replace[SelectFirst[styles[[#]], ! MatchQ[#, Automatic | True | _Function] &, Nothing], None -> Nothing], dual = ports[[First[#]]]["DualQ"]},
                    {style, BSplineCurve[If[dual, Identity, Reverse] @ {p[[1]], 2 * p[[1]] - p[[2]], 2 * #[[1]] - #[[2]], #[[1]]}] & /@ DeleteCases[None] @ ps[[Rest[#]]]}
                ] & /@ wires // If[d["FlipQ"], GeometricTransformation[#, RotationTransform[2 a, c] @* ReflectionTransform[{0, 1}, c]] &, Identity]
            ],
            "Wire" :> With[{
                ps = Catenate[node["PortArrows", opts]]
            },
                BSplineCurve[{ps[[1, 1]], 2 * ps[[1, 1]] - ps[[1, 2]], c, 2 * #[[1]] - #[[2]], #[[1]]}] & /@ Rest[ps]
            ],
            "Point" :> {PointSize[Medium], Point[c]},
            f_Function :> f[d],
            shape_ :> transform @ GeometricTransformation[shape, TranslationTransform[c]]
        }
    ];
    If[ MatchQ[d["OptionValue"["Outline"], opts], Automatic | True],
        primitives = {primitives, EdgeForm[Directive[Dashed, $Black]], FaceForm[None], transform[Rectangle[{c[[1]]- w / 2, c[[2]] - h / 2}, {c[[1]] + w / 2, c[[2]] + h / 2}]]},
        primitives
    ]
]

DiagramProp[d_, "PortArrows", opts : OptionsPattern[]] := Block[{
    w = d["Width", opts],
    h = d["Height", opts],
    c = Replace[d["Center", opts], _Offset -> {0, 0}],
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
                    "Circle" | "Disk" :> With[{p = {w Cos[#1], h Sin[#1]}}, {c + p / 2, c + p / 2 + Normalize[p] / 4}],
                    "Point" :> With[{p = {w Cos[#1], h Sin[#1]}}, {c, c + Normalize[p]}],
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
                    "Circle" | "Disk" :> With[{p = {w Cos[#1], h Sin[#1]}}, {c + p / 2, c + p / 2 + Normalize[p] / 4}],
                    "Point" :> With[{p = {w Cos[#1], h Sin[#1]}}, {c, c + Normalize[p]}],
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
    Replace[fillAutomatic[d["OptionValue"["PortArrows"], opts], {d["InputArity"], d["OutputArity"]}, Automatic], {Placed[x_, _] :> Replace[x, True -> Automatic], True -> Automatic}, {2}]

DiagramProp[d_, "PortLabels", opts : OptionsPattern[]] :=
    Replace[fillAutomatic[d["OptionValue"["PortLabels"], opts], {d["InputArity"], d["OutputArity"]}, Automatic], {Placed[x_, pos_] :> Placed[Replace[x, True -> Automatic], pos], True -> Automatic}, {2}]


DiagramProp[_, prop_] := Missing[prop]


(* ::Subsection:: *)
(* Formatting *)

$DefaultPortLabelFunction = Function[If[TrueQ[$PlotInteractivity], ClickToCopy, #1 &][#2 /. Automatic :> If[#1["DualQ"], #1["Dual"], #1], #1["View"]]]

Options[DiagramGraphics] = Join[{
    "Shape" -> Automatic,
    "Center" -> Automatic,
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
    "PortsFirst" -> True,
    "Outline" -> None,
    "Style" -> Automatic
}, Options[Graphics]];

DiagramGraphics[diagram_ ? DiagramQ, opts : OptionsPattern[]] := Enclose @ With[{
    points = diagram["PortArrows", opts],
    arities = {diagram["InputArity"], diagram["OutputArity"]},
    center = diagram["Center", opts],
    shape = diagram["OptionValue"["Shape"], opts],
    style = Replace[diagram["OptionValue"["Style"], opts], {Automatic -> Directive[EdgeForm[$Black], FaceForm[$Gray]], None -> Nothing}],
    interactiveQ = Replace[OptionValue[PlotInteractivity], Automatic -> True]
}, {
    portArrows = diagram["PortStyles", opts],
    portLabels = diagram["PortLabels", opts],
    labelFunction = diagram["OptionValue"["LabelFunction"], opts],
    portArrowFunction = Replace[diagram["OptionValue"["PortArrowFunction"], opts], Automatic -> (Arrow[If[#1["DualQ"], Reverse, Identity] @ #2] &)],
    portLabelFunction = Replace[diagram["OptionValue"["PortLabelFunction"], opts], Automatic -> $DefaultPortLabelFunction]
}, Graphics[If[TrueQ["PortsFirst"], Identity, Permute[#, Cycles[{{2, 3}}]] &] @ {
    Arrowheads @ If[shape === "Point", {{Small, .7}}, Small],
    MapThread[{ports, ps, arrows, labels, dir} |->
        MapThread[{x, p, arrow, label} |-> {
            If[ MatchQ[arrow, None | False],
                Nothing,
                {Replace[arrow, True | Automatic | _Function -> Nothing], Replace[portArrowFunction[x, p, dir], True | Automatic | Inherited :> Arrow[If[x["DualQ"], Reverse, Identity][p]]]}
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
    ],
    {
        style,
        Confirm @ diagram["Shape", opts]
    },
    Replace[
        If[ MatchQ[diagram["OptionValue"["ShowLabel"], opts], None | False],
            "\t\t\t",
            Replace[labelFunction,
                Automatic :> Function[If[interactiveQ, ClickToCopy, # &][
                    #["Label"],
                    #["View"]
                ]]
            ] @ diagram
        ],
        {
            Placed[l_, Offset[offset_]] :> Text[l, center + offset],
            Placed[l_, pos_] :> Text[l, pos],
            label_ :> Text[label, center]
        }
    ]
},
    FilterRules[{opts, diagram["DiagramOptions"]}, Options[Graphics]],
    ImageSize -> Tiny,
    FormatType -> StandardForm
]]

Diagram /: MakeBoxes[diagram : Diagram[_Association] ? DiagramQ, form_] := With[{boxes = ToBoxes[Show[
    If[diagram["NetworkQ"], diagram["NetGraph"], Replace[$DiagramDefaultGraphics, {"Grid" :> diagram["Grid"], f_Function :> f[diagram], _ :> diagram["Graphics"]}]], BaseStyle -> {GraphicsHighlightColor -> Magenta}], form]},
    diagramBox[boxes, #] & @ diagram
]


SetAttributes[diagramBox, HoldAllComplete];
diagramBox[GraphicsBox[box_, opts___], d_] := GraphicsBox[
	NamespaceBox["Diagram", DynamicModuleBox[{Typeset`d = HoldComplete[d]}, box]],
	opts
]

diagramBox[_, d_] := ToBoxes[d, TraditionalForm]


DiagramBoxQ[HoldPattern[GraphicsBox[NamespaceBox["Diagram", _, ___], ___]]] := True

DiagramBoxQ[___] := False


FromGraphicsBox[HoldPattern[GraphicsBox[NamespaceBox["Diagram", DynamicModuleBox[vars_, ___], ___], ___]], _] := Module[vars, Typeset`d]

Unprotect[GraphicsBox, Graphics3DBox]
Scan[head |->
    With[{lhs = HoldPattern[MakeExpression[g_head ? DiagramBoxQ, fmt_]]},
        If[	!KeyExistsQ[FormatValues[head], lhs],
            PrependTo[
                FormatValues[head],
                lhs :> FromGraphicsBox[g, fmt]
            ]
        ]
    ],
    {GraphicsBox, Graphics3DBox}
]
Protect[GraphicsBox, Graphics3DBox]

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
    {net, v} |-> Block[{d = AnnotationValue[{net, v}, "Diagram"], wires, out, in, ports, dPorts, portWires, portFunction},
        (wires = If[MatchQ[#, "Wires"[_]], First[#], {}]) & @ d["OptionValue"["Shape"]];
        (* portFunction = d["PortFunction"]; *)
        If[wires === {}, Return[net, Block]];
        in = EdgeList[net, DirectedEdge[_, v]];
        out = EdgeList[net, DirectedEdge[v, _]];
        ports = Join[SortBy[in, #[[1, 3]] &], SortBy[out, #[[2, 3]] &]];
        (* dPorts = Join[portFunction /@ PortDual /@ d["InputPorts"], portFunction /@ d["OutputPorts"]]; *)
        portWires = DeleteCases[{{_, _, {}}, {_, _, {}}}] @ Map[
            With[{ps = ports[[#]]},
                Replace[
                    ps,
                    DirectedEdge[port_List, _] | DirectedEdge[_, port_List] :> ({port, #, DeleteCases[AdjacencyList[net, #, 1], port]} & @ FirstCase[AdjacencyList[net, port, 1], _HoldForm]),
                    1
                ]
            ] &,
            wires
        ];
        If[ Length[portWires] == Length[wires],
            VertexReplace[
                VertexDelete[
                    net, 
                    Append[v] @ Catenate[portWires[[All, All, 1]]]
                ],
                First @ Solve[Equal @@@ portWires[[All, All, 2]]]
            ],
            net
        ]
    ],
    g,
    VertexList[g, _Integer]
]


untagPort[p_Port] := Function[Null, Port[p, "Expression" :> #], HoldFirst] @@ Replace[p["HoldExpression"], {
    HoldForm[Interpretation[x_, tag_ -> _]] :> HoldForm[Interpretation[x, tag]],
    HoldForm[PortDual[Interpretation[x_, tag_ -> _]]] :> HoldForm[PortDual[Interpretation[x, tag]]],
    HoldForm[Interpretation[x_, _]] :> HoldForm[x],
    HoldForm[PortDual[Interpretation[x_, _]]] :> HoldForm[PortDual[x]]
}]

restorePorts[d_Diagram] := DiagramAssignPorts[d, {untagPort /@ d["InputPorts"], untagPort /@ d["OutputPorts"]}]

toIdentities[ds : {__Diagram}] := Map[
	Replace[#["HoldExpression"],
		{
			_[Interpretation["\[Pi]", cycles_Cycles]] :> Splice[IdentityDiagram /@ Thread[PortDual /@ #["InputPorts"] -> Permute[#["OutputPorts"], cycles]]],
			_ -> #
		}
	] &,
	ds
]

Options[SimplifyDiagram] = Options[DiagramsNetGraph]

SimplifyDiagram[diag_ ? DiagramQ, opts : OptionsPattern[]] /; diag["NetworkQ"] := Block[{
    portFunction = diag["PortFunction"],
	net,
    in = PortDual /@ diag["InputPorts"],
    out = diag["OutputPorts"]
},
    net = DiagramsNetGraph[
        diag["Graph", "Simplify" -> True, "PortFunction" -> portFunction],
        FilterRules[{opts}, Options[DiagramsNetGraph]],
        "PortFunction" -> portFunction, "UnarySpiders" -> False, "BinarySpiders" -> False
    ];
    DiagramNetwork[##, diag["DiagramOptions"], "PortFunction" -> portFunction] & @@ toIdentities @ AnnotationValue[{net, VertexList[net]}, "Diagram"]
]

SimplifyDiagram[diag_ ? DiagramQ, opts : OptionsPattern[]] := With[{
    d = restorePorts @ restorePorts @ DiagramArrange[SimplifyDiagram[diag["Network"], opts], "PortFunction" -> diag["PortFunction"], "AssignPorts" -> True],
    portFunction = $DefaultPortFunction,
    in = PortDual /@ diag["InputPorts"],
    out = diag["OutputPorts"]
},
    Which[
        portFunction /@ PortDual /@ d["InputPorts"] === portFunction /@ in && portFunction /@ d["OutputPorts"] === portFunction /@ out,
        d,
        d["InputArity"] == Length[in] && d["OutputArity"] == Length[out],
        Diagram[SingletonDiagram[d], in, out],
        True,
        DiagramNetwork[SingletonDiagram[Diagram[d]], "ShowWireLabels" -> False]
    ]
]


Options[DiagramsGraph] = Join[{"Simplify" -> False, "PortFunction" -> $DefaultNetworkPortFunction}, Options[Graph]];
DiagramsGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] := Block[{
    ports = Thread[{Through[#["InputPorts"]], Through[#["OutputPorts"]]}] & @ Through[diagrams["Flatten"]], indexedPorts,
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
                With[{diagram = #2[[1]], port = #2, wire = portFunction[If[#2[[2]] == 1, PortDual[#1], #1]]},
                    Switch[port[[2]],
                        1, {DirectedEdge[port, diagram], If[#1["DualQ"], Identity, Reverse] @ DirectedEdge[wire, port]},
                        2, {DirectedEdge[diagram, port], If[#1["DualQ"], Reverse, Identity] @ DirectedEdge[port, wire]}
                    ]
                ] &,
                ports,
                {3}
            ],
            3
        ],
        VertexLabels -> MapAt[Placed[#, Center] &, {All, 2}] @ Join[
            {_ -> Automatic},
            Thread[Range[Length[diagrams]] -> (#["HoldExpression"] & /@ diagrams)],
            Flatten[MapIndexed[#2 -> If[#1["DualQ"], #1["Dual"], #1]["Label"] &, ports, {3}], 2]
        ],
        VertexSize -> {_ -> Medium, _Integer -> Large, {__Integer} -> Medium},
        VertexShapeFunction -> {_ -> "Diamond", _Integer -> "Square", {__Integer} -> "Circle"},
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



findNodeCycle[g_] := Block[{vs = VertexList[g], diagrams = AssociationThread[VertexList[g], AnnotationValue[{g, VertexList[g]}, "Diagram"]], node},
    node = SelectFirst[
        Pick[vs, VertexInDegree[g], 0],
        Lookup[diagrams, Key[#], False, #["InputArity"] > 0 && #["OutputArity"] > 0 &] &
    ];
    If[! MissingQ[node], Return[EdgeList[g, DirectedEdge[node, _, _]]]];

    node = SelectFirst[
        Pick[vs, VertexOutDegree[g], 0],
        Lookup[diagrams, Key[#], False, #["InputArity"] > 0 && #["OutputArity"] > 0 &] &
    ];

    If[! MissingQ[node], EdgeList[g, DirectedEdge[_, node, _]], Missing[]]
]

Options[RemoveDiagramsNetGraphCycles] = Join[{"LoopDiagrams" -> True, "NodeCycles" -> False}, Options[Graph]]

RemoveDiagramsNetGraphCycles[g_ ? DirectedGraphQ, opts : OptionsPattern[]] := Enclose @ Block[{
    net = g, diagrams, cycle, id, edge, cups = {}, caps = {}, cupDiagrams = {}, capDiagrams = {}, cup, cap,
    nodeCyclesQ = TrueQ[OptionValue["NodeCycles"]],
    newSrcPort, newTgtPort
},
    
    If[ TrueQ[OptionValue["LoopDiagrams"]] || ! LoopFreeGraphQ[g],
    
        diagrams = AssociationThread[VertexList[g], AnnotationValue[{g, VertexList[g]}, "Diagram"]];
        id = Max[VertexList[g, _Integer], 0] + 1;

        While[
            ! MissingQ[
                cycle = First[
                    FindCycle[net, Infinity, 1],
                    FirstCase[
                        EdgeList[net],
                        e : _[x_, x_, ___] :> {e},
                        If[nodeCyclesQ, nodeCyclesQ = False; findNodeCycle[net], Missing[]]
                    ]
                ]
            ],
            edge = cycle[[1]];
            With[{
                src = Lookup[diagrams, edge[[1]]],
                tgt = Lookup[diagrams, edge[[2]]],
                srcSide = If[edge[[3, 1, 1]] == 1, "InputPorts", "OutputPorts"],
                tgtSide = If[edge[[3, -1, 1]] == 1, "InputPorts", "OutputPorts"],
                i = edge[[3, 1, 3]],
                j = edge[[3, -1, 3]],
                n = edge[[3, 1, 2]],
                m = edge[[3, -1, 2]]
            },
            {
                srcPort = src[srcSide][[i]],
                tgtPort = tgt[tgtSide][[j]]
            },
                Switch[edge,
                    _[_, _, {{1, _, _}, ___, {2, _, _}}],
                        AppendTo[cups, cup = id++];
                        AppendTo[caps, cap = id++];

                        newSrcPort = Port @ srcPort["Apply", tag[#["HoldName"], cup] &];
                        newTgtPort = Port @ tgtPort["Apply", tag[#["HoldName"], cap] &];

                        diagrams[edge[[1]]] = Diagram[src, srcSide -> ReplacePart[src[srcSide], i -> newSrcPort]];
                        diagrams[edge[[2]]] = Diagram[If[edge[[1]] === edge[[2]], diagrams[edge[[1]]], tgt], tgtSide -> ReplacePart[tgt[tgtSide], j -> newTgtPort]];

                        net = EdgeDelete[net, {edge}];
                        net = VertexAdd[net, {cap, cup}];


                        If[ i <= n / 2 && j <= m / 2,
                            AppendTo[diagrams, cup -> CupDiagram[{PortDual[srcPort], PortDual[newTgtPort]}]];
                            AppendTo[diagrams, cap -> CapDiagram[{tgtPort, newSrcPort}]];

                            
                            net = EdgeAdd[net, {
                                DirectedEdge[edge[[1]], cap, {edge[[3, 1]], {1, 2, 2}}],
                                DirectedEdge[cup, cap, {{2, 2, 1}, {1, 2, 1}}],
                                DirectedEdge[cup, edge[[2]], {{2, 2, 2}, edge[[3, -1]]}]
                            }]
                            ,
                            AppendTo[diagrams, cup -> CupDiagram[{PortDual[newTgtPort], PortDual[srcPort]}]];
                            AppendTo[diagrams, cap -> CapDiagram[{newSrcPort, tgtPort}]];

                            
                            net = EdgeAdd[net, {
                                DirectedEdge[edge[[1]], cap, {edge[[3, 1]], {1, 2, 1}}],
                                DirectedEdge[cup, cap, {{2, 2, 2}, {1, 2, 2}}],
                                DirectedEdge[cup, edge[[2]], {{2, 2, 1}, edge[[3, -1]]}]
                            }]
                        ]
                    ,
                    _[_, _, {{2, _, _}, ___, {1, _, _}}],
                        AppendTo[cups, cup = id++];
                        AppendTo[caps, cap = id++];

                        newSrcPort = Port @ srcPort["Apply", tag[#["HoldName"], cap] &];
                        newTgtPort = Port @ tgtPort["Apply", tag[#["HoldName"], cup] &];

                        diagrams[edge[[1]]] = Diagram[src, srcSide -> ReplacePart[src[srcSide], i -> newSrcPort]];
                        diagrams[edge[[2]]] = Diagram[If[edge[[1]] === edge[[2]], diagrams[edge[[1]]], tgt], tgtSide -> ReplacePart[tgt[tgtSide], j -> newTgtPort]];

                        net = EdgeDelete[net, {edge}];
                        net = VertexAdd[net, {cap, cup}];  

                        If[ i <= n / 2 && j <= m / 2,
                            AppendTo[diagrams, cup -> CupDiagram[{PortDual[srcPort], PortDual[newTgtPort]}]];
                            AppendTo[diagrams, cap -> CapDiagram[{tgtPort, newSrcPort}]];
                            
                            net = EdgeAdd[net, {
                                DirectedEdge[edge[[1]], cap, {edge[[3, 1]], {1, 2, 2}}],
                                DirectedEdge[cup, cap, {{2, 2, 1}, {1, 2, 1}}],
                                DirectedEdge[cup, edge[[2]], {{2, 2, 2}, edge[[3, -1]]}]
                            }]
                            ,
                            AppendTo[diagrams, cup -> CupDiagram[{PortDual[newTgtPort], PortDual[srcPort]}]];
                            AppendTo[diagrams, cap -> CapDiagram[{newSrcPort, tgtPort}]];
                            
                            net = EdgeAdd[net, {
                                DirectedEdge[edge[[1]], cap, {edge[[3, 1]], {1, 2, 1}}],
                                DirectedEdge[cup, cap, {{2, 2, 2}, {1, 2, 2}}],
                                DirectedEdge[cup, edge[[2]], {{2, 2, 1}, edge[[3, -1]]}]
                            }]
                        ]
                    , 
                    _[_, _, {{1, _, _}, ___, {1, _, _}}],
                        AppendTo[cups, cup = id++];

                        newSrcPort = Port @ srcPort["Apply", tag[#["HoldName"], cup] &];
                       
                        diagrams[edge[[1]]] = Diagram[src, srcSide -> ReplacePart[src[srcSide], i -> newSrcPort]];

                        AppendTo[diagrams, cup -> CupDiagram[{PortDual[newSrcPort], PortDual[tgtPort]}]];

                        net = EdgeDelete[net, {edge}];
                        net = VertexAdd[net, cup];
                        net = EdgeAdd[net, {
                            DirectedEdge[cup, edge[[1]], {{2, 2, 1}, edge[[3, 1]]}],
                            DirectedEdge[cup, edge[[2]], {{2, 2, 2}, edge[[3, -1]]}]
                        }]
                    ,
                    _[_, _, {{2, _, _}, ___, {2, _, _}}],
                        AppendTo[caps, cap = id++];

                        newTgtPort = Port @ tgtPort["Apply", tag[#["HoldName"], cap] &];
                        
                        diagrams[edge[[2]]] = Diagram[tgt, tgtSide -> ReplacePart[tgt[tgtSide], j -> newTgtPort]];

                        AppendTo[diagrams, cap -> CapDiagram[{srcPort, newTgtPort}]];

                        net = EdgeDelete[net, {edge}];
                        net = VertexAdd[net, cap];
                        net = EdgeAdd[net, {
                            DirectedEdge[edge[[1]], cap, {edge[[3, 1]], {1, 2, 1}}],
                            DirectedEdge[edge[[2]], cap, {edge[[3, -1]], {1, 2, 2}}]
                        }]
                ]
            ]
        ];
        Graph[net,
            FilterRules[{opts}, Options[Graph]],
            AnnotationRules -> Join[
                KeyValueMap[#1 -> {"Diagram" -> #2} &, diagrams]
            ]
        ]
    ,
        While[
            ! MissingQ[cycle = First[FindCycle[net, Infinity, 1], Missing[]]],
            edge = FirstCase[cycle, _[_, _, {{1, _, _}, __}], cycle[[-1]]];
            net = EdgeAdd[EdgeDelete[net, edge], reverseEdge[edge]]
        ];
        Graph[net, FilterRules[{opts}, Options[Graph]]]
    ]
]

normalEdges[g_] := Graph[VertexList[g], Replace[EdgeList[g], edge : DirectedEdge[_, _, {{1, __}, ___, {2, __}}] :> reverseEdge[edge], 1], Options[g]]

Options[DiagramsNetGraph] = DeleteDuplicatesBy[First] @ Join[{
    "ShowPortLabels" -> False,
    "ShowWireLabels" -> True,
    "WireLabelFunction" -> Automatic,
    "Scale" -> Automatic,
    "ArrowSize" -> Small, 
    "SpiderRadius" -> 0.2,
    "Orientation" -> Automatic,
    "UnarySpiders" -> True,
    "BinarySpiders" -> True,
    "SpiderMethod" -> 2,
    "RemoveCycles" -> False
}, Options[DiagramsGraph], Options[DiagramGraphics], Options[RemoveDiagramsNetGraphCycles], Options[Graph]];
DiagramsNetGraph[diagrams : {___Diagram ? DiagramQ}, opts : OptionsPattern[]] :=
    DiagramsNetGraph[
        DiagramsGraph[diagrams, FilterRules[{opts}, {GraphLayout, FilterRules[Options[DiagramsGraph], Except[Options[Graph]]]}]],
        FilterRules[{opts}, Except[GraphLayout]]
    ]
DiagramsNetGraph[graph_Graph, opts : OptionsPattern[]] := Enclose @ Block[{
	diagramVertices = VertexList[graph, _Integer], vertices, edges, netGraph,
    spiderVertices, spiderDiagrams,
	diagrams, ports, outDegrees, inDegrees,
	embedding, vertexCoordinates,
    orientations, orientation = OptionValue["Orientation"],
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
	ports = AssociationMap[AnnotationValue[{graph, #}, "Port"] &, VertexList[graph, _List]];
	If[Length[diagrams] == 0, Return[Graph[{}, {}, FilterRules[Join[{opts}, Options[graph]], Options[Graph]]]]];
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
			Block[{in = Sort @ VertexInComponent[graph, v, {1}], out = Sort @ VertexOutComponent[graph, v, {1}], wirePorts, sIn, sOut},
				wirePorts = Join[in, out];
				If[ Length[wirePorts] > 2 ||
                    Length[wirePorts] == 1 && MatchQ[unarySpiders, True] ||
                    Length[wirePorts] == 2 && Switch[binarySpiders,
                        All | Full,
                            True,
                        True,
                            SameQ @@ Lookup[ports, wirePorts, None, #["DualQ"] &],
                        Automatic,
                            SameQ @@ wirePorts[[All, 2]] || SameQ @@ Lookup[ports, wirePorts, None, #["DualQ"] &],
                        _,
                            False
                    ]
                    ,
                    {sIn, sOut} = Switch[
                        OptionValue["SpiderMethod"],
                        1,
                        Lookup[GroupBy[{diagrams[#1]["InputOutputPorts"][[#2, #3]], diagrams[#1]["PortStyles"][[#2, #3]], {##}} & @@@ wirePorts, #[[3, 2]] &], {2, 1}, {}],
                        _,
                        Lookup[GroupBy[{diagrams[#1]["InputOutputPorts"][[#2, #3]], diagrams[#1]["PortStyles"][[#2, #3]], {##}} & @@@ wirePorts, #[[1]]["DualQ"] &], {False, True}, {}]
                    ];
					Sow[{v,
                        Which[
                            Length[sIn] == 1,
                                CopyDiagram,
                            Length[sOut] == 1,
                                CopyDiagram[#2, #1, ##3] &,
                            Length[sIn] == 0 && Length[sOut] == 2,
                                CupDiagram[#2, ##3] &,
                            Length[sOut] == 0 && Length[sIn] == 2,
                                CapDiagram[#1, ##3] &,
                            True,
                                SpiderDiagram
                        ][
                            If[  #1["DualQ"], PortDual[tag[portFunction[PortDual[#1]], #3]], tag[portFunction[#1], #3]] & @@@ sIn,
                            If[! #1["DualQ"], PortDual[tag[portFunction[PortDual[#1]], #3]], tag[portFunction[#1], #3]] & @@@ sOut,
                            "PortArrows" -> {sIn[[All, 2]], sOut[[All, 2]]}
                        ]
                    }];
                    Splice @ Join[
                        MapIndexed[
                            If[ Lookup[ports, Key[#], False, #["DualQ"] &], reverseEdge, Identity] @
                                DirectedEdge[#[[1]], v, {{#[[2]], Lookup[Switch[#[[2]], 1, inDegrees, 2, outDegrees], #[[1]]], #[[3]]}, {1, Length[sIn], #2[[1]]}}] &,
                            sIn[[All, 3]]
                        ],
                        MapIndexed[
                            If[ Lookup[ports, Key[#], True, #["DualQ"] &], Identity, reverseEdge] @
                                DirectedEdge[v, #[[1]], {{2, Length[sOut], #2[[1]]}, {#[[2]], Lookup[Switch[#[[2]], 1, inDegrees, 2, outDegrees], #[[1]]], #[[3]]}}] &,
                            sOut[[All, 3]]
                        ]
                    ]
                    ,
					If[ Length[wirePorts] == 2,
                        Block[{src, tgt, srcDegree, tgtDegree},
                            {src, tgt} = If[ wirePorts[[1, 2]] == 1, {wirePorts[[2]], wirePorts[[1]]}, {wirePorts[[1]], wirePorts[[2]]}];
                            srcDegree = If[ src[[2]] == 1, inDegrees, outDegrees][src[[1]]];
                            tgtDegree = If[ tgt[[2]] == 1, inDegrees, outDegrees][tgt[[1]]];
                            If[ Lookup[ports, Key[src], False, #["DualQ"] &], reverseEdge, Identity] @
                                DirectedEdge[src[[1]], tgt[[1]], {{src[[2]], srcDegree, src[[3]]}, v, {tgt[[2]], tgtDegree, tgt[[3]]}}]
                        ],
                        Nothing
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
                    "OutputPorts" -> MapThread[With[{makePort = If[#1["DualQ"], PortDual[getName[#1], ##2] &, Port[getName[#1], ##2] &]},
                        FirstCase[edges,
                            edge: DirectedEdge[#2[[1]], tgtIdx_, {{2, _, #2[[3]]}, _, {i_, _, portIdx_}}] :>
                                With[{tgt = diagrams[tgtIdx]["InputOutputPorts", True][[i]][[portIdx]]},
                                   makePort[tag[portFunction @ tgt, {tgtIdx, i, portIdx}], "NeutralQ" -> tgt["NeutralQ"]]
                                ],
                            makePort[tag[portFunction @ #1, #2], "NeutralQ" -> #1["NeutralQ"]]
                        ]] &,
                        {#2["OutputPorts"], Thread[{#1, 2, Range[#2["OutputArity"]]}]}
                    ],
                    "InputPorts" -> MapThread[With[{makePort = If[#1["DualQ"], PortDual[getName[#1], ##2] &, Port[getName[#1], ##2] &]},
                        FirstCase[edges,
                            DirectedEdge[#2[[1]], tgtIdx_, {{1, _, #2[[3]]}, _, {i_, _, portIdx_}}] :>
                            With[{tgt = diagrams[tgtIdx]["InputOutputPorts", True][[i]][[portIdx]]},
                                makePort[tag[portFunction @ tgt, {tgtIdx, i, portIdx}], "NeutralQ" -> tgt["NeutralQ"]]
                            ],
                            makePort[tag[portFunction @ #1, #2], "NeutralQ" -> #1["NeutralQ"]]
                        ]["Dual"]] &,
                        {Through[#2["InputPorts"]["Dual"]], Thread[{#1, 1, Range[#2["InputArity"]]}]}
                    ]
                ] &,
                diagrams
            ]]],
            Thread[spiderVertices -> List /@ Thread["Diagram" -> spiderDiagrams]]
        ]
    ];
    If[TrueQ[OptionValue["RemoveCycles"]], netGraph = Confirm @ RemoveDiagramsNetGraphCycles[normalEdges @ netGraph, FilterRules[{opts}, Options[RemoveDiagramsNetGraphCycles]]]];
    vertexCoordinates = Thread[vertices -> Join[MapThread[Replace[#1, {Automatic -> #2, Offset[x_] :> #2 + x}] &, {Through[Values[diagrams]["OptionValue"["Center"]]], Lookup[embedding, diagramVertices]}], Lookup[embedding, spiderVertices]]];
	Graph[
		netGraph,
		FilterRules[{opts}, Options[Graph]],
		VertexCoordinates -> vertexCoordinates,
		VertexShapeFunction -> Join[
			Thread[diagramVertices ->
				MapThread[{diagram, orientation} |-> With[{
						shape = First @ diagram["Graphics",
                            "Center" -> Automatic,
                            "PortArrowFunction" -> (Nothing &),
                            "PortLabels" -> If[portLabelsQ, Automatic, None],
                            "LabelFunction" -> Function[d, d["Label"]]
                        ],
						transform = RotationTransform[{{0, 1}, orientation}] @* ScalingTransform[scale {1, 1}]
					},
						Function[{
							$Black,
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
					point1, point2, normal1, normal2, orientation1 = orientations[v], orientation2 = orientations[w],
                    style1, style2, label1, label2,
                    diagram1 = diagrams[v], diagram2 = diagrams[w],
                    port1, port2,
                    points1, points2,
                    hold
				},
                    port1 = diagram1[Replace[i, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[p]];
                    port2 = diagram2[Replace[j, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[q]];
                    points1 = diagram1["PortArrows"][[i, p]];
                    points2 = diagram2["PortArrows"][[j, q]];
                    style1 = diagram1["PortStyles"][[i, p]];
                    style2 = diagram2["PortStyles"][[j, q]];
                    label1 = diagram1["PortLabels"][[i, p]];
                    label2 = diagram2["PortLabels"][[j, q]];
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
                        lindep = v == w && TrueQ[Quiet[Chop[Det[{normal1, normal2}]]] == 0],
                        wireLabelFunction = Replace[OptionValue["WireLabelFunction"], {Automatic | True -> (#3 &), None | False -> ("" &)}],
                        p1 = points1, p2 = points2,
                        label = Replace[Replace[label2, {Automatic -> label1, _ -> label2}], {Placed[Automatic | True, _] | Automatic | True -> port1, Placed[l_, _] :> l}]
                    },
						With[{primitive = If[style1 === style2 || style1 === Automatic || style2 === Automatic,
                            {
                                Arrowheads[
                                    If[ port1["DualQ"] != port2["DualQ"],
                                        {{If[port1["DualQ"], -1, 1] arrowSize, .5}},
                                        {
                                            If[port1["DualQ"], {- arrowSize, .3}, {arrowSize, .3}],
                                            If[port2["DualQ"], {arrowSize, .7}, {- arrowSize, .7}]
                                        }
                                    ]
                                ],
                                With[{style = Replace[style1, Automatic :> Replace[style2, Automatic -> {}]]},
                                    If[ MatchQ[style, _Function],
                                        hold[style][#, "Net"] &,
                                        {style, Arrow @ BSplineCurve @ #} &
                                    ] @ {
                                        a + point1, a + point1 + normal1,
                                        If[lindep, (a + b) / 2 + 2 * RotationTransform[Pi / 2][normal1], Nothing],
                                        b + point2 + normal2, b + point2
                                    }
                                ]
                            },
                            {
                                If[ style1 === None, {},
                                    With[{arrowheads = Arrowheads[{
                                            If[port1["DualQ"], {- arrowSize, .5}, {arrowSize, .5}]
                                        }]
                                    },
                                        If[ MatchQ[style1, _Function],
                                            {arrowheads, hold[style1][#, "Net"]} &,
                                            {arrowheads, Replace[style1, Automatic -> Nothing], Arrow @ BSplineCurve @ #} &
                                        ]
                                    ] @ {
                                        a + point1, a + point1 + normal1,
                                        (a + b) / 2 + 2 * RotationTransform[Pi / 2][normal1]
                                        (* b + point2 + normal2, b + point2 *)
                                    }
                                ],
                                If[ style2 === None, {},
                                    With[{
                                        arrowheads = Arrowheads[{
                                            If[port2["DualQ"], {arrowSize, .5}, {- arrowSize, .5}]
                                        }]
                                    },
                                        If[ MatchQ[style2, _Function],
                                            {arrowheads, hold[style2][#, "Net"]} &,
                                            {arrowheads, Replace[style2, Automatic -> Nothing], Arrow @ BSplineCurve @ #} &
                                        ]
                                    ] @ {
                                        (* a + point1, a + point1 + normal1, *)
                                        (a + b) / 2 + 2 * RotationTransform[Pi / 2][normal1],
                                        b + point2 + normal2, b + point2
                                    }
                                ]
                            }
                        ],
                        labelPos = If[ lindep,
                            (a + b) / 2 + 1.25 RotationTransform[Pi / 2][normal1],
                            (a + point1 + normal1 + b + point2 + normal2) / 2 + .1 normal1
                        ]
                        },
                        If[ wireLabelsQ,
                            Function @ With[{
                                edgeShape = primitive /. {a :> #[[1]], b :> #[[-1]], hold[expr_] :> expr},
                                wireLabel = Replace[
                                    Replace[wireLabelFunction[p1, p2, label], {
                                        Placed[l_, pos_] :> {l, pos},
                                        l_ :> {l, Automatic}
                                    }],
                                    {l_, pos_} :> {Replace[l, Automatic | True -> label], pos}
                                ]
                            }, {
                                edgeShape,
                                If[ MatchQ[wireLabel[[1]], None | False],
                                    Nothing,
                                    Text[
                                        Style[ClickToCopy[InterpretationForm[wireLabel[[1]]], x], $Black],
                                        With[{pos = 
                                            With[{center = Quiet @ RegionCentroid @ DiscretizeRegion[
                                                    RegionUnion[ResourceFunction["ExtractGraphicsPrimitives"][edgeShape] /. {Arrow[Line[a_] | a_] :> Line[a]}],
                                                    MaxCellMeasure -> {"Length", 0.1}
                                                ]
                                            },
                                                If[ MatchQ[center, {_ ? NumericQ, _ ? NumericQ}],
                                                    center,
                                                    labelPos /. {a :> #[[1]], b :> #[[-1]]}
                                                ]
                                            ]
                                        },
                                            Replace[wireLabel[[2]], {
                                                Automatic :> pos,
                                                Offset[offset_] :> pos + offset
                                            }]
                                        ]
                                    ]
                                ]
                            }],
                            Function[primitive /. {a :> #[[1]], b :> #[[-1]], hold[expr_] :> expr}]
                        ]
					]
				]
            ],
				edge : DirectedEdge[v_Integer, _, {{i : 1 | 2, _Integer, p_Integer}, _}] | DirectedEdge[_, v_Integer, {_, {i : 1 | 2, _Integer, p_Integer}}] :> edge -> Block[{
					point, normal, orientation = orientations[v], portCoords = Lookup[embedding, Key[{v, i, p}]],
                    style = diagrams[v]["PortStyles"][[i, p]],
                    diagram = diagrams[v],
                    port, points,
                    hold
				},
                    port = diagram[Replace[i, {1 -> "InputPorts", 2 -> "OutputPorts"}]][[p]];
                    points = diagram["PortArrows"][[i, p]];
                    point = points[[1]] * scale;
                    normal = (points[[-1]] - points[[1]]) * scale * 3;
					point = RotationTransform[{{0, 1}, orientation}] @ point;
					normal = RotationTransform[{{0, 1}, orientation}] @ normal;

					With[{a = VectorSymbol["p", 2], b = VectorSymbol["q", 2]},
						Function[Evaluate @ If[style === None, {}, {
							With[{arrowheads = Arrowheads[If[port["DualQ"], {{-arrowSize, .5}}, {{arrowSize, .5}}]]},
                                If[ MatchQ[style, _Function],
                                    {arrowheads, hold[style][#, "Net"]} &,
                                    {arrowheads, Replace[style, Automatic -> Nothing], Arrow @ BSplineCurve @ #} &
                                ]
                            ] @ {a + point, a + point + normal, b + scale Normalize[portCoords - b], b + rad scale Normalize[portCoords - b]}
						}]] /. With[{s = If[IntegerQ[edge[[1]]], 1, -1]}, {a :> #[[s]], b :> #[[-s]], hold[expr_] :> expr}]
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


Options[ToDiagramNetwork] := Options[toDiagramNetwork] = Join[{"Unique" -> True, "Grid" -> True, "Arrange" -> False}, Options[DiagramNetwork]];

ToDiagramNetwork[d_Diagram, opts : OptionsPattern[]] := Which[
    d["NetworkQ"],
    Diagram[d, Inherited, Inherited, FilterRules[{opts}, Options[Diagram]]]
    ,
    TrueQ[OptionValue["Grid"]],
    Diagram[d,
        "Expression" :> DiagramNetwork[##],
        "PortFunction" -> $DefaultNetworkPortFunction,
        FilterRules[{opts}, Options[Diagram]]
    ] & @@ toDiagramNetwork[If[TrueQ[OptionValue["Arrange"]], d["Arrange", opts], d]["Decompose", "Unary" -> True, "Diagram" -> True], {}, {}, FilterRules[{opts}, Options[toDiagramNetwork]]],
    True,
    DiagramNetwork[##, opts] & @@ AnnotationValue[{#, VertexList[#]}, "Diagram"] & @ DiagramsNetGraph[d["Graph"]]
]

toDiagramNetwork[d_Diagram -> None, pos_, ports_, opts : OptionsPattern[]] := Block[{
    portFunction = OptionValue["PortFunction"],
    uniqueQ = TrueQ[OptionValue["Unique"]],
    mports = ports, port
}, {
	Diagram[d,
		"InputPorts" -> MapIndexed[If[#1["NeutralQ"], #1, With[{p = portFunction[PortDual[#1]]},
            If[ KeyExistsQ[mports, p],
                Sow[port = p -> Lookup[mports, p], "Port"];
                mports = DeleteElements[mports, 1 -> {port}];
                port[[2]]["Dual"]
                ,
                Port @ tag[p, If[uniqueQ, Join[pos, {1}, #2], pos]]
            ]]] &,
            d["SubInputPorts"]
        ],
		"OutputPorts" -> MapIndexed[If[#1["NeutralQ"], #1, With[{p = portFunction[#1]}, Port @ tag[p, If[uniqueQ, Join[pos, {2}, #2], pos]]]] &, d["SubOutputPorts"]],
        FilterRules[{opts}, Options[Diagram]]
	]
}
]

toDiagramNetwork[CirclePlus[ds___] -> d_, pos_, ports_, opts : OptionsPattern[]] :=
    Catenate @ MapIndexed[toDiagramNetwork[#1, Join[pos, #2], ports, "Unique" -> True, "PortFunction" -> d["PortFunction"], opts] &, {ds}]

toDiagramNetwork[CircleTimes[ds___] -> d_, pos_, ports_, opts : OptionsPattern[]] :=
    Catenate @ FoldPairList[With[{net = Reap[toDiagramNetwork[#2, Append[pos, #1[[1]]], #1[[2]], "Unique" -> True, "PortFunction" -> d["PortFunction"], opts], "Port"]}, {net[[1]], {#1[[1]] + 1, DeleteElements[#1[[2]], 1 -> Catenate[net[[2]]]]}}] &, {1, ports}, {ds}]

toDiagramNetwork[CircleDot[ds__] -> d_, pos_, ports_, opts : OptionsPattern[]] := With[{
    portFunction = With[{f = d["PortFunction"]}, f @* untagPort]
},
	Fold[
		{
            DiagramNetwork[##, "PortFunction" -> d["PortFunction"], FilterRules[{opts}, Options[DiagramNetwork]]] & @@
                Join[#1[[1]]["SubDiagrams"], toDiagramNetwork[#2, Append[pos, #1[[2]]], Join[portFunction[#] -> # & /@ untagPort /@ #1[[1]]["Arrange", "AssignPorts" -> False]["OutputPorts"], ports], "PortFunction" -> d["PortFunction"], "Unique" -> True, opts]],
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


DiagramSplit[diagram_Diagram /; diagram["SingletonNodeQ"], n : _Integer | Infinity | - Infinity : Infinity, dualQ : _ ? BooleanQ : True, ___] :=
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

DiagramPermute[diagram_ /; diagram["SingletonNodeQ"], perm_, dualQ : _ ? BooleanQ : True] := diagram["Permute", perm, dualQ]

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
    DiagramComposition[RowDiagram[Diagram["\[DoubleStruckCapitalI]", d["OutputPorts"][[#]], {}, "Shape" -> "Wires"[{{1, 2}}], "ShowLabel" -> False] & /@ indices], PermutationDiagram[d["OutputPorts"] -> Permute[d["OutputPorts"], perm], perm], d]["Network"]
]

TensorDiagram[scalar_, opts : OptionsPattern[]] := Diagram[scalar, {}, {}, FilterRules[{opts}, Options[Diagram]]]



$FunctionPortsType = "Association" | "List" | "Sequence"
$FunctionType = $FunctionPortsType -> $FunctionPortsType

Options[DiagramFunction] = {"Input" -> "Sequence", "Output" -> "Sequence", "Parallel" -> False, "PortFunction" -> Function[#["Name"]]};
 
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
		Function @@ ReplaceAt[Switch[OptionValue["Input"], "List" | "Association", x_ :> Join @@ x, "Sequence", x_ :> Sequence @@ x], 1][
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