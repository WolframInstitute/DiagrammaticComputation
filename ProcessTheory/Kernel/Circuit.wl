BeginPackage["ProcessTheory`Circuit`", {"ProcessTheory`Port`", "ProcessTheory`Node`"}];

NodesToCircuitDiagram

Begin["ProcessTheory`Circuit`Private`"];


NodesToCircuitDiagram[nodes_] := Block[{
    portIndex = First /@ PositionIndex[Union @ Through[Catenate[#["Flatten"]["Ports"] & /@ nodes]["Name"]]]
},
    <|
        "Elements" -> Map[node |-> 
            <|
                "Type" -> If[node["ComposeQ"], "Diagram", "Operator"],
                "Label" -> node["Expression"],
                "Thickness" -> {ConstantArray[2, node["OutputArity"]], ConstantArray[2, node["InputArity"]]},
                "Position" -> (Lookup[portIndex, Through[Catenate[Through[node[#]["ProductList"]]]["Name"]]] & /@ {"OutputPorts", "InputPorts"}),
                "Thick" -> False,
                "Diagram" -> Replace[node["HoldExpression"], {HoldForm[NodeCompose[ns___]] :> NodesToCircuitDiagram[{ns}], _ -> None}]
            |>
            ,
            nodes
        ],
        "Label" -> None,
        "Expand" -> True
    |>
]


End[];

EndPackage[];

