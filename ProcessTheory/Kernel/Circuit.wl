BeginPackage["ProcessTheory`Circuit`", {"ProcessTheory`Port`", "ProcessTheory`Diagram`"}];

DiagramsToCircuitDiagram

Begin["ProcessTheory`Circuit`Private`"];


DiagramsToCircuitDiagram[diagrams_List] := Block[{
    portIndex = First /@ PositionIndex[Union @ Through[Catenate[#["Flatten"]["Ports"] & /@ diagrams]["Name"]]]
},
    <|
        "Elements" -> Map[diagram |-> 
            <|
                "Type" -> If[diagram["CompositionQ"], "Diagram", "Operator"],
                "Label" -> diagram["Expression"],
                "Thickness" -> {ConstantArray[2, diagram["OutputArity"]], ConstantArray[2, diagram["InputArity"]]},
                "Position" -> (Lookup[portIndex, Through[Catenate[Through[diagram[#]["ProductList"]]]["Name"]]] & /@ {"OutputPorts", "InputPorts"}),
                "Thick" -> False,
                "Diagram" -> Replace[diagram["HoldExpression"], {HoldForm[DiagramComposition[ds___]] :> DiagramsToCircuitDiagram[{ds}], _ -> None}]
            |>
            ,
            diagrams
        ],
        "Label" -> None,
        "Expand" -> True
    |>
]


End[];

EndPackage[];

