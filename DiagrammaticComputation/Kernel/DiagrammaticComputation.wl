BeginPackage["Wolfram`DiagrammaticComputation`"]

EndPackage[]

Scan[
    (ClearAll[Evaluate[# <> "*"]]; Get[#]) &,
    {
        "Wolfram`DiagrammaticComputation`Port`",
        "Wolfram`DiagrammaticComputation`Diagram`",
        "Wolfram`DiagrammaticComputation`Diagram`Grid`",
        "Wolfram`DiagrammaticComputation`Diagram`ToDiagram`",
        "Wolfram`DiagrammaticComputation`Diagram`Surgery`",
        "Wolfram`DiagrammaticComputation`Diagram`DiagramDraw`",
        "Wolfram`DiagrammaticComputation`Diagram`Feynman`"
    }
]
