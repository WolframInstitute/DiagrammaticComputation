(* Structured Package Format loader (Wolfram Language 15.0+).
   PackageInitialize scans the .wl files alongside this loader (and up to
   three levels below) for Package* declarations, then loads them.

   - IgnoreFiles excludes Circuit.wl: the QuantumFramework-dependent circuit
     bridge is an optional submodule loaded on demand, not at paclet load.
   - LoadFirstFiles pins the file order to the original dependency order so
     load-time option inheritance (Options[X] = Options[Y]) resolves exactly
     as before. *)

PackageInitialize["Wolfram`DiagrammaticComputation`",
    "IgnoreFiles" -> {"Circuit.wl"},
    "LoadFirstFiles" -> {
        "Utilities.wl",
        "Port.wl",
        FileNameJoin[{"Diagram", "Diagram.wl"}],
        FileNameJoin[{"Diagram", "Grid.wl"}],
        FileNameJoin[{"Diagram", "ToDiagram.wl"}],
        FileNameJoin[{"Diagram", "Surgery.wl"}],
        FileNameJoin[{"Diagram", "DiagramDraw.wl"}],
        FileNameJoin[{"Diagram", "Rewriting.wl"}],
        FileNameJoin[{"Diagram", "Feynman.wl"}]
    }
]
