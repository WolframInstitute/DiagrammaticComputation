(* Structured Package Format loader (Wolfram Language 15.0+).
   PackageInitialize scans the .wl files alongside this loader (and up to
   three levels below) for Package* declarations, then loads them.

   IgnoreFiles excludes the optional submodules that pull external paclets, so
   the base paclet loads without those dependencies present. Each is its own
   context with its own loader, loaded on demand:
     Circuit.wl                  - depends on Wolfram`QuantumFramework`
     Diagram/Rewriting/          - depends on WolframInstitute`Hypergraph`; the
                                   Kernel extension maps the context
                                   Wolfram`DiagrammaticComputation`Rewriting` to
                                   Diagram/Rewriting/Init.wl, so it loads via
                                   Needs["Wolfram`DiagrammaticComputation`Rewriting`"] *)

PackageInitialize["Wolfram`DiagrammaticComputation`",
    "IgnoreFiles" -> {
        "Circuit.wl",
        FileNameJoin[{"Diagram", "Rewriting", "Init.wl"}],
        FileNameJoin[{"Diagram", "Rewriting", "Rewriting.wl"}]
    }
]
