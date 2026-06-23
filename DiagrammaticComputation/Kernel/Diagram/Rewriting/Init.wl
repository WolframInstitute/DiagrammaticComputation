(* Structured Package Format loader for the Rewriting submodule.
   Mapped from Wolfram`DiagrammaticComputation`Rewriting` by the paclet's Kernel
   extension, so Needs["Wolfram`DiagrammaticComputation`Rewriting`"] runs this and
   loads the sibling content file into that context. *)

PackageInitialize["Wolfram`DiagrammaticComputation`Rewriting`"]

(* The rule port atoms live in the Rules subcontext (see Rewriting.wl): not part
   of the public API, but put on $ContextPath so the rules print with short atom
   names. PackageInitialize restores $ContextPath as it returns, so prepend here -
   after it - for the change to persist into the caller's session. *)
If[ ! MemberQ[$ContextPath, "Wolfram`DiagrammaticComputation`Rewriting`Rules`"],
    PrependTo[$ContextPath, "Wolfram`DiagrammaticComputation`Rewriting`Rules`"];
]
