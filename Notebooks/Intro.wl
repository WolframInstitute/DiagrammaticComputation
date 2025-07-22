(* ::Package:: *)

(* ::Title:: *)
(*Introduction to Diagrammatic Computation*)


(* ::Text:: *)
(*Diagrammatic Computation (DC) involves representing operations and their connections visually, much like diagrams in mathematics or engineering. This approach emphasizes modular building blocks that can be composed in various ways to model complex systems. To illustrate these concepts computationally, we start by installing and loading the paclet:*)


(* ::Input:: *)
(*PacletInstall["Wolfram/DiagrammaticComputation"]*)


(* ::Input:: *)
(*<< Wolfram`DiagrammaticComputation`*)


(* ::Section:: *)
(*Core Ideas of Diagrammatic Thinking*)


(* ::Text:: *)
(*At its essence, DC treats computations as abstract structures: boxes representing operations, with ports for inputs and outputs. These can be wired together to form larger diagrams, revealing patterns and relationships that might be less apparent in linear code. The focus is on composition, modularity, and visualization, rather than specific applications.*)


(* ::Section:: *)
(*Constructing a Diagram*)


(* ::Text:: *)
(*Consider representing addition with two inputs (x) and (y) and one output (z):*)


(* ::Input:: *)
(*Diagram[Plus, {x, y}, z]*)


(* ::Text:: *)
(*This creates a symbolic diagram: a box labeled "Plus" with input ports (x) and (y), and a single output port (z). It remains unevaluated, serving as a blueprint. By default, such diagrams format visually, showing wires connecting the ports to the operation.*)


(* ::Text:: *)
(*There are a few custom shapes that will be useful for changing diagram default appearance:*)


(* ::Input:: *)
(*Diagram["",a,b,"Shape"->#]&/@{"RoundedRectangle","Triangle","UpsideDownTriangle","Disk","Point"}*)


(* ::Section:: *)
(*Vertical and Horizontal Composition*)


(* ::Text:: *)
(*Vertical composition connects diagrams end-to-end, with outputs from one feeding inputs to the next, mirroring function composition. Matching port labels enable automatic wiring.*)
(**)
(*Consider numerical operations: one doubles a number, another increments it by 1:*)


(* ::Input:: *)
(*double = Diagram["[2\[Times]]", x, y]*)


(* ::Input:: *)
(*increment = Diagram["[+1]", y, z]*)


(* ::Text:: *)
(*Vertical composition (increment after double):*)


(* ::Input:: *)
(*DiagramComposition[increment, double]*)


(* ::Text:: *)
(*This connects \[y\] from double to \[y\] in increment. The rendering shows stacked boxes connected by a wire. Using standard sequential Composition (\[@*\]) this can be represented like this:*)


(* ::Input:: *)
(*("[+1]"@*"[2\[Times]]")@3*)


(* ::Text:: *)
(*Or using RightComposition (/\*) producing the same expression:*)


(* ::Input:: *)
(*("[2\[Times]]"/*"[+1]")@3*)


(* ::Text:: *)
(*If abstract nodes are replaced by actual functions, this would produce the expected result. For input 3, double produces 6, increment yields 7:*)


(* ::Input:: *)
(*((y |-> 2 y)/*(x |-> x + 1))@3*)


(* ::Text:: *)
(*We'll create function representations of diagrams like this and more complex ones automatically later.*)
(*But for now, let's try to compose these functions in the opposite order:*)


(* ::Input:: *)
(*DiagramComposition[double, increment]*)


(* ::Text:: *)
(*The result may be unexpected because port \[z\] is followed by port \[x\], which do not match, so the diagrams compose horizontally in parallel. To fix this, it is possible to reassign ports for a diagram. For example, a new double diagram with adjusted port names can be constructed like this:*)


(* ::Input:: *)
(*double2 = Diagram[double, z, x]*)


(* ::Text:: *)
(*With the new input port name matching the output of the incrementing diagram, composition works correctly:*)


(* ::Input:: *)
(*DiagramComposition[double2, increment]*)


(* ::Text:: *)
(*Which, after turning into a function, would produce a different result:*)


(* ::Input:: *)
(*((z |-> z + 1)/*(y |-> 2 y))@3*)


(* ::Text:: *)
(*The parallel composition above can also be done directly using DiagramProduct in any order; this ensures that ports of horizontally composed diagrams never wire together:*)


(* ::Input:: *)
(*DiagramProduct[increment, double]*)


(* ::Input:: *)
(*DiagramProduct[double, increment]*)


(* ::Text:: *)
(*These diagrams also show that, in principle, diagrams can have multiple inputs and multiple outputs:*)


(* ::Input:: *)
(*Diagram[f, {x, y}, {a, b, c}]*)


(* ::Text:: *)
(*This also includes zero inputs and/or zero outputs:*)


(* ::Input:: *)
(*{Diagram[x, a], Diagram[x, a, {}], Diagram[x]}*)


(* ::Text:: *)
(*For example, the input to a computation can be represented as a diagram with no inputs:*)


(* ::Input:: *)
(*three = Diagram[3, x]*)


(* ::Text:: *)
(*And it can also be used in a composition to diagrammatically represent the whole computation:*)


(* ::Input:: *)
(*DiagramComposition[increment, double, three]*)


(* ::Section:: *)
(*Building More Complex Circuits*)


(* ::Text:: *)
(*Building on simple compositions, we can create more intricate circuits by combining vertical and horizontal arrangements, introducing branching and merging. This allows modeling workflows with parallel paths that diverge and reconverge, such as processing a number through multiple operations before combining results.*)
(**)
(*Extend the example by adding a "square" operation and a final "add" to merge branches. Define the new diagrams with compatible ports:*)


(* ::Input:: *)
(*square = Diagram["[^2]", q, r]*)


(* ::Input:: *)
(*add = Diagram["[+]", {s, t}, result]*)


(* ::Text:: *)
(*To create a circuit: start with an input, double it, then explicitly branch the output into parallel paths (increment on one, square on the other), and finally add the results.*)
(**)
(*First, prepare the input and initial double:*)


(* ::Input:: *)
(*inputNum = Diagram[3, in]*)


(* ::Input:: *)
(*doubled = Diagram["[2\[Times]]", in, out]*)


(* ::Text:: *)
(*To branch, introduce an explicit copy diagram that duplicates the output port:*)


(* ::Input:: *)
(*copier = Diagram["", out, {p, q}, "Shape" -> "Point"]*)


(* ::Text:: *)
(*Now, define the branches with matching input ports:*)


(* ::Input:: *)
(*incrementBranch = Diagram["[+1]", p, s]*)


(* ::Input:: *)
(*squareBranch = Diagram["[^2]", q, t]*)


(* ::Text:: *)
(*Compose the branches horizontally for parallelism:*)


(* ::Input:: *)
(*branched = DiagramProduct[incrementBranch, squareBranch]*)


(* ::Text:: *)
(*Then, compose vertically with the copier and the doubled diagram:*)


(* ::Input:: *)
(*parallelPaths = DiagramComposition[branched, copier, doubled]*)


(* ::Text:: *)
(*Finally, merge with add:*)


(* ::Input:: *)
(*complexCircuit = DiagramComposition[add, parallelPaths, inputNum]*)


(* ::Text:: *)
(*This yields a diagram with explicit branching: input 3 doubles to 6, copies to two paths yielding increment (7) and square (36), then adds to 43. The visual renders as a tree-like structure with wires splitting at the copy point and joining at the add.*)
(**)
(*Such circuits demonstrate DC's power for modular, visual modeling of non-linear computations.*)
