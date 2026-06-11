PacletDirectoryLoad["DiagrammaticComputation"]
<< Wolfram`DiagrammaticComputation`

(* Shared fixtures: a flat composition and a nested composition of a product. *)
$flat = DiagramComposition[Diagram["A", b, a], Diagram["B", c, b]]
$nested = Diagram[DiagramProduct[Diagram["A", a, c], Diagram["B", b]] /* Diagram["C", {c, b}, e]]

exprs[d_Diagram] := #["Expression"] & /@ d["SubDiagrams"]
leafExprs[d_Diagram] := #["Expression"] & /@ DiagramSubdiagrams[d, {1}]


(* DiagramPositions / DiagramSubdiagrams *)

VerificationTest[
    Keys @ DiagramPositions[$flat],
    {{}, {1}, {2}},
    TestID -> "Surgery-Positions-All"
]

VerificationTest[
    Keys @ DiagramPositions[$flat, {1}],
    {{1}, {2}},
    TestID -> "Surgery-Positions-Level"
]

VerificationTest[
    Keys @ DiagramPositions[$nested],
    {{}, {1}, {2}, {2, 1}, {2, 2}},
    TestID -> "Surgery-Positions-Nested"
]

VerificationTest[
    Length @ DiagramSubdiagrams[$flat],
    3,
    TestID -> "Surgery-Subdiagrams-Count"
]


(* DiagramExtract *)

VerificationTest[
    DiagramExtract[$flat, {1}]["Expression"],
    "A",
    TestID -> "Surgery-Extract-Single"
]

VerificationTest[
    DiagramExtract[$flat, {}]["HoldExpression"],
    $flat["HoldExpression"],
    TestID -> "Surgery-Extract-Empty"
]

VerificationTest[
    #["Expression"] & /@ DiagramExtract[$flat, {{1}, {2}}],
    {"A", "B"},
    TestID -> "Surgery-Extract-Multiple"
]

VerificationTest[
    DiagramExtract[$nested, {2, 1}]["Expression"],
    "A",
    TestID -> "Surgery-Extract-Nested"
]


(* DiagramInsert *)

VerificationTest[
    exprs @ DiagramInsert[$flat, Diagram["I0", b, b], {2}],
    {"A", "I0", "B"},
    TestID -> "Surgery-Insert-Single"
]

VerificationTest[
    exprs @ DiagramInsert[$flat, Diagram["I0", b, b], {{1}, {2}}],
    {"I0", "A", "I0", "B"},
    TestID -> "Surgery-Insert-Multiple"
]

VerificationTest[
    DiagramQ @ DiagramInsert[$nested, Diagram["D", b, b], {2, 2}],
    True,
    TestID -> "Surgery-Insert-Nested"
]


(* DiagramDelete *)

VerificationTest[
    (* a single-subdiagram composition normalizes to the remaining diagram *)
    DiagramDelete[$flat, {1}]["Expression"],
    "B",
    TestID -> "Surgery-Delete-Single"
]

VerificationTest[
    leafExprs @ DiagramDelete[$nested, {2, 1}],
    {"C", "B"},
    TestID -> "Surgery-Delete-Nested"
]

VerificationTest[
    (* inserting and deleting at the same position is the identity *)
    exprs @ DiagramDelete[DiagramInsert[$flat, Diagram["I0", b, b], {2}], {2}],
    {"A", "B"},
    TestID -> "Surgery-Insert-Delete-Roundtrip"
]


(* DiagramReplacePart *)

VerificationTest[
    exprs @ DiagramReplacePart[$flat, {2} -> Diagram["X", c, b]],
    {"A", "X"},
    TestID -> "Surgery-ReplacePart"
]


(* DiagramMap / DiagramMapAt *)

VerificationTest[
    leafExprs @ DiagramMap[Diagram[#, "Expression" -> "Z"] &, $flat],
    {"Z", "Z"},
    TestID -> "Surgery-Map-Leaves"
]

VerificationTest[
    (* the function receives the subdiagram and its position *)
    exprs @ DiagramMapAt[Diagram[#1, "Expression" -> ToString[#2]] &, $flat, {2}],
    {"A", "{2}"},
    TestID -> "Surgery-MapAt-Position"
]


(* DiagramCases / DiagramPosition / DiagramPattern *)

VerificationTest[
    Length @ DiagramCases[$flat, DiagramPattern["A"]],
    1,
    TestID -> "Surgery-Cases-Pattern"
]

VerificationTest[
    DiagramPosition[$flat, DiagramPattern["B"]],
    {{2}},
    TestID -> "Surgery-Position-Pattern"
]

VerificationTest[
    Length @ DiagramCases[$flat],
    3,
    TestID -> "Surgery-Cases-All"
]
