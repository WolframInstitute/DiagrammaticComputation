#!/usr/bin/env wolframscript
(* ::Package:: *)

(*
   Build the paclet's documentation from the markdown sources under `docs/`.

   For each markdown source two outputs are produced:

     1. The DocumentationTools authoring notebook (.nb) that
        `DocumentationBuild` turns into the published ref/guide page.
        Lives under the paclet's `Documentation/English/` tree, flattened
        to one directory per page kind (Guides vs Symbols).

     2. A GitHub-renderable markdown "twin" (`<name>-out.md`) in the same
        directory as the source, with every evaluated example output
        rasterised as a PNG in an adjacent `images/` folder. Open the
        twin to preview the page on GitHub without building the paclet.

   Layout:

       docs/guides/Foo.md
         -> DiagrammaticComputation/Documentation/English/Guides/Foo.nb
         -> docs/guides/Foo-out.md  (+ docs/guides/images/...)

       docs/symbols/Sub/Bar.md
         -> DiagrammaticComputation/Documentation/English/ReferencePages/Symbols/Bar.nb
         -> docs/symbols/Sub/Bar-out.md  (+ docs/symbols/Sub/images/...)

   Usage:

       wolframscript -f scripts/build-docs.wls           (* all pages *)
       wolframscript -f scripts/build-docs.wls Diagram   (* one page *)

   Flags (any position):

       --nb-only       skip the twin markdown
       --twin-only     skip the .nb build
       --dark          render example outputs in dark mode
       --no-cache      clear the MarkdownToNotebook example cache first
*)

mtn = ResourceFunction[ResourceObject[
    "https://www.wolframcloud.com/obj/nikm/DeployedResources/Function/MarkdownToNotebook"
]];

$root      = FileNameDrop[$InputFileName, -2];

(* Make the in-development paclet visible AND actually load its symbols, so
   MarkdownToNotebook can resolve inline `<code>[Foo]()</code>` links to
   paclet:Wolfram/DiagrammaticComputation/ref/Foo URLs in the body text.
   The converter resolves an inline `[Foo]()` by checking
   `Names[$docContext <> "Foo"]`. Our $docContext is the top-level
   `Wolfram`DiagrammaticComputation`` but the actual symbol definitions
   live in subcontexts (`Wolfram`DiagrammaticComputation`Diagram`Diagram`,
   `…`Port`Port`, …), so by default `Names[]` finds nothing and the body
   refs render as plain code spans.

   The PacletInfo's `Symbols` extension already lists every exported name
   (the same list the front end uses for paclet doc resolution); we stub
   each one in the top-level context so `Names[]` can see them. The stubs
   are name-only — calling them still routes to the subpackage definitions
   because those are on `$ContextPath` after `Needs[]`. *)
PacletDirectoryLoad[$root];
Needs["Wolfram`DiagrammaticComputation`"];

(* One stub per documented symbol — we use the docs/symbols/ tree as the
   source of truth (the PacletInfo's Symbols extension currently lists only
   the original 25 symbols; the docs cover all 95).

   IMPORTANT: a bare `ToExpression["Wolfram`DiagrammaticComputation`Foo"]`
   creates a top-level stub that *shadows* the real subpackage symbol
   (`…`Diagram`Foo`, `…`Port`Foo`, …) on $ContextPath — so cells like
   `Diagram["A", …]` would resolve to the empty stub and render as plain
   expression text instead of evaluating to a graphic.

   To make link-resolution happy *and* keep evaluation working, each stub
   is set as an alias (OwnValue) to its real subpackage symbol: looking up
   the bare `Diagram` resolves to the stub, the stub evaluates to the real
   `…`Diagram`Diagram`, and the call proceeds with the real DownValues. *)
(* Look up the real symbol via $ContextPath (NOT via Symbol[name], which
   blindly creates a fresh symbol in $Context = Global` regardless of what
   the path holds — that bug pinned every stub to an empty Global` symbol
   and broke every example output). ToExpression with `Hold` resolves the
   short name through $ContextPath without evaluating it. *)
stubAlias[name_String] := Module[{held, realFullName, stubFullName},
    held = Quiet @ ToExpression[name, InputForm, Hold];
    If[Head[held] =!= Hold, Return[]];
    realFullName = ReleaseHold[Context[#] <> SymbolName[#] & @@ held];
    stubFullName = "Wolfram`DiagrammaticComputation`" <> name;
    (* Skip if the real symbol is already at the top context. *)
    If[realFullName === stubFullName, Return[]];
    ToExpression[stubFullName <> " = " <> realFullName]
];

With[{
    symbolNames = DeleteCases[
        FileBaseName /@ FileNames["*.md", FileNameJoin[{$root, "docs", "symbols"}], Infinity],
        _?(StringEndsQ["-out"])
    ]
},
    Quiet[Scan[stubAlias, symbolNames], {General::shdw}];
    Print["[stubs] declared ", Length @ symbolNames, " top-level symbol aliases for link resolution"]
];

$docsRoot     = FileNameJoin[{$root, "docs"}];
$guidesIn     = FileNameJoin[{$docsRoot, "guides"}];
$symbolsIn    = FileNameJoin[{$docsRoot, "symbols"}];
$tutorialsIn  = FileNameJoin[{$docsRoot, "tutorials"}];

$pacletDoc    = FileNameJoin[{$root, "DiagrammaticComputation", "Documentation", "English"}];
$guidesOut    = FileNameJoin[{$pacletDoc, "Guides"}];
$symbolsOut   = FileNameJoin[{$pacletDoc, "ReferencePages", "Symbols"}];
$tutorialsOut = FileNameJoin[{$pacletDoc, "Tutorials"}];

ensureDir[d_] := If[! DirectoryQ[d], CreateDirectory[d, CreateIntermediateDirectories -> True]];

ensureDir[$guidesOut];
ensureDir[$symbolsOut];
ensureDir[$tutorialsOut];

(* --- argv parsing ----------------------------------------------------- *)

$args = Rest @ $ScriptCommandLine;

flag[name_] := MemberQ[$args, name];

$buildNb   = ! flag["--twin-only"];
$buildTwin = ! flag["--nb-only"];
$darkMode  = flag["--dark"];
$clearCache = flag["--no-cache"];

(* Positional filter: any non-flag args restrict the build to matching basenames. *)
$names = DeleteCases[$args, _String?(StringStartsQ["--"])];
filter[src_] := $names === {} || MemberQ[$names, FileBaseName[src]];

(* --- driver ---------------------------------------------------------- *)

If[$clearCache,
    Print["[cache] clearing MarkdownToNotebook/ExampleOutput/*"];
    Scan[DeleteObject, PersistentObjects["MarkdownToNotebook/ExampleOutput/*", "Local"]]
];

(* The converter's $lightDark lives in its own ResourceFunction private
   context (FunctionRepository`$<hash>`), not Global`. We need to evaluate
   one mtn call first so the package loads and the variable becomes
   findable via Names, then we can set it there. The actual mtn evaluation
   below will pick up the override. *)
setConverterLightDark[mode_String] := Module[{names},
    names = Names["FunctionRepository`*`$lightDark"];
    If[names === {},
        (* prime the package by querying mtn's information *)
        Quiet @ mtn[];
        names = Names["FunctionRepository`*`$lightDark"]
    ];
    Scan[ToExpression[# <> " = \"" <> mode <> "\""] &, names];
    Length[names]
];

If[$darkMode,
    With[{n = setConverterLightDark["Dark"]},
        Print["[dark] set $lightDark = Dark in ", n, " converter context(s)"]
    ]
];

build1[src_String, nbDst_String] := Module[{twinDst},
    twinDst = FileNameJoin[{DirectoryName[src], FileBaseName[src] <> "-out.md"}];
    If[$buildNb,
        Print["[ nb ] ", FileNameTake[src, -2], "  ->  ", FileNameTake[nbDst, -2]];
        mtn[src, nbDst]
    ];
    If[$buildTwin,
        Print["[twin] ", FileNameTake[src, -2], "  ->  ", FileNameTake[twinDst, -2]];
        mtn[src, twinDst]
    ];
];

(* The paclet definition notebook builds from docs/ResourceDefinition.md to
   the non-standard in-repo filename. *)
$definitionIn  = FileNameJoin[{$docsRoot, "ResourceDefinition.md"}];
$definitionOut = FileNameJoin[{$root, "DiagrammaticComputation", "DiagrammaticComputation | Definition Notebook.nb"}];

run[] := Module[{guideFiles, symbolFiles, tutorialFiles},
    guideFiles    = Select[FileNames["*.md", $guidesIn], filter];
    symbolFiles   = Select[FileNames["*.md", $symbolsIn, Infinity], filter];
    tutorialFiles = Select[FileNames["*.md", $tutorialsIn], filter];
    If[ FileExistsQ[$definitionIn] && filter[$definitionIn],
        build1[$definitionIn, $definitionOut]
    ];
    (* Skip already-emitted twin files. *)
    symbolFiles   = DeleteCases[symbolFiles,   _?(StringEndsQ["-out.md"])];
    guideFiles    = DeleteCases[guideFiles,    _?(StringEndsQ["-out.md"])];
    tutorialFiles = DeleteCases[tutorialFiles, _?(StringEndsQ["-out.md"])];
    Print["Guides: ",    Length[guideFiles]];
    Print["Symbols: ",   Length[symbolFiles]];
    Print["Tutorials: ", Length[tutorialFiles]];
    Scan[
        build1[#, FileNameJoin[{$guidesOut,  FileBaseName[#] <> ".nb"}]] &,
        guideFiles
    ];
    Scan[
        build1[#, FileNameJoin[{$symbolsOut, FileBaseName[#] <> ".nb"}]] &,
        symbolFiles
    ];
    Scan[
        build1[#, FileNameJoin[{$tutorialsOut, FileBaseName[#] <> ".nb"}]] &,
        tutorialFiles
    ];
    Print["Done."]
];

(* Hold a single front-end session open across the whole pass: both the
   example evaluation and the per-output rasterisation need it, and starting
   one per call is slow. *)
UsingFrontEnd[
    If[$darkMode, CurrentValue[$FrontEnd, LightDark] = "Dark"];
    run[]
]
