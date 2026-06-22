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

       wolframscript -f scripts/build-docs.wls               (* all pages *)
       wolframscript -f scripts/build-docs.wls Diagram       (* one page *)
       wolframscript -f scripts/build-docs.wls "Diagram*"    (* basename pattern *)
       wolframscript -f scripts/build-docs.wls Surgery       (* path subset: docs/symbols/Diagram/Surgery *)
       wolframscript -f scripts/build-docs.wls tutorials     (* every tech note *)

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

(* Load the in-development paclet so MarkdownToNotebook can resolve inline
   `<code>[Foo]()</code>` links (it accepts symbols defined in subcontexts of
   the document's Context) and so the examples evaluate against the real
   definitions. *)
PacletDirectoryLoad[$root];
Needs["Wolfram`DiagrammaticComputation`"];
(* The Rewriting submodule is its own on-demand context; load it too so its
   reference pages resolve their symbol links and evaluate their examples. *)
Needs["Wolfram`DiagrammaticComputation`Rewriting`"];

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

(* Positional selectors: any non-flag args restrict the build to matching
   sources. A selector matches when, case-insensitively,
     - the page basename matches it as an abbreviated string pattern
       ("Diagram", "Diagram*", "*Rule"), or
     - it occurs in the source path relative to docs/
       ("Surgery", "symbols/Diagram/Grid", "tutorials").
   Multiple selectors are a union. *)
$selectors = DeleteCases[$args, _String?(StringStartsQ["--"])];

filter[src_String] := $selectors === {} || With[
    {base = FileBaseName[src], rel = StringDelete[src, $docsRoot <> $PathnameSeparator]},
    AnyTrue[$selectors,
        StringMatchQ[base, #, IgnoreCase -> True] ||
        StringContainsQ[rel, #, IgnoreCase -> True] &
    ]
];

(* --- driver ---------------------------------------------------------- *)

If[$clearCache,
    Print["[cache] clearing MarkdownToNotebook/ExampleOutput/*"];
    Scan[DeleteObject, PersistentObjects["MarkdownToNotebook/ExampleOutput/*", "Local"]]
];

$m2nOptions = If[$darkMode, {"LightDark" -> "Dark"}, {}];

build1[src_String, nbDst_String] := Module[{twinDst},
    twinDst = FileNameJoin[{DirectoryName[src], FileBaseName[src] <> "-out.md"}];
    If[$buildNb,
        Print["[ nb ] ", FileNameTake[src, -2], "  ->  ", FileNameTake[nbDst, -2]];
        mtn[src, nbDst, Sequence @@ $m2nOptions]
    ];
    If[$buildTwin,
        Print["[twin] ", FileNameTake[src, -2], "  ->  ", FileNameTake[twinDst, -2]];
        mtn[src, twinDst, Sequence @@ $m2nOptions]
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
