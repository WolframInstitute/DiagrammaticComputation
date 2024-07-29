(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


System`Private`NewContextPath[{"System`", "ProcessTheory`"}];

ProcessTheory`ProcessTheoryDump`$exported = {
	System`CircuitDiagramQ,
	System`DiagramAdjoint,
	System`DiagramComposition,
	System`DiagramConjugate,
	System`DiagramPlot,
	System`DiagramProduct,
	System`DiagramSum,
	System`DiagramTranspose,
	System`ProcessDiagram
};

Unprotect /@ ProcessTheory`ProcessTheoryDump`$exported;
ClearAll /@ ProcessTheory`ProcessTheoryDump`$exported;

Begin["ProcessTheory`ProcessTheoryDump`"];


(* ::Section:: *)
(*Definitions*)


(* ::Section::Closed:: *)
(*Package Footer*)


End[]; (* ProcessTheory`ProcessTheoryDump` *)

System`Private`RestoreContextPath[];

ProcessTheory`ProcessTheoryDump`$exported
