(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


System`Private`NewContextPath[{"System`", "ProcessTheory`"}];

ProcessTheory`ProcessTheoryDump`$exported = {
	System`DiagramQ,
	System`Diagram,
	System`ToDiagram,
	System`DiagramDual,
	System`DiagramFlip,
	System`DiagramReverse,
	System`DiagramProduct,
	System`DiagramSum,
	System`DiagramComposition,
	System`DiagramNetwork,
	System`ColumnDiagram,
	System`RowDiagram,
	System`DiagramGrid,
	System`DiagramDraw
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
