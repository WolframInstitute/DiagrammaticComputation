BeginPackage["Wolfram`DiagrammaticComputation`Diagram`DiagramDraw`", {"Wolfram`DiagrammaticComputation`Port`", "Wolfram`DiagrammaticComputation`Diagram`"}];

DiagramDraw

Begin["Wolfram`DiagrammaticComputation`Diagram`DiagramDraw`Private`"];


findBoxId[boxes_, mousePos_] := Replace[FirstPosition[boxes, "Box"[boxPos_, _] /; RegionDistance[RegionBoundary[Rectangle @@ boxPos], mousePos] < .01, Missing[], {1}, Heads -> False], {id_} :> id]
findConnector[box_, mousePos_] := Replace[FirstPosition[box[[2]], p_ /; EuclideanDistance[p, mousePos] < .02, Missing[], {1}, Heads -> False], {id_} :> id]

connectorNormal[box_, point_] := Block[{normal},
	normal = point - Mean /@ Transpose[box];
	If[point[[1]] == box[[1, 1]] || point[[1]] == box[[2, 1]], normal[[2]] = 0];
	If[point[[2]] == box[[1, 2]] || point[[2]] == box[[2, 2]], normal[[1]] = 0];
	Normalize[normal]
]

wirePoints[{from_, to_, box1_, box2_}] := Block[{
	center = (from + to) / 2,
	normal1, normal2, points,
	scale = .2
},
	normal1 = connectorNormal[box1, from] scale;
	points = If[ box2 =!= None,
		normal2 = to - Mean /@ Transpose[box2];
		If[to[[1]] == box2[[1, 1]] || to[[1]] == box2[[2, 1]], normal2[[2]] = 0];
		If[to[[2]] == box2[[1, 2]] || to[[2]] == box2[[2, 2]], normal2[[1]] = 0];
		normal2 = Normalize[normal2] scale;
		{from, from + normal1, to + normal2, to}
		,
		{from, from + normal1, center + normal1, to}
	];
	points
]

renderWire[arg_] := {Arrowheads[{{Automatic, .5}}], Arrow[BSplineCurve @ wirePoints[arg]]}


Options[DiagramDraw] = Options[Graphics]
DiagramDraw[diagram_ : <||>, opts : OptionsPattern[]] := DynamicModule[{
	boxes = Lookup[diagram, "Boxes", <||>],
	wires = Lookup[diagram, "Wires", {}],
	actions = {}, do,undo,
	startMousePos = Missing[], mousePos = Missing[],
	boxPositions = {}, selectedBoxes = {}, selectedConnectors = {}, selectedBox, selectedConnector,
	prevBoxes = <||>,
	dragBoxQ = False, dragConnectorQ = False,
	wire = None, targetConnector = None,
	graphicsEnteredQ = False,
	graphics, canvas, widget
},
	do[action_] := (
		AppendTo[actions, action];
		Replace[
			action,
			{
				"AddBox"[pos : {Repeated[{_Real, _Real}, {2, Infinity}]}] :> (
					AppendTo[boxes, Unique[] -> "Box"[pos, {}]]
				),
				"SelectBox"[Key[boxId_] | boxId_] :> If[MemberQ[selectedBoxes, boxId], selectedBoxes = DeleteElements[selectedBoxes, {boxId}], AppendTo[selectedBoxes, boxId]],
				"SelectConnector"[Key[boxId_] | boxId_, connectorId_] :> If[MemberQ[selectedConnectors, {boxId, connectorId}],
					selectedConnectors = DeleteElements[selectedConnectors, {{boxId, connectorId}}], AppendTo[selectedConnectors, {boxId, connectorId}]
				],
				"RemoveBoxSelection"[boxIds_List, _] :> (
					boxes = KeyDrop[boxes, boxIds];
					wires = DeleteCases[wires, {{Alternatives @@ boxIds, _}, _} | {_, {Alternatives @@ boxIds, _}}];
					selectedBoxes = {}
				),
				"RemoveConnectorSelection"[connectors_List, _] :> (
					boxes = MapAt[Nothing &, boxes, {Key[#[[1]]], 2, #[[2]]} & /@ connectors];
					wires = DeleteCases[wires, {Alternatives @@ connectors, _} | {_, Alternatives @@ connectors}];
					selectedConnectors = {}
				),
				"AddConnector"[boxId_Key, pos_] :> AppendTo[boxes[[boxId, 2]], pos],
				"AddWire"[{Key[boxId1_] | boxId1_, connectorId1_}, {Key[boxId2_] | boxId2_, connectorId2_}] :> AppendTo[wires, {{boxId1, connectorId1}, {boxId2, connectorId2}}]
			}
		]
	);
	canvas = Pane[
		Row[{
			EventHandler[
				Style[
					Graphics[Dynamic[graphics = {
						KeyValueMap[{id, box} |-> {
							FaceForm[None], EdgeForm[If[MemberQ[selectedBoxes, id], Directive[Dashed, Black], Black]], Rectangle @@ box[[1]],
							MapIndexed[With[{color = Switch[{Key[id], #2[[1]]}, targetConnector, Red, {selectedBox, selectedConnector}, Blue, _, Black]}, {If[MemberQ[selectedConnectors, {id, #2[[1]]}], Directive[Dotted, color], color], Circle[#, .01]}] &, box[[2]]]
						}, boxes],
						If[Length[boxPositions] > 1, {FaceForm[None], EdgeForm[Black], Rectangle @@ boxPositions}, Nothing],
						If[wire =!= None, renderWire[wire]],
						renderWire[{boxes[[Key[#[[1, 1]]], 2, #[[1, 2]]]], boxes[[Key[#[[2, 1]]], 2, #[[2, 2]]]], boxes[[Key[#[[1, 1]]], 1]], boxes[[Key[#[[2, 1]]], 1]]}] & /@ wires
					}],
						FilterRules[{opts}, Options[Graphics]],
						ImageSize -> {512, 512},
						PlotRange -> {{0, 1}, {0, 1}},
						Frame -> True,
						FrameTicks -> None,
						ContentSelectable -> False
					],
					Selectable -> True, ShowSelection -> False
				], {
					{"MouseDown", 1} :> (
						startMousePos = mousePos = MousePosition["Graphics"];
						selectedBox = findBoxId[boxes, mousePos];
						prevBoxes = boxes;
						If[ ! MissingQ[selectedBox],
							selectedConnector = findConnector[boxes[[selectedBox]], mousePos];
							If[ MissingQ[selectedConnector],
								do["SelectBox"[selectedBox]];
								dragBoxQ = True
								,
								do["SelectConnector"[selectedBox, selectedConnector]];
								dragConnectorQ = True
							]
							,
							selectedBoxes = {}; selectedConnectors = {}; boxPositions = {mousePos}
						];
					),
					{"MouseDown", 2} :> (
						mousePos = MousePosition["Graphics"];
						selectedBox = findBoxId[boxes, mousePos];
						If[ ! MissingQ[selectedBox],
							do["AddConnector"[selectedBox, RegionNearest[RegionBoundary[Rectangle @@ boxes[[selectedBox, 1]]], mousePos]]]
						]
					),
					"MouseMoved" :> (If[
						Length[boxPositions] >= 1,
						(* draw a new box *)
						boxPositions = PadRight[boxPositions, 2, None]; boxPositions[[2]] = MousePosition["Graphics"]
						
						,
						(* drag stuff *)
						boxPositions = {};
						mousePos = MousePosition["Graphics"];
						If[ dragBoxQ && ! MissingQ[selectedBox], With[{diff = mousePos - startMousePos},
							boxes[[selectedBox]] = "Box"[Transpose[Transpose[prevBoxes[[selectedBox, 1]]] + diff], With[{connectors = prevBoxes[[selectedBox, 2]]}, If[connectors === {}, {}, connectors + Threaded[diff]]]]
						]];
						If[ dragConnectorQ && ! MissingQ[selectedBox] && ! MissingQ[selectedConnector],
							With[{newPos = RegionNearest[RegionBoundary[Rectangle @@ boxes[[selectedBox, 1]]], mousePos]},
								If[ wire === None && EuclideanDistance[newPos, mousePos] < 0.05,
									boxes[[selectedBox, 2, selectedConnector]] = newPos
									,
									wire = {boxes[[selectedBox, 2, selectedConnector]], mousePos, boxes[[selectedBox, 1]], None}
								]
							];
							(* connect wire *)
							With[{otherBox = findBoxId[boxes, mousePos]},
								If[ ! MissingQ[otherBox],
									With[{otherConnector = findConnector[boxes[[otherBox]], mousePos]},
										If[ ! MissingQ[otherConnector],
											targetConnector = {otherBox, otherConnector};
											If[wire =!= None, wire[[2]] = boxes[[otherBox, 2, otherConnector]]; wire[[4]] = boxes[[otherBox, 1]]]
											,
											targetConnector = None
										]
									]
								]
							]
						]
					]),
					{"MouseUp", 1} :> (
						If[Length[boxPositions] > 1 && Area[Rectangle @@ boxPositions] > .005, do["AddBox"[boxPositions]]];
						If[! MissingQ[selectedBox] && ! MissingQ[selectedConnector] && ! MissingQ[targetConnector] && wire =!= None && wire[[4]] =!= None, do["AddWire"[{selectedBox, selectedConnector}, targetConnector]]];
						dragBoxQ = False; dragConnectorQ = False; boxPositions = {}; wire = None
					),
					"MouseEntered" :> (graphicsEnteredQ = True),
					"MouseExited" :> (graphicsEnteredQ = False)
				}
			],
			Dynamic @ Row[{Column[{
				Button["Delete",
					do["RemoveConnectorSelection"[selectedConnectors, {#[[1]], boxes[[Key[#[[1]]], 2, #[[2]]]]} & /@ selectedConnectors]];
					do["RemoveBoxSelection"[selectedBoxes, Lookup[boxes, selectedBoxes]]]
				],
				Button["Print",
					CellPrint[ExpressionCell[Graphics[graphics, PlotRange -> {{0, 1}, {0, 1}}, ContentSelectable -> True], "Input"]]
				],
				Button["Copy boxes",
					CopyToClipboard[<|"Boxes" -> boxes, "Wires" -> wires|>]
				],
				Button["Copy Diagram",
					CopyToClipboard[DiagramNetwork[##, "UnarySpiders" -> False, "BinarySpiders" -> False, "Orientation" -> False, "ShowWireLabels" -> False, VertexCoordinates -> MapIndexed[#2[[1]] -> Mean @ #1[[1]] &, Values[boxes]]] & @@
						KeyValueMap[
							Diagram[#1,
								Replace[#1 /@ Range[Length[#2[[2]]]], Rule @@@ Apply[Construct, wires, {2}], 1],
								"Width" -> Abs[#2[[1, 2, 1]] - #2[[1, 1, 1]]],
								"Height" -> Abs[#2[[1, 2, 2]] - #2[[1, 1, 2]]],
								"LabelFunction" -> ("" &),
								"PortArrows" -> {(point |-> Placed[Automatic, {point - Mean[#2[[1]]], point - Mean[#2[[1]]] + 0.05 connectorNormal[#2[[1]], point]}]) /@ #2[[2]]}
							] &,
							boxes
						]
					]
				]
			}]}]
		}]
	];
	canvas
]


End[];

EndPackage[];

