PacletDirectoryLoad["DiagrammaticComputation"]
<< Wolfram`DiagrammaticComputation`
Quiet @ Needs["Wolfram`TensorNetworks`" -> "TN`"]

tensor = Inactive[ArrayDot][
    RandomReal[1, {2, 2}], 
    Inactive[Transpose][
        Inactive[ArrayDot][
            Inactive[Transpose][
                RandomReal[1, {2, 2, 2}], 
                Cycles[{{1, 3, 2}}]
            ],
            RandomReal[1, {2}],
            1
        ],
        Cycles[{{1, 2}}]
    ],
    1
]

res1 = TN`ActivateTensors @ tensor
res2 = TN`ActivateTensors @ DiagramTensor @ TensorDiagram @ tensor

VerificationTest[res1, res2, "TestID" -> "test_tensor"]