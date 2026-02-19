PacletDirectoryLoad["DiagrammaticComputation"]
<< Wolfram`DiagrammaticComputation`
Quiet @ Needs["Wolfram`TensorNetworks`" -> "TN`"]

SeedRandom[1]

(* Helper function for roundtrip testing with tolerance for floating-point differences *)
roundtripTest[tensor_, testID_] := With[{
    res1 = TN`ActivateTensors @ tensor,
    res2 = TN`ActivateTensors @ DiagramTensor @ TensorDiagram @ tensor
},
    VerificationTest[res1, res2, "TestID" -> testID, SameTest -> (Max[Abs[#1 - #2]] < 10^-10 &)]
]

(* Test 1: Original nested ArrayDot with Transpose *)
tensor1 = Inactive[ArrayDot][
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
roundtripTest[tensor1, "nested_arraydot_transpose"]

(* Test 2: Simple ArrayDot - matrix times vector *)
tensor2 = Inactive[ArrayDot][RandomReal[1, {3, 3}], RandomReal[1, {3}], 1]
roundtripTest[tensor2, "simple_matrix_vector"]

(* Test 3: Simple ArrayDot - matrix times matrix *)
tensor3 = Inactive[ArrayDot][RandomReal[1, {3, 3}], RandomReal[1, {3, 3}], 1]
roundtripTest[tensor3, "simple_matrix_matrix"]

(* Test 4: Chained ArrayDot - matrix . (3D . vector) *)
tensor4 = Inactive[ArrayDot][
    RandomReal[1, {3, 3}], 
    Inactive[ArrayDot][RandomReal[1, {3, 3, 3}], RandomReal[1, {3}], 1], 
    1
]
roundtripTest[tensor4, "chained_matrix_3d_vector"]

(* Test 5: Chained ArrayDot - 3D . (matrix . vector) *)
tensor5 = Inactive[ArrayDot][
    RandomReal[1, {3, 3, 3}], 
    Inactive[ArrayDot][RandomReal[1, {3, 3}], RandomReal[1, {3}], 1], 
    1
]
roundtripTest[tensor5, "chained_3d_matrix_vector"]

(* Test 6: Double contraction - higher k value *)
tensor6 = Inactive[ArrayDot][RandomReal[1, {3, 3, 3}], RandomReal[1, {3, 3, 3}], 2]
roundtripTest[tensor6, "double_contraction_3d"]

(* Test 7: Triple chain - A . (B . (C . D)) *)
tensor7 = Inactive[ArrayDot][
    RandomReal[1, {2, 2}],
    Inactive[ArrayDot][
        RandomReal[1, {2, 2}],
        Inactive[ArrayDot][RandomReal[1, {2, 2}], RandomReal[1, {2}], 1],
        1
    ],
    1
]
roundtripTest[tensor7, "triple_chain_matrices"]

(* Test 8: With explicit Transpose *)
tensor8 = Inactive[ArrayDot][
    Inactive[Transpose][RandomReal[1, {3, 3}], Cycles[{{1, 2}}]],
    RandomReal[1, {3}],
    1
]
roundtripTest[tensor8, "transpose_then_contract"]

(* Test 9: 4D tensor contraction *)
tensor9 = Inactive[ArrayDot][RandomReal[1, {2, 2, 2, 2}], RandomReal[1, {2, 2}], 2]
roundtripTest[tensor9, "4d_with_matrix"]

(* Test 10: Multiple contractions in chain *)
tensor10 = Inactive[ArrayDot][
    RandomReal[1, {2, 2, 2}],
    Inactive[ArrayDot][RandomReal[1, {2, 2, 2}], RandomReal[1, {2, 2}], 2],
    1
]
roundtripTest[tensor10, "chain_with_double_contraction"]

(* Test 11: MINIMAL FAILING CASE - Outer Transpose wrapping composition with inner Transposes *)
(* Pattern: Transpose[Tr(vec.3D) . Tr(3D.vec)] - produces transposed result *)
innerA11 = Inactive[Transpose][
    Inactive[ArrayDot][RandomReal[1, {2}], RandomReal[1, {2, 2, 2}], 1],
    Cycles[{{1, 2}}]
]
innerB11 = Inactive[Transpose][
    Inactive[ArrayDot][RandomReal[1, {2, 2, 2}], RandomReal[1, {2}], 1],
    Cycles[{{1, 2}}]
]
tensor11 = Inactive[Transpose][
    Inactive[ArrayDot][innerA11, innerB11, 1],
    Cycles[{{1, 2}}]
]
roundtripTest[tensor11, "outer_transpose_with_inner_transposes"]

(* Test 12: 3-cycle permutation on 3D tensor *)
tensor12 = Inactive[Transpose][RandomReal[1, {2, 3, 4}], Cycles[{{1, 2, 3}}]]
roundtripTest[tensor12, "3_cycle_permutation"]

(* Test 13: Full contraction to scalar - matrix trace via double contraction *)
tensor13 = Inactive[ArrayDot][RandomReal[1, {3, 3}], RandomReal[1, {3, 3}], 2]
roundtripTest[tensor13, "full_contraction_scalar"]

(* Test 14: TensorContract - trace of a matrix *)
tensor14 = Inactive[TensorContract][RandomReal[1, {3, 3}], {{1, 2}}]
roundtripTest[tensor14, "tensor_contract_trace"]

(* Test 15: TensorContract on 4D tensor - contract two pairs *)
tensor15 = Inactive[TensorContract][RandomReal[1, {2, 3, 3, 2}], {{1, 4}, {2, 3}}]
roundtripTest[tensor15, "tensor_contract_two_pairs"]

(* Test 16: Double transpose - Transpose[Transpose[A]] should roundtrip *)
tensor16 = Inactive[Transpose][
    Inactive[Transpose][RandomReal[1, {2, 3, 4}], Cycles[{{1, 3}}]],
    Cycles[{{1, 2}}]
]
roundtripTest[tensor16, "double_transpose"]

(* Test 17: Transpose after contraction *)
tensor17 = Inactive[Transpose][
    Inactive[ArrayDot][RandomReal[1, {2, 3}], RandomReal[1, {3, 4}], 1],
    Cycles[{{1, 2}}]
]
roundtripTest[tensor17, "transpose_after_contraction"]

(* Test 18: 5D tensor with 3-cycle permutation *)
tensor18 = Inactive[Transpose][RandomReal[1, {2, 2, 2, 2, 2}], Cycles[{{1, 3, 5}}]]
roundtripTest[tensor18, "5d_3_cycle"]

(* Test 19: Contraction of transposed tensors *)
tensor19 = Inactive[ArrayDot][
    Inactive[Transpose][RandomReal[1, {3, 2}], Cycles[{{1, 2}}]],
    Inactive[Transpose][RandomReal[1, {4, 3}], Cycles[{{1, 2}}]],
    1
]
roundtripTest[tensor19, "contract_transposed_tensors"]

(* Tests 20-24: Complex nesting patterns from RandomTensorNetwork *)

(* Test 20: 3-node network - ArrayDot[mat, ArrayDot[Tr[mat], mat, 1], 2] -> scalar *)
tensor20 = Inactive[ArrayDot][
    RandomReal[1, {2, 2}],
    Inactive[ArrayDot][
        Inactive[Transpose][RandomReal[1, {2, 2}], Cycles[{{1, 2}}]],
        RandomReal[1, {2, 2}],
        1
    ],
    2
]
roundtripTest[tensor20, "network_3node_scalar"]

(* Test 21: 4-node network - ArrayDot[mat, ArrayDot[mat, Tr[ArrayDot[mat, Tr[mat], 1]], 1], 2] *)
tensor21 = Inactive[ArrayDot][
    RandomReal[1, {2, 2}],
    Inactive[ArrayDot][
        RandomReal[1, {2, 2}],
        Inactive[Transpose][
            Inactive[ArrayDot][
                RandomReal[1, {2, 2}],
                Inactive[Transpose][RandomReal[1, {2, 2}], Cycles[{{1, 2}}]],
                1
            ],
            Cycles[{{1, 2}}]
        ],
        1
    ],
    2
]
roundtripTest[tensor21, "network_4node_double_transpose"]

(* Test 22: dim=3 network - ArrayDot[3x3, Tr[ArrayDot[3x3, 3x3, 1]], 2] *)
tensor22 = Inactive[ArrayDot][
    RandomReal[1, {3, 3}],
    Inactive[Transpose][
        Inactive[ArrayDot][RandomReal[1, {3, 3}], RandomReal[1, {3, 3}], 1],
        Cycles[{{1, 2}}]
    ],
    2
]
roundtripTest[tensor22, "network_dim3_transpose_contract"]

(* Test 23: Outer 3-cycle on heterogeneous dims - Transpose[ArrayDot[{2,3,4},{4,5},1], 3-cycle] *)
(* Result is {2,3,5} with 3-cycle → {5,2,3} *)
tensor23 = Inactive[Transpose][
    Inactive[ArrayDot][RandomReal[1, {2, 3, 4}], RandomReal[1, {4, 5}], 1],
    Cycles[{{1, 2, 3}}]
]
roundtripTest[tensor23, "hetero_dim_3cycle"]

(* Test 24: TensorContract on TensorProduct - partial trace *)
tensor24 = Inactive[TensorContract][
    Inactive[TensorProduct][RandomReal[1, {2, 3}], RandomReal[1, {3, 2}]],
    {{2, 3}}
]
roundtripTest[tensor24, "tensorcontract_product"]

(* Tests 25-32: Generated from RandomTensorNetwork structures with random arrays *)

(* Test 25: net{3,3} dim2 -> scalar: 3 matrices, transposes, full contraction *)
tensor25 = Inactive[ArrayDot][RandomReal[1, {2, 2}],
    Inactive[ArrayDot][
        Inactive[Transpose][RandomReal[1, {2, 2}], Cycles[{{1, 2}}]],
        Inactive[Transpose][RandomReal[1, {2, 2}], Cycles[{{1, 2}}]],
    1],
2]
roundtripTest[tensor25, "net3x3_dim2_scalar"]

(* Test 26: net{4,3} dim3 -> scalar: vector-tensor chain with 3-cycle *)
tensor26 = Inactive[ArrayDot][RandomReal[1, {2}],
    Inactive[ArrayDot][RandomReal[1, {2}],
        Inactive[Transpose][
            Inactive[ArrayDot][RandomReal[1, {3}], RandomReal[1, {3, 2, 2}], 1],
            Cycles[{{1, 2}}]],
    1],
1]
roundtripTest[tensor26, "net4x3_dim3_scalar"]

(* Test 27: net{5,3} dim4 -> scalar: TensorProduct with inner dot, transpose *)
tensor27 = Inactive[ArrayDot][
    Inactive[TensorProduct][RandomReal[1, {4}],
        Inactive[ArrayDot][RandomReal[1, {3}], RandomReal[1, {3}], 1]],
    Inactive[ArrayDot][
        Inactive[Transpose][RandomReal[1, {4, 4}], Cycles[{{1, 2}}]],
        RandomReal[1, {4}],
    1],
1]
roundtripTest[tensor27, "net5x3_dim4_scalar"]

(* Test 28: net{4,4} dim2 -> {2,2}: outer transpose, inner 3D tensor with Cycles[{{2,3}}] *)
tensor28 = Inactive[Transpose][
    Inactive[ArrayDot][RandomReal[1, {2, 2}],
        Inactive[ArrayDot][RandomReal[1, {2, 2}],
            Inactive[ArrayDot][
                Inactive[Transpose][RandomReal[1, {2, 2, 2}], Cycles[{{2, 3}}]],
                RandomReal[1, {2}],
            1],
        1],
    1],
Cycles[{{1, 2}}]]
roundtripTest[tensor28, "net4x4_dim2_array"]

(* Test 29: net{4,4} dim4 -> {3,3}: triple transpose chain with 3D tensor *)
tensor29 = Inactive[Transpose][
    Inactive[ArrayDot][
        Inactive[Transpose][RandomReal[1, {3, 3}], Cycles[{{1, 2}}]],
        Inactive[ArrayDot][
            Inactive[Transpose][RandomReal[1, {3, 3}], Cycles[{{1, 2}}]],
            Inactive[ArrayDot][RandomReal[1, {3, 3, 3}], RandomReal[1, {3}], 1],
        1],
    1],
Cycles[{{1, 2}}]]
roundtripTest[tensor29, "net4x4_dim4_array"]

(* Test 30: net{4,5} dim2 -> {2,2}: 3-cycle permutations on rank-3 tensors *)
tensor30 = Inactive[ArrayDot][RandomReal[1, {2, 2, 2}],
    Inactive[ArrayDot][
        Inactive[Transpose][RandomReal[1, {2, 2}], Cycles[{{1, 2}}]],
        Inactive[Transpose][
            Inactive[ArrayDot][
                Inactive[Transpose][RandomReal[1, {2, 2}], Cycles[{{1, 2}}]],
                Inactive[Transpose][RandomReal[1, {2, 2, 2}], Cycles[{{1, 2, 3}}]],
            1],
        Cycles[{{1, 2, 3}}]],
    1],
2]
roundtripTest[tensor30, "net4x5_dim2_3cycle"]

(* Test 31: net{5,5} dim2 -> {2,2}: TensorProduct + nested ArrayDot + 3-cycle transpose *)
tensor31 = Inactive[Transpose][
    Inactive[TensorProduct][RandomReal[1, {2}],
        Inactive[ArrayDot][RandomReal[1, {2, 2, 2}],
            Inactive[Transpose][
                Inactive[ArrayDot][
                    Inactive[Transpose][RandomReal[1, {2, 2}], Cycles[{{1, 2}}]],
                    Inactive[Transpose][
                        Inactive[ArrayDot][RandomReal[1, {2, 2}], RandomReal[1, {2, 2}], 1],
                    Cycles[{{1, 2}}]],
                1],
            Cycles[{{1, 2}}]],
        2]],
Cycles[{{1, 2}}]]
roundtripTest[tensor31, "net5x5_dim2_tprod"]

(* Test 32: net{4,6} dim2 -> {2,2}: 4-tensor chain with 3-cycle and 4-cycle permutations *)
tensor32 = Inactive[ArrayDot][
    Inactive[Transpose][RandomReal[1, {2, 2, 2}], Cycles[{{1, 2}}]],
    Inactive[Transpose][
        Inactive[ArrayDot][RandomReal[1, {2, 2, 2}],
            Inactive[Transpose][
                Inactive[ArrayDot][RandomReal[1, {2, 2, 2}], RandomReal[1, {2, 2, 2}], 1],
            Cycles[{{2, 3, 4}}]],
        2],
    Cycles[{{1, 2, 3}}]],
2]
roundtripTest[tensor32, "net4x6_dim2_4cycle"]