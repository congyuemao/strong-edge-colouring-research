import Se20Part.TransferMatrix
noncomputable section
open scoped Classical BigOperators
namespace Se20Part
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def certificateEntries : Matrix (Fin 42) (Fin 42) ℚ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21654, 21654, 21654, 21654, 21654, 21654, 0, 21654, 21654, 21654, 21654, 21654, 21654, 0, 21654, 21654, 21654, 21654, 21654, 21654, 0, 0, 0, 0, 0, 0, 0], ![0, 19663518, 0, 0, 0, 0, 0, 0, 64962, 0, 0, 0, 0, 0, 0, 64962, 0, 0, 0, 0, 0, 0, 64962, 0, 0, 0, 0, 0, 0, 64962, 64962, 64962, 64962, 64962, 64962, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 19663518, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 19468632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 18883974, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 17130000, 17130000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 194886, 779544, 2533518, 2533518, 0, 0, 64962, 64962, 64962, 64962, 64962, 0, 0, 64962, 64962, 64962, 64962, 64962, 0, 0, 64962, 64962, 64962, 64962, 64962, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 19663518, 0, 0, 0, 0, 0, 0, 194886, 0, 0, 0, 0, 0, 0, 194886, 0, 0, 0, 0, 0, 0, 194886, 194886, 194886, 194886, 194886, 194886, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 19663518, 0, 0, 0, 0, 0, 0, 194886, 0, 0, 0, 0, 0, 0, 194886, 194886, 194886, 194886, 194886, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19468632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18883974, 18883974, 18883974, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 194886, 779544, 779544, 779544, 0, 0, 0, 194886, 194886, 194886, 194886, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19468632, 0, 0, 0, 0, 0, 0, 584658, 0, 0, 0, 0, 0, 0, 584658, 584658, 584658, 584658, 584658, 584658, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19468632, 0, 0, 0, 0, 0, 0, 584658, 584658, 584658, 584658, 584658, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19468632, 19468632, 19468632, 19468632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18883974, 0, 0, 0, 0, 0, 0, 1753974, 1753974, 1753974, 1753974, 1753974, 1753974, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18883974, 18883974, 18883974, 18883974, 18883974, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17130000, 17130000, 17130000, 17130000, 17130000, 17130000, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
theorem certificateEntries_column_0 (i : Fin 42) :
    exp31Matrix5710 i 0 = certificateEntries i 0 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_1 (i : Fin 42) :
    exp31Matrix5710 i 1 = certificateEntries i 1 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_2 (i : Fin 42) :
    exp31Matrix5710 i 2 = certificateEntries i 2 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_3 (i : Fin 42) :
    exp31Matrix5710 i 3 = certificateEntries i 3 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_4 (i : Fin 42) :
    exp31Matrix5710 i 4 = certificateEntries i 4 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_5 (i : Fin 42) :
    exp31Matrix5710 i 5 = certificateEntries i 5 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_6 (i : Fin 42) :
    exp31Matrix5710 i 6 = certificateEntries i 6 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_7 (i : Fin 42) :
    exp31Matrix5710 i 7 = certificateEntries i 7 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_8 (i : Fin 42) :
    exp31Matrix5710 i 8 = certificateEntries i 8 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_9 (i : Fin 42) :
    exp31Matrix5710 i 9 = certificateEntries i 9 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_10 (i : Fin 42) :
    exp31Matrix5710 i 10 = certificateEntries i 10 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_11 (i : Fin 42) :
    exp31Matrix5710 i 11 = certificateEntries i 11 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_12 (i : Fin 42) :
    exp31Matrix5710 i 12 = certificateEntries i 12 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_13 (i : Fin 42) :
    exp31Matrix5710 i 13 = certificateEntries i 13 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_14 (i : Fin 42) :
    exp31Matrix5710 i 14 = certificateEntries i 14 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_15 (i : Fin 42) :
    exp31Matrix5710 i 15 = certificateEntries i 15 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_16 (i : Fin 42) :
    exp31Matrix5710 i 16 = certificateEntries i 16 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_17 (i : Fin 42) :
    exp31Matrix5710 i 17 = certificateEntries i 17 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_18 (i : Fin 42) :
    exp31Matrix5710 i 18 = certificateEntries i 18 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_19 (i : Fin 42) :
    exp31Matrix5710 i 19 = certificateEntries i 19 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_20 (i : Fin 42) :
    exp31Matrix5710 i 20 = certificateEntries i 20 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_21 (i : Fin 42) :
    exp31Matrix5710 i 21 = certificateEntries i 21 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_22 (i : Fin 42) :
    exp31Matrix5710 i 22 = certificateEntries i 22 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_23 (i : Fin 42) :
    exp31Matrix5710 i 23 = certificateEntries i 23 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_24 (i : Fin 42) :
    exp31Matrix5710 i 24 = certificateEntries i 24 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_25 (i : Fin 42) :
    exp31Matrix5710 i 25 = certificateEntries i 25 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_26 (i : Fin 42) :
    exp31Matrix5710 i 26 = certificateEntries i 26 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_27 (i : Fin 42) :
    exp31Matrix5710 i 27 = certificateEntries i 27 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_28 (i : Fin 42) :
    exp31Matrix5710 i 28 = certificateEntries i 28 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_29 (i : Fin 42) :
    exp31Matrix5710 i 29 = certificateEntries i 29 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_30 (i : Fin 42) :
    exp31Matrix5710 i 30 = certificateEntries i 30 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_31 (i : Fin 42) :
    exp31Matrix5710 i 31 = certificateEntries i 31 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_32 (i : Fin 42) :
    exp31Matrix5710 i 32 = certificateEntries i 32 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_33 (i : Fin 42) :
    exp31Matrix5710 i 33 = certificateEntries i 33 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_34 (i : Fin 42) :
    exp31Matrix5710 i 34 = certificateEntries i 34 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_35 (i : Fin 42) :
    exp31Matrix5710 i 35 = certificateEntries i 35 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_36 (i : Fin 42) :
    exp31Matrix5710 i 36 = certificateEntries i 36 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_37 (i : Fin 42) :
    exp31Matrix5710 i 37 = certificateEntries i 37 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_38 (i : Fin 42) :
    exp31Matrix5710 i 38 = certificateEntries i 38 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_39 (i : Fin 42) :
    exp31Matrix5710 i 39 = certificateEntries i 39 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_40 (i : Fin 42) :
    exp31Matrix5710 i 40 = certificateEntries i 40 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_column_41 (i : Fin 42) :
    exp31Matrix5710 i 41 = certificateEntries i 41 / 5710000 := by
  fin_cases i <;> norm_num [exp31Matrix5710,exp31Matrix,transferL,transferS,
    t5710,beta5710,certificateEntries,Finset.sum_Icc_succ_top]
theorem certificateEntries_correct (i j : Fin 42) :
    exp31Matrix5710 i j = certificateEntries i j / 5710000 := by
  fin_cases j
  · exact certificateEntries_column_0 i
  · exact certificateEntries_column_1 i
  · exact certificateEntries_column_2 i
  · exact certificateEntries_column_3 i
  · exact certificateEntries_column_4 i
  · exact certificateEntries_column_5 i
  · exact certificateEntries_column_6 i
  · exact certificateEntries_column_7 i
  · exact certificateEntries_column_8 i
  · exact certificateEntries_column_9 i
  · exact certificateEntries_column_10 i
  · exact certificateEntries_column_11 i
  · exact certificateEntries_column_12 i
  · exact certificateEntries_column_13 i
  · exact certificateEntries_column_14 i
  · exact certificateEntries_column_15 i
  · exact certificateEntries_column_16 i
  · exact certificateEntries_column_17 i
  · exact certificateEntries_column_18 i
  · exact certificateEntries_column_19 i
  · exact certificateEntries_column_20 i
  · exact certificateEntries_column_21 i
  · exact certificateEntries_column_22 i
  · exact certificateEntries_column_23 i
  · exact certificateEntries_column_24 i
  · exact certificateEntries_column_25 i
  · exact certificateEntries_column_26 i
  · exact certificateEntries_column_27 i
  · exact certificateEntries_column_28 i
  · exact certificateEntries_column_29 i
  · exact certificateEntries_column_30 i
  · exact certificateEntries_column_31 i
  · exact certificateEntries_column_32 i
  · exact certificateEntries_column_33 i
  · exact certificateEntries_column_34 i
  · exact certificateEntries_column_35 i
  · exact certificateEntries_column_36 i
  · exact certificateEntries_column_37 i
  · exact certificateEntries_column_38 i
  · exact certificateEntries_column_39 i
  · exact certificateEntries_column_40 i
  · exact certificateEntries_column_41 i
end Se20Part

