import Se20Part.CertificateEntries

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Integer numerator of multiplication by the concrete matrix. -/
def certificateStep (x : Fin 42 → ℚ) : Fin 42 → ℚ :=
  ![0, 0, 0, 0, 0, 0, 21654 * x 15 + 21654 * x 16 + 21654 * x 17 + 21654 * x 18 + 21654 * x 19 + 21654 * x 20 + 21654 * x 22 + 21654 * x 23 + 21654 * x 24 + 21654 * x 25 + 21654 * x 26 + 21654 * x 27 + 21654 * x 29 + 21654 * x 30 + 21654 * x 31 + 21654 * x 32 + 21654 * x 33 + 21654 * x 34, 19663518 * x 1 + 64962 * x 8 + 64962 * x 15 + 64962 * x 22 + 64962 * x 29 + 64962 * x 30 + 64962 * x 31 + 64962 * x 32 + 64962 * x 33 + 64962 * x 34, 19663518 * x 2, 19468632 * x 3, 18883974 * x 4, 17130000 * x 5 + 17130000 * x 6, 0, 194886 * x 3 + 779544 * x 4 + 2533518 * x 5 + 2533518 * x 6 + 64962 * x 9 + 64962 * x 10 + 64962 * x 11 + 64962 * x 12 + 64962 * x 13 + 64962 * x 16 + 64962 * x 17 + 64962 * x 18 + 64962 * x 19 + 64962 * x 20 + 64962 * x 23 + 64962 * x 24 + 64962 * x 25 + 64962 * x 26 + 64962 * x 27, 19663518 * x 8 + 194886 * x 15 + 194886 * x 22 + 194886 * x 29 + 194886 * x 30 + 194886 * x 31 + 194886 * x 32 + 194886 * x 33 + 194886 * x 34, 19663518 * x 9 + 194886 * x 16 + 194886 * x 23 + 194886 * x 24 + 194886 * x 25 + 194886 * x 26 + 194886 * x 27, 19468632 * x 10, 18883974 * x 11 + 18883974 * x 12 + 18883974 * x 13, 0, 0, 194886 * x 10 + 779544 * x 11 + 779544 * x 12 + 779544 * x 13 + 194886 * x 17 + 194886 * x 18 + 194886 * x 19 + 194886 * x 20, 19468632 * x 15 + 584658 * x 22 + 584658 * x 29 + 584658 * x 30 + 584658 * x 31 + 584658 * x 32 + 584658 * x 33 + 584658 * x 34, 19468632 * x 16 + 584658 * x 23 + 584658 * x 24 + 584658 * x 25 + 584658 * x 26 + 584658 * x 27, 19468632 * x 17 + 19468632 * x 18 + 19468632 * x 19 + 19468632 * x 20, 0, 0, 0, 0, 18883974 * x 22 + 1753974 * x 29 + 1753974 * x 30 + 1753974 * x 31 + 1753974 * x 32 + 1753974 * x 33 + 1753974 * x 34, 18883974 * x 23 + 18883974 * x 24 + 18883974 * x 25 + 18883974 * x 26 + 18883974 * x 27, 0, 0, 0, 0, 0, 17130000 * x 29 + 17130000 * x 30 + 17130000 * x 31 + 17130000 * x 32 + 17130000 * x 33 + 17130000 * x 34, 0, 0, 0, 0, 0, 0]

/-- Expanded multiplication: independently checked against the original 42-state definition. -/
theorem certificateStep_eq (x : Fin 42 → ℚ) :
    certificateStep x = fun i => 5710000 * (exp31Matrix5710.mulVec x) i := by
  funext i
  simp only [Matrix.mulVec,dotProduct,certificateEntries_correct]
  fin_cases i <;>
    norm_num [certificateStep,certificateEntries,Fin.sum_univ_succ] <;> ring

def certificateRho : ℚ := 24657/25000

/-- Six rounded-up transient vectors. All rounding is checked below. -/
def certificateTransient : Fin 7 → Fin 42 → ℚ :=
  ![![1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000], ![0, 0, 0, 0, 0, 0, 68262, 3546091, 3443699, 3409568, 3307176, 6000000, 0, 1228704, 3716744, 3648483, 3409568, 9921528, 0, 0, 580222, 4126312, 3921528, 13638272, 0, 0, 0, 0, 5150231, 16535880, 0, 0, 0, 0, 0, 18000000, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 195893, 313429, 0, 0, 0, 204786, 0, 502372, 12681811, 12323378, 11276041, 23906596, 0, 0, 1458189, 14534424, 13021603, 35806429, 0, 0, 0, 0, 18048606, 45104164, 0, 0, 0, 0, 0, 49607640, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 541906, 801492, 0, 0, 0, 587679, 0, 919187, 2404475, 1606956, 0, 2338696, 0, 0, 962260, 47969003, 42112716, 86482954, 0, 0, 0, 0, 56919640, 118418157, 0, 0, 0, 0, 0, 135312492, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 955362, 1844624, 0, 0, 0, 1625718, 0, 1279048, 5533870, 2951720, 0, 4983471, 0, 0, 318386, 21916094, 8855158, 11254834, 0, 0, 0, 0, 175649353, 286014336, 0, 0, 0, 0, 0, 355254471, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1192214, 3388278, 0, 0, 0, 2866086, 0, 645304, 10164832, 384135, 0, 9606572, 0, 0, 577522, 40256351, 1152405, 18077041, 0, 0, 0, 0, 117142257, 37221715, 0, 0, 0, 0, 0, 858043008, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 254158, 440949, 0, 0, 0, 3576642, 0, 890456, 1322845, 616982, 0, 11612785, 0, 0, 826974, 5238936, 1850944, 34723359, 0, 0, 0, 0, 15244818, 59783954, 0, 0, 0, 0, 0, 111665145, 0, 0, 0, 0, 0, 0]]

def certificateVector : Fin 42 → ℚ :=
  ![0, 0, 0, 0, 0, 0, 1279596, 2803574, 0, 0, 0, 3892193, 0, 1675086, 8410722, 2408840, 0, 18668115, 0, 0, 1467434, 33309449, 7226519, 69608626, 0, 0, 0, 0, 96927421, 233410619, 0, 0, 0, 0, 0, 709973488, 0, 0, 0, 0, 0, 0]

theorem certificateVector_nonneg : ∀ i, 0 ≤ certificateVector i := by
  intro i; fin_cases i <;> norm_num [certificateVector]

theorem certificateVector_contract :
    ∀ i, certificateStep certificateVector i ≤
      5710000 * certificateRho * certificateVector i := by
  intro i; fin_cases i <;> norm_num [certificateStep,certificateVector,certificateRho]

theorem certificateTransient_start : certificateTransient 0 = fun _ => 1000000 := by
  funext i; fin_cases i <;> norm_num [certificateTransient]

theorem certificateTransient_step : ∀ k : Fin 6, ∀ i,
    certificateStep (certificateTransient k.castSucc) i ≤
      5710000 * certificateTransient k.succ i := by
  intro k i; fin_cases k <;> fin_cases i <;>
    norm_num [certificateStep,certificateTransient,Fin.succ,Fin.castSucc]

theorem certificateTransient_end : ∀ i,
    certificateTransient 6 i ≤ certificateRho^6 * certificateVector i := by
  intro i; fin_cases i <;>
    norm_num [certificateTransient,certificateVector,certificateRho]

theorem certificateVector_sum :
    ∑ i, certificateVector i ≤ 1200 * 1000000 := by
  norm_num [certificateVector,Fin.sum_univ_succ]

theorem certificateTransient_sum : ∀ k : Fin 7,
    ∑ i, certificateTransient k i ≤ 1200 * 1000000 * certificateRho^k.val := by
  intro k; fin_cases k <;>
    norm_num [certificateTransient,certificateRho,Fin.sum_univ_succ]

end Se20Part

