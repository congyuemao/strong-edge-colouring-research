import Se20Part.TransferAutomaton
import Se20Part.TransferEstimate

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
set_option maxHeartbeats 2000000

@[reducible] def TransferRun : ℕ → Type
  | 0 => Fin 42
  | n+1 => (TransferRun n × Fin 6) × Fin 42

@[reducible] instance transferRunFintype : (n : ℕ) → Fintype (TransferRun n)
  | 0 => inferInstanceAs (Fintype (Fin 42))
  | n+1 => letI := transferRunFintype n
           inferInstanceAs (Fintype ((TransferRun n × Fin 6) × Fin 42))

@[reducible] def runEnd : {n : ℕ} → TransferRun n → Fin 42
  | 0, r => r
  | _+1, r => r.2

@[reducible] def runValid : {n : ℕ} → TransferRun n → Prop
  | 0, _ => True
  | _+1, r => runValid r.1.1 ∧ transferStep (runEnd r.1.1) r.1.2 r.2

@[reducible] def runWeight : {n : ℕ} → TransferRun n → ℚ
  | 0, _ => 1
  | _+1, r => runWeight r.1.1 * transferLetterWeight r.1.2

def runEndpointMass (n : ℕ) (q : Fin 42) : ℚ :=
  ∑ r : TransferRun n, if runValid r ∧ runEnd r = q then runWeight r else 0

theorem runEndpointMass_zero (q : Fin 42) : runEndpointMass 0 q = 1 := by
  simp [runEndpointMass,runEnd,runValid,runWeight,TransferRun]

theorem runEndpointMass_succ (n : ℕ) (q : Fin 42) :
    runEndpointMass (n+1) q = ∑ p, exp31Matrix5710 q p * runEndpointMass n p := by
  have hexpand : runEndpointMass (n+1) q =
      ∑ r : TransferRun n, (if runValid r then runWeight r else 0) * exp31Matrix5710 q (runEnd r) := by
    simp only [runEndpointMass,runValid,runEnd,runWeight]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have he (r : TransferRun n) (d : Fin 6) (p : Fin 42) :
        (if (runValid r ∧ transferStep (runEnd r) d p) ∧ p = q
          then runWeight r * transferLetterWeight d else 0) =
        if p = q then (if runValid r then runWeight r else 0) *
          (if transferStep (runEnd r) d q then transferLetterWeight d else 0) else 0 := by
      by_cases hp : p = q
      · subst p; split_ifs <;> simp_all
      · simp [hp]
    simp_rw [he]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp_rw [← Finset.mul_sum,transferStep_matrix]
  rw [hexpand]
  unfold runEndpointMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have he (p : Fin 42) : exp31Matrix5710 q p *
      (if runValid r ∧ runEnd r = p then runWeight r else 0) =
      if runEnd r = p then (if runValid r then runWeight r else 0) *
        exp31Matrix5710 q (runEnd r) else 0 := by
    by_cases hp : runEnd r = p
    · rw [← hp]; split_ifs <;> simp_all [mul_comm]
    · simp [hp]
  simp_rw [he]
  simp

theorem runEndpointMass_eq_orbit (n : ℕ) :
    runEndpointMass n = transferOrbit exp31Matrix5710 n := by
  induction n with
  | zero => funext q; exact runEndpointMass_zero q
  | succ n ih =>
    funext q
    rw [runEndpointMass_succ,transferOrbit,ih]
    rfl

theorem run_mass (n : ℕ) :
    (∑ r : TransferRun n, if runValid r then runWeight r else 0) =
      transferMass exp31Matrix5710 n := by
  rw [transferMass_eq_sum_orbit,← runEndpointMass_eq_orbit]
  unfold runEndpointMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : runValid r <;> simp [h]

@[reducible] def runAt : {n : ℕ} → TransferRun n → ℕ → Fin 6
  | 0, _, _ => 0
  | n+1, r, j => if j = n then r.1.2 else runAt r.1.1 j

def mkTransferRun (states : ℕ → Fin 42) (letters : ℕ → Fin 6) : (n : ℕ) → TransferRun n
  | 0 => states 0
  | n+1 => ((mkTransferRun states letters n,letters n),states (n+1))

@[simp] theorem runEnd_mk (states : ℕ → Fin 42) (letters : ℕ → Fin 6) (n : ℕ) :
    runEnd (mkTransferRun states letters n) = states n := by cases n <;> rfl

theorem runAt_mk (states : ℕ → Fin 42) (letters : ℕ → Fin 6) (n j : ℕ) (hj : j < n) :
    runAt (mkTransferRun states letters n) j = letters j := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j = n
    · subst j; simp [mkTransferRun,runAt]
    · simp only [mkTransferRun,runAt,if_neg he]
      exact ih (by omega)

theorem runWeight_mk (states : ℕ → Fin 42) (letters : ℕ → Fin 6) (n : ℕ) :
    runWeight (mkTransferRun states letters n) =
      ∏ j ∈ Finset.range n, transferLetterWeight (letters j) := by
  induction n with
  | zero => simp [mkTransferRun,runWeight]
  | succ n ih => simp only [mkTransferRun,runWeight,Finset.prod_range_succ,ih]

theorem runValid_mk (states : ℕ → Fin 42) (letters : ℕ → Fin 6) (n : ℕ)
    (h : ∀ j < n, transferStep (states j) (letters j) (states (j+1))) :
    runValid (mkTransferRun states letters n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact ⟨ih (fun j hj => h j (by omega)),by simpa only [mkTransferRun,runEnd_mk] using h n (by omega)⟩

theorem transferLetterWeight_nonneg (d : Fin 6) : 0 ≤ transferLetterWeight d := by
  unfold transferLetterWeight
  split_ifs <;> norm_num [t5710,beta5710] <;> positivity

theorem runWeight_nonneg {n : ℕ} (r : TransferRun n) : 0 ≤ runWeight r := by
  induction n with
  | zero => norm_num [runWeight]
  | succ n ih => exact mul_nonneg (ih r.1.1) (transferLetterWeight_nonneg r.1.2)

theorem valid_run_mass (n : ℕ) :
    (∑ r : {r : TransferRun n // runValid r}, runWeight r.val) = transferMass exp31Matrix5710 n := by
  rw [← run_mass]
  rw [← Finset.sum_filter]
  symm
  exact Finset.sum_subtype (p := runValid) (Finset.univ.filter runValid) (by simp) runWeight

end Se20Part
