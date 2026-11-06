import Se20Part.TransferRuns

noncomputable section
open scoped Classical BigOperators
open Finset
namespace Se20Part
set_option maxHeartbeats 2000000

def wordExtend {n : ℕ} (f : SpanningPattern n) (j : ℕ) : Fin 6 :=
  f ⟨min j n,by omega⟩

theorem wordExtend_at {n : ℕ} (f : SpanningPattern n) (i : Fin (n+1)) :
    wordExtend f i.val = f i := by
  unfold wordExtend
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

theorem spanningPattern_validNat {n : ℕ} {f : SpanningPattern n} (hf : ValidSpanningPattern f) :
    ValidDepthPattern (fun j => (wordExtend f j).val) n := by
  refine ⟨?_,?_,?_,?_⟩
  · have hh : wordExtend f 0 = f 0 := wordExtend_at f 0
    rw [hh]
    exact Nat.pos_of_ne_zero hf.1
  · intro i hi
    exact Nat.le_of_lt_succ (wordExtend f i).isLt
  · intro i j hij hj hfi hfj
    let a : Fin (n+1) := ⟨i,by omega⟩
    let b : Fin (n+1) := ⟨j,by omega⟩
    have ha : wordExtend f i = f a := wordExtend_at f a
    have hb : wordExtend f j = f b := wordExtend_at f b
    have h := hf.2.1 a b hij (by rw [← ha]; omega) (by rw [← hb]; omega)
    simpa only [ha,hb] using h
  · intro j hj
    obtain ⟨a,b,ha,hb,hfa,hfb,hspan⟩ := hf.2.2 j hj
    refine ⟨a.val,b.val,ha,hb,by omega,?_,?_,?_⟩
    · rw [wordExtend_at]; omega
    · rw [wordExtend_at]; omega
    · simpa only [wordExtend_at] using hspan

abbrev RootedPattern (n k : ℕ) (hk : k ≤ n) (d : Fin 6) :=
  {f : SpanningPattern n // ValidSpanningPattern f ∧ f ⟨k,by omega⟩ = d}

def rootedPatternWeight {n : ℕ} (k : ℕ) (f : SpanningPattern n) : ℚ :=
  (∏ j ∈ range k, transferLetterWeight (wordExtend f (n-(n-k+j+1)))) *
    (∏ j ∈ range (n-k), transferLetterWeight (wordExtend f (k+j+1)))

theorem rootedPattern_runs {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) {f : SpanningPattern n}
    (hf : ValidSpanningPattern f) :
    ∃ L : TransferRun k, ∃ R : TransferRun (n-k), runValid L ∧ runValid R ∧
      (∀ j < k, runAt L j = wordExtend f (k-(j+1))) ∧
      (∀ j < n-k, runAt R j = wordExtend f (k+j+1)) ∧
      runWeight L * runWeight R = rootedPatternWeight k f := by
  have hfn := spanningPattern_validNat hf
  obtain ⟨q,hq⟩ := hfn.exists_run
  obtain ⟨qr,hqr⟩ := (hfn.reverse hn).exists_run
  let L := mkTransferRun (fun j => qr (n-k+j)) (fun j => wordExtend f (n-(n-k+j+1))) k
  let R := mkTransferRun (fun j => q (k+j)) (fun j => wordExtend f (k+j+1)) (n-k)
  have hl : runValid L := by
    apply runValid_mk
    intro j hj
    simpa only [Nat.add_assoc] using hqr (n-k+j) (by omega)
  have hr : runValid R := by
    apply runValid_mk
    intro j hj
    simpa only [Nat.add_assoc] using hq (k+j) (by omega)
  refine ⟨L,R,hl,hr,?_,?_,?_⟩
  · intro j hj
    have hh := runAt_mk (fun j => qr (n-k+j)) (fun j => wordExtend f (n-(n-k+j+1))) k j hj
    have he : n-(n-k+j+1) = k-(j+1) := by omega
    simpa only [he] using hh
  · intro j hj
    exact runAt_mk _ _ _ _ hj
  · simp only [L,R,runWeight_mk,rootedPatternWeight]

theorem rootedPattern_convolution {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (d : Fin 6) :
    (∑ f : RootedPattern n k hk d, rootedPatternWeight k f.val) ≤
      transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (n-k) := by
  let A := RootedPattern n k hk d
  choose L R hL hR hleft hright hweight using fun f : A => rootedPattern_runs hn hk f.property.1
  let φ : A → {r : TransferRun k // runValid r} × {r : TransferRun (n-k) // runValid r} :=
    fun f => (⟨L f,hL f⟩,⟨R f,hR f⟩)
  have hinj : Function.Injective φ := by
    intro f g heq
    have hLe : L f = L g := congrArg (fun p : {r : TransferRun k // runValid r} ×
      {r : TransferRun (n-k) // runValid r} => p.1.val) heq
    have hRe : R f = R g := congrArg (fun p : {r : TransferRun k // runValid r} ×
      {r : TransferRun (n-k) // runValid r} => p.2.val) heq
    apply Subtype.ext
    funext i
    rcases lt_trichotomy i.val k with hi | hi | hi
    · have hidx : k-(k-i.val-1+1) = i.val := by omega
      have hh := congrArg (fun r : TransferRun k => runAt r (k-i.val-1)) hLe
      rw [hleft f _ (by omega),hleft g _ (by omega),hidx,wordExtend_at,wordExtend_at] at hh
      exact hh
    · have he : i = ⟨k,by omega⟩ := Fin.ext hi
      rw [he,f.property.2,g.property.2]
    · have hidx : k+(i.val-k-1)+1 = i.val := by omega
      have hh := congrArg (fun r : TransferRun (n-k) => runAt r (i.val-k-1)) hRe
      rw [hright f _ (by omega),hright g _ (by omega),hidx,wordExtend_at,wordExtend_at] at hh
      exact hh
  let w : {r : TransferRun k // runValid r} × {r : TransferRun (n-k) // runValid r} → ℚ :=
    fun p => runWeight p.1.val * runWeight p.2.val
  have hsum : (∑ f : A, w (φ f)) ≤ ∑ p, w p := by
    calc
      _ = ∑ p ∈ univ.image φ, w p := (sum_image (fun a _ b _ h => hinj h)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ =>
        mul_nonneg (runWeight_nonneg p.1.val) (runWeight_nonneg p.2.val))
  have heq : (∑ f : A, w (φ f)) = ∑ f : A, rootedPatternWeight k f.val := by
    apply sum_congr rfl
    intro f _
    exact hweight f
  rw [heq] at hsum
  have htarget : (∑ p, w p) = transferMass exp31Matrix5710 k * transferMass exp31Matrix5710 (n-k) := by
    simp only [w,Fintype.sum_prod_type,← mul_sum,← sum_mul,valid_run_mass]
  rw [htarget] at hsum
  exact hsum

end Se20Part
