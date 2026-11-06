import Se20Part.CertificateEntries

noncomputable section
open scoped BigOperators
namespace Se20Part
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packState (l s : ℕ) : Fin 42 :=
  ⟨((l-1)*7 + if s = 99 then 6 else s-1) % 42, Nat.mod_lt _ (by decide)⟩

def transferStep (src : Fin 42) (d : Fin 6) (dst : Fin 42) : Prop :=
  let l := transferL src
  let s := transferS src
  let l₁ := min (l+1) 6
  let s₁ := min s (7-l) - 1
  l ≤ 5 ∧
    if d.val = 0 then 1 ≤ s₁ ∧ dst = packState l₁ s₁
    else 5 ≤ l₁+d.val ∧ (d.val ≤ s₁ ∨ 1 ≤ s₁) ∧
      dst = packState (min l₁ d.val) (if d.val ≤ s₁ then 99 else s₁)

instance (src : Fin 42) (d : Fin 6) (dst : Fin 42) : Decidable (transferStep src d dst) :=
  inferInstanceAs (Decidable (_ ∧ _))

def transferLetterWeight (d : Fin 6) : ℚ :=
  if d.val = 0 then 3 else 6*3^d.val*t5710

theorem transferStep_entries : ∀ dst src : Fin 42,
    (∑ d : Fin 6, if transferStep src d dst then transferLetterWeight d else 0) =
      certificateEntries dst src / 5710000 := by decide +kernel

theorem transferStep_matrix (dst src : Fin 42) :
    (∑ d : Fin 6, if transferStep src d dst then transferLetterWeight d else 0) =
      exp31Matrix5710 dst src := by
  rw [certificateEntries_correct]
  exact transferStep_entries dst src

theorem packState_values {l s : ℕ} (hl : 1 ≤ l ∧ l ≤ 6)
    (hs : (1 ≤ s ∧ s ≤ 6) ∨ s = 99) :
    transferL (packState l s) = l ∧ transferS (packState l s) = s := by
  unfold transferL transferS packState
  dsimp
  rcases hs with hs | rfl
  · have hne : s ≠ 99 := by omega
    simp only [hne,ite_false]
    have hmod : ((l-1)*7+(s-1)) % 42 = (l-1)*7+(s-1) := Nat.mod_eq_of_lt (by omega)
    simp only [hmod]
    have hdiv : ((l-1)*7+(s-1))/7+1 = l := by omega
    have hrem : ((l-1)*7+(s-1))%7 = s-1 := by omega
    simp only [hrem,if_pos (by omega : s-1 < 6)]
    exact ⟨hdiv,by omega⟩
  · norm_num only [ite_true]
    have hmod : ((l-1)*7+6) % 42 = (l-1)*7+6 := Nat.mod_eq_of_lt (by omega)
    simp only [hmod]
    have hdiv : ((l-1)*7+6)/7+1 = l := by omega
    have hrem : ((l-1)*7+6)%7 = 6 := by omega
    simp [hdiv,hrem]

theorem transferState_values (q : Fin 42) :
    (1 ≤ transferL q ∧ transferL q ≤ 6) ∧
    ((1 ≤ transferS q ∧ transferS q ≤ 6) ∨ transferS q = 99) := by
  unfold transferL transferS
  have := q.isLt
  split_ifs <;> omega

/-- The two automaton summaries needed for an arbitrary valid full pattern:
the closest placement to the left and a future witness for the pending budget. -/
structure PrefixSummary (f : ℕ → ℕ) (n j : ℕ) (q : Fin 42) : Prop where
  lower : ∀ i ≤ j, 0 < f i → transferL q ≤ f i + (j-i)
  attained : transferL q = 6 ∨ ∃ i ≤ j, 0 < f i ∧ transferL q = f i + (j-i)
  pending : transferS q = 99 ∨
    ∃ k, j < k ∧ k ≤ n ∧ 0 < f k ∧ f k + (k-j) ≤ transferS q

structure ValidDepthPattern (f : ℕ → ℕ) (n : ℕ) : Prop where
  first : 0 < f 0
  bounded : ∀ i ≤ n, f i ≤ 5
  spacing : ∀ i j, i < j → j ≤ n → 0 < f i → 0 < f j →
    5 ≤ f i + f j + (j-i)
  spans : ∀ j < n, ∃ i k, i ≤ j ∧ j < k ∧ k ≤ n ∧
    0 < f i ∧ 0 < f k ∧ f i + f k + (k-i) ≤ 7

theorem prefix_start {f : ℕ → ℕ} {n : ℕ} (hf : ValidDepthPattern f n) :
    PrefixSummary f n 0 (packState (f 0) 99) := by
  have hvals := packState_values ⟨hf.first,by have := hf.bounded 0 (by omega); omega⟩ (Or.inr rfl)
  refine ⟨?_,Or.inr ⟨0,le_rfl,hf.first,?_⟩,Or.inl hvals.2⟩
  · intro i hi _
    have : i = 0 := by omega
    simp [this,hvals.1]
  · simpa using hvals.1

theorem prefix_advance {f : ℕ → ℕ} {n j : ℕ} (hf : ValidDepthPattern f n)
    (hj : j < n) {q : Fin 42} (hq : PrefixSummary f n j q) :
    ∃ q', transferStep q ⟨f (j+1),by have := hf.bounded (j+1) (by omega); omega⟩ q' ∧
      PrefixSummary f n (j+1) q' := by
  have qval := transferState_values q
  obtain ⟨i,k,hij,hjk,hkn,hfi,hfk,hspan⟩ := hf.spans j hj
  have hlower := hq.lower i hij hfi
  have hl5 : transferL q ≤ 5 := by omega
  let l := transferL q + 1
  let s := min (transferS q) (7-transferL q) - 1
  have hl : 2 ≤ l ∧ l ≤ 6 := by dsimp [l]; omega
  have hfuture : ∃ k, j < k ∧ k ≤ n ∧ 0 < f k ∧ f k + (k-(j+1)) ≤ s := by
    by_cases hsmall : transferS q ≤ 7-transferL q
    · have hn99 : transferS q ≠ 99 := by omega
      obtain ⟨k,hk,hkn,hfk,hbudget⟩ := hq.pending.resolve_left hn99
      refine ⟨k,hk,hkn,hfk,?_⟩
      dsimp [s]
      omega
    · refine ⟨k,hjk,hkn,hfk,?_⟩
      dsimp [s]
      omega
  have hs : 1 ≤ s ∧ s ≤ 5 := by
    obtain ⟨k,hk,hkn,hfk,hbudget⟩ := hfuture
    dsimp [s] at *
    omega
  have hlat : ∃ i ≤ j, 0 < f i ∧ l = f i + (j+1-i) := by
    obtain ⟨i,hi,hfi,heq⟩ := hq.attained.resolve_left (by omega)
    exact ⟨i,hi,hfi,by dsimp [l]; omega⟩
  have hllow : ∀ i ≤ j, 0 < f i → l ≤ f i + (j+1-i) := by
    intro i hi hfi
    have := hq.lower i hi hfi
    dsimp [l]; omega
  have hlmin : min (transferL q+1) 6 = l := min_eq_left (by omega)
  by_cases hd : f (j+1) = 0
  · let q' := packState l s
    have hv := packState_values ⟨by omega,hl.2⟩ (Or.inl ⟨hs.1,by omega⟩)
    refine ⟨q',?_,?_,?_,?_⟩
    · simp only [transferStep,hd,hlmin,ite_true]
      exact ⟨hl5,hs.1,rfl⟩
    · intro a ha hfa
      have haj : a ≤ j := by
        by_cases hae : a = j+1
        · rw [hae,hd] at hfa; omega
        · omega
      rw [show transferL q' = l from hv.1]
      exact hllow a haj hfa
    · right
      obtain ⟨a,ha,hfa,heq⟩ := hlat
      exact ⟨a,by omega,hfa,hv.1.trans heq⟩
    · right
      obtain ⟨a,ha,han,hfa,hbudget⟩ := hfuture
      refine ⟨a,?_,han,hfa,?_⟩
      · have hane : a ≠ j+1 := by intro heq; rw [heq,hd] at hfa; omega
        omega
      · rw [show transferS q' = s from hv.2]
        exact hbudget
  · have hdpos : 0 < f (j+1) := by omega
    have hd5 := hf.bounded (j+1) (by omega)
    have hspace : 5 ≤ l + f (j+1) := by
      obtain ⟨a,ha,hfa,heq⟩ := hlat
      have hsp := hf.spacing a (j+1) (by omega) (by omega) hfa hdpos
      omega
    let s' := if f (j+1) ≤ s then 99 else s
    let q' := packState (min l (f (j+1))) s'
    have hls : 1 ≤ min l (f (j+1)) ∧ min l (f (j+1)) ≤ 6 := by omega
    have hss : (1 ≤ s' ∧ s' ≤ 6) ∨ s' = 99 := by
      dsimp [s']; split_ifs <;> omega
    have hv := packState_values hls hss
    refine ⟨q',?_,?_,?_,?_⟩
    · simp only [transferStep,hd,hlmin,ite_false]
      exact ⟨hl5,hspace,Or.inr hs.1,rfl⟩
    · intro a ha hfa
      rw [show transferL q' = min l (f (j+1)) from hv.1]
      by_cases hae : a = j+1
      · subst a; omega
      · have := hllow a (by omega) hfa
        omega
    · right
      by_cases hdl : f (j+1) ≤ l
      · refine ⟨j+1,le_rfl,hdpos,?_⟩
        rw [show transferL q' = min l (f (j+1)) from hv.1]
        omega
      · obtain ⟨a,ha,hfa,heq⟩ := hlat
        refine ⟨a,by omega,hfa,?_⟩
        rw [show transferL q' = min l (f (j+1)) from hv.1]
        omega
    · by_cases hds : f (j+1) ≤ s
      · left
        exact hv.2.trans (if_pos hds)
      · right
        obtain ⟨a,ha,han,hfa,hbudget⟩ := hfuture
        refine ⟨a,?_,han,hfa,?_⟩
        · have hane : a ≠ j+1 := by intro heq; rw [heq] at hbudget; omega
          omega
        · rw [show transferS q' = s' from hv.2]
          simpa only [s',if_neg hds] using hbudget

theorem ValidDepthPattern.exists_run {f : ℕ → ℕ} {n : ℕ} (hf : ValidDepthPattern f n) :
    ∃ q : ℕ → Fin 42, ∀ j (hj : j < n),
      transferStep (q j) ⟨f (j+1),by have := hf.bounded (j+1) (by omega); omega⟩ (q (j+1)) := by
  have hex (m : ℕ) (hm : m ≤ n) : ∃ q : ℕ → Fin 42,
      PrefixSummary f n m (q m) ∧ ∀ j (hj : j < m),
        transferStep (q j) ⟨f (j+1),by have := hf.bounded (j+1) (by omega); omega⟩ (q (j+1)) := by
    induction m with
    | zero => exact ⟨fun _ => packState (f 0) 99,prefix_start hf,by intro j hj; omega⟩
    | succ m ih =>
      obtain ⟨q,hq,hsteps⟩ := ih (by omega)
      obtain ⟨q',hstep,hnext⟩ := prefix_advance hf (by omega : m < n) hq
      let Q := Function.update q (m+1) q'
      have hQ (j : ℕ) (hj : j ≤ m) : Q j = q j := by simp [Q,Function.update_of_ne (by omega : j ≠ m+1)]
      have hQlast : Q (m+1) = q' := by simp [Q]
      refine ⟨Q,by simpa only [hQlast] using hnext,?_⟩
      intro j hj
      by_cases he : j = m
      · subst j; simpa only [hQ m le_rfl,hQlast] using hstep
      · rw [hQ j (by omega),hQ (j+1) (by omega)]
        exact hsteps j (by omega)
  obtain ⟨q,_,hq⟩ := hex n le_rfl
  exact ⟨q,hq⟩

theorem ValidDepthPattern.last {f : ℕ → ℕ} {n : ℕ} (hf : ValidDepthPattern f n) (hn : 0 < n) :
    0 < f n := by
  obtain ⟨i,k,hi,hk,hkn,hfi,hfk,hspan⟩ := hf.spans (n-1) (by omega)
  have hke : k = n := by omega
  simpa only [hke] using hfk

theorem ValidDepthPattern.reverse {f : ℕ → ℕ} {n : ℕ} (hf : ValidDepthPattern f n) (hn : 0 < n) :
    ValidDepthPattern (fun j => f (n-j)) n := by
  refine ⟨by simpa using hf.last hn,?_,?_,?_⟩
  · intro i hi; exact hf.bounded _ (by omega)
  · intro i j hij hj hfi hfj
    have h := hf.spacing (n-j) (n-i) (by omega) (by omega) hfj hfi
    omega
  · intro j hj
    obtain ⟨a,b,ha,hb,hbn,hfa,hfb,hspan⟩ := hf.spans (n-j-1) (by omega)
    refine ⟨n-b,n-a,by omega,by omega,by omega,?_,?_,?_⟩
    · simpa only [Nat.sub_sub_self hbn] using hfb
    · have han : a ≤ n := by omega
      simpa only [Nat.sub_sub_self han] using hfa
    · have han : a ≤ n := by omega
      rw [Nat.sub_sub_self hbn,Nat.sub_sub_self han]
      omega

end Se20Part
