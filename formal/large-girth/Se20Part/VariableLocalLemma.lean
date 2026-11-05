import Se20Part.External
import Mathlib.Logic.Equiv.Prod

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part

def uniformWeight (Ω : Type) [Fintype Ω] (_ : Ω) : ℝ := (Fintype.card Ω : ℝ)⁻¹

theorem uniformWeight_nonneg (Ω : Type) [Fintype Ω] (ω : Ω) : 0 ≤ uniformWeight Ω ω := by
  unfold uniformWeight; positivity

theorem uniformWeight_sum (Ω : Type) [Fintype Ω] [Nonempty Ω] :
    ∑ ω, uniformWeight Ω ω = 1 := by
  simp [uniformWeight,Fintype.card_ne_zero]

theorem uniformProb_equiv {Ω Ω' : Type} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (S : Set Ω') :
    eventProb (uniformWeight Ω) (e ⁻¹' S) = eventProb (uniformWeight Ω') S := by
  unfold eventProb uniformWeight
  apply Fintype.sum_equiv e
  intro ω
  simp [Fintype.card_congr e]

theorem uniformProb_product {A B : Type} [Fintype A] [Fintype B]
    (S : Set A) (T : Set B) :
    eventProb (uniformWeight (A × B)) (S ×ˢ T) =
      eventProb (uniformWeight A) S * eventProb (uniformWeight B) T := by
  simp only [eventProb,uniformWeight,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,
    Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hs : a ∈ S <;> by_cases ht : b ∈ T <;> simp [hs,ht,mul_comm]

theorem uniformProb_univ (Ω : Type) [Fintype Ω] [Nonempty Ω] :
    eventProb (uniformWeight Ω) Set.univ = 1 := by
  simp [eventProb,uniformWeight_sum]

theorem uniformProb_singleton {Ω : Type} [Fintype Ω] (ω : Ω) :
    eventProb (uniformWeight Ω) {ω} = (Fintype.card Ω : ℝ)⁻¹ := by
  simp [eventProb,uniformWeight]

def Cylinder {I : Type} {A : I → Type} (S : Finset I) (a : ∀ i, A i) : Set (∀ i, A i) :=
  {ω | ∀ i ∈ S, ω i = a i}

/-- An arbitrary event determined by coordinates outside S is independent of
fixing the coordinates in S. This is joint independence, not merely pairwise. -/
theorem uniform_cylinder_independence {I : Type} [Fintype I] (A : I → Type)
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (S : Finset I) (a : ∀ i, A i)
    (T : Set (∀ i, A i))
    (hT : ∀ ω ω', (∀ i, i ∉ S → ω i = ω' i) → (ω ∈ T ↔ ω' ∈ T)) :
    eventProb (uniformWeight (∀ i, A i)) (Cylinder S a ∩ T) =
      eventProb (uniformWeight (∀ i, A i)) (Cylinder S a) *
        eventProb (uniformWeight (∀ i, A i)) T := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) A
  let b : ∀ i : {i // i ∈ S}, A i := fun i => a i
  let R : Set (∀ i : {i // i ∉ S}, A i) := {c | e.symm (b,c) ∈ T}
  have hc : Cylinder S a = e ⁻¹' ({b} ×ˢ Set.univ) := by
    ext ω
    simp only [Cylinder,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_prod,Set.mem_singleton_iff,
      Set.mem_univ,and_true]
    constructor
    · intro h; funext i; exact h i i.property
    · intro h i hi; exact congrFun h ⟨i,hi⟩
  have ht : T = e ⁻¹' (Set.univ ×ˢ R) := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and]
    apply hT
    intro i hi
    simp [e,Equiv.piEquivPiSubtypeProd,hi]
  have hi : Cylinder S a ∩ T = e ⁻¹' ({b} ×ˢ R) := by
    rw [hc,ht,← Set.preimage_inter]
    congr 1
    ext ω
    simp
  rw [hi,hc,ht,uniformProb_equiv,uniformProb_equiv,uniformProb_equiv,
    uniformProb_product,uniformProb_product,uniformProb_product,
    uniformProb_univ,uniformProb_univ,mul_one,one_mul]

theorem uniform_cylinder_probability {I : Type} [Fintype I] (A : I → Type)
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (S : Finset I) (a : ∀ i, A i) :
    eventProb (uniformWeight (∀ i, A i)) (Cylinder S a) =
      ∏ i ∈ S, (Fintype.card (A i) : ℝ)⁻¹ := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) A
  let b : ∀ i : {i // i ∈ S}, A i := fun i => a i
  have hc : Cylinder S a = e ⁻¹' ({b} ×ˢ Set.univ) := by
    ext ω
    simp only [Cylinder,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_prod,Set.mem_singleton_iff,
      Set.mem_univ,and_true]
    constructor
    · intro h; funext i; exact h i i.property
    · intro h i hi; exact congrFun h ⟨i,hi⟩
  rw [hc,uniformProb_equiv,uniformProb_product,uniformProb_singleton,uniformProb_univ,mul_one]
  simp only [Fintype.card_pi,Nat.cast_prod,Finset.prod_inv_distrib]
  exact congrArg Inv.inv (Finset.prod_coe_sort S (fun i => (Fintype.card (A i) : ℝ)))

def variableDependencyGraph {I B : Type} (vars : B → Finset I) : SimpleGraph B where
  Adj b c := b ≠ c ∧ ¬ Disjoint (vars b) (vars c)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,fun hdis => h.2 hdis.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem variable_cylinder_joint_independence {I B : Type} [Fintype I] [Fintype B]
    (A : I → Type) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (vars : B → Finset I) (choice : B → ∀ i, A i)
    (b : B) (S : Finset B) (hb : b ∉ S)
    (hdis : ∀ c ∈ S, ¬ (variableDependencyGraph vars).Adj b c) :
    eventProb (uniformWeight (∀ i, A i)) (Cylinder (vars b) (choice b) ∩
      Avoid (fun c => Cylinder (vars c) (choice c)) S) =
    eventProb (uniformWeight (∀ i, A i)) (Cylinder (vars b) (choice b)) *
      eventProb (uniformWeight (∀ i, A i)) (Avoid (fun c => Cylinder (vars c) (choice c)) S) := by
  apply uniform_cylinder_independence
  intro ω ω' heq
  have hfix (c : B) (hc : c ∈ S) : Disjoint (vars b) (vars c) := by
    by_contra hn
    exact hdis c hc ⟨fun he => hb (he ▸ hc),hn⟩
  have hevent (c : B) (hc : c ∈ S) :
      ω ∈ Cylinder (vars c) (choice c) ↔ ω' ∈ Cylinder (vars c) (choice c) := by
    unfold Cylinder
    simp only [Set.mem_setOf_eq]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    rw [heq i (fun hib => Finset.disjoint_left.mp (hfix c hc) hib hi)]
  simp only [Avoid,Set.mem_setOf_eq]
  exact forall_congr' (fun c => forall_congr' (fun hc => not_congr (hevent c hc)))

theorem variable_product_condition {I B : Type} [Fintype I] [Fintype B]
    (vars : B → Finset I) (hne : ∀ b, (vars b).Nonempty) (x : B → ℝ)
    (hx : ∀ b, 0 ≤ x b ∧ x b < 1) {β : ℝ} (hβ : 0 ≤ β)
    (hbudget : ∀ i, 1 ≤ β * ∏ b ∈ Finset.univ.filter (fun b => i ∈ vars b), (1-x b))
    (b : B) : 1 ≤ β ^ (vars b).card *
      ∏ c ∈ (variableDependencyGraph vars).neighborFinset b, (1-x c) := by
  let N := (variableDependencyGraph vars).neighborFinset b
  have hshare (c : B) (hc : c ∈ N) : ∃ i, i ∈ vars b ∧ i ∈ vars c := by
    have hh : ¬ Disjoint (vars b) (vars c) := (show (variableDependencyGraph vars).Adj b c by simpa [N] using hc).2
    simpa only [Finset.disjoint_left,not_forall,not_not,exists_prop] using hh
  obtain ⟨i₀,hi₀⟩ := hne b
  let owner : B → I := fun c => if hc : c ∈ N then (hshare c hc).choose else i₀
  have howner (c : B) (hc : c ∈ N) : owner c ∈ vars b ∧ owner c ∈ vars c := by
    simpa [owner,hc] using (hshare c hc).choose_spec
  have hlocal (i : I) : 1 ≤ β * ∏ c ∈ N.filter (fun c => owner c = i), (1-x c) := by
    apply (hbudget i).trans
    apply mul_le_mul_of_nonneg_left _ hβ
    apply Finset.prod_le_prod_of_subset_of_le_one₀
    · intro c hc
      obtain ⟨hc,he⟩ := Finset.mem_filter.mp hc
      simp [← he,(howner c hc).2]
    · intro c hc; linarith [(hx c).2]
    · intro c hc hcn; linarith [(hx c).1]
  have hh : (∏ i ∈ vars b, (1 : ℝ)) ≤ ∏ i ∈ vars b,
      β * ∏ c ∈ N.filter (fun c => owner c = i), (1-x c) :=
    Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => hlocal i)
  rw [Finset.prod_const_one,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.prod_fiberwise_of_maps_to (fun c hc => (howner c hc).1)] at hh
  exact hh

theorem variable_local_lemma {I B : Type} [Fintype I] [Fintype B]
    (lll : LovaszLocalLemma) (A : I → Type) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (vars : B → Finset I) (hne : ∀ b, (vars b).Nonempty) (choice : B → ∀ i, A i)
    {β : ℝ} (hβ : 0 ≤ β)
    (hx : ∀ b, 0 ≤ (∏ i ∈ vars b, β / Fintype.card (A i)) ∧
      (∏ i ∈ vars b, β / Fintype.card (A i)) < 1)
    (hbudget : ∀ i, 1 ≤ β * ∏ b ∈ Finset.univ.filter (fun b => i ∈ vars b),
      (1 - ∏ j ∈ vars b, β / Fintype.card (A j))) :
    ∃ ω : ∀ i, A i, ∀ b, ω ∉ Cylinder (vars b) (choice b) := by
  let x : B → ℝ := fun b => ∏ i ∈ vars b, β / Fintype.card (A i)
  have hlll := lll (∀ i, A i) B (uniformWeight _) (fun b => Cylinder (vars b) (choice b))
    (variableDependencyGraph vars) x (uniformWeight_nonneg _) (uniformWeight_sum _)
    (variable_cylinder_joint_independence A vars choice) hx
  have hcond (b : B) : eventProb (uniformWeight (∀ i, A i)) (Cylinder (vars b) (choice b)) ≤
      x b * ∏ c ∈ (variableDependencyGraph vars).neighborFinset b, (1-x c) := by
    rw [uniform_cylinder_probability]
    have hprod := variable_product_condition vars hne x hx hβ hbudget b
    have hnonneg : 0 ≤ ∏ i ∈ vars b, (Fintype.card (A i) : ℝ)⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_left hprod hnonneg
    simpa [x,div_eq_mul_inv,Finset.prod_mul_distrib,mul_assoc,mul_comm,mul_left_comm] using hh
  have hpos := hlll hcond
  by_contra! hn
  have hempty : Avoid (fun b => Cylinder (vars b) (choice b)) Finset.univ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    obtain ⟨b,hb⟩ := hn ω
    exact hω b (Finset.mem_univ b) hb
  simp [hempty,eventProb] at hpos

theorem log_budget_product {B : Type} [Fintype B] (S : Finset B) (x : B → ℝ)
    {β t C : ℝ} (hβ : 0 < β) (ht : t < 1)
    (hx : ∀ b ∈ S, 0 ≤ x b ∧ x b ≤ t)
    (hsum : ∑ b ∈ S, x b ≤ C) (hlog : C / (1-t) ≤ Real.log β) :
    1 ≤ β * ∏ b ∈ S, (1-x b) := by
  have hpos (b : B) (hb : b ∈ S) : 0 < 1-x b := by linarith [(hx b hb).2]
  have hb (b : B) (hb : b ∈ S) : -x b / (1-t) ≤ Real.log (1-x b) := by
    have h := Real.one_sub_inv_le_log_of_pos (hpos b hb)
    have hd : x b / (1-x b) ≤ x b / (1-t) :=
      div_le_div_of_nonneg_left (hx b hb).1 (by linarith) (by linarith [(hx b hb).2])
    have he : 1-(1-x b)⁻¹ = -x b/(1-x b) := by
      field_simp [ne_of_gt (hpos b hb)]
      ring
    rw [he] at h
    simp only [neg_div] at h ⊢
    linarith
  have hlogs : -(∑ b ∈ S, x b) / (1-t) ≤ Real.log (∏ b ∈ S, (1-x b)) := by
    rw [Real.log_prod (fun b hb => ne_of_gt (hpos b hb))]
    simpa only [div_eq_mul_inv,← Finset.sum_mul,Finset.sum_neg_distrib] using Finset.sum_le_sum hb
  have hc : (∑ b ∈ S, x b) / (1-t) ≤ Real.log β :=
    (div_le_div_of_nonneg_right hsum (by linarith)).trans hlog
  have hp : 0 < ∏ b ∈ S, (1-x b) := Finset.prod_pos hpos
  have hh : 0 ≤ Real.log (β * ∏ b ∈ S, (1-x b)) := by
    rw [Real.log_mul (ne_of_gt hβ) (ne_of_gt hp)]
    simp only [neg_div] at hlogs
    linarith
  exact (Real.log_nonneg_iff (mul_pos hβ hp)).mp hh

end Se20Part
