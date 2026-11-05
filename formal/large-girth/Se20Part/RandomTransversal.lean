import Se20Part.VariableLocalLemma
import Se20Part.TransferMatrix

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part

def partSize {X I : Type} [Fintype X] (part : X → I) (i : I) : ℕ :=
  Fintype.card {e // part e = i}

def familyWeight {X I : Type} [Fintype X] (part : X → I) (β : ℝ) (S : Finset X) : ℝ :=
  ∏ i ∈ S.image part, β / partSize part i

theorem family_choice {X I : Type} [Fintype X] (part : X → I)
    (hsurj : Function.Surjective part) (S : Finset X) (hinj : Set.InjOn part (S : Set X)) :
    ∃ a : ∀ i, {e // part e = i}, ∀ e ∈ S, (a (part e)).val = e := by
  have hex (i : I) : ∃ a : {e // part e = i}, ∀ e ∈ S, part e = i → a.val = e := by
    by_cases hh : ∃ e ∈ S, part e = i
    · obtain ⟨e,he,hei⟩ := hh
      exact ⟨⟨e,hei⟩,fun e' he' he'i => hinj he he' (hei.trans he'i.symm)⟩
    · obtain ⟨e,he⟩ := hsurj i
      exact ⟨⟨e,he⟩,fun e' he' he'i => (hh ⟨e',he',he'i⟩).elim⟩
  choose a ha using hex
  exact ⟨a,fun e he => ha (part e) e he rfl⟩

theorem family_cylinder_iff {X I : Type} (part : X → I) (S : Finset X)
    (a ω : ∀ i, {e // part e = i}) (ha : ∀ e ∈ S, (a (part e)).val = e) :
    ω ∈ Cylinder (S.image part) a ↔ ∀ e ∈ S, e ∈ Set.range (fun i => (ω i).val) := by
  constructor
  · intro hh e he
    exact ⟨part e,(congrArg Subtype.val (hh _ (Finset.mem_image_of_mem part he))).trans (ha e he)⟩
  · intro hh i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j,hj⟩ := hh e he
    have hj' : j = part e := (ω j).property.symm.trans (congrArg part hj)
    apply Subtype.ext
    rw [ha e he,← hj']
    exact hj

theorem familyWeight_bounds {X I : Type} [Fintype X] (part : X → I)
    (hsize : ∀ i, 5710 ≤ partSize part i) (S : Finset X) (hne : S.Nonempty) :
    0 ≤ familyWeight part (1203/1000) S ∧ familyWeight part (1203/1000) S ≤ (t5710 : ℝ) := by
  have hfactor (i : I) : 0 ≤ (1203/1000 : ℝ) / partSize part i ∧
      (1203/1000 : ℝ) / partSize part i ≤ (t5710 : ℝ) := by
    constructor
    · positivity
    · have hi : (5710 : ℝ) ≤ partSize part i := by exact_mod_cast hsize i
      have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1203/1000)
        (by norm_num : (0 : ℝ) < 5710) hi
      convert hh using 1 <;> norm_num [t5710,beta5710]
  constructor
  · exact Finset.prod_nonneg (fun i _ => (hfactor i).1)
  · obtain ⟨e,he⟩ := hne
    have hle := Finset.prod_le_prod_of_subset_of_le_one₀
      (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem part he))
      (fun i _ => (hfactor i).1) (fun i _ _ => (hfactor i).2.trans (by norm_num [t5710,beta5710]))
    have hh : familyWeight part (1203/1000) S ≤ (1203/1000 : ℝ) / partSize part (part e) := by
      simpa [familyWeight] using hle
    exact hh.trans (hfactor (part e)).2

/-- Finite random-transversal selection with all probability and dependency
bookkeeping proved. Only an explicit per-part weighted count remains as input. -/
theorem random_transversal_of_weight_bound {X I B : Type} [Fintype X] [Fintype I] [Fintype B]
    (lll : LovaszLocalLemma) (part : X → I) (hsurj : Function.Surjective part)
    (hsize : ∀ i, 5710 ≤ partSize part i) (family : B → Finset X)
    (hne : ∀ b, (family b).Nonempty) (hinj : ∀ b, Set.InjOn part (family b : Set X))
    (C : ℝ)
    (hcount : ∀ i, ∑ b ∈ Finset.univ.filter (fun b => i ∈ (family b).image part),
      familyWeight part (1203/1000) (family b) ≤ C)
    (hlog : C / (1-(t5710 : ℝ)) ≤ Real.log (1203/1000)) :
    ∃ f : I → X, (∀ i, part (f i) = i) ∧
      ∀ b, ¬ ∀ e ∈ family b, e ∈ Set.range f := by
  let A : I → Type := fun i => {e // part e = i}
  letI (i : I) : Nonempty (A i) := by obtain ⟨e,he⟩ := hsurj i; exact ⟨⟨e,he⟩⟩
  choose choice hchoice using fun b => family_choice part hsurj (family b) (hinj b)
  let vars : B → Finset I := fun b => (family b).image part
  have hx (b : B) : 0 ≤ (∏ i ∈ vars b, (1203/1000 : ℝ) / Fintype.card (A i)) ∧
      (∏ i ∈ vars b, (1203/1000 : ℝ) / Fintype.card (A i)) < 1 := by
    have hh := familyWeight_bounds part hsize (family b) (hne b)
    exact ⟨hh.1,hh.2.trans_lt (by norm_num [t5710,beta5710])⟩
  have hbudget (i : I) : 1 ≤ (1203/1000 : ℝ) * ∏ b ∈ Finset.univ.filter (fun b => i ∈ vars b),
      (1 - ∏ j ∈ vars b, (1203/1000 : ℝ) / Fintype.card (A j)) := by
    apply log_budget_product _ _ (t := (t5710 : ℝ)) (C := C) (by norm_num)
      (by norm_num [t5710,beta5710])
    · intro b hb; exact familyWeight_bounds part hsize (family b) (hne b)
    · exact hcount i
    · exact hlog
  obtain ⟨ω,hω⟩ := variable_local_lemma lll A vars
    (fun b => (hne b).image part) choice (by norm_num : (0 : ℝ) ≤ 1203/1000) hx hbudget
  exact ⟨fun i => (ω i).val,fun i => (ω i).property,fun b hh =>
    hω b ((family_cylinder_iff part (family b) (choice b) ω (hchoice b)).mpr hh)⟩

end Se20Part
