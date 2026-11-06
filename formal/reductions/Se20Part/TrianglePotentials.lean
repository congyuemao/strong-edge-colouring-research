import Se20Part.CompactTriangles
import Se20Part.PathEndpointDegree

noncomputable section
open scoped Classical
namespace Se20Part.Partition
variable {W C : Type*} [Fintype W] [Fintype C] (H : SimpleGraph W)

/-- Two-vertex monochromatic components of a specified geometric type.
The closure condition is essential: monochromatic edges alone do not count K₂ components. -/
def typedPairs (R : Finset W → Prop) (π : W → C) : Finset (Finset W) :=
  Finset.univ.filter (fun S => S.card = 2 ∧ R S ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b ∧ π a = π b) ∧
    ∀ a ∈ S, ∀ b, H.Adj a b → π a = π b → b ∈ S)

theorem mem_typedPairs (R : Finset W → Prop) (π : W → C) (S : Finset W) :
    S ∈ typedPairs H R π ↔ S.card = 2 ∧ R S ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b ∧ π a = π b) ∧
      ∀ a ∈ S, ∀ b, H.Adj a b → π a = π b → b ∈ S := by
  simp only [typedPairs, Finset.mem_filter, Finset.mem_univ, true_and]

def MinimumFour (R S : Finset W → Prop) (π : W → C) : Prop :=
  MinimumThree H R π ∧ ∀ σ : W → C, MinimumThree H R σ →
    (typedTriangles H S π).card ≤ (typedTriangles H S σ).card

/-- The last coordinate is maximized, representing the minus sign in
`(Φ₁, Φ₂, compact triangles, diffuse triangles, − linked K₂ components)`. -/
def MinimumFive (R S L : Finset W → Prop) (π : W → C) : Prop :=
  MinimumFour H R S π ∧ ∀ σ : W → C, MinimumFour H R S σ →
    (typedPairs H L σ).card ≤ (typedPairs H L π).card

theorem exists_minimumFive [Nonempty C] (R S L : Finset W → Prop) :
    ∃ π : W → C, MinimumFive H R S L π := by
  obtain ⟨π,hπ⟩ := exists_minimumThree H R (C := C)
  let A : Finset (W → C) := Finset.univ.filter (MinimumThree H R)
  obtain ⟨σ,hσ,hmin⟩ := A.exists_min_image (fun q => (typedTriangles H S q).card)
    ⟨π,by simp [A,hπ]⟩
  have hs : MinimumFour H R S σ :=
    ⟨(Finset.mem_filter.mp hσ).2,fun τ hτ => hmin τ (by simp [A,hτ])⟩
  let B : Finset (W → C) := Finset.univ.filter (MinimumFour H R S)
  obtain ⟨τ,hτ,htmin⟩ := B.exists_max_image (fun q => (typedPairs H L q).card)
    ⟨σ,by simp [B,hs]⟩
  exact ⟨τ,(Finset.mem_filter.mp hτ).2,fun ρ hρ => htmin ρ (by simp [B,hρ])⟩

/-- Relative comparison against the original minimum. No minimality of an
intermediate partition is required. -/
theorem minimumFive_relative {R S L : Finset W → Prop} {π σ : W → C}
    (hπ : MinimumFive H R S L π) (hσ : MinimumTwo H σ)
    (hR : (typedTriangles H R σ).card ≤ (typedTriangles H R π).card)
    (hS : (typedTriangles H S σ).card ≤ (typedTriangles H S π).card) :
    MinimumFour H R S σ ∧
    (typedPairs H L σ).card ≤ (typedPairs H L π).card := by
  have hs3 : MinimumThree H R σ :=
    ⟨hσ,fun τ hτ => hR.trans (hπ.1.1.2 τ hτ)⟩
  have hs4 : MinimumFour H R S σ :=
    ⟨hs3,fun τ hτ => hS.trans (hπ.1.2 τ hτ)⟩
  exact ⟨hs4,hπ.2 σ hs4⟩

theorem typed_triangle_neighbours {R : Finset W → Prop} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    {T : Finset W} (hT : T ∈ typedTriangles H R π) {x : W} (hx : x ∈ T) :
    T.erase x = Finset.univ.filter (fun y => H.Adj x y ∧ π y = π x) := by
  obtain ⟨ht,_,hcl⟩ := (mem_typedTriangles H R π T).mp hT
  have hsub : T.erase x ⊆ Finset.univ.filter (fun y => H.Adj x y ∧ π y = π x) := by
    intro y hy
    obtain ⟨hne,hy⟩ := Finset.mem_erase.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hcl x hx y hy hne.symm).1,
      (hcl x hx y hy hne.symm).2.symm⟩
  apply Finset.eq_of_subset_of_card_le hsub
  have hb := hΔ x
  rw [degreeIn_eq_card] at hb
  have he := Finset.card_erase_add_one hx
  omega

theorem typed_triangle_unique_at {R S : Finset W → Prop} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    {T U : Finset W} (hT : T ∈ typedTriangles H R π)
    (hU : U ∈ typedTriangles H S π) {x : W} (hx : x ∈ T) (hxu : x ∈ U) : T = U := by
  have he := (typed_triangle_neighbours H hΔ hT hx).trans
    (typed_triangle_neighbours H hΔ hU hxu).symm
  simpa only [Finset.insert_erase hx,Finset.insert_erase hxu] using
    congrArg (fun s : Finset W => insert x s) he

theorem typedTriangles_update_off (R : Finset W → Prop) (π : W → C) (x : W) (j : C)
    (T : Finset W) (hx : x ∉ T) :
    T ∈ typedTriangles H R π ↔ T ∈ typedTriangles H R (Function.update π x j) := by
  have he (a : W) (ha : a ∈ T) : Function.update π x j a = π a :=
    Function.update_of_ne (show a ≠ x from fun h => hx (h ▸ ha)) _ _
  simp only [mem_typedTriangles]
  constructor <;> rintro ⟨ht,hr,hcl⟩ <;> refine ⟨ht,hr,?_⟩
  · intro a ha b hb hab; rw [he a ha,he b hb]; exact hcl a ha b hb hab
  · intro a ha b hb hab; simpa only [he a ha,he b hb] using hcl a ha b hb hab

/-- Exact triangle-coordinate change when a flip creates a triangle.
Counts are of unordered vertex sets, each once. -/
theorem typedTriangles_flip_count {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    (x : W) (j : C)
    (hΔ' : ∀ v, degreeIn H (Function.update π x j) v ((Function.update π x j) v) ≤ 2)
    {T U : Finset W} (hT : T ∈ typedTriangles H (fun _ => True) π) (hx : x ∈ T)
    (hU : U ∈ typedTriangles H (fun _ => True) (Function.update π x j)) (hxu : x ∈ U)
    (R : Finset W → Prop) :
    (typedTriangles H R (Function.update π x j)).card + (if R T then 1 else 0) =
      (typedTriangles H R π).card + (if R U then 1 else 0) := by
  let A := (typedTriangles H R π).filter (fun Q => x ∉ Q)
  have hoff : (typedTriangles H R (Function.update π x j)).filter (fun Q => x ∉ Q) = A := by
    ext Q
    simp only [Finset.mem_filter, A]
    exact and_congr_left (fun h => (typedTriangles_update_off H R π x j Q h).symm)
  have count (ρ : W → C) (hb : ∀ v, degreeIn H ρ v (ρ v) ≤ 2)
      (Q : Finset W) (hq : Q ∈ typedTriangles H (fun _ => True) ρ) (hxq : x ∈ Q) :
      (typedTriangles H R ρ).card =
        ((typedTriangles H R ρ).filter (fun Z => x ∉ Z)).card + (if R Q then 1 else 0) := by
    have he : (typedTriangles H R ρ).filter (fun Z => x ∈ Z) = if R Q then {Q} else ∅ := by
      ext Z
      simp only [Finset.mem_filter]
      by_cases hr : R Q
      · simp only [if_pos hr, Finset.mem_singleton]
        constructor
        · rintro ⟨hz,hxz⟩; exact typed_triangle_unique_at H hb hz hq hxz hxq
        · intro heq
          subst Z
          exact ⟨(mem_typedTriangles H R ρ Q).mpr
            ⟨((mem_typedTriangles H _ ρ Q).mp hq).1,hr,
              ((mem_typedTriangles H _ ρ Q).mp hq).2.2⟩,hxq⟩
      · simp only [if_neg hr, Finset.notMem_empty, iff_false, not_and]
        intro hz hxz
        have hzq := typed_triangle_unique_at H hb hz hq hxz hxq
        exact hr (hzq ▸ ((mem_typedTriangles H R ρ Z).mp hz).2.1)
    have hc := Finset.card_filter_add_card_filter_not
      (s := typedTriangles H R ρ) (p := fun Z => x ∈ Z)
    rw [he] at hc
    split_ifs at hc ⊢ <;> simp_all <;> omega
  have h1 := count π hΔ T hT hx
  have h2 := count (Function.update π x j) hΔ' U hU hxu
  rw [hoff] at h2
  dsimp only [A] at h2
  omega

theorem typed_triangle_closed {R : Finset W → Prop} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    {T : Finset W} (hT : T ∈ typedTriangles H R π) {a : W} (ha : a ∈ T)
    {b : W} (hab : H.Adj a b) (hc : π a = π b) : b ∈ T := by
  have hb : b ∈ T.erase a := by
    rw [typed_triangle_neighbours H hΔ hT ha]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab,hc.symm⟩
  exact (Finset.mem_erase.mp hb).2

theorem pair_triangle_disjoint {R S : Finset W → Prop} {π : W → C}
    {T U : Finset W} (hT : T ∈ typedTriangles H R π) (hU : U ∈ typedPairs H S π) :
    Disjoint T U := by
  obtain ⟨ht,_,hcl⟩ := (mem_typedTriangles H R π T).mp hT
  obtain ⟨hu,_,_,hclosed⟩ := (mem_typedPairs H S π U).mp hU
  apply Finset.disjoint_left.mpr
  intro a ha hau
  have hsub : T ⊆ U := by
    intro b hb
    by_cases he : a = b
    · exact he ▸ hau
    · exact hclosed a hau b (hcl a ha b hb he).1 (hcl a ha b hb he).2
  have := Finset.card_le_card hsub
  omega

/-- Deleting a vertex of a monochromatic triangle leaves a whole K₂
component, even when the move creates a triangle of another type. -/
theorem triangle_erase_mem_pairs {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    (x : W) (j : C) (hj : j ≠ π x)
    {T : Finset W} (hT : T ∈ typedTriangles H (fun _ => True) π) (hx : x ∈ T)
    {R : Finset W → Prop} (hR : R (T.erase x)) :
    T.erase x ∈ typedPairs H R (Function.update π x j) := by
  obtain ⟨ht,_,hcl⟩ := (mem_typedTriangles H _ π T).mp hT
  apply (mem_typedPairs H R _ _).mpr
  refine ⟨by have := Finset.card_erase_add_one hx; omega,hR,?_,?_⟩
  · intro a ha b hb hab
    obtain ⟨hax,ha⟩ := Finset.mem_erase.mp ha
    obtain ⟨hbx,hb⟩ := Finset.mem_erase.mp hb
    simpa only [Function.update_of_ne hax,Function.update_of_ne hbx] using hcl a ha b hb hab
  · intro a ha b hab hc
    obtain ⟨hax,ha⟩ := Finset.mem_erase.mp ha
    have hbx : b ≠ x := by
      intro he
      subst b
      rw [Function.update_self,Function.update_of_ne hax] at hc
      exact hj (hc.symm.trans (hcl a ha x hx hax).2)
    rw [Function.update_of_ne hax,Function.update_of_ne hbx] at hc
    exact Finset.mem_erase.mpr ⟨hbx,typed_triangle_closed H hΔ
      ((mem_typedTriangles H (fun _ => True) π T).mpr ⟨ht,trivial,hcl⟩) ha hab hc⟩

/-- The only old two-vertex component a triangle-to-triangle flip can
consume is the target triangle with the moved vertex removed. -/
theorem typedPair_flip_survives {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    (x : W) (j : C)
    (hΔ' : ∀ v, degreeIn H (Function.update π x j) v ((Function.update π x j) v) ≤ 2)
    {T U : Finset W} (hT : T ∈ typedTriangles H (fun _ => True) π) (hx : x ∈ T)
    (hU : U ∈ typedTriangles H (fun _ => True) (Function.update π x j)) (hxu : x ∈ U)
    {R : Finset W → Prop} {S : Finset W} (hS : S ∈ typedPairs H R π)
    (hne : S ≠ U.erase x) : S ∈ typedPairs H R (Function.update π x j) := by
  have hav {a : W} (ha : a ∈ S) : a ≠ x := by
    intro he
    exact Finset.disjoint_left.mp (pair_triangle_disjoint H hT hS) hx (he ▸ ha)
  obtain ⟨hs,hr,hcl,hclosed⟩ := (mem_typedPairs H R π S).mp hS
  apply (mem_typedPairs H R _ S).mpr
  refine ⟨hs,hr,?_,?_⟩
  · intro a ha b hb hab
    simpa only [Function.update_of_ne (hav ha),Function.update_of_ne (hav hb)]
      using hcl a ha b hb hab
  · intro a ha b hab hc
    by_cases hbx : b = x
    · subst b
      have hau : a ∈ U := typed_triangle_closed H hΔ' hU hxu hab.symm hc.symm
      have hsub : S ⊆ U.erase x := by
        intro c hcs
        refine Finset.mem_erase.mpr ⟨hav hcs,?_⟩
        by_cases hca : a = c
        · exact hca ▸ hau
        · have hac := hcl a ha c hcs hca
          exact typed_triangle_closed H hΔ' hU hau hac.1 (by
            simpa only [Function.update_of_ne (hav ha),Function.update_of_ne (hav hcs)] using hac.2)
      apply False.elim
      apply hne
      apply Finset.eq_of_subset_of_card_le hsub
      have hu := ((mem_typedTriangles H _ _ U).mp hU).1
      have he := Finset.card_erase_add_one hxu
      omega
    · rw [Function.update_of_ne (hav ha),Function.update_of_ne hbx] at hc
      exact hclosed a ha b hab hc

/-- Exact linked-component accounting for a triangle-to-triangle flip. -/
theorem typedPairs_flip_count {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    (x : W) (j : C) (hj : j ≠ π x)
    (hΔ' : ∀ v, degreeIn H (Function.update π x j) v ((Function.update π x j) v) ≤ 2)
    {T U : Finset W} (hT : T ∈ typedTriangles H (fun _ => True) π) (hx : x ∈ T)
    (hU : U ∈ typedTriangles H (fun _ => True) (Function.update π x j)) (hxu : x ∈ U)
    (R : Finset W → Prop) :
    (typedPairs H R (Function.update π x j)).card + (if R (U.erase x) then 1 else 0) =
      (typedPairs H R π).card + (if R (T.erase x) then 1 else 0) := by
  let σ := Function.update π x j
  have hinv : Function.update σ x (π x) = π := by simp [σ]
  have hj' : π x ≠ σ x := by simpa [σ] using hj.symm
  have hΔ'' : ∀ v, degreeIn H (Function.update σ x (π x)) v
      ((Function.update σ x (π x)) v) ≤ 2 := by rw [hinv]; exact hΔ
  have hT' : T ∈ typedTriangles H (fun _ => True) (Function.update σ x (π x)) := by
    rw [hinv]; exact hT
  have hA : T.erase x ∉ typedPairs H R π := by
    intro h
    have hd := pair_triangle_disjoint H hT h
    have he := Finset.card_erase_add_one hx
    have ht := ((mem_typedTriangles H _ _ T).mp hT).1
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase x).card)
    exact Finset.disjoint_left.mp hd (Finset.mem_erase.mp ha).2 ha
  have hB : U.erase x ∉ typedPairs H R σ := by
    intro h
    have hd := pair_triangle_disjoint H hU h
    have he := Finset.card_erase_add_one hxu
    have ht := ((mem_typedTriangles H _ _ U).mp hU).1
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (U.erase x).card)
    exact Finset.disjoint_left.mp hd (Finset.mem_erase.mp ha).2 ha
  have hmemA : T.erase x ∈ typedPairs H R σ ↔ R (T.erase x) := by
    constructor
    · intro h; exact ((mem_typedPairs H R σ _).mp h).2.1
    · exact triangle_erase_mem_pairs H hΔ x j hj hT hx
  have hmemB : U.erase x ∈ typedPairs H R π ↔ R (U.erase x) := by
    constructor
    · intro h; exact ((mem_typedPairs H R π _).mp h).2.1
    · intro h
      have hh := triangle_erase_mem_pairs H hΔ' x (π x) hj' hU hxu h
      simpa only [Function.update_idem,Function.update_eq_self] using hh
  have heq : (typedPairs H R σ).erase (T.erase x) = (typedPairs H R π).erase (U.erase x) := by
    ext S
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hne,hS⟩
      have hold := typedPair_flip_survives H hΔ' x (π x) hΔ'' hU hxu hT' hx hS hne
      rw [hinv] at hold
      exact ⟨fun he => hB (he ▸ hS),hold⟩
    · rintro ⟨hne,hS⟩
      exact ⟨fun he => hA (he ▸ hS),typedPair_flip_survives H hΔ x j hΔ' hT hx hU hxu hS hne⟩
  have hc := congrArg Finset.card heq
  change (typedPairs H R σ).card + (if R (U.erase x) then 1 else 0) =
    (typedPairs H R π).card + (if R (T.erase x) then 1 else 0)
  by_cases ha : R (T.erase x) <;> by_cases hb : R (U.erase x)
  · have hca := Finset.card_erase_add_one (hmemA.mpr ha)
    have hcb := Finset.card_erase_add_one (hmemB.mpr hb)
    simp only [if_pos ha,if_pos hb]; omega
  · rw [Finset.erase_eq_of_notMem (mt hmemB.mp hb)] at hc
    have hca := Finset.card_erase_add_one (hmemA.mpr ha)
    simp only [if_pos ha,if_neg hb]; omega
  · rw [Finset.erase_eq_of_notMem (mt hmemA.mp ha)] at hc
    have hcb := Finset.card_erase_add_one (hmemB.mpr hb)
    simp only [if_neg ha,if_pos hb]; omega
  · rw [Finset.erase_eq_of_notMem (mt hmemA.mp ha),Finset.erase_eq_of_notMem (mt hmemB.mp hb)] at hc
    simp only [if_neg ha,if_neg hb]; exact hc

/-- A flip out of a diffuse triangle at a four-coordinate minimum cannot
replace it by a longer odd cycle. This uses the original minimum only. -/
theorem minimumFour_triangle_replacement {R S : Finset W → Prop} {π : W → C}
    (hπ : MinimumFour H R S π) (x : W) (j : C)
    (hmin : MinimumTwo H (Function.update π x j))
    {T : Finset W} (hT : T ∈ typedTriangles H S π) (hx : x ∈ T) :
    ∃ U ∈ typedTriangles H (fun _ => True) (Function.update π x j), x ∈ U := by
  by_contra! hn
  have avoid (P : Finset W → Prop) {U : Finset W}
      (hU : U ∈ typedTriangles H P (Function.update π x j)) : x ∉ U := by
    apply hn U
    obtain ⟨hu,_,hcl⟩ := (mem_typedTriangles H _ _ U).mp hU
    exact (mem_typedTriangles H _ _ U).mpr ⟨hu,trivial,hcl⟩
  have sub (P : Finset W → Prop) : typedTriangles H P (Function.update π x j) ⊆
      typedTriangles H P π := by
    intro U hU
    exact (typedTriangles_update_off H P π x j U (avoid P hU)).mpr hU
  have hs3 : MinimumThree H R (Function.update π x j) :=
    ⟨hmin, fun σ hσ => (Finset.card_le_card (sub R)).trans (hπ.1.2 σ hσ)⟩
  have hstrict : typedTriangles H S (Function.update π x j) ⊂ typedTriangles H S π :=
    Finset.ssubset_iff_subset_ne.mpr ⟨sub S,fun he => avoid S (he.symm ▸ hT) hx⟩
  have hlt := Finset.card_lt_card hstrict
  have hle := hπ.2 _ hs3
  omega

/-- If both triangle coordinates return to their old values, a flip from
a triangle leaving a linked pair must also consume a linked pair. -/
theorem minimumFive_pair_type {R S L : Finset W → Prop} {π : W → C}
    (hπ : MinimumFive H R S L π)
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    (x : W) (j : C) (hj : j ≠ π x)
    (hmin : MinimumTwo H (Function.update π x j))
    (hΔ' : ∀ v, degreeIn H (Function.update π x j) v ((Function.update π x j) v) ≤ 2)
    {T U : Finset W} (hT : T ∈ typedTriangles H (fun _ => True) π) (hx : x ∈ T)
    (hU : U ∈ typedTriangles H (fun _ => True) (Function.update π x j)) (hxu : x ∈ U)
    (hR : R T ↔ R U) (hS : S T ↔ S U) (hL : L (T.erase x)) : L (U.erase x) := by
  have hr := typedTriangles_flip_count H hΔ x j hΔ' hT hx hU hxu R
  have hs := typedTriangles_flip_count H hΔ x j hΔ' hT hx hU hxu S
  have hri : (if R T then 1 else 0 : ℕ) = (if R U then 1 else 0) := by simp only [hR]
  have hsi : (if S T then 1 else 0 : ℕ) = (if S U then 1 else 0) := by simp only [hS]
  have hcmp := (minimumFive_relative H hπ hmin (by omega) (by omega)).2
  have hp := typedPairs_flip_count H hΔ x j hj hΔ' hT hx hU hxu L
  by_contra hn
  simp only [if_pos hL,if_neg hn] at hp
  omega

/-- Exact triangle-coordinate change when the new odd component is longer
than a triangle. -/
theorem typedTriangles_flip_no_triangle_count {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    (x : W) (j : C)
    {T : Finset W} (hT : T ∈ typedTriangles H (fun _ => True) π) (hx : x ∈ T)
    (hn : ∀ U ∈ typedTriangles H (fun _ => True) (Function.update π x j), x ∉ U)
    (R : Finset W → Prop) :
    (typedTriangles H R (Function.update π x j)).card + (if R T then 1 else 0) =
      (typedTriangles H R π).card := by
  have avoid {U : Finset W} (hU : U ∈ typedTriangles H R (Function.update π x j)) : x ∉ U := by
    obtain ⟨hu,_,hcl⟩ := (mem_typedTriangles H R _ U).mp hU
    exact hn U ((mem_typedTriangles H _ _ U).mpr ⟨hu,trivial,hcl⟩)
  have heq : typedTriangles H R (Function.update π x j) = (typedTriangles H R π).erase T := by
    ext U
    simp only [Finset.mem_erase]
    constructor
    · intro hU
      exact ⟨fun he => avoid hU (he.symm ▸ hx),
        (typedTriangles_update_off H R π x j U (avoid hU)).mpr hU⟩
    · rintro ⟨hne,hU⟩
      have hav : x ∉ U := fun hxU => hne (typed_triangle_unique_at H hΔ hU hT hxU hx)
      exact (typedTriangles_update_off H R π x j U hav).mp hU
  rw [heq]
  by_cases hr : R T
  · have ht : T ∈ typedTriangles H R π := by
      obtain ⟨ht,_,hcl⟩ := (mem_typedTriangles H _ _ T).mp hT
      exact (mem_typedTriangles H R π T).mpr ⟨ht,hr,hcl⟩
    simpa only [if_pos hr] using Finset.card_erase_add_one ht
  · have ht : T ∉ typedTriangles H R π := fun h => hr ((mem_typedTriangles H R π T).mp h).2.1
    simp only [if_neg hr,Finset.erase_eq_of_notMem ht,Nat.add_zero]

theorem minimumFive_of_equal {R S L : Finset W → Prop} {π σ : W → C}
    (hπ : MinimumFive H R S L π) (hσ : MinimumTwo H σ)
    (hR : (typedTriangles H R σ).card = (typedTriangles H R π).card)
    (hS : (typedTriangles H S σ).card = (typedTriangles H S π).card)
    (hL : (typedPairs H L σ).card = (typedPairs H L π).card) :
    MinimumFive H R S L σ :=
  ⟨(minimumFive_relative H hπ hσ hR.le hS.le).1,
    fun τ hτ => (hπ.2 τ hτ).trans_eq hL.symm⟩

/-- Case B's two-move comparison. The middle state is only a minimum of
the first two coordinates. All comparisons of later coordinates are with π. -/
theorem two_flip_compact_replacement {R L : Finset W → Prop} {π : W → C}
    (hπ : MinimumFive H R (fun T => ¬ R T) L π)
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    (x : W) (j : C) (hj : j ≠ π x)
    (hΔ' : ∀ v, degreeIn H (Function.update π x j) v ((Function.update π x j) v) ≤ 2)
    {T U : Finset W} (hT : T ∈ typedTriangles H (fun _ => True) π) (hx : x ∈ T)
    (hU : U ∈ typedTriangles H (fun _ => True) (Function.update π x j)) (hxu : x ∈ U)
    (hRT : ¬ R T) (hRU : R U) (hLT : L (T.erase x)) (hLU : ¬ L (U.erase x))
    (y : W) (hy : y ∈ U) (hLy : L (U.erase y)) (k : C)
    (hk : k ≠ Function.update π x j y)
    (hmin : MinimumTwo H (Function.update (Function.update π x j) y k))
    (hΔ'' : ∀ v, degreeIn H (Function.update (Function.update π x j) y k) v
      ((Function.update (Function.update π x j) y k) v) ≤ 2) :
    ∃ Q ∈ typedTriangles H R (Function.update (Function.update π x j) y k), y ∈ Q := by
  have hr1 := typedTriangles_flip_count H hΔ x j hΔ' hT hx hU hxu R
  have hs1 := typedTriangles_flip_count H hΔ x j hΔ' hT hx hU hxu (fun T => ¬ R T)
  have hl1 := typedPairs_flip_count H hΔ x j hj hΔ' hT hx hU hxu L
  simp only [if_neg hRT,if_pos hRU,if_pos hRT,if_neg (not_not_intro hRU),
    if_pos hLT,if_neg hLU,Nat.add_zero] at hr1 hs1 hl1
  by_contra! hn
  by_cases hex : ∃ Q ∈ typedTriangles H (fun _ => True)
      (Function.update (Function.update π x j) y k), y ∈ Q
  · obtain ⟨Q,hQ,hyQ⟩ := hex
    have hRQ : ¬ R Q := by
      intro h
      have hh := (mem_typedTriangles H _ _ Q).mp hQ
      exact hn Q ((mem_typedTriangles H R _ Q).mpr ⟨hh.1,h,hh.2.2⟩) hyQ
    have hr2 := typedTriangles_flip_count H hΔ' y k hΔ'' hU hy hQ hyQ R
    have hs2 := typedTriangles_flip_count H hΔ' y k hΔ'' hU hy hQ hyQ (fun T => ¬ R T)
    have hl2 := typedPairs_flip_count H hΔ' y k hk hΔ'' hU hy hQ hyQ L
    simp only [if_pos hRU,if_neg hRQ,if_neg (not_not_intro hRU),if_pos hRQ,
      if_pos hLy,Nat.add_zero] at hr2 hs2 hl2
    have hc := (minimumFive_relative H hπ hmin (by omega) (by omega)).2
    split_ifs at hl2 <;> omega
  · have hn' : ∀ Q ∈ typedTriangles H (fun _ => True)
        (Function.update (Function.update π x j) y k), y ∉ Q := by simpa using hex
    have hr2 := typedTriangles_flip_no_triangle_count H hΔ' y k hU hy hn' R
    have hs2 := typedTriangles_flip_no_triangle_count H hΔ' y k hU hy hn' (fun T => ¬ R T)
    simp only [if_pos hRU,if_neg (not_not_intro hRU),Nat.add_zero] at hr2 hs2
    have hs3 : MinimumThree H R (Function.update (Function.update π x j) y k) :=
      ⟨hmin, fun τ hτ => (show (typedTriangles H R (Function.update (Function.update π x j) y k)).card ≤
        (typedTriangles H R π).card by omega).trans (hπ.1.1.2 τ hτ)⟩
    have hc := hπ.1.2 _ hs3
    omega

end Se20Part.Partition
