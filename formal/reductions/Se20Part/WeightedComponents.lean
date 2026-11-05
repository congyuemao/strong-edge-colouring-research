import Se20Part.WeightedExchange

noncomputable section
open scoped Classical
namespace Se20Part.Partition
variable {W C : Type*} [Fintype W] [Fintype C] (H : SimpleGraph W)
set_option maxHeartbeats 2000000

/-- The actual bad-component potential, including odd cycles in capacity-two
classes. Capacities are read at any vertex of a monochromatic component. -/
abbrev WeightedBadComponent (d : C → ℕ) (π : W → C) :=
  {K : (monochrome H π).ConnectedComponent // ¬ K.toSimpleGraph.Colorable (d (π K.out))}

def weightedPhi2 (d : C → ℕ) (π : W → C) : ℕ := Fintype.card (WeightedBadComponent H d π)

def WeightedComponentMinimumTwo (d : C → ℕ) (π : W → C) : Prop :=
  WeightedMinimum H d π ∧ ∀ σ, WeightedMinimum H d σ → weightedPhi2 H d π ≤ weightedPhi2 H d σ

def WeightedComponentMinimumThree (R : SimpleGraph W) (d : C → ℕ) (π : W → C) : Prop :=
  WeightedComponentMinimumTwo H d π ∧ ∀ σ, WeightedComponentMinimumTwo H d σ → energy R π ≤ energy R σ

theorem exists_weightedComponentMinimumThree [Nonempty C] (R : SimpleGraph W) (d : C → ℕ) :
    ∃ π : W → C, WeightedComponentMinimumThree H R d π := by
  obtain ⟨π,hπ⟩ := exists_weighted_minimum H d
  let A : Finset (W → C) := Finset.univ.filter (WeightedMinimum H d)
  obtain ⟨σ,hσ,hmin⟩ := A.exists_min_image (weightedPhi2 H d) ⟨π,by simp [A,hπ]⟩
  have hs : WeightedComponentMinimumTwo H d σ :=
    ⟨(Finset.mem_filter.mp hσ).2,fun τ hτ => hmin τ (by simp [A,hτ])⟩
  let B : Finset (W → C) := Finset.univ.filter (WeightedComponentMinimumTwo H d)
  obtain ⟨τ,hτ,htmin⟩ := B.exists_min_image (energy R) ⟨σ,by simp [B,hs]⟩
  exact ⟨τ,(Finset.mem_filter.mp hτ).2,fun ρ hρ => htmin ρ (by simp [B,hρ])⟩

theorem badClique_component_support {d : C → ℕ} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ d (π v))
    {T : Finset W} (hT : T ∈ badCliques H d π) {x : W} (hx : x ∈ T) :
    ∀ y ∈ ((monochrome H π).connectedComponentMk x).supp, y ∈ T := by
  have hclosed {a b : W} (ha : a ∈ T) (hab : (monochrome H π).Adj a b) : b ∈ T := by
    have hh : b ∈ T.erase a := by
      rw [badClique_neighbours H hΔ hT ha]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab.1,hab.2.symm⟩
    exact (Finset.mem_erase.mp hh).2
  have walkClosed {a b : W} (p : (monochrome H π).Walk a b) : a ∈ T → b ∈ T := by
    induction p with
    | nil => exact id
    | cons hab p ih => exact fun ha => ih (hclosed ha hab)
  intro y hy
  have hr := ((monochrome H π).connectedComponentMk x).reachable_of_mem_supp
    (((monochrome H π).connectedComponentMk x).mem_supp_iff x |>.mpr rfl) hy
  exact walkClosed hr.some hx

theorem badClique_component_bad {d : C → ℕ} {π : W → C}
    {T : Finset W} (hT : T ∈ badCliques H d π) {x : W} (hx : x ∈ T) :
    ¬ ((monochrome H π).connectedComponentMk x).toSimpleGraph.Colorable
      (d (π ((monochrome H π).connectedComponentMk x).out)) := by
  let K := (monochrome H π).connectedComponentMk x
  obtain ⟨c,ht,hcol,hcl⟩ := (mem_badCliques H d π T).mp hT
  have hm (y : T) : y.val ∈ K.supp := by
    by_cases hy : y.val = x
    · exact hy ▸ (K.mem_supp_iff x |>.mpr rfl)
    · exact K.mem_supp_of_adj_mem_supp (K.mem_supp_iff x |>.mpr rfl)
        ⟨hcl hx y.prop (Ne.symm hy),(hcol x hx).trans (hcol y y.prop).symm⟩
  have hcolour : π K.out = c :=
    (monochrome_class_constant H π K K.out_eq (K.mem_supp_iff x |>.mpr rfl)).trans (hcol x hx)
  let f : T → K.supp := fun y => ⟨y,hm y⟩
  intro hc
  have hh := hc.card_le_of_pairwise_adj f (by
    intro a b hab
    exact ⟨hcl a.prop b.prop (fun h => hab (Subtype.ext h)),(hcol a a.prop).trans (hcol b b.prop).symm⟩)
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,hcolour] at hh
  omega

theorem weighted_bad_transfer {d : C → ℕ} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ d (π v))
    (x : W) (j : C) {T : Finset W} (hT : T ∈ badCliques H d π) (hxT : x ∈ T)
    (K : WeightedBadComponent H d (Function.update π x j)) (hx : x ∉ K.val.supp) :
    ¬ ((monochrome H π).connectedComponentMk K.val.out).toSimpleGraph.Colorable
      (d (π ((monochrome H π).connectedComponentMk K.val.out).out)) ∧
      x ∉ ((monochrome H π).connectedComponentMk K.val.out).supp := by
  let σ := Function.update π x j
  let A := (monochrome H π).connectedComponentMk K.val.out
  have hav {y : W} (hy : y ∈ K.val.supp) : y ≠ x := fun he => hx (he ▸ hy)
  have hmem {y : W} (hy : y ∈ K.val.supp) : y ∈ A.supp :=
    component_image_mem (monochrome H π) (monochrome H σ) K.val
      (fun a ha b hb h => (monochrome_update_off H π x j a b (hav ha) (hav hb)).mpr h) hy
  have hrep : K.val.out ∈ A.supp := A.mem_supp_iff _ |>.mpr rfl
  have hcolour : π A.out = σ K.val.out := by
    rw [show σ K.val.out = π K.val.out from Function.update_of_ne (hav K.val.out_eq) _ _]
    exact monochrome_class_constant H π A A.out_eq hrep
  let f : K.val.toSimpleGraph →g A.toSimpleGraph := {
    toFun y := ⟨y,hmem y.prop⟩
    map_rel' := fun {a b} h => (monochrome_update_off H π x j a b (hav a.prop) (hav b.prop)).mpr h }
  constructor
  · intro hc
    rw [hcolour] at hc
    exact K.prop ⟨hc.some.comap f⟩
  · intro hxA
    have hAx : A = (monochrome H π).connectedComponentMk x := (A.mem_supp_iff x).mp hxA |>.symm
    have hsub {y : W} (hy : y ∈ K.val.supp) : y ∈ T :=
      badClique_component_support H hΔ hT hxT y (hAx ▸ hmem hy)
    let f' : K.val.supp → T.erase x := fun y =>
      ⟨y,Finset.mem_erase.mpr ⟨hav y.prop,hsub y.prop⟩⟩
    have hf' : Function.Injective f' := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : T.erase x => z.val) hab)
    let col : K.val.toSimpleGraph.Coloring (T.erase x) :=
      SimpleGraph.Coloring.mk f' (fun {a b} hab he => hab.ne (hf' he))
    obtain ⟨c,ht,hcol,_⟩ := (mem_badCliques H d π T).mp hT
    have hcard : Fintype.card (T.erase x) = d c := by
      rw [Fintype.card_coe]
      have hh := Finset.card_erase_add_one hxT
      omega
    have hc := col.colorable
    rw [hcard] at hc
    have hkc : σ K.val.out = c := by
      rw [show σ K.val.out = π K.val.out from Function.update_of_ne (hav K.val.out_eq) _ _]
      exact hcol K.val.out (hsub K.val.out_eq)
    apply K.prop
    change K.val.toSimpleGraph.Colorable (d (σ K.val.out))
    rw [hkc]
    exact hc

theorem weighted_bad_count_update_le {d : C → ℕ} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ d (π v))
    (x : W) (j : C) {T : Finset W} (hT : T ∈ badCliques H d π) (hxT : x ∈ T) :
    weightedPhi2 H d (Function.update π x j) ≤ weightedPhi2 H d π := by
  let σ := Function.update π x j
  let f : WeightedBadComponent H d σ → WeightedBadComponent H d π := fun K =>
    if hx : x ∈ K.val.supp then
      ⟨(monochrome H π).connectedComponentMk x,badClique_component_bad H hT hxT⟩
    else ⟨(monochrome H π).connectedComponentMk K.val.out,
      (weighted_bad_transfer H hΔ x j hT hxT K hx).1⟩
  have fav (K : WeightedBadComponent H d σ) (hx : x ∉ K.val.supp) : x ∉ (f K).val.supp := by
    simpa only [f,dif_neg hx] using (weighted_bad_transfer H hΔ x j hT hxT K hx).2
  apply Fintype.card_le_of_injective f
  intro K L hKL
  have he : (f K).val = (f L).val := congrArg Subtype.val hKL
  by_cases hK : x ∈ K.val.supp <;> by_cases hL : x ∈ L.val.supp
  · exact Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex hK hL)
  · apply False.elim
    apply fav L hL
    rw [← he]
    simp only [f,dif_pos hK]
    exact ((monochrome H π).connectedComponentMk x).mem_supp_iff x |>.mpr rfl
  · apply False.elim
    apply fav K hK
    rw [he]
    simp only [f,dif_pos hL]
    exact ((monochrome H π).connectedComponentMk x).mem_supp_iff x |>.mpr rfl
  · let A := (f K).val
    have hmK : K.val.out ∈ A.supp := by
      simp only [A,f,dif_neg hK]
      exact ((monochrome H π).connectedComponentMk K.val.out).mem_supp_iff _ |>.mpr rfl
    have hmL : L.val.out ∈ A.supp := by
      change L.val.out ∈ (f K).val.supp
      rw [he]
      simp only [f,dif_neg hL]
      exact ((monochrome H π).connectedComponentMk L.val.out).mem_supp_iff _ |>.mpr rfl
    let g : A.toSimpleGraph →g monochrome H σ := {
      toFun := Subtype.val
      map_rel' := fun {a b} h => (monochrome_update_off H π x j a b
        (fun hh => fav K hK (hh ▸ a.prop)) (fun hh => fav K hK (hh ▸ b.prop))).mp h }
    have hh := SimpleGraph.ConnectedComponent.sound
      (((A.connected_toSimpleGraph ⟨K.val.out,hmK⟩ ⟨L.val.out,hmL⟩).some.map g).reachable)
    apply Subtype.ext
    exact K.val.out_eq.symm.trans (hh.trans L.val.out_eq)

/-- Full Lemma 4.10, including capacity-two targets. The replacement
component may be a long odd cycle; the count comparison does not call it a
clique. Thus it repairs the overly narrow sentence in the manuscript proof. -/
theorem weighted_component_hub_monotone (R : SimpleGraph W) {d : C → ℕ} {π : W → C}
    (hπ : WeightedComponentMinimumThree H R d π)
    (hbudget : ∀ x, (H.degree x : ℤ) < ∑ c, ((d c : ℤ)+1))
    {T : Finset W} (hT : T ∈ badCliques H d π) {x : W} (hx : x ∈ T)
    (j : C) (hj : degreeIn H π x j = d j) :
    degreeIn R π x (π x) ≤ degreeIn R π x j := by
  have hold := lovasz_degree_bound H hπ.1.1 hbudget
  have hown := badClique_own_degree H hold hT hx
  let σ := Function.update π x j
  have henergy : weightedEnergy H d σ = weightedEnergy H d π := by
    rw [weightedEnergy_update,hj,hown]
    omega
  have hσ : WeightedMinimum H d σ := fun ρ => henergy ▸ hπ.1.1 ρ
  have hc := weighted_bad_count_update_le H hold x j hT hx
  have hσtwo : WeightedComponentMinimumTwo H d σ := ⟨hσ,fun ρ hρ => hc.trans (hπ.1.2 ρ hρ)⟩
  have hh := hπ.2 σ hσtwo
  rw [energy_update] at hh
  omega

end Se20Part.Partition
