import Se20Part.ComponentExchange

noncomputable section
open scoped Classical
namespace Se20Part
variable {W : Type*} [Fintype W] (H J : SimpleGraph W)

theorem bad_count_le_of_no_new (hΔ : ∀ v, H.degree v ≤ 2) (x : W)
    (heq : ∀ a b, a ≠ x → b ≠ x → (H.Adj a b ↔ J.Adj a b))
    (hnew : (J.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    Fintype.card (BadComponent J) ≤ Fintype.card (BadComponent H) := by
  have hav (K : BadComponent J) : x ∉ K.val.supp := by
    intro hx
    exact K.prop ((K.val.mem_supp_iff x).mp hx ▸ hnew)
  let f : BadComponent J → BadComponent H := fun K =>
    ⟨H.connectedComponentMk K.val.out,
      (bad_component_transfer H J hΔ x heq K (hav K)).1⟩
  apply Fintype.card_le_of_injective f
  intro K L hKL
  have he : (f K).val = (f L).val := congrArg Subtype.val hKL
  let C := (f K).val
  have hx : x ∉ C.supp := (bad_component_transfer H J hΔ x heq K (hav K)).2
  have hK : K.val.out ∈ C.supp := (C.mem_supp_iff _).mpr rfl
  have hL : L.val.out ∈ C.supp := by
    change L.val.out ∈ (f K).val.supp
    rw [he]
    exact ((f L).val.mem_supp_iff _).mpr rfl
  let g : C.toSimpleGraph →g J := {
    toFun := Subtype.val
    map_rel' := fun {a b} h => (heq a b (fun hh => hx (hh ▸ a.prop))
      (fun hh => hx (hh ▸ b.prop))).mp h }
  have hh := SimpleGraph.ConnectedComponent.sound
    (((C.connected_toSimpleGraph ⟨K.val.out,hK⟩ ⟨L.val.out,hL⟩).some.map g).reachable)
  apply Subtype.ext
  exact K.val.out_eq.symm.trans (hh.trans L.val.out_eq)

theorem bad_at_transfer (hΔ : ∀ v, H.degree v ≤ 2) (x e : W)
    (heq : ∀ a b, a ≠ x → b ≠ x → (H.Adj a b ↔ J.Adj a b))
    (hbad : ¬ (J.connectedComponentMk e).toSimpleGraph.Colorable 2)
    (hx : x ∉ (J.connectedComponentMk e).supp) :
    ¬ (H.connectedComponentMk e).toSimpleGraph.Colorable 2 ∧
      x ∉ (H.connectedComponentMk e).supp := by
  let K := J.connectedComponentMk e
  have hmem : e ∈ (H.connectedComponentMk K.out).supp :=
    component_image_mem H J K
      (fun a ha b hb h => (heq a b (fun he => hx (he ▸ ha))
        (fun he => hx (he ▸ hb))).mpr h) ((K.mem_supp_iff e).mpr rfl)
  have he := ((H.connectedComponentMk K.out).mem_supp_iff e).mp hmem
  have hh := bad_component_transfer H J hΔ x heq ⟨K,hbad⟩ hx
  exact he ▸ hh

namespace Partition
variable {C : Type*} [Fintype C]

theorem monochrome_update_off (π : W → C) (x : W) (c : C)
    (a b : W) (ha : a ≠ x) (hb : b ≠ x) :
    (monochrome H π).Adj a b ↔ (monochrome H (Function.update π x c)).Adj a b := by
  simp [monochrome, Function.update_of_ne ha, Function.update_of_ne hb]

/-- Lemma 4.8. The second move may go back to the original class of e; the
proof compares component counts and does not assume full optimality after
an arbitrary intermediate move. -/
theorem internal_zero_class_even_path {π : W → C} (hπ : MinimumTwo H π)
    (hbound : ∀ σ : W → C, Minimum H σ → ∀ v, degreeIn H σ v (σ v) ≤ 2)
    (e : W) (j : C) (hj : j ≠ π e)
    (hzero : degreeIn H π e j = degreeIn H π e (π e))
    (hodd : ¬ ((monochrome H π).connectedComponentMk e).toSimpleGraph.Colorable 2)
    (P : EvenPathClosure H π e j) (i : Fin P.size)
    (hi : i.val ≠ 0) (hil : i.val+1 ≠ P.size)
    (k : C) (hk : k ≠ j)
    (hpk : degreeIn H π (P.vertex i) k = degreeIn H π (P.vertex i) j) :
    Nonempty (EvenPathClosure H π (P.vertex i) k) := by
  let p := P.vertex i
  let σ := Function.update π p k
  let τ := Function.update π e j
  let ρ := Function.update σ e j
  have hp : π p = j := P.in_class i
  have hpe : p ≠ e := fun he => hj (by simpa [he] using hp.symm)
  have hno : ¬ H.Adj e p := by
    intro hep
    obtain ⟨a,ha,haend⟩ := (P.neighbours p).mp ⟨hep,hp⟩
    have ha' : a = i := P.vertex.injective ha
    subst a
    exact haend.elim hi hil
  have hσ : Minimum H σ := minimum_update H hπ.1 p k (by simpa [hp] using hpk)
  have hd (s : W → C) (hs : Minimum H s) : ∀ v, (monochrome H s).degree v ≤ 2 := by
    intro v
    have hh := hbound s hs v
    rw [← monochrome_degree] at hh
    exact_mod_cast hh
  apply even_path_of_flip_bad H p k (by simpa [hp] using hk) (hbound σ hσ)
  intro hσgood
  have hcnt := bad_count_le_of_no_new (monochrome H π) (monochrome H σ)
    (hd π hπ.1) p (monochrome_update_off H π p k) hσgood
  have hσtwo : MinimumTwo H σ := by
    refine ⟨hσ, fun s hs => ?_⟩
    rw [← phi2_eq_card_bad, ← phi2_eq_card_bad] at hcnt
    exact hcnt.trans (hπ.2 s hs)
  have hav : p ∉ ((monochrome H π).connectedComponentMk e).supp := by
    intro hm
    have hh := monochrome_class_constant H π _ hm
      (((monochrome H π).connectedComponentMk e).mem_supp_iff e |>.mpr rfl)
    exact hj (hp.symm.trans hh)
  have hσbad := (bad_at_transfer (monochrome H σ) (monochrome H π) (hd σ hσ) p e
    (fun a b ha hb => (monochrome_update_off H π p k a b ha hb).symm) hodd hav).1
  have hezero : degreeIn H σ e j = degreeIn H σ e (σ e) := by
    simp only [σ, Function.update_of_ne hpe.symm, degreeIn_update, hno, false_and,
      ite_false, add_zero, sub_zero]
    exact hzero
  have hρbad : ¬ ((monochrome H ρ).connectedComponentMk e).toSimpleGraph.Colorable 2 :=
    flip_creates_odd_component H hσtwo (hbound σ hσ) e j hezero hσbad
  have hτ : Minimum H τ := minimum_update H hπ.1 e j hzero
  have hcomm : ρ = Function.update τ p k := by
    ext a
    by_cases ha : a = e <;> by_cases hb : a = p <;>
      simp_all [ρ,τ,σ,Function.update]
  have havρ : p ∉ ((monochrome H ρ).connectedComponentMk e).supp := by
    intro hm
    have hh := monochrome_class_constant H ρ _ hm
      (((monochrome H ρ).connectedComponentMk e).mem_supp_iff e |>.mpr rfl)
    have hpk' : ρ p = k := by simp [ρ,σ,Function.update_of_ne hpe]
    have hej' : ρ e = j := by simp [ρ]
    exact hk (hpk'.symm.trans (hh.trans hej'))
  have hnot := (bad_at_transfer (monochrome H τ) (monochrome H ρ) (hd τ hτ) p e
    (by rw [hcomm]; exact monochrome_update_off H τ p k) hρbad havρ).2
  apply hnot
  let f : SimpleGraph.pathGraph P.size →g monochrome H τ := {
    toFun := P.vertex
    map_rel' := by
      intro a b hab
      have hna : P.vertex a ≠ e := fun he => hj (by simpa [he] using (P.in_class a).symm)
      have hnb : P.vertex b ≠ e := fun he => hj (by simpa [he] using (P.in_class b).symm)
      exact ⟨(P.adj_iff a b).mpr (SimpleGraph.pathGraph_adj.mp hab),
        by simp [τ, Function.update_of_ne hna, Function.update_of_ne hnb, P.in_class]⟩ }
  let a : Fin P.size := ⟨0,by have := P.two_le; omega⟩
  have hea : (monochrome H τ).Adj e (P.vertex a) := by
    refine ⟨((P.neighbours _).mpr ⟨a,rfl,Or.inl rfl⟩).1, ?_⟩
    have hna : P.vertex a ≠ e := fun he => hj (by simpa [he] using (P.in_class a).symm)
    simp [τ, Function.update_of_ne hna, P.in_class]
  apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
  apply SimpleGraph.ConnectedComponent.sound
  exact (((SimpleGraph.pathGraph_preconnected P.size i a).some.map f).reachable.trans hea.symm.reachable)

end Partition
end Se20Part
