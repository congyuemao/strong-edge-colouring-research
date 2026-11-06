import Se20Part.TrianglePotentials
import Se20Part.DiffuseGeometry

noncomputable section
open scoped Classical
namespace Se20Part
open Partition
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance : DecidableEq G.edgeSet := Classical.decEq _
local instance : DecidableEq (Fin 10) := Classical.decEq _

theorem mem_zeroClasses_ten (π : G.edgeSet → Fin 10) (e : G.edgeSet) (j : Fin 10) :
    j ∈ zeroClasses (L2 G) π e ↔ j ≠ π e ∧ degreeIn (L2 G) π e j = 2 := by
  simp [zeroClasses]

abbrev RouteMinimum (π : G.edgeSet → Fin 10) : Prop :=
  MinimumFive (L2 G) (Compact G) (Diffuse G) (Linked G) π

theorem conflict_degree_le_twentyFour (hΔ : MaxDegreeFour G) (e : G.edgeSet) :
    (L2 G).degree e ≤ 24 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have heq : (L2 G).neighborFinset e = conflicts G e := by ext f; simp
  rw [heq]
  exact card_conflicts_le_twentyFour G hΔ e

theorem route_minimum_degree (hΔ : MaxDegreeFour G) {π : G.edgeSet → Fin 10}
    (hπ : Minimum (L2 G) π) : ∀ e, degreeIn (L2 G) π e (π e) ≤ 2 :=
  minimum_ten_degree_le_two (L2 G) hπ (conflict_degree_le_twentyFour G hΔ)

/-- Every zero-cost closure at a shared edge of a diffuse triangle is a
triangle and contains a hub of that edge. -/
theorem diffuse_zero_hub (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {π : G.edgeSet → Fin 10} (hπ : RouteMinimum G π)
    {T : Finset G.edgeSet} (hT : T ∈ typedTriangles (L2 G) (Diffuse G) π)
    {e b : G.edgeSet} (he : e ∈ T) (hb : b ∈ T) (hbh : b ∈ hubs G e)
    {j : Fin 10} (hj : j ∈ zeroClasses (L2 G) π e) :
    ∃ U ∈ typedTriangles (L2 G) (fun _ => True) (Function.update π e j),
      e ∈ U ∧ ∃ f ∈ U, f ∈ hubs G e ∧ π f = j := by
  obtain ⟨hjne,hjdeg⟩ := (mem_zeroClasses_ten G _ _ _).mp hj
  have hd := route_minimum_degree G hΔ hπ.1.1.1.1
  have hown := typed_triangle_own_degree (L2 G) hd hT he
  have hmin := minimumTwo_update_of_bad (L2 G) hπ.1.1.1 hd e j
    (hjdeg.trans hown.symm) (typed_triangle_bad (L2 G) hT he)
  have hd' := route_minimum_degree G hΔ hmin.1
  obtain ⟨U,hU,heU⟩ := minimumFour_triangle_replacement (L2 G) hπ.1 e j hmin hT he
  obtain ⟨ht,hD,hcl⟩ := (mem_typedTriangles (L2 G) _ _ T).mp hT
  have hT' : T ∈ typedTriangles (L2 G) (fun _ => True) π :=
    (mem_typedTriangles _ _ _ _).mpr ⟨ht,trivial,hcl⟩
  obtain ⟨hu,_,hclu⟩ := (mem_typedTriangles (L2 G) _ _ U).mp hU
  have hhub : ∃ f ∈ U, f ∈ hubs G e := by
    by_cases hco : Compact G U
    · exact compact_has_hub G U hu hco e heU
    · have hl := minimumFive_pair_type (L2 G) hπ hd e j hjne hmin hd' hT' he hU heU
        (by exact iff_of_false hD hco) (by exact iff_of_true hD hco)
        (diffuse_erase_linked G ht hD he hb hbh)
      exact linked_triangle_has_hub G hg hu (fun a ha b hb hab => (hclu a ha b hb hab).1) e heU hl
  obtain ⟨f,hf,hfh⟩ := hhub
  refine ⟨U,hU,heU,f,hf,hfh,?_⟩
  have hfe := ((mem_hubs G _ _).mp hfh).1
  have hc := (hclu f hf e heU hfe).2
  simpa only [Function.update_of_ne hfe,Function.update_self] using hc

/-- Zero-slack hub saturation. Every available hub lies in a zero class,
and two distinct available hubs cannot have the same colour. -/
theorem diffuse_hub_saturation (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {π : G.edgeSet → Fin 10} (hπ : RouteMinimum G π)
    {T : Finset G.edgeSet} (hT : T ∈ typedTriangles (L2 G) (Diffuse G) π)
    {e b : G.edgeSet} (he : e ∈ T) (hb : b ∈ T) (hbh : b ∈ hubs G e) :
    (zeroClasses (L2 G) π e).card = 5 ∧
    (∀ f ∈ hubs G e, π f ≠ π e → π f ∈ zeroClasses (L2 G) π e) ∧
    ∀ f ∈ hubs G e, ∀ g ∈ hubs G e,
      π f ≠ π e → π g ≠ π e → π f = π g → f = g := by
  let A := (hubs G e).filter (fun f => π f ≠ π e)
  have hA : A.card ≤ 5 := by
    have hc := (mem_typedTriangles (L2 G) _ _ T).mp hT
    have hbe := ((mem_hubs G _ _).mp hbh).1
    have hsub : A ⊆ (hubs G e).erase b := by
      intro f hf
      obtain ⟨hfh,hfcol⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_erase.mpr ⟨fun heq => hfcol (heq ▸ (hc.2.2 b hb e he hbe).2),hfh⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_add_one hbh
    have h3 := hubs_card_le_six G hΔ e
    omega
  let Z := zeroClasses (L2 G) π e
  have hZ : 5 ≤ Z.card := zeroClasses_ten (L2 G) hπ.1.1.1.1 e
    (typed_triangle_own_degree (L2 G) (route_minimum_degree G hΔ hπ.1.1.1.1) hT he)
    (conflict_degree_le_twentyFour G hΔ e)
  have hex (j : Z) : ∃ f : A, π f = j.val := by
    obtain ⟨_,_,_,f,_,hfh,hfj⟩ := diffuse_zero_hub G hΔ hg hπ hT he hb hbh j.prop
    exact ⟨⟨f,Finset.mem_filter.mpr ⟨hfh,fun hh =>
      (((mem_zeroClasses_ten G _ _ _).mp j.prop).1) (hfj.symm.trans hh)⟩⟩,hfj⟩
  choose q hq using hex
  have hinj : Function.Injective q := by
    intro j k heq
    apply Subtype.ext
    exact (hq j).symm.trans ((congrArg (fun f : A => π f.val) heq).trans (hq k))
  have hcard := Fintype.card_le_of_injective q hinj
  have hcard' : Z.card ≤ A.card := by simpa only [Fintype.card_coe] using hcard
  have hsurj : Function.Surjective q := by
    apply (Fintype.bijective_iff_injective_and_card q).mpr ⟨hinj,?_⟩ |>.2
    simp only [Fintype.card_coe]
    omega
  have hzc : Z.card = 5 := by omega
  refine ⟨hzc,?_,?_⟩
  · intro f hf hfc
    obtain ⟨j,hj⟩ := hsurj ⟨f,Finset.mem_filter.mpr ⟨hf,hfc⟩⟩
    have hh : π f = j.val := by simpa only [hj] using hq j
    exact hh ▸ j.prop
  · intro f hf g hg hfc hgc heq
    obtain ⟨j,hj⟩ := hsurj ⟨f,Finset.mem_filter.mpr ⟨hf,hfc⟩⟩
    obtain ⟨k,hk⟩ := hsurj ⟨g,Finset.mem_filter.mpr ⟨hg,hgc⟩⟩
    have hjc : π f = j.val := by simpa only [hj] using hq j
    have hkc : π g = k.val := by simpa only [hk] using hq k
    have hjk : j = k := Subtype.ext (hjc.symm.trans (heq.trans hkc))
    exact congrArg Subtype.val (hj.symm.trans ((congrArg q hjk).trans hk))

/-- The compact pivot's four available hubs cannot serve five distinct
zero classes. The middle partition need not minimize later coordinates. -/
theorem compact_closures_le_four {π : G.edgeSet → Fin 10}
    (hΔ : MaxDegreeFour G)
    {T : Finset G.edgeSet} (hT : T ∈ typedTriangles (L2 G) (Compact G) π)
    {e : G.edgeSet} (he : e ∈ T) (hp : T.erase e ⊆ hubs G e)
    (hclose : ∀ j ∈ zeroClasses (L2 G) π e,
      ∃ U ∈ typedTriangles (L2 G) (Compact G) (Function.update π e j), e ∈ U) :
    (zeroClasses (L2 G) π e).card ≤ 4 := by
  obtain ⟨ht,_,hcl⟩ := (mem_typedTriangles (L2 G) _ _ T).mp hT
  let A := (hubs G e).filter (fun f => π f ≠ π e)
  have hA : A.card ≤ 4 := by
    have hsub : A ⊆ hubs G e \ T.erase e := by
      intro f hf
      obtain ⟨hfh,hfc⟩ := Finset.mem_filter.mp hf
      refine Finset.mem_sdiff.mpr ⟨hfh,?_⟩
      rintro hfT
      obtain ⟨hfe,hfT⟩ := Finset.mem_erase.mp hfT
      exact hfc (hcl f hfT e he hfe).2
    have hh := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hp] at hh
    have hc := hubs_card_le_six G hΔ e
    have hec := Finset.card_erase_add_one he
    omega
  have hex (j : zeroClasses (L2 G) π e) : ∃ f : A, π f = j.val := by
    obtain ⟨U,hU,heU⟩ := hclose j j.prop
    obtain ⟨hu,hco,hclu⟩ := (mem_typedTriangles (L2 G) _ _ U).mp hU
    obtain ⟨f,hf,hfh⟩ := compact_has_hub G U hu hco e heU
    have hfe := ((mem_hubs G _ _).mp hfh).1
    have hc : π f = j.val := by simpa only [Function.update_of_ne hfe,Function.update_self] using
      (hclu f hf e heU hfe).2
    exact ⟨⟨f,Finset.mem_filter.mpr ⟨hfh,fun heq =>
      ((mem_zeroClasses_ten G _ _ _).mp j.prop).1 (hc.symm.trans heq)⟩⟩,hc⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro j k h
    exact Subtype.ext ((hf j).symm.trans ((congrArg (fun a : A => π a.val) h).trans (hf k)))
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe] at hc
  exact hc.trans hA

end Se20Part
