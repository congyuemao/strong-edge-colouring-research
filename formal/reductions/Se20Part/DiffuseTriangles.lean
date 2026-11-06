import Se20Part.DiffuseSaturation

noncomputable section
open scoped Classical
namespace Se20Part
open Partition
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance : DecidableEq G.edgeSet := Classical.decEq _
local instance : DecidableEq (Fin 10) := Classical.decEq _
set_option maxHeartbeats 2000000

theorem hubs_conflict {e f : G.edgeSet} (h : f ∈ hubs G e) : (L2 G).Adj e f := by
  obtain ⟨hne,v,hve,hvf⟩ := (mem_hubs G _ _).mp h
  exact ⟨hne.symm,v,hve,v,hvf,Or.inl rfl⟩

theorem third_triangle_edge {T : Finset G.edgeSet} (hT : T.card = 3)
    {e f : G.edgeSet} (he : e ∈ T) (hf : f ∈ T) (hef : e ≠ f) :
    ∃ g ∈ T, g ≠ e ∧ g ≠ f ∧ T = {e,f,g} := by
  obtain ⟨g,hg,hgn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({e,f} : Finset G.edgeSet).card < T.card by simp [hT,hef])
  have hge : g ≠ e := fun h => hgn (by simp [h])
  have hgf : g ≠ f := fun h => hgn (by simp [h])
  refine ⟨g,hg,hge,hgf,?_⟩
  apply (Finset.eq_of_subset_of_card_le
    (show {e,f,g} ⊆ T by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨he,hf,hg⟩)
    (by simp [hT,hef,hge.symm,hgf.symm])).symm

theorem linked_pair_of_not_hub (e f : G.edgeSet) (h : f ∉ hubs G e) : Linked G {e,f} := by
  intro a ha b hb hab hh
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact hab rfl
  · exact h hh
  · exact h (hubs_symm G hh)
  · exact hab rfl

/-- Lemma 4.7. The full five-coordinate minimum has no diffuse triangle.
The proof works for maximum degree four, without regularity. -/
theorem no_diffuse_triangles_ten (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {π : G.edgeSet → Fin 10} (hπ : RouteMinimum G π) :
    typedTriangles (L2 G) (Diffuse G) π = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  obtain ⟨ht,hD,hcl⟩ := (mem_typedTriangles (L2 G) _ _ T).mp hT
  have hT' : T ∈ typedTriangles (L2 G) (fun _ => True) π :=
    (mem_typedTriangles _ _ _ _).mpr ⟨ht,trivial,hcl⟩
  obtain ⟨e,he,b,hb,hbh⟩ := triangle_has_hub G hg ht
    (fun a ha b hb hab => (hcl a ha b hb hab).1)
  have hbe := ((mem_hubs G _ _).mp hbh).1
  obtain ⟨g,hgT,hge,hgb,hset⟩ := third_triangle_edge G ht he hb hbe.symm
  have hghe : g ∉ hubs G e := fun hh => hgb
    (diffuse_at_most_one_hub G ht hD he hgT hb hh hbh)
  have hghb : g ∉ hubs G b := fun hh => hge
    (diffuse_at_most_one_hub G ht hD hb hgT he hh (hubs_symm G hbh))
  obtain ⟨δ,hδe,hδb,hδg⟩ := shared_triangle_bridge G hg e b g hbh hghe hghb
    (hcl e he g hgT hge.symm).1 (hcl b hb g hgT hgb.symm).1
  have hδne := ((mem_hubs G _ _).mp hδe).1
  have hδnb := ((mem_hubs G _ _).mp hδb).1
  have hδng := ((mem_hubs G _ _).mp hδg).1
  have hd := route_minimum_degree G hΔ hπ.1.1.1.1
  have hδcol : π δ ≠ π e := by
    intro hc
    have hδT := typed_triangle_closed (L2 G) hd hT he (hubs_conflict G hδe) hc.symm
    exact hδnb (diffuse_at_most_one_hub G ht hD he hδT hb hδe hbh)
  have hsate := diffuse_hub_saturation G hΔ hg hπ hT he hb hbh
  have hj := hsate.2.1 δ hδe hδcol
  have hjd := ((mem_zeroClasses_ten G _ _ _).mp hj).2
  have hown := typed_triangle_own_degree (L2 G) hd hT he
  have hmin := minimumTwo_update_of_bad (L2 G) hπ.1.1.1 hd e (π δ)
    (hjd.trans hown.symm) (typed_triangle_bad (L2 G) hT he)
  let σ := Function.update π e (π δ)
  have hd' : ∀ v, degreeIn (L2 G) σ v (σ v) ≤ 2 := route_minimum_degree G hΔ hmin.1
  obtain ⟨U,hU,heU,_,_,_,_⟩ := diffuse_zero_hub G hΔ hg hπ hT he hb hbh hj
  have hδU : δ ∈ U := typed_triangle_closed (L2 G) hd' hU heU (hubs_conflict G hδe)
    (by simp [σ,Function.update_of_ne hδne])
  have hcu := (mem_typedTriangles (L2 G) _ _ U).mp hU
  obtain ⟨t,htU,hte,htδ,hUset⟩ := third_triangle_edge G hcu.1 heU hδU hδne.symm
  have htcol : π t = π δ := by
    simpa only [Function.update_of_ne hte,Function.update_self] using (hcu.2.2 t htU e heU hte).2
  have hth : t ∉ hubs G e := by
    intro hh
    exact htδ (hsate.2.2 t hh δ hδe (fun hc => hδcol (htcol.symm.trans hc)) hδcol htcol)
  have hLT := diffuse_erase_linked G ht hD he hb hbh
  by_cases hco : Compact G U
  · have htδh : δ ∈ hubs G t := by
      obtain ⟨f,hf,hfh⟩ := compact_has_hub G U hcu.1 hco t htU
      rw [hUset] at hf
      simp only [Finset.mem_insert,Finset.mem_singleton] at hf
      rcases hf with rfl|rfl|rfl
      · exact False.elim (hth (hubs_symm G hfh))
      · exact hfh
      · exact False.elim (((mem_hubs G _ _).mp hfh).1 rfl)
    have hLU : ¬ Linked G (U.erase e) := by
      intro hl
      exact hl t (Finset.mem_erase.mpr ⟨hte,htU⟩) δ (Finset.mem_erase.mpr ⟨hδne,hδU⟩) htδ htδh
    have hUerase : U.erase δ = {e,t} := by
      ext f
      simp only [hUset,Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
      aesop
    have hLy : Linked G (U.erase δ) := by rw [hUerase]; exact linked_pair_of_not_hub G e t hth
    have hUp : U.erase δ ⊆ hubs G δ := by
      rw [hUerase]
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hubs_symm G hδe,hubs_symm G htδh⟩
    have hUco : U ∈ typedTriangles (L2 G) (Compact G) σ :=
      (mem_typedTriangles _ _ _ _).mpr ⟨hcu.1,hco,hcu.2.2⟩
    have h4 := compact_closures_le_four G hΔ hUco hδU hUp (by
      intro k hk
      obtain ⟨hkne,hkdeg⟩ := (mem_zeroClasses_ten G _ _ _).mp hk
      have hownδ := typed_triangle_own_degree (L2 G) hd' hU hδU
      have hmin2 := minimumTwo_update_of_bad (L2 G) hmin hd' δ k
        (hkdeg.trans hownδ.symm) (typed_triangle_bad (L2 G) hU hδU)
      exact two_flip_compact_replacement (L2 G) hπ hd e (π δ) hδcol hd'
        hT' he hU heU hD hco hLT hLU δ hδU hLy k hkne hmin2
        (route_minimum_degree G hΔ hmin2.1))
    have h5 := zeroClasses_ten (L2 G) hmin.1 δ
      (typed_triangle_own_degree (L2 G) hd' hU hδU) (conflict_degree_le_twentyFour G hΔ δ)
    dsimp only [σ] at h4
    omega
  · have hLU := minimumFive_pair_type (L2 G) hπ hd e (π δ) hδcol hmin hd' hT' he hU heU
      (iff_of_false hD hco) (iff_of_true hD hco) hLT
    have hr := typedTriangles_flip_count (L2 G) hd e (π δ) hd' hT' he hU heU (Compact G)
    have hs := typedTriangles_flip_count (L2 G) hd e (π δ) hd' hT' he hU heU (Diffuse G)
    have hl := typedPairs_flip_count (L2 G) hd e (π δ) hδcol hd' hT' he hU heU (Linked G)
    simp only [if_neg hD,if_neg hco,Nat.add_zero] at hr
    have hDU : Diffuse G U := hco
    simp only [if_pos hD,if_pos hDU] at hs
    simp only [if_pos hLT,if_pos hLU] at hl
    have hσ : RouteMinimum G σ := minimumFive_of_equal (L2 G) hπ hmin hr
      (Nat.add_right_cancel hs) (Nat.add_right_cancel hl)
    have hUD : U ∈ typedTriangles (L2 G) (Diffuse G) σ :=
      (mem_typedTriangles _ _ _ _).mpr ⟨hcu.1,hco,hcu.2.2⟩
    have hsatδ := (diffuse_hub_saturation G hΔ hg hσ hUD hδU heU (hubs_symm G hδe)).2.2
    have hbcol : σ b = π e := by
      simp only [σ,Function.update_of_ne hbe]; exact (hcl b hb e he hbe).2
    have hgcol : σ g = π e := by
      simp only [σ,Function.update_of_ne hge]; exact (hcl g hgT e he hge).2
    have hδcol' : σ δ = π δ := by simp [σ,Function.update_of_ne hδne]
    exact hgb (hsatδ g (hubs_symm G hδg) b (hubs_symm G hδb)
      (by rw [hgcol,hδcol']; exact hδcol.symm)
      (by rw [hbcol,hδcol']; exact hδcol.symm) (hgcol.trans hbcol.symm))

end Se20Part
