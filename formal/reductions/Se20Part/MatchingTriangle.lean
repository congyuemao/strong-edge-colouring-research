import Se20Part.CompactGeometry

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
variable {V : Type*} {G : SimpleGraph V}

theorem forest_matching_clique_two (hg : G.IsAcyclic) (T : Finset G.edgeSet)
    (hcl : (L2 G).IsClique (T : Set G.edgeSet))
    (hmatch : ∀ e ∈ T, ∀ f ∈ T, e ≠ f → ∀ v ∈ e.val, v ∉ f.val) : T.card ≤ 2 := by
  by_contra hh
  obtain ⟨e,he,hm⟩ := T.exists_max_image (ForestL2.height G) (Finset.card_pos.mp (by omega))
  have hc := Finset.card_erase_add_one he
  obtain ⟨f,hf,k,hk,hfk⟩ := Finset.one_lt_card.mp (by omega : 1 < (T.erase e).card)
  obtain ⟨hfe,hf⟩ := Finset.mem_erase.mp hf
  obtain ⟨hke,hk⟩ := Finset.mem_erase.mp hk
  obtain ⟨p,c,hep,hpc,hd,hheight⟩ := ForestL2.orient hg e
  have hpf : p ∉ f.val := hmatch e he f hf hfe.symm p (hep ▸ Sym2.mem_mk_left p c)
  have hpk : p ∉ k.val := hmatch e he k hk hke.symm p (hep ▸ Sym2.mem_mk_left p c)
  obtain ⟨q,hqf,hpq,hq⟩ :=
    (ForestL2.neighbour_cover hg hep hpc hd (hheight ▸ hm f hf) (hcl he hf hfe.symm)).resolve_left hpf
  obtain ⟨r,hrk,hpr,hr⟩ :=
    (ForestL2.neighbour_cover hg hep hpc hd (hheight ▸ hm k hk) (hcl he hk hke.symm)).resolve_left hpk
  have hqr := ForestL2.lower_neighbour_unique hg hpq hpr hq hr
  exact hmatch f hf k hk hfk q hqf (hqr ▸ hrk)

variable [Fintype V] (G : SimpleGraph V)

theorem small_support_acyclic (S : Finset V) (hg : 7 ≤ G.egirth) (hS : S.card ≤ 6) :
    (G.induce (S : Set V)).IsAcyclic := by
  by_contra hn
  obtain ⟨v,w,hw,_⟩ := SimpleGraph.exists_girth_eq_length.mpr hn
  have hc : w.length ≤ S.card := by
    have hp := hw.isPath_tail.length_lt
    have hl := SimpleGraph.Walk.length_tail_add_one hw.not_nil
    have hcard : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
    rw [hcard] at hp
    omega
  have hh := hg.trans (hw.map (f := (inducedEmbedding G S).toHom)
    (inducedEmbedding G S).injective).egirth_le_length
  simp only [SimpleGraph.Walk.length_map] at hh
  have hh' : 7 ≤ w.length := by exact_mod_cast hh
  omega

/-- A matching of three edges cannot be a strong clique at girth at least
seven. Conflict witnesses remain in the fixed ambient graph throughout. -/
theorem no_matching_clique_three (hg : 7 ≤ G.egirth) (T : Finset G.edgeSet)
    (hT : T.card = 3) (hcl : (L2 G).IsClique (T : Set G.edgeSet))
    (hmatch : ∀ e ∈ T, ∀ f ∈ T, e ≠ f → ∀ v ∈ e.val, v ∉ f.val) : False := by
  let S := edgeSupport G T
  have hS : S.card ≤ 6 := by
    calc
      S.card ≤ ∑ e ∈ T, e.val.toFinset.card := Finset.card_biUnion_le
      _ = ∑ _e ∈ T, 2 := Finset.sum_congr rfl (fun e _ => edge_endpoints_card G e)
      _ = 6 := by simp [hT]
  have hq (e : T) : ∃ f : (G.induce (S : Set V)).edgeSet,
      (inducedEmbedding G S).mapEdgeSet f = e.val := by
    apply exists_edge_induce
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨e,e.prop,Sym2.mem_toFinset.mpr hv⟩
  choose q hq using hq
  let U : Finset (G.induce (S : Set V)).edgeSet := Finset.univ.image q
  have hqinj : Function.Injective q := by
    intro e f hef
    apply Subtype.ext
    rw [← hq e,← hq f,hef]
  have hU : U.card = 3 := by
    rw [Finset.card_image_of_injective _ hqinj,Finset.card_univ,Fintype.card_coe,hT]
  have hclU : (L2 (G.induce (S : Set V))).IsClique (U : Set _) := by
    intro e he f hf hef
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hf
    apply (L2_induce_adj_iff G S _ _).mp
    rw [hq a,hq b]
    exact hcl a.prop b.prop (fun hh => hef (congrArg q (Subtype.ext hh)))
  have hmatchU : ∀ e ∈ U, ∀ f ∈ U, e ≠ f → ∀ v ∈ e.val, v ∉ f.val := by
    intro e he f hf hef v hv hvf
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hf
    apply hmatch a a.prop b b.prop (fun hh => hef (congrArg q (Subtype.ext hh))) v.val
    · rw [← hq a]
      exact Sym2.mem_map.mpr ⟨v,hv,rfl⟩
    · rw [← hq b]
      exact Sym2.mem_map.mpr ⟨v,hvf,rfl⟩
  have hh := forest_matching_clique_two (small_support_acyclic G S hg hS) U hclU hmatchU
  omega

end Se20Part
