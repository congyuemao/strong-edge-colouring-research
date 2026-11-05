import Se20Part.CompactExchange

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def edgeSupport (T : Finset G.edgeSet) : Finset V := T.biUnion (fun e => e.val.toFinset)
def Compact (T : Finset G.edgeSet) : Prop := (edgeSupport G T).card ≤ 4
def hubs (e : G.edgeSet) : Finset G.edgeSet :=
  Finset.univ.filter (fun f => f ≠ e ∧ ∃ v ∈ e.val, v ∈ f.val)

theorem edge_endpoints_card (e : G.edgeSet) : e.val.toFinset.card = 2 := by
  apply Sym2.card_toFinset_of_not_isDiag
  exact G.not_isDiag_of_mem_edgeSet e.prop

theorem compact_has_hub (T : Finset G.edgeSet) (hT : T.card = 3)
    (hc : Compact G T) (e : G.edgeSet) (he : e ∈ T) :
    ∃ f ∈ T, f ∈ hubs G e := by
  by_contra! hn
  let S := edgeSupport G T
  let U := S \ e.val.toFinset
  have hes : e.val.toFinset ⊆ S := fun v hv =>
    Finset.mem_biUnion.mpr ⟨e,he,hv⟩
  have hU : U.card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset hes]
    have hh := edge_endpoints_card G e
    change S.card ≤ 4 at hc
    omega
  have hsub (f : G.edgeSet) (hf : f ∈ T.erase e) : f.val.toFinset ⊆ U := by
    intro v hv
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨f,(Finset.mem_erase.mp hf).2,hv⟩,?_⟩
    intro hve
    exact hn f (Finset.mem_erase.mp hf).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_erase.mp hf).1,
        v,Sym2.mem_toFinset.mp hve,Sym2.mem_toFinset.mp hv⟩)
  have htwo : (T.erase e).card = 2 := by
    have hh := Finset.card_erase_add_one he
    omega
  obtain ⟨f,g,hfg,hset⟩ := Finset.card_eq_two.mp htwo
  have hf : f ∈ T.erase e := by rw [hset]; simp
  have hg : g ∈ T.erase e := by rw [hset]; simp
  have hfU := Finset.eq_of_subset_of_card_le (hsub f hf) (hU.trans_eq (edge_endpoints_card G f).symm)
  have hgU := Finset.eq_of_subset_of_card_le (hsub g hg) (hU.trans_eq (edge_endpoints_card G g).symm)
  apply hfg
  apply Subtype.ext
  apply Sym2.ext
  intro v
  simpa only [Sym2.mem_toFinset] using
    (show v ∈ f.val.toFinset ↔ v ∈ g.val.toFinset from by rw [hfU,hgU])

theorem hubs_symm {e f : G.edgeSet} (hf : f ∈ hubs G e) : e ∈ hubs G f := by
  obtain ⟨hne,v,he,hf⟩ := (Finset.mem_filter.mp hf).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne.symm,v,hf,he⟩

/-- The compact-support classification needed by 4.6, without a drawing:
some edge meets each of the other two edges. -/
theorem compact_has_pivot (T : Finset G.edgeSet) (hT : T.card = 3)
    (hc : Compact G T) : ∃ e ∈ T, T.erase e ⊆ hubs G e := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hT
  have ha := compact_has_hub G _ (by simp [hab,hac,hbc]) hc a (by simp)
  have hb := compact_has_hub G _ (by simp [hab,hac,hbc]) hc b (by simp)
  have hc' := compact_has_hub G _ (by simp [hab,hac,hbc]) hc c (by simp)
  have hself (e : G.edgeSet) : e ∉ hubs G e := by simp [hubs]
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb hc'
  by_cases hab' : b ∈ hubs G a
  · by_cases hac' : c ∈ hubs G a
    · exact ⟨a,by simp,by intro x hx; simp only [Finset.mem_erase,Finset.mem_insert,
        Finset.mem_singleton] at hx; rcases hx.2 with rfl|rfl|rfl; exact False.elim (hx.1 rfl); exact hab'; exact hac'⟩
    · have hcb : b ∈ hubs G c := by
        rcases hc' with ⟨f,(rfl|rfl|rfl),hf⟩
        · exact False.elim (hac' (hubs_symm G hf))
        · exact hf
        · exact False.elim (hself _ hf)
      refine ⟨b,by simp,?_⟩
      intro x hx
      simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx.2 with rfl|rfl|rfl
      · exact hubs_symm G hab'
      · exact False.elim (hx.1 rfl)
      · exact hubs_symm G hcb
  · have hac' : c ∈ hubs G a := by
      rcases ha with ⟨f,(rfl|rfl|rfl),hf⟩
      · exact False.elim (hself _ hf)
      · exact False.elim (hab' hf)
      · exact hf
    have hbc' : c ∈ hubs G b := by
      rcases hb with ⟨f,(rfl|rfl|rfl),hf⟩
      · exact False.elim (hab' (hubs_symm G hf))
      · exact False.elim (hself _ hf)
      · exact hf
    refine ⟨c,by simp,?_⟩
    intro x hx
    simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx.2 with rfl|rfl|rfl
    · exact hubs_symm G hac'
    · exact hubs_symm G hbc'
    · exact False.elim (hx.1 rfl)

theorem hubs_card_le_six (hΔ : MaxDegreeFour G) (e : G.edgeSet) :
    (hubs G e).card ≤ 6 := by
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hu : e ∈ incident G u := (mem_incident G u e).mpr (he ▸ Sym2.mem_mk_left u v)
  have hv : e ∈ incident G v := (mem_incident G v e).mpr (he ▸ Sym2.mem_mk_right u v)
  have hh : hubs G e = (incident G u).erase e ∪ (incident G v).erase e := by
    ext f
    simp only [hubs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
      Finset.mem_erase,mem_incident,he,Sym2.mem_iff]
    aesop
  rw [hh]
  have h1 := Finset.card_erase_add_one hu
  have h2 := Finset.card_erase_add_one hv
  rw [card_incident] at h1 h2
  have hd1 := hΔ u
  have hd2 := hΔ v
  have hh := Finset.card_union_le ((incident G u).erase e) ((incident G v).erase e)
  omega

end Se20Part
