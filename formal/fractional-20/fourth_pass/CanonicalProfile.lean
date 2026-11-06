import fourth_pass.RootProfile

namespace Se20Fractional.FourthPass.Canonical
open Finset ThirdPass Encoding Packed
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def predicateCode (es : List Edge) (p : Edge → Bool) : Nat :=
  Finset.equivBitIndices.symm ((range es.length).filter (fun i => p (es[i]?.getD (0,0))))

theorem predicateCode_bit (es : List Edge) (p : Edge → Bool) (i : Nat) :
    (predicateCode es p).testBit i = true ↔ i < es.length ∧ p (es[i]?.getD (0,0)) = true := by
  have he := Finset.equivBitIndices.apply_symm_apply
    ((range es.length).filter (fun i => p (es[i]?.getD (0,0))))
  change (predicateCode es p).bitIndices.toFinset = _ at he
  simpa using Finset.ext_iff.mp he i

theorem predicateCode_lt (es : List Edge) (p : Edge → Bool) : predicateCode es p < 2^es.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro h
  have := ((predicateCode_bit es p i).mp h).1
  omega

theorem code_select (es : List Edge) (p : Edge → Bool) (e : Edge) :
    e ∈ (es.zipIdx.filter (fun q => (predicateCode es p).testBit q.2)).map Prod.fst ↔
      e ∈ es ∧ p e = true := by
  constructor
  · intro h
    obtain ⟨⟨f,i⟩,hf,he⟩ := List.mem_map.mp h
    dsimp only at he
    subst f
    obtain ⟨hzip,hbit⟩ := List.mem_filter.mp hf
    have hget := List.mk_mem_zipIdx_iff_getElem?.mp hzip
    have hp := ((predicateCode_bit es p i).mp hbit).2
    rw [hget] at hp
    exact ⟨List.mem_of_getElem? hget,hp⟩
  · rintro ⟨he,hp⟩
    obtain ⟨i,hi,hie⟩ := List.mem_iff_getElem.mp he
    refine List.mem_map.mpr ⟨(e,i),List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · apply List.mk_mem_zipIdx_iff_getElem?.mpr
      simpa [hie] using List.getElem?_eq_getElem hi
    · apply (predicateCode_bit es p i).mpr
      exact ⟨hi,by simpa [List.getElem?_eq_getElem hi,hie] using hp⟩

noncomputable def Listing.types {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : List Nat := L.U.map (typeMask G r L.A)
noncomputable def Listing.innerCode {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : Nat := predicateCode (innerPairs (G.degree r))
      (fun e => adjacent 14 (encodeGraph L.graph) e.1 e.2)

theorem Listing.profile {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (hΔ : ∀ v, G.degree v ≤ 4) (hQ : Clique (L2 G) Q)
    (hLow : DReduction.LocallyLow G Q) (hsize : Q.card = 16)
    (hs : 3 ≤ (labels Q r).card) :
    RootProfile (G.degree r) (labels Q r).card L.innerCode L.types
      (encodeSelected L.graph L.selected) := by
  obtain ⟨hΔ',hcard,hQ',hLow'⟩ := relabel_data L.iso hΔ Q hQ hLow
  have hsle : (labels Q r).card ≤ G.degree r := by
    have hsub : labels Q r ⊆ G.neighborFinset r := filter_subset _ _
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using card_le_card hsub
  have hmem (e : Edge) : e ∈ (encodeSelected L.graph L.selected).chosen ↔
      ∃ a b : Fin 14, (a.val,b.val) = e ∧ a < b ∧
        ∃ h : L.graph.Adj a b, (⟨s(a,b),h⟩ : L.graph.edgeSet) ∈ L.selected := by
    simp only [encodeSelected,Finset.mem_toList]
    exact mem_selectedPairs L.graph L.selected e
  refine ⟨encodeSelected_model L.graph hΔ' L.selected hQ' hLow',hΔ r,hsle,hs,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hl := L.length
    simp only [List.length_cons,List.length_append] at hl
    simpa only [Listing.types,List.length_map,← L.A_length] using (by rw [L.A_length] at hl; omega : G.degree r+1+L.U.length=14)
  · intro e he
    obtain ⟨a,b,rfl,hab,_,_⟩ := (hmem e).mp he
    exact hab
  · exact nodup_toList _
  · rw [encodeSelected_length]
    exact hcard.trans hsize
  · intro v hv
    exact (encoded_adj L.graph 0 ⟨v,hv⟩).trans (L.graph_root ⟨v,hv⟩)
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    have hi' : i < (labels Q r).card := List.mem_range.mp hi
    have hv : i+1 < 14 := by have := hΔ r; omega
    have ha : L.graph.Adj 0 ⟨i+1,hv⟩ := (L.graph_root _).mpr ⟨by simp,by change i+1 ≤ G.degree r; omega⟩
    apply (hmem (0,i+1)).mpr
    exact ⟨0,⟨i+1,hv⟩,rfl,by change 0 < i+1; omega,ha,
      (L.selected_root _ ha).mpr (by change i+1 ≤ (labels Q r).card; omega)⟩
  · intro e he he0
    obtain ⟨a,b,rfl,_,hab,heQ⟩ := (hmem e).mp he
    have ha0 : a = 0 := Fin.ext he0
    subst a
    exact (L.selected_root b hab).mp heQ
  · intro a b ha hab hbd
    change (a,b) ∈ innerEdges (G.degree r) L.innerCode ↔
      adjacent 14 (encodeGraph L.graph) a b = true
    rw [innerEdges,Listing.innerCode,code_select]
    have hm : (a,b) ∈ innerPairs (G.degree r) := by
      apply List.mem_filter.mpr
      exact ⟨(mem_pairs _ a b).mpr ⟨by omega,by omega,hab⟩,by simp only [decide_eq_true_eq]; omega⟩
    simp only [hm,true_and]
  · intro x hx a ha
    have hx' : x < L.U.length := by simpa [Listing.types] using hx
    have ha' : a < L.A.length := by simpa [L.A_length] using ha
    have hbA : a+1 < 14 := by have := hΔ r; omega
    have hbU : G.degree r+1+x < 14 := by
      have := L.length
      simp only [List.length_cons,List.length_append,L.A_length] at this
      omega
    have hget : L.types[x]?.getD 0 = typeMask G r L.A L.U[x] := by
      simp [Listing.types,List.getElem?_eq_getElem hx']
    apply Bool.eq_iff_iff.mpr
    rw [hget,typeMask_bit]
    simp only [ha',true_and,List.getElem?_eq_getElem ha',Option.getD_some]
    change adjacent 14 (encodeGraph L.graph) (a+1) (G.degree r+1+x) = true ↔ _
    rw [encoded_adj L.graph ⟨a+1,hbA⟩ ⟨G.degree r+1+x,hbU⟩,L.graph_adj,
      L.equiv_A a ha']
    have he : L.equiv ⟨G.degree r+1+x,hbU⟩ = L.U[x] := by
      simpa only [L.A_length] using L.equiv_U x hx'
    rw [he]
    exact G.adj_comm _ _

#print axioms Listing.profile
end Se20Fractional.FourthPass.Canonical
