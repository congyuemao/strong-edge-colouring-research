import Se20Part.PetersenMinusSupport

namespace Se20Part

/-- The endpoint order is a0,a1,b0,b1,c0,c1,x0,x1,y0,y1.
The five matching edges and nine normalized witnesses of G16 are all
included. Normalization of an arbitrary overlap is a separate obligation. -/
def matchingOverlapPairs : Finset (Fin 10 × Fin 10) :=
  {(0,1),(2,3),(4,5),(6,7),(8,9),
   (0,2),(0,5),(3,4),(1,6),(2,7),(4,6),(1,8),(3,8),(5,9)}

def MatchingOverlapGraph : SimpleGraph (Fin 10) where
  Adj u v := u ≠ v ∧ ((u,v) ∈ matchingOverlapPairs ∨ (v,u) ∈ matchingOverlapPairs)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel MatchingOverlapGraph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

def matchingOverlapVertexEquiv : Fin 10 ≃ Fin 10 where
  toFun := ![1,5,9,4,2,6,8,0,3,7]
  invFun := ![7,0,4,8,3,1,5,9,6,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem matchingOverlap_adj_iff : ∀ u v,
    PetersenMinusGraph.Adj (matchingOverlapVertexEquiv u) (matchingOverlapVertexEquiv v) ↔
      MatchingOverlapGraph.Adj u v := by
  decide +kernel

/-- The manuscript's explicit endpoint map, checked against the actual
original Petersen-minus graph, not merely against its conflict graph. -/
def matchingOverlapIso : MatchingOverlapGraph ≃g PetersenMinusGraph where
  toEquiv := matchingOverlapVertexEquiv
  map_rel_iff' := matchingOverlap_adj_iff _ _

theorem matchingOverlap_matching_edges : ∀ i : Fin 5,
    MatchingOverlapGraph.Adj ⟨2*i.val,by omega⟩ ⟨2*i.val+1,by omega⟩ := by
  decide +kernel

noncomputable section
open scoped Classical

/-- Between disjoint matching edges, once a witness a--c is present, none
of the other three cross edges is possible in girth at least five. -/
theorem matching_cross_witness_unique {V : Type*} {G : SimpleGraph V}
    (hg : 5 ≤ G.egirth) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d) (hac : G.Adj a c)
    (had : a ≠ d) (hbc : b ≠ c) :
    ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
  refine ⟨?_,?_,?_⟩
  · intro h
    exact GirthFive.no_triangle hg hac hcd h.symm
  · intro h
    exact GirthFive.no_triangle hg hab h hac.symm
  · intro h
    rcases GirthFive.square_backtrack hg hab h hcd.symm hac.symm with he | he
    · exact had he
    · exact hbc he

/-- Once the nine witnesses have the stated normal form, the G15-based
support exclusion applies. This is not the full K4-overlap theorem. -/
theorem critical21_no_normalized_matching_overlap {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG15 : PetersenMinusListTheoremG15)
    (hΔ : MaxDegreeFour G) (hg : 5 ≤ G.egirth)
    (f : MatchingOverlapGraph →g G) (hf : Function.Injective f)
    {F : Finset G.edgeSet} (hF : Critical21 G F) :
    ¬ (∀ u : Fin 10, ∃ e ∈ F, f u ∈ e.val) := by
  intro hs
  let g : PetersenMinusGraph →g G := f.comp matchingOverlapIso.symm.toHom
  have hg' : Function.Injective g := hf.comp matchingOverlapIso.symm.injective
  exact critical21_no_supported_petersenMinus_subgraph hG15 hΔ hg g hg' hF
    (fun u => hs (matchingOverlapIso.symm u))

end
end Se20Part
