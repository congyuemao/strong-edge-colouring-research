import Se20Insertion.ShellChains

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion

/-- Maximum degree four on a possibly infinite graph, with no global Fintype. -/
def LocalMaxDegreeFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v (N : Finset V), (∀ w ∈ N, G.Adj v w) → N.card ≤ 4

/-- Exactly four neighbours at every vertex, also usable on infinite trees. -/
def InfiniteFourRegular {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v, ∃ N : Finset V, N.card = 4 ∧ ∀ w, G.Adj v w ↔ w ∈ N

theorem InfiniteFourRegular.localMaxDegreeFour {V : Type*} {G : SimpleGraph V}
    (hG : InfiniteFourRegular G) : LocalMaxDegreeFour G := by
  intro v N hN
  obtain ⟨M,hM,hm⟩ := hG v
  have hs : N ⊆ M := fun w hw => (hm w).mp (hN w hw)
  exact (Finset.card_le_card hs).trans hM.le

theorem localMaxDegreeFour_induce {V : Type*} {G : SimpleGraph V}
    (hG : LocalMaxDegreeFour G) (S : Finset V) : MaxDegreeFour (G.induce (S : Set V)) := by
  intro v
  let N := (G.induce (S : Set V)).neighborFinset v
  have hh := hG v.val (N.image Subtype.val) (by
    intro w hw; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    exact ((G.induce (S : Set V)).mem_neighborFinset v x).mp hx)
  rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hh

namespace PartialColouring
variable {V : Type*} {G : SimpleGraph V} {F : Finset G.edgeSet}

/-- 11.1 on arbitrary, including infinite, forests with a finite colouring domain.
The finite support is induced on endpoints, so all ambient conflict witnesses remain. -/
theorem infinite_forest_separable (φ : PartialColouring (L2 G) F)
    (hG : G.IsAcyclic) (hΔ : LocalMaxDegreeFour G) {e : G.edgeSet} (he : e ∉ F) :
    ∃ a b, a ≠ b ∧ φ.Separable e a b := by
  classical
  let S : Finset V := (insert e F).biUnion (fun f => f.val.toFinset)
  let G' := G.induce (S : Set V)
  let emb := inducedEmbedding G (S : Set V)
  have covered (f : G.edgeSet) (hf : f ∈ insert e F) :
      ∃ f' : G'.edgeSet, emb.mapEdgeSet f' = f := by
    have endpoints (v : V) (hv : v ∈ f.val) : v ∈ S :=
      Finset.mem_biUnion.mpr ⟨f,hf,Sym2.mem_toFinset.mpr hv⟩
    obtain ⟨u,v,hfv⟩ : ∃ u v, f.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) f.val
    let u' : S := ⟨u,endpoints u (hfv ▸ Sym2.mem_mk_left u v)⟩
    let v' : S := ⟨v,endpoints v (hfv ▸ Sym2.mem_mk_right u v)⟩
    have huv : G'.Adj u' v' := G.mem_edgeSet.mp (hfv ▸ f.2)
    exact ⟨⟨s(u',v'),huv⟩,Subtype.ext hfv.symm⟩
  obtain ⟨e',he'⟩ := covered e (Finset.mem_insert_self _ _)
  let F' : Finset G'.edgeSet := Finset.univ.filter (fun f => emb.mapEdgeSet f ∈ F)
  let ψ : PartialColouring (L2 G') F' :=
    ⟨fun f => φ.colour (emb.mapEdgeSet f), by
      intro x y hx hy hxy
      exact φ.proper (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
        ((L2Map emb.toHom emb.injective).map_adj hxy)⟩
  have heout : e' ∉ F' := fun h => he (he' ▸ (Finset.mem_filter.mp h).2)
  obtain ⟨a,b,hab,hsep⟩ := ψ.finite_forest_separable (hG.induce (S : Set V))
    (localMaxDegreeFour_induce hΔ S) heout
  refine ⟨a,b,hab,?_⟩
  by_contra hn
  obtain ⟨f,g,hf,hg,hfg⟩ := φ.forest_tangled_direct hG he hab
    ((φ.tangledAt_iff_not_separable e a b).mpr hn)
  obtain ⟨f',hf'⟩ := covered f (Finset.mem_insert_of_mem hf.1)
  obtain ⟨g',hg'⟩ := covered g (Finset.mem_insert_of_mem hg.1)
  have nf : ψ.Neighbour e' a f' := by
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf' ▸ hf.1⟩,?_,by simpa [ψ,hf'] using hf.2.2⟩
    apply (L2_embedding_adj_iff emb e' f').mp
    simpa [he',hf'] using hf.2.1
  have ng : ψ.Neighbour e' b g' := by
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg' ▸ hg.1⟩,?_,by simpa [ψ,hg'] using hg.2.2⟩
    apply (L2_embedding_adj_iff emb e' g').mp
    simpa [he',hg'] using hg.2.1
  have fg : (L2 G').Adj f' g' := by
    apply (L2_embedding_adj_iff emb f' g').mp
    simpa [hf',hg'] using hfg
  exact hsep f' g' nf ng (ψ.sameComponent_of_adj ⟨nf.1,Or.inl nf.2.2⟩ ⟨ng.1,Or.inr ng.2.2⟩ fg)

theorem infinite_four_regular_tree_separable (φ : PartialColouring (L2 G) F)
    (hG : G.IsTree) (hreg : InfiniteFourRegular G) {e : G.edgeSet} (he : e ∉ F) :
    ∃ a b, a ≠ b ∧ φ.Separable e a b :=
  φ.infinite_forest_separable hG.2 hreg.localMaxDegreeFour he

end PartialColouring
end Se20Insertion
