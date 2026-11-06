import fourth_pass.CanonicalRoot

namespace Se20Fractional.FourthPass.Canonical
open Finset DReduction ThirdPass
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable def relabelSelected (f : H ≃g G) (Q : Finset G.edgeSet) : Finset H.edgeSet :=
  Q.map f.mapEdgeSet.symm.toEmbedding

theorem mem_relabelSelected (f : H ≃g G) (Q : Finset G.edgeSet) (e : H.edgeSet) :
    e ∈ relabelSelected f Q ↔ f.mapEdgeSet e ∈ Q := by
  simp [relabelSelected]

theorem relabel_data (f : H ≃g G) (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q) (hLow : LocallyLow G Q) :
    (∀ v, H.degree v ≤ 4) ∧ (relabelSelected f Q).card = Q.card ∧
      Clique (L2 H) (relabelSelected f Q) ∧ LocallyLow H (relabelSelected f Q) := by
  refine ⟨?_,by simp [relabelSelected],?_,?_⟩
  · intro v
    exact (embedding_degree_le f.toEmbedding v).trans (hΔ (f v))
  · intro e he g hg hne
    apply (l2_embedding_iff f.toEmbedding e g).mp
    exact hQ _ ((mem_relabelSelected f Q e).mp he) _ ((mem_relabelSelected f Q g).mp hg)
      (fun h => hne (f.mapEdgeSet.injective h))
  · intro a b hab he
    have hmem := (mem_relabelSelected f Q _).mp he
    have hl := hLow (f a) (f b) (f.map_adj_iff.mpr hab) hmem
    exact (embedding_local_le f.toEmbedding a b).trans hl

noncomputable def Listing.graph {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : SimpleGraph (Fin 14) := G.comap L.equiv
noncomputable def Listing.iso {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : L.graph ≃g G := SimpleGraph.Iso.comap L.equiv G
noncomputable def Listing.selected {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) : Finset L.graph.edgeSet := relabelSelected L.iso Q

theorem Listing.graph_adj {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (a b : Fin 14) : L.graph.Adj a b ↔ G.Adj (L.equiv a) (L.equiv b) :=
  L.iso.map_adj_iff.symm

theorem Listing.graph_root {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (v : Fin 14) :
    L.graph.Adj 0 v ↔ 0 < v.val ∧ v.val ≤ G.degree r := by
  rw [L.graph_adj,L.equiv_zero,L.root_adj_iff]

theorem Listing.selected_A {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (i : Nat) (hi : i < L.A.length) :
    let v : Fin 14 := ⟨i+1,by
      have := L.length; simp only [List.length_cons,List.length_append] at this; omega⟩
    ∀ h : L.graph.Adj 0 v, (⟨s(0,v),h⟩ : L.graph.edgeSet) ∈ L.selected ↔
      i < (labels Q r).card := by
  dsimp only
  intro h
  refine (mem_relabelSelected L.iso Q _).trans ?_
  have ha : G.Adj r L.A[i] := (L.A_mem _).mp (List.getElem_mem hi)
  have heq : L.iso.mapEdgeSet ⟨s(0,⟨i+1,by
      have := L.length; simp only [List.length_cons,List.length_append] at this; omega⟩),h⟩ =
      (⟨s(r,L.A[i]),ha⟩ : G.edgeSet) := by
    apply Subtype.ext
    change s(L.equiv 0,L.equiv ⟨i+1,_⟩) = s(r,L.A[i])
    rw [L.equiv_zero,L.equiv_A _ hi]
  rw [heq]
  have hmem : (⟨s(r,L.A[i]),ha⟩ : G.edgeSet) ∈ Q ↔ L.A[i] ∈ labels Q r := by
    constructor
    · intro hq
      exact (mem_labels Q r _).mpr ⟨ha,hq⟩
    · intro hl
      obtain ⟨_,hq⟩ := (mem_labels Q r _).mp hl
      exact hq
  exact hmem.trans (L.A_label_iff i hi)

theorem Listing.selected_root {G : SimpleGraph (Fin 14)} {Q : Finset G.edgeSet} {r : Fin 14}
    (L : Listing G Q r) (v : Fin 14) (h : L.graph.Adj 0 v) :
    (⟨s(0,v),h⟩ : L.graph.edgeSet) ∈ L.selected ↔ v.val ≤ (labels Q r).card := by
  have hv := (L.graph_root v).mp h
  have hi : v.val-1 < L.A.length := by rw [L.A_length]; omega
  have hidx : (v.val-1)+1 < 14 := by have := v.isLt; omega
  have heq : (⟨(v.val-1)+1,hidx⟩ : Fin 14) = v := by
    apply Fin.ext
    change (v.val-1)+1 = v.val
    omega
  have hh : L.graph.Adj 0 (⟨(v.val-1)+1,hidx⟩ : Fin 14) := heq.symm ▸ h
  have ht := L.selected_A (v.val-1) hi hh
  have ht' : (⟨s(0,v),h⟩ : L.graph.edgeSet) ∈ L.selected ↔ v.val-1 < (labels Q r).card := by
    simpa only [heq] using ht
  exact ht'.trans (by omega)

#print axioms relabel_data
#print axioms Listing.selected_A
end Se20Fractional.FourthPass.Canonical
