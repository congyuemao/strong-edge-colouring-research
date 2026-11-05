import Se20Part.ColouringTheorems
import Se20Part.Domination

noncomputable section
open scoped Classical
namespace Se20Part

theorem GirthAtLeast.induce {V : Type*} {G : SimpleGraph V} {g : ℕ}
    (hg : GirthAtLeast G g) (S : Set V) : GirthAtLeast (G.induce S) g := by
  intro v p hp
  let f : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  have hc : (p.map f.toHom).IsCycle := hp.map f.injective
  exact (hg v.val (p.map f.toHom) hc).trans_eq (SimpleGraph.Walk.length_map f.toHom p)

/-- Theorem B, steps 4–6, with precisely the still-needed geometric seed supplied.
This is a reduction theorem, not a proof of Theorem B's seed or decomposition. -/
theorem twenty_of_dominating_seed {V : Type} [Fintype V] (kost : Kostochka)
    {G : SimpleGraph V} (hd : MaxDegreeFour G) (hg : GirthAtLeast G 69)
    (M : Fin 4 → Set G.edgeSet) (D : Set G.edgeSet)
    (hm : ∀ i, IsMatching (M i)) (hD : IsInducedMatching D)
    (hcover : ∀ e, e ∈ D ∨ ∃ i, e ∈ M i)
    (J : Set (M 3)) (hJ : Independent (ConflictGraph G (M 3)) J)
    (havoid : ∀ j ∈ J, ∀ r ∈ D, ¬ (L2 G).Adj j.val r)
    (hdom : ∀ h : M 3, (∃ r ∈ D, (L2 G).Adj h.val r) →
      Nat.card ((ConflictGraph G (M 3)).neighborSet h) = 6 →
      ∃ j ∈ J, (ConflictGraph G (M 3)).Adj h j) : StrongColourable G 20 := by
  let H := ConflictGraph G (M 3)
  let N : Set (M 3) := {h | ∃ r ∈ D, (L2 G).Adj h.val r}
  have hjn : J ⊆ Nᶜ := by
    intro j hj hn
    obtain ⟨r,hr,hjr⟩ := hn
    exact havoid j hj r hr hjr
  obtain ⟨I,hJI,hIN,hI,hdeg⟩ := domination_reduces_degree H N J
    (d := 5) (matching_maxDegree_six hd (hg.mono (by omega)) (hm 3)) hjn hJ hdom
  let K : Set G.edgeSet := {e | e ∈ M 3 ∧ ¬ ∃ h ∈ I, h.val = e}
  let R : Set G.edgeSet := D ∪ Subtype.val '' I
  have hR : IsInducedMatching R := by
    intro e he f hf hef
    rcases he with he | ⟨i,hi,rfl⟩ <;> rcases hf with hf | ⟨j,hj,rfl⟩
    · exact hD he hf hef
    · exact hIN hj ⟨e,he,hef.symm⟩
    · exact hIN hi ⟨f,hf,hef⟩
    · exact hI hi hj hef
  have hKgirth : GirthAtLeast (H.induce Iᶜ) 35 :=
    (matching_girth (hm 3) hg).induce Iᶜ
  have hKaux := kost.to_K5 _ _ hdeg hKgirth
  let kmap : ConflictGraph G K →g H.induce Iᶜ := {
    toFun := fun e => ⟨⟨e.val,e.property.1⟩, fun hi => e.property.2 ⟨_,hi,rfl⟩⟩
    map_rel' := by intro a b hab; exact hab }
  have hK : (ConflictGraph G K).Colorable 4 :=
    SimpleGraph.Colorable.of_hom kmap hKaux
  have hfive (i : Fin 4) : (ConflictGraph G (M i)).Colorable 5 :=
    kost.to_K6 _ _ (matching_maxDegree_six hd (hg.mono (by omega)) (hm i))
      ((matching_girth (hm i) hg).mono (by norm_num))
  let family : Fin 5 → Set G.edgeSet := ![M 0,M 1,M 2,K,R]
  have hfamily : ∀ e, ∃ i, e ∈ family i := by
    intro e
    rcases hcover e with he | ⟨i,hi⟩
    · exact ⟨4,Or.inl he⟩
    · fin_cases i
      · exact ⟨0,hi⟩
      · exact ⟨1,hi⟩
      · exact ⟨2,hi⟩
      · by_cases heI : ∃ h ∈ I, h.val = e
        · exact ⟨4,Or.inr heI⟩
        · exact ⟨3,hi,heI⟩
  have hc := assembly G family ![5,5,5,4,1] hfamily (by
    intro i
    fin_cases i
    · exact hfive 0
    · exact hfive 1
    · exact hfive 2
    · exact hK
    · exact inducedMatching_colorable_one hR)
  simpa [Fin.sum_univ_succ] using hc

end Se20Part
