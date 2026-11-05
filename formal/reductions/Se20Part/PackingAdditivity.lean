import Se20Part.PackingTightness

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
variable {W : Type*} (H : SimpleGraph W)

theorem exists_maximum_independent (F : Finset W) :
    ∃ M ⊆ F, Independent H M ∧ M.card = packingRank H F := by
  obtain ⟨M,hM,hm⟩ := Finset.exists_mem_eq_sup F.powerset
    (by exact ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩)
    (fun M => if Independent H M then M.card else 0)
  by_cases hi : Independent H M
  · exact ⟨M,Finset.mem_powerset.mp hM,hi,by simpa only [packingRank,if_pos hi] using hm.symm⟩
  · refine ⟨∅,Finset.empty_subset _,by simp [Independent],?_⟩
    simpa only [packingRank,if_neg hi,Finset.card_empty] using hm.symm

theorem packingRank_union [DecidableEq W] (F E : Finset W) (hd : Disjoint F E)
    (hs : ∀ x ∈ F, ∀ y ∈ E, ¬ H.Adj x y) :
    packingRank H (F ∪ E) = packingRank H F + packingRank H E := by
  apply Nat.le_antisymm
  · obtain ⟨M,hM,hi,hm⟩ := exists_maximum_independent H (F ∪ E)
    have hF := independent_le_packingRank H F (M ∩ F) Finset.inter_subset_right
      (fun x hx y hy => hi x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1)
    have hE := independent_le_packingRank H E (M ∩ E) Finset.inter_subset_right
      (fun x hx y hy => hi x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1)
    have he : M = M ∩ F ∪ M ∩ E := by rw [← Finset.inter_union_distrib_left,Finset.inter_eq_left.mpr hM]
    have hc := Finset.card_union_of_disjoint (s := M ∩ F) (t := M ∩ E)
      (hd.mono Finset.inter_subset_right Finset.inter_subset_right)
    rw [← he] at hc
    omega
  · obtain ⟨M,hM,hi,hm⟩ := exists_maximum_independent H F
    obtain ⟨N,hN,hj,hn⟩ := exists_maximum_independent H E
    have hu : Independent H (M ∪ N) := by
      intro x hx y hy
      rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
      · exact hi x hx y hy
      · exact hs x (hM hx) y (hN hy)
      · exact fun h => hs y (hM hy) x (hN hx) h.symm
      · exact hj x hx y hy
    have hh := independent_le_packingRank H (F ∪ E) (M ∪ N) (Finset.union_subset_union hM hN) hu
    rw [Finset.card_union_of_disjoint (hd.mono hM hN),hm,hn] at hh
    exact hh

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem tauG_union (F E : Finset G.edgeSet) (hd : Disjoint F E)
    (hs : ∀ x ∈ F, ∀ y ∈ E, ¬ (L2 G).Adj x y) :
    tauG G (F ∪ E) = tauG G F + tauG G E := by
  have hb (B : Finset G.edgeSet) (hB : B ∈ (tightBlocks G).blocks) :
      Disjoint F B ∨ Disjoint E B := by
    by_cases hf : F ∩ B = ∅
    · exact Or.inl (Finset.disjoint_iff_inter_eq_empty.mpr hf)
    · right
      apply Finset.disjoint_left.mpr
      intro y hyE hyB
      obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hf
      obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hB
      exact hs x (Finset.mem_inter.mp hx).1 y hyE
        (tight_component_clique G C hC (Finset.mem_inter.mp hx).2 hyB
          (fun he => Finset.disjoint_left.mp hd (Finset.mem_inter.mp hx).1 (he ▸ hyE)))
  unfold tauG Packing.tau
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  letI : DecidableEq G.edgeSet := fun a b => Classical.propDecidable (a=b)
  have hh := hb B hB
  rcases hh with hh|hh
  · have hz := Finset.disjoint_iff_inter_eq_empty.mp hh
    rw [hz]
    simp only [Finset.card_empty,Nat.zero_sub,zero_add]
    congr 2
    ext x
    simp only [Finset.mem_inter,Finset.mem_union]
    have hn : x ∈ F → x ∈ B → False := fun hx hb => Finset.disjoint_left.mp hh hx hb
    tauto
  · have hz := Finset.disjoint_iff_inter_eq_empty.mp hh
    rw [hz]
    simp only [Finset.card_empty,Nat.zero_sub,add_zero]
    congr 2
    ext x
    simp only [Finset.mem_inter,Finset.mem_union]
    have hn : x ∈ E → x ∈ B → False := fun hx hb => Finset.disjoint_left.mp hh hx hb
    tauto

/-- Equality cases are closed under disjoint, mutually nonconflicting union.
In particular this applies to arbitrary unions in different G-components. -/
theorem packing_equality_union (F E : Finset G.edgeSet) (hd : Disjoint F E)
    (hs : ∀ x ∈ F, ∀ y ∈ E, ¬ (L2 G).Adj x y)
    (hF : F.card = 18 * packingRank (L2 G) F + tauG G F)
    (hE : E.card = 18 * packingRank (L2 G) E + tauG G E) :
    (F ∪ E).card = 18 * packingRank (L2 G) (F ∪ E) + tauG G (F ∪ E) := by
  rw [Finset.card_union_of_disjoint hd,packingRank_union (L2 G) F E hd hs,tauG_union G F E hd hs]
  omega

end Se20Part
