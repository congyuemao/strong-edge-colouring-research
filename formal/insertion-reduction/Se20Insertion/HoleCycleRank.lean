import Se20Insertion.CriticalLists
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.ComponentInsertion
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)

def edges (S : Finset W) : ℕ := Nat.card (H.induce (S : Set W)).edgeSet

theorem twice_edges (S : Finset W) :
    2 * edges H S = ∑ x ∈ S, (S.filter (H.Adj x)).card := by
  have hh := (H.induce (S : Set W)).sum_degrees_eq_twice_card_edges
  simp_rw [degree_induce_finset H S] at hh
  have hedge : (H.induce (S : Set W)).edgeFinset.card = edges H S := by
    simp only [edges,SimpleGraph.edgeFinset,Set.toFinset_card,Nat.card_eq_fintype_card]
  rw [hedge] at hh
  exact hh.symm.trans (Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun x => (S.filter (H.Adj x)).card)).symm

theorem edges_insert (S : Finset W) (f : W) (hf : f ∉ S) :
    edges H (insert f S) = edges H S + (S.filter (H.Adj f)).card := by
  have hi := twice_edges H (insert f S)
  have hs := twice_edges H S
  have root : ((insert f S).filter (H.Adj f)).card = (S.filter (H.Adj f)).card := by
    congr 1; ext x; simp only [Finset.mem_filter,Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hx,hfx⟩
      · exact (hfx.ne rfl).elim
      · exact ⟨hx,hfx⟩
    · exact fun h => ⟨Or.inr h.1,h.2⟩
  have deg (x : W) : ((insert f S).filter (H.Adj x)).card =
      (S.filter (H.Adj x)).card + if H.Adj x f then 1 else 0 := by
    rw [Finset.filter_insert]
    by_cases hx : H.Adj x f
    · simp [hx,Finset.card_insert_of_notMem (show f ∉ S.filter (H.Adj x) by simp [hf])]
    · simp [hx]
  rw [Finset.sum_insert hf,root] at hi
  simp_rw [deg] at hi
  rw [Finset.sum_add_distrib] at hi
  have hp : (∑ x ∈ S, if H.Adj x f then 1 else 0) = (S.filter (H.Adj f)).card := by
    simp only [SimpleGraph.adj_comm,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hp] at hi
  omega

/-- The usual E - V + C, with actual induced edges and connected components. -/
def cycleRank (S : Finset W) : ℤ := (edges H S : ℤ) - S.card + count H S

theorem cycleRank_insert (S : Finset W) (f : W) (hf : f ∉ S) :
    cycleRank H (insert f S) - cycleRank H S =
      ((S.filter (H.Adj f)).card : ℤ) - touchingCount H S f := by
  have hc := count_insert H S f hf
  have hc' : (count H (insert f S) : ℤ) + touchingCount H S f = count H S + 1 := by exact_mod_cast hc
  unfold cycleRank
  rw [edges_insert H S f hf,Finset.card_insert_of_notMem hf]
  push_cast
  omega

end Se20Insertion.ComponentInsertion
namespace Se20Insertion.PartialColouring
variable {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

def totalCycleRank (φ : PartialColouring H F) : ℤ :=
  ∑ a : Colour, ∑ b : Colour, if a < b then ComponentInsertion.cycleRank H (φ.pairVertices a b) else 0

theorem holeMove_cycleRank (φ : PartialColouring H F) {h f : W} {p : Colour}
    (hh : h ∉ F) (hs : φ.Single h p f) :
    (φ.holeMove hs).totalCycleRank - φ.totalCycleRank =
      ∑ x ∈ (Finset.univ.erase p),
        (((φ.colouredNeighbours h).filter (fun y => φ.colour y = x)).card -
          (ComponentInsertion.touchingCount H ((φ.pairVertices p x).erase f) h : ℤ) -
          (((φ.colouredNeighbours f).filter (fun y => φ.colour y = x)).card -
            (ComponentInsertion.touchingCount H ((φ.pairVertices p x).erase f) f : ℤ))) := by
  let ψ := φ.holeMove hs
  let d := fun a b => ComponentInsertion.cycleRank H (ψ.pairVertices a b) -
    ComponentInsertion.cycleRank H (φ.pairVertices a b)
  let t := fun x => if x = p then 0 else d p x
  have symm (a b : Colour) : d a b = d b a := by
    have eqv {F' : Finset W} (θ : PartialColouring H F') : θ.pairVertices a b = θ.pairVertices b a := by
      ext x; simp [pairVertices,or_comm]
    dsimp [d]; rw [eqv ψ,eqv φ]
  have unchanged (a b : Colour) (ha : a ≠ p) (hb : b ≠ p) : ψ.pairVertices a b = φ.pairVertices a b := by
    ext y
    by_cases hyh : y = h
    · subst y; simp [ψ,pairVertices,holeMove_colour,hh,ha.symm,hb.symm]
    by_cases hyf : y = f
    · subst y; simp [ψ,pairVertices,holeMove_colour,hyh,hs.1.2.2,ha.symm,hb.symm]
    simp [ψ,pairVertices,holeMove_colour,hyh,hyf]
  have expand (a b : Colour) (hab : a ≠ b) : d a b = if a = p then t b else if b = p then t a else 0 := by
    by_cases ha : a = p <;> by_cases hb : b = p
    · exact (hab (ha.trans hb.symm)).elim
    · subst a; simp [t,hb]
    · subst b; simp [t,ha,symm]
    · simp [ha,hb,d,unchanged a b ha hb]
  have summation : ψ.totalCycleRank - φ.totalCycleRank = ∑ x ∈ Finset.univ.erase p, d p x := by
    unfold totalCycleRank
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have heq : (∑ a : Colour, ∑ b : Colour,
        ((if a < b then ComponentInsertion.cycleRank H (ψ.pairVertices a b) else 0) -
        (if a < b then ComponentInsertion.cycleRank H (φ.pairVertices a b) else 0))) =
        ∑ a : Colour, ∑ b : Colour, if a < b then (if a = p then t b else if b = p then t a else 0) else 0 := by
      apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
      by_cases hab : a < b
      · simp only [hab,ite_true]; exact expand a b (ne_of_lt hab)
      · simp [hab]
    rw [heq,sum_pair_star p t (by simp [t])]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p)]
    have tp : t p = 0 := by simp [t]
    rw [tp,add_zero]
    apply Finset.sum_congr rfl; intro x hx
    simp [t,(Finset.mem_erase.mp hx).1]
  rw [summation]
  apply Finset.sum_congr rfl
  intro x hx
  have hxp : x ≠ p := (Finset.mem_erase.mp hx).1
  let S := (φ.pairVertices p x).erase f
  have hf : f ∉ S := Finset.notMem_erase _ _
  have hhin : h ∉ S := fun h => hh (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).1
  have old : φ.pairVertices p x = insert f S := (Finset.insert_erase (by simp [pairVertices,hs.1.1,hs.1.2.2])).symm
  have new : ψ.pairVertices p x = insert h S := by
    ext y; by_cases hy : y = h <;> simp [ψ,pairVertices,holeMove_colour,hy,S,hh,and_assoc]
  have neighbours (v : W) (hv : v = h ∨ v = f) :
      S.filter (H.Adj v) = (φ.colouredNeighbours v).filter (fun y => φ.colour y = x) := by
    ext y
    have noP (hyF : y ∈ F) (hvy : H.Adj v y) (hyf : y ≠ f) : φ.colour y ≠ p := by
      rcases hv with rfl | rfl
      · exact fun h => hyf (hs.2 y ⟨hyF,hvy,h⟩)
      · exact fun h => φ.proper hs.1.1 hyF hvy (hs.1.2.2.trans h.symm)
    simp only [S,pairVertices,colouredNeighbours,Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨hyf,hyF,hyp | hyx⟩,hvy⟩
      · exact (noP hyF hvy hyf hyp).elim
      · exact ⟨⟨hyF,hvy⟩,hyx⟩
    · rintro ⟨⟨hyF,hvy⟩,hyx⟩
      exact ⟨⟨(fun h => hxp (hyx.symm.trans (h ▸ hs.1.2.2))),hyF,Or.inr hyx⟩,hvy⟩
  have hi := ComponentInsertion.cycleRank_insert H S h hhin
  have hd := ComponentInsertion.cycleRank_insert H S f hf
  rw [neighbours h (Or.inl rfl)] at hi
  rw [neighbours f (Or.inr rfl)] at hd
  dsimp only [d]
  rw [old,new]
  simp only [Finset.erase_insert hf]
  omega

end Se20Insertion.PartialColouring
