import Se20Insertion.GirthBounds
import Se20Insertion.ColourSetCore
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace GirthGeometry
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def nearNeighbours (v : G.edgeSet) : Finset G.edgeSet :=
  (conflicts G v).filter (fun w => ∃ a, a ∈ v.val ∧ a ∈ w.val)

theorem nearNeighbours_card (hΔ : MaxDegreeFour G) (v : G.edgeSet) :
    (nearNeighbours G v).card ≤ 6 := by
  obtain ⟨a,b,hv⟩ : ∃ a b, v.val = s(a,b) := Sym2.ind (fun a b => ⟨a,b,rfl⟩) v.val
  have hs : nearNeighbours G v ⊆ (incident G a).erase v ∪ (incident G b).erase v := by
    intro w hw
    obtain ⟨hw, x, hx, hxw⟩ := Finset.mem_filter.mp hw
    have hne := (mem_conflicts G v w).mp hw |>.ne.symm
    rcases (show x = a ∨ x = b by simpa [hv, Sym2.mem_iff] using hx) with rfl | rfl
    · exact Finset.mem_union_left _ (by simp [hne, hxw])
    · exact Finset.mem_union_right _ (by simp [hne, hxw])
  have h1 := card_incident_erase_le_three G hΔ v (a := a) (by simp [hv])
  have h2 := card_incident_erase_le_three G hΔ v (a := b) (by simp [hv])
  have h3 := Finset.card_union_le ((incident G a).erase v) ((incident G b).erase v)
  have h4 := Finset.card_le_card hs
  omega

def neighbourhoodGraph (v : G.edgeSet) := (L2 G).induce (↑(conflicts G v) : Set G.edgeSet)

theorem neighbourhood_degree (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    (v : G.edgeSet) (w : (↑(conflicts G v) : Set G.edgeSet)) :
    (neighbourhoodGraph G v).degree w ≤
      if w.val ∈ nearNeighbours G v then 14 else 5 := by
  let A := (conflicts G v).filter (fun z => (L2 G).Adj w.val z)
  have hcard : (neighbourhoodGraph G v).degree w = A.card := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Fintype.card_coe A]
    apply Fintype.card_congr
      { toFun := fun z => ⟨z.val.val, Finset.mem_filter.mpr ⟨z.val.prop, z.prop⟩⟩
        invFun := fun z => ⟨⟨z.val, (Finset.mem_filter.mp z.prop).1⟩,
          (Finset.mem_filter.mp z.prop).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hw : (L2 G).Adj v w.val := (mem_conflicts G v w.val).mp w.prop
  have hn : w.val ∉ A := by simp [A]
  have hc := Finset.card_insert_of_notMem hn
  have hA : ∀ z ∈ insert w.val A, (L2 G).Adj v z ∧ (w.val = z ∨ (L2 G).Adj w.val z) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨hw, Or.inl rfl⟩
    · obtain ⟨hz, h⟩ := Finset.mem_filter.mp hz
      exact ⟨(mem_conflicts G v z).mp hz, Or.inr h⟩
  rw [hcard]
  split_ifs with hnear
  · obtain ⟨a, hav, haw⟩ := (Finset.mem_filter.mp hnear).2
    obtain ⟨b,hv⟩ := Sym2.mem_iff_exists.mp hav
    obtain ⟨c,hw'⟩ := Sym2.mem_iff_exists.mp haw
    have := common_near_card G hΔ hg hv hw' hw.ne (insert w.val A) hA
    omega
  · have hdis : ¬ ∃ a, a ∈ v.val ∧ a ∈ w.val.val := by
      intro h
      exact hnear (Finset.mem_filter.mpr ⟨w.prop, h⟩)
    have := common_far_card G hΔ hg hw hdis (insert w.val A) hA
    omega

theorem neighbourhood_edges_le_87 (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    (v : G.edgeSet) : Nat.card (neighbourhoodGraph G v).edgeSet ≤ 87 := by
  have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (↑(conflicts G v) : Set G.edgeSet))) =>
    neighbourhood_degree G hΔ hg v w)
  have he := (neighbourhoodGraph G v).sum_degrees_eq_twice_card_edges
  have hn := card_conflicts_le_twentyFour G hΔ v
  have ht := nearNeighbours_card G hΔ v
  have hsum : (∑ w : (↑(conflicts G v) : Set G.edgeSet),
      if w.val ∈ nearNeighbours G v then 14 else 5) =
      5 * (conflicts G v).card + 9 * (nearNeighbours G v).card := by
    change (∑ w : ↥(conflicts G v), if w.val ∈ nearNeighbours G v then 14 else 5) = _
    rw [Finset.sum_coe_sort (conflicts G v) (fun w => if w ∈ nearNeighbours G v then 14 else 5)]
    have hpoint : ∀ w : G.edgeSet, (if w ∈ nearNeighbours G v then 14 else 5) =
        5 + if w ∈ nearNeighbours G v then 9 else 0 := by intro w; split_ifs <;> rfl
    simp_rw [hpoint, Finset.sum_add_distrib]
    have hinter : conflicts G v ∩ nearNeighbours G v = nearNeighbours G v :=
      Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    simp [hinter, mul_comm]
  rw [hsum] at hs
  rw [he] at hs
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card] at hs
  omega

end GirthGeometry

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def DirectAt (φ : PartialColouring H F) (v : W) (a b : Colour) : Prop :=
  ∃ x y, φ.Neighbour v a x ∧ φ.Neighbour v b y ∧ H.Adj x y

theorem directAt_tangled (φ : PartialColouring H F) {v : W} {a b : Colour}
    (h : φ.DirectAt v a b) : φ.TangledAt v a b := by
  obtain ⟨x,y,hx,hy,hxy⟩ := h
  exact ⟨x,y,hx,hy,φ.sameComponent_of_adj ⟨hx.1,Or.inl hx.2.2⟩
    ⟨hy.1,Or.inr hy.2.2⟩ hxy⟩

/-- Unordered colour pairs witnessed by a conflict between coloured neighbours. -/
def directPairs (φ : PartialColouring H F) (v : W) : Finset (Sym2 Colour) :=
  Finset.univ.filter (fun c => ∃ a b, c = s(a,b) ∧ φ.DirectAt v a b)

theorem directPairs_le_neighbourhood_edges {V : Type*} [Fintype V]
    {G : SimpleGraph V} {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (v : G.edgeSet) : (φ.directPairs v).card ≤
      Nat.card (GirthGeometry.neighbourhoodGraph G v).edgeSet := by
  let N := GirthGeometry.neighbourhoodGraph G v
  let colour : (↑(conflicts G v) : Set G.edgeSet) → Colour := fun x => φ.colour x.val
  have hs : φ.directPairs v ⊆ N.edgeFinset.image (Sym2.map colour) := by
    intro c hc
    obtain ⟨a,b,rfl,x,y,hx,hy,hxy⟩ := (Finset.mem_filter.mp hc).2
    let x' : (↑(conflicts G v) : Set G.edgeSet) := ⟨x, (mem_conflicts G v x).mpr hx.2.1⟩
    let y' : (↑(conflicts G v) : Set G.edgeSet) := ⟨y, (mem_conflicts G v y).mpr hy.2.1⟩
    refine Finset.mem_image.mpr ⟨s(x',y'), ?_, ?_⟩
    · exact N.mem_edgeFinset.mpr hxy
    · change s(φ.colour x,φ.colour y) = s(a,b)
      rw [hx.2.2,hy.2.2]
  calc
    _ ≤ (N.edgeFinset.image (Sym2.map colour)).card := Finset.card_le_card hs
    _ ≤ N.edgeFinset.card := Finset.card_image_le
    _ = _ := by rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]

theorem directPairs_le_87 {V : Type*} [Fintype V]
    {G : SimpleGraph V} {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) (v : G.edgeSet) :
    (φ.directPairs v).card ≤ 87 :=
  (φ.directPairs_le_neighbourhood_edges v).trans
    (GirthGeometry.neighbourhood_edges_le_87 G hΔ hg v)

end PartialColouring
end Se20Insertion
