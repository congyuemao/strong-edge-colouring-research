import Se20Insertion.P2Identity

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem regular_girth_conflicts_card (hreg : FourRegular G) (hg : 7 ≤ G.egirth)
    (e : G.edgeSet) : (conflicts G e).card = 24 := by
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.2)
  have hd : Disjoint ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    have huw := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2
    have hvw := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw').2
    exact GirthGeometry.no_triangle hg huv hvw huw.symm
  have hr : (rim G u v).card = 6 := by
    have hu := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)
    have hv := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv.symm)
    rw [SimpleGraph.card_neighborFinset_eq_degree,hreg] at hu hv
    rw [rim,Finset.card_union_of_disjoint hd]
    omega
  have noedge (w : V) (hw : w ∈ rim G u v) (z : V) (hz : z ∈ rim G u v) : ¬ G.Adj w z := by
    rcases Finset.mem_union.mp hw with hw | hw <;> rcases Finset.mem_union.mp hz with hz | hz
    · exact fun h => GirthGeometry.no_triangle hg
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2) h
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2).symm
    · intro h
      have hs := GirthGeometry.square_backtrack hg
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2) h
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2).symm huv.symm
      exact hs.elim (fun h => (Finset.mem_erase.mp hz).1 h.symm) (Finset.mem_erase.mp hw).1
    · intro h
      have hs := GirthGeometry.square_backtrack hg
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2) h
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2).symm huv
      exact hs.elim (fun h => (Finset.mem_erase.mp hz).1 h.symm) (Finset.mem_erase.mp hw).1
    · exact fun h => GirthGeometry.no_triangle hg
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2) h
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2).symm
  have hdis : (↑(rim G u v) : Set V).PairwiseDisjoint (incident G) := by
    intro w hw z hz hwz
    apply Finset.disjoint_left.mpr
    intro f hfw hfz
    have hf : f.val = s(w,z) := (Sym2.mem_and_mem_iff hwz).mp
      ⟨(mem_incident G w f).mp hfw,(mem_incident G z f).mp hfz⟩
    exact noedge w hw z hz (G.mem_edgeSet.mp (hf ▸ f.2))
  rw [conflicts_eq_rim G e he,Finset.card_biUnion hdis]
  simp only [card_incident]
  calc
    _ = ∑ _x ∈ rim G u v, 4 := Finset.sum_congr rfl (fun x _ => hreg x)
    _ = 24 := by simp [hr]

namespace PartialColouring

theorem unexposed_partner_bound (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (R S : Finset G.edgeSet) (hSR : S ⊆ R) (hSF : S ⊆ F) {f : G.edgeSet} (hf : f ∈ S) :
    (φ.singleTargets S f).card + 3 * (φ.unexposedPartners R S f).card ≤ 24 := by
  apply GirthGeometry.dominator_bound G hΔ hg f (φ.singleTargets S f) (φ.unexposedPartners R S f)
  · intro z hz; exact (Finset.mem_filter.mp hz).2.1
  · intro w hw
    obtain ⟨hwp,_⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwS,hfw,hwf⟩ := Finset.mem_filter.mp hwp
    exact Finset.mem_filter.mpr ⟨hwS,hfw.1.2.1,hwf⟩
  · intro w hw z hz
    obtain ⟨hwp,hnexp⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwS,hfw,hwf⟩ := Finset.mem_filter.mp hwp
    obtain ⟨hzS,hfz,hzf⟩ := Finset.mem_filter.mp hz
    by_cases hwz : w = z
    · exact Or.inl hwz
    by_cases hadj : (L2 G).Adj w z
    · exact Or.inr hadj
    exact (hnexp ⟨z,hSR hzS,⟨hSF hf,hSF hwS,hfz.symm,hfw.1.2.1,Ne.symm hwz,
      fun h => hadj h.symm,hzf,hwf,hfw⟩⟩).elim

/-- Proposition P2, with all quantities defined by actual finite sets and
the nonnegative geometric slack. The domain is exactly all edges except h. -/
theorem propositionP2 (hreg : FourRegular G) (hg : 7 ≤ G.egirth) (h : G.edgeSet)
    (φ : PartialColouring (L2 G) (Finset.univ \ {h}))
    (R : Finset G.edgeSet) (hhR : h ∈ R)
    (hblocked : ∀ a, ∃ f, φ.Neighbour h a f) (hclosed : φ.SingleClosed R) :
    let S := R.erase h
    let ε := fun x => if (L2 G).Adj x h then 1 else 0
    let v := φ.p2Terms R S ε
    0 ≤ v.L ∧ 14*v.D + 3*v.B = 2*v.n + 10*v.M + 3*v.T + 7*v.E + 6*v.Z + v.L := by
  let S := R.erase h
  let ε := fun x => if (L2 G).Adj x h then 1 else 0
  have hSF : S ⊆ Finset.univ \ {h} := by intro x hx; simpa using (Finset.mem_erase.mp hx).1
  have hSR : S ⊆ R := Finset.erase_subset _ _
  have hCS : φ.SingleClosed S := by
    intro x hx y hy
    exact Finset.mem_erase.mpr ⟨by simpa using hy.1.1,hclosed x (hSR hx) y hy⟩
  have hdeg (x : G.edgeSet) (_ : x ∈ S) : (φ.colouredNeighbours x).card + ε x = 24 := by
    have heq : φ.colouredNeighbours x = (conflicts G x).erase h := by
      ext y; simp [colouredNeighbours,and_comm]
    rw [heq]
    have hc := regular_girth_conflicts_card G hreg hg x
    by_cases hxh : (L2 G).Adj x h
    · have hp := Finset.card_erase_add_one ((mem_conflicts G x h).mpr hxh)
      simp only [ε,hxh,ite_true]; omega
    · simp [ε,hxh,Finset.erase_eq_of_notMem ((mem_conflicts G x h).not.mpr hxh),hc]
  refine ⟨?_,φ.p2_identity R S ε hSF hCS hdeg⟩
  change 0 ≤ ∑ x ∈ S, (24 - ((φ.singleTargets S x).card : ℤ) - 3 * (φ.unexposedPartners R S x).card)
  apply Finset.sum_nonneg
  intro x hx
  have hb := φ.unexposed_partner_bound G (fun v => (hreg v).le) hg R S hSR hSF hx
  omega

end PartialColouring
end Se20Insertion
