import Se20Insertion.GirthBounds
import Se20Insertion.ReachabilityCounting

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring

/-- Absence of a double-hole configuration yields the required local partner
bound. The vertex `g` used in the contradiction is an arbitrary member of
`S`, and is generally coloured. -/
theorem partner_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (R S : Finset G.edgeSet) (hSR : S ⊆ R) (hSF : S ⊆ F)
    (hc : φ.NoDoubleHole R) (f : G.edgeSet) (hf : f ∈ S) :
    (φ.singleTargets S f).card + 3 * (φ.partners S f).card ≤ 24 := by
  apply GirthGeometry.dominator_bound G hΔ hg f (φ.singleTargets S f) (φ.partners S f)
  · intro z hz
    exact (Finset.mem_filter.mp hz).2.1
  · intro w hw
    obtain ⟨hwS, hfw, hwf⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwS, hfw.1.2.1, hwf⟩
  · intro w hw z hz
    obtain ⟨hwS, hfw, hwf⟩ := Finset.mem_filter.mp hw
    obtain ⟨hzS, hfz, hzf⟩ := Finset.mem_filter.mp hz
    by_cases hwz : w = z
    · exact .inl hwz
    by_cases hadj : (L2 G).Adj w z
    · exact .inr hadj
    exact False.elim (hc z (hSR hzS) f w
      ⟨hSF hf, hSF hwS, hfz.symm, hfw.1.2.1, Ne.symm hwz,
        fun h => hadj h.symm, hzf, hwf, hfw⟩)

end PartialColouring

/-- A stronger form of Theorem 11.44: maximum degree at most four suffices.
The hypotheses (a), (b), and (c) are the original ones. Girth uses Mathlib's
`egirth`, including infinity for acyclic graphs. -/
theorem theorem1144_maxDegree {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) (h : G.edgeSet)
    (φ : PartialColouring (L2 G) (Finset.univ \ {h})) :
    ¬ ∃ R : Finset G.edgeSet, h ∈ R ∧ φ.SaturatedOn R ∧
      φ.SingleClosed R ∧ φ.NoDoubleHole R := by
  rintro ⟨R, hhR, ha, hb, hc⟩
  let S := R.erase h
  have hhout : h ∉ (Finset.univ \ {h} : Finset G.edgeSet) := by simp
  have hSR : S ⊆ R := Finset.erase_subset _ _
  have hSF : S ⊆ (Finset.univ \ {h} : Finset G.edgeSet) := by
    intro x hx
    have hxh := (Finset.mem_erase.mp hx).1
    simpa using hxh
  have hblocked : ∀ a, ∃ z, φ.Neighbour h a z := fun a => ha h hhR a (.inl hhout)
  have hsingles := at_least_sixteen_add_uncoloured_single G hΔ φ h hblocked
  have hpos : 0 < (φ.singleColours h).card := by omega
  obtain ⟨a, haSingle⟩ := Finset.card_pos.mp hpos
  obtain ⟨z, hz⟩ := (φ.mem_singleColours h a).mp haSingle
  have hzR : z ∈ R := hb h hhR z (by simpa [hz.1.2.2] using hz)
  have hzh : z ≠ h := by intro heq; exact hhout (heq ▸ hz.1.1)
  have hS : S.Nonempty := ⟨z, Finset.mem_erase.mpr ⟨hzh, hzR⟩⟩
  apply φ.counting_contradiction S hSF hS
  · intro x hx a hax
    exact ha x (hSR hx) a hax
  · intro x hx y hsingle
    have hyh : y ≠ h := by intro heq; exact hhout (heq ▸ hsingle.1.1)
    exact Finset.mem_erase.mpr ⟨hyh, hb x (hSR hx) y hsingle⟩
  · intro x _hx
    have hsub : φ.colouredNeighbours x ⊆ conflicts G x := by
      intro z hz
      exact (mem_conflicts G x z).mpr (Finset.mem_filter.mp hz).2
    exact (Finset.card_le_card hsub).trans (card_conflicts_le_twentyFour G hΔ x)
  · intro f hf
    exact φ.partner_bound G hΔ hg R S hSR hSF hc f hf

/-- Theorem 11.44, with precisely the stated finite 4-regular graph and the
original three conditions. No conjecture is a hypothesis. -/
theorem theorem1144 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hreg : FourRegular G) (hg : 7 ≤ G.egirth) (h : G.edgeSet)
    (φ : PartialColouring (L2 G) (Finset.univ \ {h})) :
    ¬ ∃ R : Finset G.edgeSet, h ∈ R ∧ φ.SaturatedOn R ∧
      φ.SingleClosed R ∧ φ.NoDoubleHole R :=
  theorem1144_maxDegree G (fun v => (hreg v).le) hg h φ

/-- The ordinary natural-valued Mathlib girth also implies our hypothesis. -/
theorem theorem1144_girth {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hreg : FourRegular G) (hg : 7 ≤ G.girth) (h : G.edgeSet)
    (φ : PartialColouring (L2 G) (Finset.univ \ {h})) :
    ¬ ∃ R : Finset G.edgeSet, h ∈ R ∧ φ.SaturatedOn R ∧
      φ.SingleClosed R ∧ φ.NoDoubleHole R := by
  apply theorem1144 G hreg _ h φ
  have hh : (7 : ℕ∞) ≤ (G.girth : ℕ∞) := by exact_mod_cast hg
  exact hh.trans G.natCast_girth_le_egirth

end Se20Insertion
