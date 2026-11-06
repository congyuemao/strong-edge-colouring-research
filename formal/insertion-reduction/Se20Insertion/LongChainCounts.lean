import Se20Insertion.FanLemma
import Se20Insertion.ColourSetCounting

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- Unordered pairs of distinct colours tangled at a vertex. -/
def tangledColourPairs (φ : PartialColouring H F) (v : W) : Finset (Finset Colour) :=
  (colourGroups 2).filter (fun Y => φ.AllTangled Y v)

/-- The same unordered direct pairs as `directPairs`, represented as colour sets. -/
def directColourPairs (φ : PartialColouring H F) (v : W) : Finset (Finset Colour) :=
  (φ.directPairs v).image Sym2.toFinset

/-- L(v): tangled unordered colour pairs having no direct witness. -/
def longColourPairs (φ : PartialColouring H F) (v : W) : Finset (Finset Colour) :=
  φ.tangledColourPairs v \ φ.directColourPairs v

def longPairCount (φ : PartialColouring H F) (v : W) : ℕ :=
  (φ.longColourPairs v).card

theorem tangled_pairs_le_direct_add_long (φ : PartialColouring H F) (v : W) :
    (φ.tangledColourPairs v).card ≤ (φ.directPairs v).card + φ.longPairCount v := by
  have hp := Finset.card_sdiff_add_card_inter (φ.tangledColourPairs v) (φ.directColourPairs v)
  have hi := Finset.card_le_card (Finset.inter_subset_right :
    φ.tangledColourPairs v ∩ φ.directColourPairs v ⊆ φ.directColourPairs v)
  have hd : (φ.directColourPairs v).card ≤ (φ.directPairs v).card := Finset.card_image_le
  unfold longPairCount longColourPairs
  omega

theorem tangleCliqueCount_le_tangled_pairs (φ : PartialColouring H F) (v : W) :
    φ.tangleCliqueCount 2 v ≤ (φ.tangledColourPairs v).card := by
  apply Finset.card_le_card
  intro Y hY
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hY).1, (Finset.mem_filter.mp hY).2.2⟩

theorem all_tangled_pairs_card (φ : PartialColouring H F) {v : W}
    (ht : ∀ a b, a ≠ b → φ.TangledAt v a b) :
    (φ.tangledColourPairs v).card = 190 := by
  have he : φ.tangledColourPairs v = colourGroups 2 := by
    apply Finset.filter_eq_self.mpr
    intro Y _ a _ b _ hab
    exact ht a b hab
  rw [he, card_colourGroups]
  decide

theorem long_pair_witness (φ : PartialColouring H F) {v : W} {Y : Finset Colour}
    (hY : Y ∈ φ.longColourPairs v) :
    ∃ a b, a ≠ b ∧ Y = {a,b} ∧ φ.TangledAt v a b ∧ ¬ φ.DirectAt v a b := by
  obtain ⟨ht, hd⟩ := Finset.mem_sdiff.mp hY
  obtain ⟨hg, ht⟩ := Finset.mem_filter.mp ht
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp (mem_colourGroups.mp hg)
  refine ⟨a,b,hab,rfl,ht a (by simp) b (by simp) hab,?_⟩
  intro hdir
  apply hd
  exact Finset.mem_image.mpr ⟨s(a,b), Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,a,b,rfl,hdir⟩, Sym2.toFinset_mk_eq⟩

theorem nineteen_single_tangleCliqueCount (φ : PartialColouring H F) {h f : W}
    (hh : h ∉ F) (hf : φ.AllGroupsFail h 19) {p : Colour} (hs : φ.Single h p f) :
    φ.tangleCliqueCount 2 f = 171 := by
  have ht := (φ.nineteen_core_iff hh hs
    (φ.allGroupsFail_tangled (by decide) (by decide) hf)).mp
    (hf (Finset.univ.erase p) (mem_colourGroups.mpr (by simp)))
  have he : (colourGroups 2).filter (fun Y => φ.colour f ∉ Y ∧ φ.AllTangled Y f) =
      (colourGroups 2).filter (fun Y => φ.colour f ∉ Y) := by
    ext Y
    simp only [Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hY,hp⟩
      refine ⟨hY,hp,fun a ha b hb hab => ht a ?_ b ?_ hab⟩
      · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro he
        exact hp (hs.1.2.2.symm ▸ he ▸ ha)
      · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro he
        exact hp (hs.1.2.2.symm ▸ he ▸ hb)
  unfold tangleCliqueCount
  rw [he, card_groups_avoiding]
  decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {E : Finset G.edgeSet}

theorem tangled_pairs_le_87_add_long (φ : PartialColouring (L2 G) E)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) (v : G.edgeSet) :
    (φ.tangledColourPairs v).card ≤ 87 + φ.longPairCount v :=
  (φ.tangled_pairs_le_direct_add_long v).trans
    (Nat.add_le_add_right (φ.directPairs_le_87 hΔ hg v) _)

/-- Section 7.7: all two-colour groups failing forces L(h) ≥ 103. -/
theorem allPairsFail_long_at_hole (φ : PartialColouring (L2 G) E)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) {h : G.edgeSet}
    (hf : φ.AllGroupsFail h 2) : 103 ≤ φ.longPairCount h := by
  have hc := φ.all_tangled_pairs_card (φ.allGroupsFail_tangled (by decide) (by decide) hf)
  have hb := φ.tangled_pairs_le_87_add_long hΔ hg h
  omega

/-- Division-free mean bound: sum L(f) ≥ 27 |N(h)|. N(h) is the actual
coloured neighbourhood, and the degree-24 premise is retained explicitly. -/
theorem allPairsFail_long_mean (φ : PartialColouring (L2 G) E)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) {h : G.edgeSet}
    (hf : φ.AllGroupsFail h 2) (hd : (φ.colouredNeighbours h).card = 24) :
    27 * (φ.colouredNeighbours h).card ≤
      ∑ f ∈ φ.colouredNeighbours h, φ.longPairCount f := by
  have hs := φ.allGroupsFail_clique_sum h (by decide) (by decide) hf
    (by simpa only [φ.hole_domainNeighbours] using hd)
  have hb := Finset.sum_le_sum (s := φ.colouredNeighbours h)
    (fun f _ => (φ.tangleCliqueCount_le_tangled_pairs f).trans
      (φ.tangled_pairs_le_87_add_long hΔ hg f))
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hd] at hb ⊢
  simp only [φ.hole_domainNeighbours] at hs hb ⊢
  norm_num [Nat.choose] at hs
  omega

theorem allPairsFail_long_mean_rat (φ : PartialColouring (L2 G) E)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) {h : G.edgeSet}
    (hf : φ.AllGroupsFail h 2) (hd : (φ.colouredNeighbours h).card = 24) :
    (27 : ℚ) ≤ (∑ f ∈ φ.colouredNeighbours h, (φ.longPairCount f : ℚ)) /
      (φ.colouredNeighbours h).card := by
  have hb := φ.allPairsFail_long_mean hΔ hg hf hd
  rw [hd] at hb ⊢
  have hb' : (27 : ℚ) * 24 ≤
      ∑ f ∈ φ.colouredNeighbours h, (φ.longPairCount f : ℚ) := by
    exact_mod_cast hb
  linarith

/-- Section 7.7: each single representative under failure at k=19 has L(f) ≥ 84. -/
theorem allNineteenFail_long_at_single (φ : PartialColouring (L2 G) E)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) {h f : G.edgeSet}
    (hh : h ∉ E) (hf : φ.AllGroupsFail h 19) {p : Colour} (hs : φ.Single h p f) :
    84 ≤ φ.longPairCount f := by
  have hc := φ.nineteen_single_tangleCliqueCount hh hf hs
  have hb := (φ.tangleCliqueCount_le_tangled_pairs f).trans
    (φ.tangled_pairs_le_87_add_long hΔ hg f)
  omega

/-- Includes the distinct single-colour count, rather than assuming sixteen representatives. -/
theorem allNineteenFail_sixteen_long_singles (φ : PartialColouring (L2 G) E)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) {h : G.edgeSet}
    (hh : h ∉ E) (hf : φ.AllGroupsFail h 19)
    (hd : (φ.colouredNeighbours h).card = 24) :
    16 ≤ (φ.singleColours h).card ∧
      ∀ p f, φ.Single h p f → 84 ≤ φ.longPairCount f :=
  ⟨φ.allGroupsFail_at_least_sixteen_single (by decide) (by decide) hf
      (by simpa only [φ.hole_domainNeighbours] using hd),
    fun _ _ hs => φ.allNineteenFail_long_at_single hΔ hg hh hf hs⟩

end Se20Insertion.PartialColouring
