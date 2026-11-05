import Se20Insertion.GroupedInsertion
import Se20Insertion.ColourSetCounting

noncomputable section
open scoped Classical
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- Among 36 pairs on 19 colours, one avoids a specified pair. -/
theorem disjoint_pair_of_thirtySix (c a b : Colour) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (S : Finset (Finset Colour))
    (hS : ∀ Y ∈ S, Y.card = 2 ∧ c ∉ Y) (hn : 36 ≤ S.card) :
    ∃ Y ∈ S, a ∉ Y ∧ b ∉ Y := by
  let A : Finset Colour := Finset.univ.erase c
  let P := A.powersetCard 2
  let Q := (A \ {a,b}).powersetCard 2
  have ha : a ∈ A := by simp [A, hac]
  have hb : b ∈ A := by simp [A, hbc]
  have hpair : ({a,b} : Finset Colour) ⊆ A := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
  have hA : A.card = 19 := by simp [A]
  have hP : P.card = 171 := by simp [P, hA]; decide
  have hQ : Q.card = 136 := by
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hpair, hA]
    simp [hab]; decide
  have hQP : Q ⊆ P := Finset.powersetCard_mono (Finset.sdiff_subset)
  have hPQ : (P \ Q).card = 35 := by
    rw [Finset.card_sdiff_of_subset hQP, hP, hQ]
  by_contra hn'
  have hsub : S ⊆ P \ Q := by
    intro Y hY
    obtain ⟨hc, hcy⟩ := hS Y hY
    have hYA : Y ⊆ A := by
      intro z hz
      simp only [A, Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun h => hcy (h ▸ hz)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨hYA, hc⟩, ?_⟩
    intro hYQ
    have hs := (Finset.mem_powersetCard.mp hYQ).1
    exact hn' ⟨Y, hY, (fun h => (Finset.mem_sdiff.mp (hs h)).2 (by simp)),
      (fun h => (Finset.mem_sdiff.mp (hs h)).2 (by simp))⟩
  have := Finset.card_le_card hsub
  omega

/-- Corollary 11.19, counting unordered pairs and excluding the class colour. -/
theorem double_colour_insertion (φ : PartialColouring H F) (e g₁ g₂ : W)
    {c a b : Colour} (hg₂ : φ.colour g₂ = c)
    (hcover : ∀ x, φ.Neighbour e c x ↔ x = g₁ ∨ x = g₂)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : φ.Separable g₁ a b) (hn : 36 ≤ φ.separablePairCount g₂) :
    Nonempty (PartialColouring H (insert e F)) := by
  obtain ⟨Y, hY, haY, hbY⟩ := disjoint_pair_of_thirtySix c a b hab hac hbc
    ((colourGroups 2).filter (fun Y => φ.colour g₂ ∉ Y ∧ ¬ φ.AllTangled Y g₂))
    (by intro Y hY; exact ⟨mem_colourGroups.mp (Finset.mem_filter.mp hY).1,
      hg₂ ▸ (Finset.mem_filter.mp hY).2.1⟩) hn
  obtain ⟨d, hd, t, ht, hdt, hsep⟩ :=
    (φ.not_allTangled_iff_separable Y g₂).mp (Finset.mem_filter.mp hY).2.2
  have hcY : c ∉ Y := hg₂ ▸ (Finset.mem_filter.mp hY).2.1
  apply φ.groupedColourClassInsertion e c
    (fun i : Bool => if i then {g₂} else {g₁})
    (fun i => if i then d else a) (fun i => if i then t else b)
  · intro x; simpa [Bool.exists_bool, or_comm] using hcover x
  · intro i; cases i <;> simp [hab, hdt]
  · intro i; cases i <;> simp [hac, show d ≠ c from fun h => hcY (h ▸ hd)]
  · intro i; cases i <;> simp [hbc, show t ≠ c from fun h => hcY (h ▸ ht)]
  · intro i j hij
    have had : a ≠ d := fun h => haY (h.symm ▸ hd)
    have hat : a ≠ t := fun h => haY (h.symm ▸ ht)
    have hbd : b ≠ d := fun h => hbY (h.symm ▸ hd)
    have hbt : b ≠ t := fun h => hbY (h.symm ▸ ht)
    cases i <;> cases j <;> simp_all [ne_comm]
  · intro i; cases i <;> simpa [JointSeparable, Separable] using (by assumption)

def outerNeighbours (φ : PartialColouring H F) (e f : W) : Finset W :=
  F.filter (fun x => H.Adj f x ∧ ¬ H.Adj e x)

def missingInside (φ : PartialColouring H F) (e f : W) : Finset Colour :=
  Finset.univ.filter (fun d => d ≠ φ.colour f ∧
    ∀ x, φ.Neighbour e d x → ¬ H.Adj f x)

/-- Lemma 11.20. No disjointness of an informally named outer shell is assumed. -/
theorem outer_cover (φ : PartialColouring H F) {e : W}
    (hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b)
    {c d : Colour} (hdc : d ≠ c)
    (hm : ∀ f, φ.Neighbour e c f → d ∈ φ.missingInside e f) :
    ∃ f, φ.Neighbour e c f ∧ ∃ x ∈ φ.outerNeighbours e f, φ.colour x = d := by
  have hex : ∃ f, φ.Neighbour e c f ∧ ¬ φ.Free f d := by
    by_contra h
    apply hnt c d hdc.symm
    intro f hf
    by_contra hn
    exact h ⟨f, hf, hn⟩
  obtain ⟨f, hf, hn⟩ := hex
  obtain ⟨x, hx⟩ := not_not.mp hn
  refine ⟨f, hf, x, Finset.mem_filter.mpr ⟨hx.1, hx.2.1, ?_⟩, hx.2.2⟩
  intro hex
  exact (Finset.mem_filter.mp (hm f hf)).2.2 x ⟨hx.1, hex, hx.2.2⟩ hx.2.1

theorem single_outer_cover (φ : PartialColouring H F) {e f : W} {c : Colour}
    (hs : φ.Single e c f)
    (hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b) :
    φ.missingInside e f ⊆ (φ.outerNeighbours e f).image φ.colour := by
  intro d hd
  have hdc : d ≠ c := hs.1.2.2 ▸ (Finset.mem_filter.mp hd).2.1
  obtain ⟨g, hg, x, hx, hxd⟩ := φ.outer_cover hnt hdc (by
    intro g hg; have := hs.2 g hg; simpa [this] using hd)
  have hgf := hs.2 g hg
  exact Finset.mem_image.mpr ⟨x, hgf ▸ hx, hxd⟩

theorem single_outer_union_bound (φ : PartialColouring H F) (e : W) (S : Finset W)
    (hs : ∀ f ∈ S, φ.Single e (φ.colour f) f)
    (hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b) :
    (S.biUnion (φ.missingInside e)).card ≤ (S.biUnion (φ.outerNeighbours e)).card := by
  apply le_trans (Finset.card_le_card (show S.biUnion (φ.missingInside e) ⊆
      (S.biUnion (φ.outerNeighbours e)).image φ.colour from ?_)) Finset.card_image_le
  intro d hd
  obtain ⟨f, hf, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp (φ.single_outer_cover (hs f hf) hnt hd)
  exact Finset.mem_image.mpr ⟨x, Finset.mem_biUnion.mpr ⟨f, hf, hx⟩, hxd⟩

/-- Lemma 11.21, with the promised bound relative to the one-component swap. -/
theorem swap_then_single_insertion (φ : PartialColouring H F) {e fp fr : W}
    {p r η : Colour} (he : e ∉ F) (hr : φ.Single e r fr)
    (hpr : φ.Single fr p fp) (hηp : η ≠ p) (hηr : η ≠ r) (hpr' : p ≠ r)
    (havoid : ∀ x, φ.Neighbour fr η x → ¬ φ.SameComponent p η fp x) :
    let ψ := φ.swap p η {x | φ.SameComponent p η fp x} (φ.component_closed p η fp)
    ∃ θ : PartialColouring H (insert e F),
      (F.filter (fun x => θ.colour x ≠ ψ.colour x)).card ≤ 1 := by
  dsimp only
  let S := {x | φ.SameComponent p η fp x}
  let ψ := φ.swap p η S (φ.component_closed p η fp)
  have hfree : ψ.Free fr p := by
    rintro ⟨x, hxF, hfx, hxc⟩
    change φ.swapColour p η S x = p at hxc
    by_cases hxS : x ∈ S
    · have hcη : φ.colour x = η := by
        simpa [swapColour, hxS, Equiv.swap_apply_eq_iff] using hxc
      exact havoid x ⟨hxF, hfx, hcη⟩ hxS
    · have hcp : φ.colour x = p := by simpa [swapColour, hxS] using hxc
      have hxfp := hpr.2 x ⟨hxF, hfx, hcp⟩
      subst x
      exact hxS (φ.sameComponent_refl ⟨hpr.1.1, Or.inl hpr.1.2.2⟩)
  have hsame (x : W) : ψ.colour x = r ↔ φ.colour x = r :=
    φ.swapColour_eq_iff hpr'.symm hηr.symm x
  have hsr : ψ.Single e r fr := by
    refine ⟨⟨hr.1.1, hr.1.2.1, (hsame fr).mpr hr.1.2.2⟩, ?_⟩
    intro x hx
    exact hr.2 x ⟨hx.1, hx.2.1, (hsame x).mp hx.2.2⟩
  exact ψ.single_free_insertion he hsr hpr' hfree

end Se20Insertion.PartialColouring

