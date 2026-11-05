import Se20Insertion.ColourSetCore

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def outsideYNeighbours (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (v : W) : Finset W :=
  domainNeighbours H (insert h F) v \ φ.yNeighbours Y v

theorem yNeighbours_subset_domain (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (v : W) :
    φ.yNeighbours Y v ⊆ domainNeighbours H (insert h F) v := by
  intro x hx
  obtain ⟨hxF, hvx, _⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hxF, hvx⟩

theorem outsideYNeighbours_card (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (v : W) :
    (φ.outsideYNeighbours h Y v).card + (φ.yNeighbours Y v).card =
      (domainNeighbours H (insert h F) v).card := by
  exact Finset.card_sdiff_add_card_eq_card (φ.yNeighbours_subset_domain h Y v)

theorem threshold_eq_outside (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (v : W) :
    φ.colourSetThreshold h Y v =
      2 * (20 - (Y.card : ℤ)) - (φ.outsideYNeighbours h Y v).card := by
  have := φ.outsideYNeighbours_card h Y v
  unfold colourSetThreshold
  omega

theorem core_neighbours_subset_outside (φ : PartialColouring H F) (h : W)
    (Y : Finset Colour) (v : W) :
    domainNeighbours H (φ.colourSetCore h Y) v ⊆ φ.outsideYNeighbours h Y v := by
  intro x hx
  obtain ⟨hxC, hvx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxD, hxY, _⟩ := Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hxC)
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hxD, hvx⟩, ?_⟩
  intro hx
  obtain ⟨hxF, _, hc⟩ := Finset.mem_filter.mp hx
  exact hxY hxF hc

theorem core_degree_bound (φ : PartialColouring H F) (h : W) (Y : Finset Colour)
    {v : W} (hv : v ∈ φ.colourSetCore h Y) :
    2 * ((φ.yNeighbours Y v).card : ℤ) ≤
      2 * (domainNeighbours H (insert h F) v).card - 2 * (20 - (Y.card : ℤ)) := by
  have hlow := (φ.colourSetCore_isCore h Y).2 v hv
  have hupp := Finset.card_le_card (φ.core_neighbours_subset_outside h Y v)
  have hparts := φ.outsideYNeighbours_card h Y v
  unfold colourSetThreshold at hlow
  omega

theorem allTangled_sees (φ : PartialColouring H F) {Y : Finset Colour} {v : W}
    (hY : 2 ≤ Y.card) (ht : φ.AllTangled Y v) : ∀ a ∈ Y, ∃ x, φ.Neighbour v a x := by
  intro a ha
  have hex : ∃ b ∈ Y, b ≠ a := by
    by_contra hn
    push_neg at hn
    have hsub : Y ⊆ {a} := by intro b hb; simpa using hn b hb
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  obtain ⟨b, hb, hba⟩ := hex
  obtain ⟨x, y, hx, _, _⟩ := ht a ha b hb hba.symm
  exact ⟨x, hx⟩

theorem core_yDegree_lower (φ : PartialColouring H F) (h : W) (Y : Finset Colour)
    (hY : 2 ≤ Y.card) {v : W} (hv : v ∈ φ.colourSetCore h Y) :
    Y.card ≤ (φ.yNeighbours Y v).card := by
  have ht := (Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hv)).2.2
  have hsub : Y ⊆ (φ.yNeighbours Y v).image φ.colour := by
    intro a ha
    obtain ⟨x, hxF, hvx, hxa⟩ := φ.allTangled_sees hY ht a ha
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxF, hvx, hxa ▸ ha⟩, hxa⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem twoColourCoreInsertion (φ : PartialColouring H F) (h : W) (hh : h ∉ F)
    {a b : Colour} (hab : a ≠ b) (hc : h ∉ φ.colourSetCore h {a, b}) :
    Nonempty (PartialColouring H (insert h F)) := by
  apply φ.colourSetInsertion h hh {a, b} _ hc
  simp [hab]

theorem twoColour_threshold (φ : PartialColouring H F) (h v : W)
    {a b : Colour} (hab : a ≠ b) :
    φ.colourSetThreshold h {a, b} v = 36 + ((φ.yNeighbours {a, b} v).card : ℤ) -
      (domainNeighbours H (insert h F) v).card := by
  simp [colourSetThreshold, hab]

theorem not_mem_core_of_separable (φ : PartialColouring H F) (h : W) (Y : Finset Colour)
    {a b : Colour} (ha : a ∈ Y) (hb : b ∈ Y) (hab : a ≠ b) (hs : φ.Separable h a b) :
    h ∉ φ.colourSetCore h Y := by
  intro hc
  have ht := (Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hc)).2.2
  exact (φ.tangledAt_iff_not_separable h a b).mp (ht a ha b hb hab) hs

theorem outsideY_single_hole (φ : PartialColouring H F) {h f : W} {u : Colour}
    (hs : φ.Single h u f) :
    φ.outsideYNeighbours h (Finset.univ.erase u) h = {f} := by
  ext x
  simp only [outsideYNeighbours, domainNeighbours, yNeighbours, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_erase, Finset.mem_univ,
    and_true, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hx, hhx⟩, hn⟩
    have hxF := hx.resolve_left hhx.ne.symm
    have hxu : φ.colour x = u := by tauto
    exact hs.2 x ⟨hxF, hhx, hxu⟩
  · rintro rfl
    exact ⟨⟨Or.inr hs.1.1, hs.1.2.1⟩, by simp [hs.1.2.2]⟩

theorem outsideY_single_target (φ : PartialColouring H F) {h f : W} {u : Colour}
    (hh : h ∉ F) (hs : φ.Single h u f) :
    φ.outsideYNeighbours h (Finset.univ.erase u) f = {h} := by
  ext x
  simp only [outsideYNeighbours, domainNeighbours, yNeighbours, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_erase, Finset.mem_univ,
    and_true, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hx, hfx⟩, hn⟩
    rcases hx with rfl | hxF
    · rfl
    · have hxu : φ.colour x = u := by tauto
      exact False.elim (φ.proper hs.1.1 hxF hfx (hs.1.2.2.trans hxu.symm))
  · rintro rfl
    exact ⟨⟨Or.inl rfl, hs.1.2.1.symm⟩, by simp [hh]⟩

theorem nineteen_core_iff (φ : PartialColouring H F) {h f : W} {u : Colour}
    (hh : h ∉ F) (hs : φ.Single h u f)
    (ht : ∀ a b, a ≠ b → φ.TangledAt h a b) :
    h ∈ φ.colourSetCore h (Finset.univ.erase u) ↔
      φ.AllTangled (Finset.univ.erase u) f := by
  let Y := (Finset.univ : Finset Colour).erase u
  have hcY : Y.card = 19 := by simp [Y]
  have hth : φ.colourSetThreshold h Y h = 1 := by
    rw [φ.threshold_eq_outside, hcY, φ.outsideY_single_hole hs]
    norm_num
  have htf : φ.colourSetThreshold h Y f = 1 := by
    rw [φ.threshold_eq_outside, hcY, φ.outsideY_single_target hh hs]
    norm_num
  constructor
  · intro hc
    have hb := (φ.colourSetCore_isCore h Y).2 h hc
    rw [hth] at hb
    have hn : (domainNeighbours H (φ.colourSetCore h Y) h).Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨x, hx⟩ := hn
    have hxf : x = f := by
      have := φ.core_neighbours_subset_outside h Y h hx
      simpa only [Y, φ.outsideY_single_hole hs, Finset.mem_singleton] using this
    subst x
    exact (Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1
      (Finset.mem_filter.mp hx).1)).2.2
  · intro hf
    have hcf : φ.IsColourCore h Y {h, f} := by
      constructor
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_filter.mpr ⟨by simp, by simp [hh], fun a _ b _ hab => ht a b hab⟩
        · have hxf : x = f := Finset.mem_singleton.mp hx
          subst x
          exact Finset.mem_filter.mpr ⟨by simp [hs.1.1], by simp [Y, hs.1.2.2], hf⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxh | hx
        · subst x
          rw [hth]
          have hp : 0 < (domainNeighbours H {h, f} h).card :=
            Finset.card_pos.mpr ⟨f, Finset.mem_filter.mpr ⟨by simp, hs.1.2.1⟩⟩
          omega
        · have hxf : x = f := Finset.mem_singleton.mp hx
          subst x
          rw [htf]
          have hp : 0 < (domainNeighbours H {h, f} f).card :=
            Finset.card_pos.mpr ⟨h, Finset.mem_filter.mpr ⟨by simp, hs.1.2.1.symm⟩⟩
          omega
    exact φ.colourSetCore_greatest hcf (by simp)

theorem nineteen_not_core_iff_separable (φ : PartialColouring H F) {h f : W} {u : Colour}
    (hh : h ∉ F) (hs : φ.Single h u f)
    (ht : ∀ a b, a ≠ b → ¬ φ.Separable h a b) :
    h ∉ φ.colourSetCore h (Finset.univ.erase u) ↔
      ∃ a b, a ≠ b ∧ a ≠ u ∧ b ≠ u ∧ φ.Separable f a b := by
  rw [φ.nineteen_core_iff hh hs (fun a b hab =>
    (φ.tangledAt_iff_not_separable h a b).mpr (ht a b hab))]
  simp only [AllTangled, tangledAt_iff_not_separable, Finset.mem_erase,
    Finset.mem_univ, and_true]
  push_neg
  constructor
  · rintro ⟨a, hau, b, hbu, hab, hsep⟩
    exact ⟨a, b, hab, hau, hbu, hsep⟩
  · rintro ⟨a, b, hab, hau, hbu, hsep⟩
    exact ⟨a, hau, b, hbu, hab, hsep⟩

/-- The single-colour instance of 11.7, derived through 11.47. -/
theorem singleInsertion_via_colourSetCore (φ : PartialColouring H F) {h f : W} {u a b : Colour}
    (hh : h ∉ F) (hs : φ.Single h u f)
    (ht : ∀ c d, c ≠ d → ¬ φ.Separable h c d)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) (hsep : φ.Separable f a b) :
    Nonempty (PartialColouring H (insert h F)) := by
  apply φ.colourSetInsertion h hh (Finset.univ.erase u) (by simp)
  exact (φ.nineteen_not_core_iff_separable hh hs ht).mpr ⟨a, b, hab, hau, hbu, hsep⟩

/-- No stuckness assumption is needed for the resulting single insertion theorem. -/
theorem singleInsertion_from_colourSetCore (φ : PartialColouring H F) {h f : W} {u a b : Colour}
    (hh : h ∉ F) (hs : φ.Single h u f)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) (hsep : φ.Separable f a b) :
    Nonempty (PartialColouring H (insert h F)) := by
  by_cases ht : ∀ c d, c ≠ d → ¬ φ.Separable h c d
  · exact φ.singleInsertion_via_colourSetCore hh hs ht hab hau hbu hsep
  · push_neg at ht
    obtain ⟨c, d, hcd, hsep'⟩ := ht
    exact φ.twoColourCoreInsertion h hh hcd
      (φ.not_mem_core_of_separable h {c, d} (by simp) (by simp) hcd hsep')

end PartialColouring

/-- Pointed star states: the conjecture supplies a good group for each chosen hole. -/
def Conj1150 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), FourRegular G →
    ∀ v, Nonexceptional G v → ∀ U : Finset G.edgeSet,
      StarSet G v U → (∀ e ∈ U, ¬ OnTriangle G e) →
      ∀ φ : PartialColouring (L2 G) (Finset.univ \ U), ∀ h ∈ U,
        ∃ Y : Finset Colour, 2 ≤ Y.card ∧ Y.card ≤ 19 ∧ h ∉ φ.colourSetCore h Y

/-- The weaker, existential choice of a hole is all that the existing reduction needs. -/
def ColourSetStarInsertion : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), FourRegular G →
    ∀ v, Nonexceptional G v → ∀ U : Finset G.edgeSet,
      StarSet G v U → (∀ e ∈ U, ¬ OnTriangle G e) →
      ∀ φ : PartialColouring (L2 G) (Finset.univ \ U),
        ∃ h ∈ U, ∃ Y : Finset Colour, 2 ≤ Y.card ∧ h ∉ φ.colourSetCore h Y

theorem colourSetStarInsertion_of_conj1150 (hc : Conj1150) : ColourSetStarInsertion := by
  intro n G hreg v hv U hU htri φ
  obtain ⟨h, hh⟩ := hU.1
  obtain ⟨Y, hY, _, hcore⟩ := hc n G hreg v hv U hU htri φ h hh
  exact ⟨h, hh, Y, hY, hcore⟩

theorem starInsertion_of_colourSetStarInsertion (hc : ColourSetStarInsertion) : StarInsertion := by
  intro n G hreg v hv U hU htri φ
  obtain ⟨h, hh, Y, hY, hcore⟩ := hc n G hreg v hv U hU htri φ
  refine ⟨h, hh, ?_⟩
  convert φ.colourSetInsertion h (by simp [hh]) Y hY hcore using 1
  congr 1
  ext x
  simp

theorem starInsertion_of_conj1150 (hc : Conj1150) : StarInsertion :=
  starInsertion_of_colourSetStarInsertion (colourSetStarInsertion_of_conj1150 hc)

theorem strongColourable_of_conj1150 (hc : Conj1150) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : MaxDegreeFour G) : StrongColourable G 20 :=
  strongColourable_of_starInsertion (starInsertion_of_conj1150 hc) G hΔ

end Se20Insertion
