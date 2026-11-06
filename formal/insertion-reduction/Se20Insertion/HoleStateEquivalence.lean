import Se20Insertion.ColourSetCore

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

theorem holeMove_same_other_classes (φ : PartialColouring H F)
    {e f : W} {p : Colour} (he : e ∉ F) (hs : φ.Single e p f) :
    φ.SameYClasses (φ.holeMove hs) (Finset.univ.erase p) := by
  intro a ha x
  have hpa : p ≠ a := (Finset.mem_erase.mp ha).1.symm
  by_cases hxe : x = e
  · subst x; simp [he, holeMove_colour, hpa]
  · by_cases hxf : x = f
    · subst x; simp [holeMove_colour, hxe, hs.1.2.2, hpa]
    · simp [holeMove_colour, hxe, hxf]

theorem holeMove_separable_iff (φ : PartialColouring H F)
    {e f v : W} {p a b : Colour} (he : e ∉ F) (hs : φ.Single e p f)
    (ha : a ≠ p) (hb : b ≠ p) :
    (φ.holeMove hs).Separable v a b ↔ φ.Separable v a b := by
  have hc := φ.holeMove_same_other_classes he hs
  have ha' : a ∈ Finset.univ.erase p := by simp [ha]
  have hb' : b ∈ Finset.univ.erase p := by simp [hb]
  simp only [Separable, ← hc.neighbour ha', ← hc.neighbour hb',
    ← hc.sameComponent ha' hb']

theorem separable_comm (φ : PartialColouring H F) (v : W) (a b : Colour) :
    φ.Separable v a b ↔ φ.Separable v b a := by
  have hc (x y : W) : φ.SameComponent a b x y ↔ φ.SameComponent b a x y := by
    have he : φ.Bicoloured a b = φ.Bicoloured b a := by
      ext z; simp only [Bicoloured, Set.mem_setOf_eq, or_comm]
    constructor
    · rintro ⟨hx,hy,hr⟩
      let m : φ.KempeGraph a b →g φ.KempeGraph b a :=
        { toFun := fun z => ⟨z.val, he ▸ z.prop⟩, map_rel' := fun h => h }
      exact ⟨he ▸ hx,he ▸ hy,hr.map m⟩
    · rintro ⟨hx,hy,hr⟩
      let m : φ.KempeGraph b a →g φ.KempeGraph a b :=
        { toFun := fun z => ⟨z.val, he.symm ▸ z.prop⟩, map_rel' := fun h => h }
      exact ⟨he.symm ▸ hx,he.symm ▸ hy,hr.map m⟩
  constructor <;> intro h x y hx hy hxy
  · exact h y x hy hx ((hc x y).mpr hxy).symm
  · exact h y x hy hx ((hc x y).mp hxy).symm

/-- Exact local equivalence underlying both state-graph forms of 11.9. -/
theorem holeMove_not_stuck_iff (φ : PartialColouring H F)
    {e f : W} {p : Colour} (he : e ∉ F) (hs : φ.Single e p f)
    (hst : φ.Stuck e) :
    ¬ (φ.holeMove hs).Stuck f ↔
      ∃ a b, a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ φ.Separable f a b := by
  constructor
  · intro hn
    have hex : ∃ a b, a ≠ b ∧ (φ.holeMove hs).Separable f a b := by
      by_contra! h
      exact hn ⟨φ.holeMove_blocked he hs hst, h⟩
    obtain ⟨a,b,hab,hsab⟩ := hex
    have ha : a ≠ p := by
      rintro rfl
      exact φ.holeMove_inseparable_moved_colour he hs hst hab hsab
    have hb : b ≠ p := by
      rintro rfl
      exact φ.holeMove_inseparable_moved_colour he hs hst hab.symm
        (((φ.holeMove hs).separable_comm f a b).mp hsab)
    exact ⟨a,b,hab,ha,hb,(φ.holeMove_separable_iff he hs ha hb).mp hsab⟩
  · rintro ⟨a,b,hab,ha,hb,hsab⟩ hn
    exact hn.2 a b hab ((φ.holeMove_separable_iff he hs ha hb).mpr hsab)

/-- The universal form is an equivalence too; neither side is asserted. -/
theorem all_holeMoves_not_stuck_iff (φ : PartialColouring H F)
    {e : W} (he : e ∉ F) (hst : φ.Stuck e) :
    (∀ p f (hs : φ.Single e p f), ¬ (φ.holeMove hs).Stuck f) ↔
      ∀ p f, φ.Single e p f →
        ∃ a b, a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ φ.Separable f a b := by
  exact forall_congr' (fun p => forall_congr' (fun f =>
    forall_congr' (fun hs => φ.holeMove_not_stuck_iff he hs hst)))

end PartialColouring

/-- Neighbours are actual legal hole moves; no choice of colours is hidden. -/
def Conj119HoleNeighbour : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), MaxDegreeFour G →
    ∀ (F : Finset G.edgeSet) (φ : PartialColouring (L2 G) F) (e : G.edgeSet),
      e ∉ F → φ.Stuck e →
        ∃ p f, ∃ hs : φ.Single e p f, ¬ (φ.holeMove hs).Stuck f

theorem conj119_iff_hole_neighbour : Conj119 ↔ Conj119HoleNeighbour := by
  constructor
  · intro h n G hd F φ e he hst
    obtain ⟨p,f,hs,hsep⟩ := h n G hd F φ e he hst
    exact ⟨p,f,hs,(φ.holeMove_not_stuck_iff he hs hst).mpr hsep⟩
  · intro h n G hd F φ e he hst
    obtain ⟨p,f,hs,hn⟩ := h n G hd F φ e he hst
    exact ⟨p,f,hs,(φ.holeMove_not_stuck_iff he hs hst).mp hn⟩

end Se20Insertion
