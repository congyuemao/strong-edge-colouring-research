import Se20Insertion.HoleMoves
import Se20Insertion.StarReduction

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- Existential tangling, including the actual two-colour component. -/
def TangledAt (φ : PartialColouring H F) (v : W) (a b : Colour) : Prop :=
  ∃ x y, φ.Neighbour v a x ∧ φ.Neighbour v b y ∧ φ.SameComponent a b x y

theorem tangledAt_iff_not_separable (φ : PartialColouring H F) (v : W) (a b : Colour) :
    φ.TangledAt v a b ↔ ¬ φ.Separable v a b := by
  simp [TangledAt, Separable]

def AllTangled (φ : PartialColouring H F) (Y : Finset Colour) (v : W) : Prop :=
  ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → φ.TangledAt v a b

/-- All degrees in this file are restricted to the specified finite domain. -/
def domainNeighbours (H : SimpleGraph W) (D : Finset W) (v : W) : Finset W :=
  D.filter (H.Adj v)

def yNeighbours (φ : PartialColouring H F) (Y : Finset Colour) (v : W) : Finset W :=
  F.filter (fun x => H.Adj v x ∧ φ.colour x ∈ Y)

def colourSetS (φ : PartialColouring H F) (h : W) (Y : Finset Colour) : Finset W :=
  (insert h F).filter (fun v => (v ∈ F → φ.colour v ∉ Y) ∧ φ.AllTangled Y v)

/-- Integer threshold: no truncated natural subtraction. -/
def colourSetThreshold (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (v : W) : ℤ :=
  2 * (20 - (Y.card : ℤ)) + (φ.yNeighbours Y v).card -
    (domainNeighbours H (insert h F) v).card

def IsColourCore (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (C : Finset W) : Prop :=
  C ⊆ φ.colourSetS h Y ∧ ∀ v ∈ C,
    φ.colourSetThreshold h Y v ≤ (domainNeighbours H C v).card

/-- The largest subset of S satisfying the local threshold inequalities. -/
def colourSetCore (φ : PartialColouring H F) (h : W) (Y : Finset Colour) : Finset W :=
  (φ.colourSetS h Y).filter (fun v => ∃ C, φ.IsColourCore h Y C ∧ v ∈ C)

theorem colourSetCore_greatest (φ : PartialColouring H F) {h : W} {Y : Finset Colour}
    {C : Finset W} (hc : φ.IsColourCore h Y C) : C ⊆ φ.colourSetCore h Y := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨hc.1 hv, C, hc, hv⟩

theorem colourSetCore_isCore (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    φ.IsColourCore h Y (φ.colourSetCore h Y) := by
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro v hv
  obtain ⟨_, C, hc, hvc⟩ := Finset.mem_filter.mp hv
  exact (hc.2 v hvc).trans (by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (φ.colourSetCore_greatest hc)))

theorem not_mem_colourSetCore_iff (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    h ∉ φ.colourSetCore h Y ↔ ∀ C ⊆ φ.colourSetS h Y, h ∈ C →
      ∃ v ∈ C, (domainNeighbours H C v).card < φ.colourSetThreshold h Y v := by
  constructor
  · intro hn C hC hh
    by_contra hn'
    push_neg at hn'
    exact hn (φ.colourSetCore_greatest ⟨hC, hn'⟩ hh)
  · intro hh hm
    obtain ⟨v, hv, hlt⟩ := hh _ (φ.colourSetCore_isCore h Y).1 hm
    exact (not_lt_of_ge ((φ.colourSetCore_isCore h Y).2 v hv)) hlt

/-- Equality of colour classes, not merely equality of their cardinalities. -/
def SameYClasses {F' : Finset W} (φ : PartialColouring H F) (ψ : PartialColouring H F')
    (Y : Finset Colour) : Prop :=
  ∀ a ∈ Y, ∀ x, (x ∈ F ∧ φ.colour x = a) ↔ (x ∈ F' ∧ ψ.colour x = a)

theorem SameYClasses.symm {F' : Finset W} {φ : PartialColouring H F}
    {ψ : PartialColouring H F'} {Y : Finset Colour} (hs : φ.SameYClasses ψ Y) :
    ψ.SameYClasses φ Y := fun a ha x => (hs a ha x).symm

theorem SameYClasses.trans {F' F'' : Finset W} {φ : PartialColouring H F}
    {ψ : PartialColouring H F'} {χ : PartialColouring H F''} {Y : Finset Colour}
    (hs : φ.SameYClasses ψ Y) (ht : ψ.SameYClasses χ Y) : φ.SameYClasses χ Y :=
  fun a ha x => (hs a ha x).trans (ht a ha x)

theorem SameYClasses.neighbour {F' : Finset W} {φ : PartialColouring H F}
    {ψ : PartialColouring H F'} {Y : Finset Colour} (hs : φ.SameYClasses ψ Y)
    {a : Colour} (ha : a ∈ Y) (v x : W) : φ.Neighbour v a x ↔ ψ.Neighbour v a x := by
  have := hs a ha x
  simp only [Neighbour]
  tauto

theorem SameYClasses.bicoloured {F' : Finset W} {φ : PartialColouring H F}
    {ψ : PartialColouring H F'} {Y : Finset Colour} (hs : φ.SameYClasses ψ Y)
    {a b : Colour} (ha : a ∈ Y) (hb : b ∈ Y) : φ.Bicoloured a b = ψ.Bicoloured a b := by
  ext x
  have := hs a ha x
  have := hs b hb x
  simp only [Bicoloured, Set.mem_setOf_eq]
  tauto

theorem SameYClasses.sameComponent {F' : Finset W} {φ : PartialColouring H F}
    {ψ : PartialColouring H F'} {Y : Finset Colour} (hs : φ.SameYClasses ψ Y)
    {a b : Colour} (ha : a ∈ Y) (hb : b ∈ Y) (x y : W) :
    φ.SameComponent a b x y ↔ ψ.SameComponent a b x y := by
  have he := hs.bicoloured ha hb
  constructor
  · rintro ⟨hx, hy, hr⟩
    let f : φ.KempeGraph a b →g ψ.KempeGraph a b :=
      { toFun := fun z => ⟨z.val, he ▸ z.property⟩, map_rel' := fun hz => hz }
    exact ⟨he ▸ hx, he ▸ hy, hr.map f⟩
  · rintro ⟨hx, hy, hr⟩
    let f : ψ.KempeGraph a b →g φ.KempeGraph a b :=
      { toFun := fun z => ⟨z.val, he.symm ▸ z.property⟩, map_rel' := fun hz => hz }
    exact ⟨he.symm ▸ hx, he.symm ▸ hy, hr.map f⟩

theorem SameYClasses.allTangled {F' : Finset W} {φ : PartialColouring H F}
    {ψ : PartialColouring H F'} {Y : Finset Colour} (hs : φ.SameYClasses ψ Y) (v : W) :
    φ.AllTangled Y v ↔ ψ.AllTangled Y v := by
  unfold AllTangled TangledAt
  constructor <;> intro ht a ha b hb hab <;>
    obtain ⟨x, y, hx, hy, hc⟩ := ht a ha b hb hab
  · exact ⟨x, y, (hs.neighbour ha v x).mp hx, (hs.neighbour hb v y).mp hy,
      (hs.sameComponent ha hb x y).mp hc⟩
  · exact ⟨x, y, (hs.neighbour ha v x).mpr hx, (hs.neighbour hb v y).mpr hy,
      (hs.sameComponent ha hb x y).mpr hc⟩

theorem SameYClasses.yNeighbours {F' : Finset W} {φ : PartialColouring H F}
    {ψ : PartialColouring H F'} {Y : Finset Colour} (hs : φ.SameYClasses ψ Y) (v : W) :
    φ.yNeighbours Y v = ψ.yNeighbours Y v := by
  apply Finset.ext
  intro x
  simp only [PartialColouring.yNeighbours, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hvx, hc⟩
    obtain ⟨hx', heq⟩ := (hs _ hc x).mp ⟨hx, rfl⟩
    exact ⟨hx', hvx, heq ▸ hc⟩
  · rintro ⟨hx, hvx, hc⟩
    obtain ⟨hx', heq⟩ := (hs _ hc x).mpr ⟨hx, rfl⟩
    exact ⟨hx', hvx, heq ▸ hc⟩

theorem holeMove_sameYClasses (φ : PartialColouring H F) {v f : W} {p : Colour}
    {Y : Finset Colour} (hv : v ∉ F) (hs : φ.Single v p f) (hp : p ∉ Y) :
    φ.SameYClasses (φ.holeMove hs) Y := by
  intro a ha x
  have hpa : p ≠ a := fun he => hp (he ▸ ha)
  by_cases hxv : x = v
  · subst x
    simp [hv, holeMove_colour, hpa]
  · by_cases hxf : x = f
    · subst x
      simp [holeMove_colour, hxv, hs.1.2.2, hpa]
    · simp [holeMove_colour, hxv, hxf]

/-- Counting the single neighbours in colours outside Y. -/
theorem outside_single_bound (φ : PartialColouring H F) (v : W) (Y : Finset Colour)
    (C : Finset W) (hb : ∀ a, ∃ f, φ.Neighbour v a f)
    (hc : ∀ a ∉ Y, ∀ f, φ.Single v a f → f ∈ C) :
    2 * (20 - (Y.card : ℤ)) + (φ.yNeighbours Y v).card -
      (φ.colouredNeighbours v).card ≤ (domainNeighbours H C v).card := by
  let N := (φ.colouredNeighbours v).filter (fun f => φ.colour f ∉ Y)
  let A := (Finset.univ : Finset Colour) \ Y
  have hb' : ∀ a ∈ A, ∃ f ∈ N, φ.colour f = a := by
    intro a ha
    obtain ⟨f, hf, hvf, hfa⟩ := hb a
    exact ⟨f, by simp [N, colouredNeighbours, hf, hvf, hfa,
      (Finset.mem_sdiff.mp ha).2], hfa⟩
  have hcount := φ.single_count N A hb'
  let B := A.filter (fun a => (N.filter (φ.colour · = a)).card = 1)
  have hsub : B ⊆ (domainNeighbours H C v).image φ.colour := by
    intro a ha
    obtain ⟨haA, hcard⟩ := Finset.mem_filter.mp ha
    have haY : a ∉ Y := (Finset.mem_sdiff.mp haA).2
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have hfN : f ∈ N.filter (φ.colour · = a) := by rw [hf]; simp
    obtain ⟨⟨hfF, hvf⟩, _, hfa⟩ := (show
        (f ∈ F ∧ H.Adj v f) ∧ φ.colour f ∉ Y ∧ φ.colour f = a from by
      simpa [N, colouredNeighbours, and_assoc] using hfN)
    have hs : φ.Single v a f := by
      refine ⟨⟨hfF, hvf, hfa⟩, ?_⟩
      intro x hx
      have hxN : x ∈ N.filter (φ.colour · = a) := by
        simp [N, colouredNeighbours, hx.1, hx.2.1, hx.2.2, haY]
      simpa [hf] using hxN
    exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hc a haY f hs, hvf⟩, hfa⟩
  have hB : B.card ≤ (domainNeighbours H C v).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hA : A.card = 20 - Y.card := by simp [A, Finset.card_sdiff]
  have hY : Y.card ≤ 20 := by simpa using Finset.card_le_univ Y
  have hparts : N.card + (φ.yNeighbours Y v).card = (φ.colouredNeighbours v).card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := φ.colouredNeighbours v) (p := fun f => φ.colour f ∈ Y)
    have heq : (φ.colouredNeighbours v).filter (fun f => φ.colour f ∈ Y) =
        φ.yNeighbours Y v := by ext; simp [colouredNeighbours, yNeighbours, and_assoc]
    rw [heq] at hpart
    exact (Nat.add_comm _ _).trans hpart
  change 2 * A.card ≤ N.card + B.card at hcount
  rw [hA] at hcount
  omega

/-- All possible hole positions while keeping the Y classes fixed. -/
def fixedClassHoles (φ : PartialColouring H F) (h : W) (Y : Finset Colour) : Finset W :=
  (insert h F).filter (fun v => ∃ ψ : PartialColouring H ((insert h F).erase v),
    φ.SameYClasses ψ Y)

theorem colourSetInsertion (φ : PartialColouring H F) (h : W) (hh : h ∉ F)
    (Y : Finset Colour) (_hY : 2 ≤ Y.card)
    (hcore : h ∉ φ.colourSetCore h Y) : Nonempty (PartialColouring H (insert h F)) := by
  by_contra hno
  let D := insert h F
  let C := φ.fixedClassHoles h Y
  have hhC : h ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, ?_⟩
    have heq : (insert h F).erase h = F := Finset.erase_insert hh
    refine ⟨φ.restrict _ (by rw [heq]), ?_⟩
    intro a ha x
    simp [restrict, heq]
  have hst : ∀ v ∈ D, ∀ ψ : PartialColouring H (D.erase v), ψ.Stuck v := by
    intro v hv ψ
    have hD : insert v (D.erase v) = D := Finset.insert_erase hv
    rcases ψ.free_or_separable_or_stuck v with ⟨a, ha⟩ | ⟨a, b, hab, hs⟩ | hs
    · exfalso
      apply hno
      change Nonempty (PartialColouring H D)
      rw [← hD]
      exact ⟨ψ.insertFree v a ha⟩
    · exfalso
      apply hno
      change Nonempty (PartialColouring H D)
      rw [← hD]
      exact ψ.insert_of_separable hab hs
    · exact hs
  have hC : φ.IsColourCore h Y C := by
    constructor
    · intro v hv
      obtain ⟨hvD, ψ, hs⟩ := Finset.mem_filter.mp hv
      refine Finset.mem_filter.mpr ⟨hvD, ?_, ?_⟩
      · intro hvF hc
        exact (Finset.notMem_erase v D) ((hs _ hc v).mp ⟨hvF, rfl⟩).1
      · apply (hs.allTangled v).mpr
        intro a ha b hb hab
        exact (ψ.tangledAt_iff_not_separable v a b).mpr ((hst v hvD ψ).2 a b hab)
    · intro v hv
      obtain ⟨hvD, ψ, hs⟩ := Finset.mem_filter.mp hv
      have hbound := ψ.outside_single_bound v Y C (hst v hvD ψ).1 (by
        intro a ha f hsingle
        have hfD : f ∈ D := Finset.mem_of_mem_erase hsingle.1.1
        refine Finset.mem_filter.mpr ⟨hfD, ?_⟩
        have heq : insert v ((D.erase v).erase f) = D.erase f := by
          rw [Finset.erase_right_comm, Finset.insert_erase]
          exact Finset.mem_erase.mpr ⟨hsingle.1.2.1.ne, hvD⟩
        let χ := (ψ.holeMove hsingle).restrict (D.erase f) (by rw [heq])
        refine ⟨χ, hs.trans ?_⟩
        have hm := ψ.holeMove_sameYClasses (by simp) hsingle ha
        intro a' ha' x
        change (x ∈ D.erase v ∧ ψ.colour x = a') ↔
          (x ∈ D.erase f ∧ (ψ.holeMove hsingle).colour x = a')
        rw [← heq]
        exact hm a' ha' x)
      have hdeg : ψ.colouredNeighbours v = domainNeighbours H D v := by
        ext x
        simp only [colouredNeighbours, domainNeighbours, Finset.mem_filter, Finset.mem_erase]
        constructor
        · tauto
        · rintro ⟨hx, hvx⟩
          exact ⟨⟨hvx.ne.symm, hx⟩, hvx⟩
      simpa only [colourSetThreshold, hs.yNeighbours v, hdeg] using hbound
  exact hcore (φ.colourSetCore_greatest hC hhC)

theorem colourSetInsertion_of_subsets (φ : PartialColouring H F) (h : W) (hh : h ∉ F)
    (Y : Finset Colour) (hY : 2 ≤ Y.card)
    (hc : ∀ C ⊆ φ.colourSetS h Y, h ∈ C →
      ∃ v ∈ C, (domainNeighbours H C v).card < φ.colourSetThreshold h Y v) :
    Nonempty (PartialColouring H (insert h F)) :=
  φ.colourSetInsertion h hh Y hY ((φ.not_mem_colourSetCore_iff h Y).mpr hc)

end PartialColouring
end Se20Insertion
