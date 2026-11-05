import Se20Insertion.ColourSetCounting

/-! An independent arbitrary-palette development. No existing declaration changes.
The constructions and proofs are generalized from the checked 20-colour modules. -/
noncomputable section
open scoped Classical
namespace Se20Insertion.Parametric
structure PartialColouring (K : Nat) {W : Type*} (H : SimpleGraph W) (F : Finset W) where
  colour : W → (Fin K)
  proper : ∀ ⦃x y⦄, x ∈ F → y ∈ F → H.Adj x y → colour x ≠ colour y

namespace PartialColouring
variable {K : Nat} {W : Type*} {H : SimpleGraph W} {F : Finset W}

def Neighbour (φ : PartialColouring K H F) (f : W) (a : (Fin K)) (g : W) : Prop :=
  g ∈ F ∧ H.Adj f g ∧ φ.colour g = a

def Free (φ : PartialColouring K H F) (f : W) (a : (Fin K)) : Prop :=
  ¬ ∃ g, φ.Neighbour f a g

def Single (φ : PartialColouring K H F) (f : W) (p : (Fin K)) (g : W) : Prop :=
  φ.Neighbour f p g ∧ ∀ g', φ.Neighbour f p g' → g' = g

def Bicoloured (φ : PartialColouring K H F) (a b : (Fin K)) : Set W :=
  {g | g ∈ F ∧ (φ.colour g = a ∨ φ.colour g = b)}

def KempeGraph (φ : PartialColouring K H F) (a b : (Fin K)) :
    SimpleGraph (φ.Bicoloured a b) := H.induce (φ.Bicoloured a b)

/-- Two edges are in the same component of the induced two-colour graph. -/
def SameComponent (φ : PartialColouring K H F) (a b : (Fin K)) (x y : W) : Prop :=
  ∃ hx : x ∈ φ.Bicoloured a b, ∃ hy : y ∈ φ.Bicoloured a b,
    (φ.KempeGraph a b).Reachable ⟨x, hx⟩ ⟨y, hy⟩

def Separable (φ : PartialColouring K H F) (f : W) (a b : (Fin K)) : Prop :=
  ∀ x y, φ.Neighbour f a x → φ.Neighbour f b y → ¬ φ.SameComponent a b x y

def JointSeparable (φ : PartialColouring K H F) (B : Set W) (a b : (Fin K)) : Prop :=
  ∀ f ∈ B, ∀ g ∈ B, ∀ x y,
    φ.Neighbour f a x → φ.Neighbour g b y → ¬ φ.SameComponent a b x y

def Stuck (φ : PartialColouring K H F) (e : W) : Prop :=
  (∀ a, ∃ g, φ.Neighbour e a g) ∧
    ∀ a b, a ≠ b → ¬ φ.Separable e a b

/-- A union of whole components of the induced two-colour graph. -/
def KempeClosed (φ : PartialColouring K H F) (a b : (Fin K)) (S : Set W) : Prop :=
  S ⊆ φ.Bicoloured a b ∧
    ∀ ⦃x y⦄, x ∈ S → y ∈ φ.Bicoloured a b → H.Adj x y → y ∈ S

def swapColour (φ : PartialColouring K H F) (a b : (Fin K)) (S : Set W) (x : W) : (Fin K) :=
  if x ∈ S then Equiv.swap a b (φ.colour x) else φ.colour x


theorem sameComponent_refl (φ : PartialColouring K H F) {a b : (Fin K)} {x : W}
    (hx : x ∈ φ.Bicoloured a b) : φ.SameComponent a b x x :=
  ⟨hx, hx, .rfl⟩

theorem SameComponent.symm {φ : PartialColouring K H F} {a b : (Fin K)} {x y : W}
    (h : φ.SameComponent a b x y) : φ.SameComponent a b y x := by
  obtain ⟨hx, hy, h⟩ := h
  exact ⟨hy, hx, h.symm⟩

theorem SameComponent.trans {φ : PartialColouring K H F} {a b : (Fin K)} {x y z : W}
    (h : φ.SameComponent a b x y) (h' : φ.SameComponent a b y z) :
    φ.SameComponent a b x z := by
  obtain ⟨hx, hy, h⟩ := h
  obtain ⟨hy', hz, h'⟩ := h'
  exact ⟨hx, hz, h.trans h'⟩

theorem sameComponent_of_adj (φ : PartialColouring K H F) {a b : (Fin K)} {x y : W}
    (hx : x ∈ φ.Bicoloured a b) (hy : y ∈ φ.Bicoloured a b) (h : H.Adj x y) :
    φ.SameComponent a b x y := ⟨hx, hy, SimpleGraph.Adj.reachable h⟩

theorem component_closed (φ : PartialColouring K H F) (a b : (Fin K)) (x : W) :
    φ.KempeClosed a b {y | φ.SameComponent a b x y} := by
  refine ⟨fun y h => h.choose_spec.choose, ?_⟩
  intro y z hy hz hyz
  exact hy.trans (φ.sameComponent_of_adj hy.choose_spec.choose hz hyz)

theorem swapColour_eq_self (φ : PartialColouring K H F) {a b : (Fin K)} {S : Set W}
    (hS : φ.KempeClosed a b S) {x : W}
    (ha : φ.colour x ≠ a) (hb : φ.colour x ≠ b) :
    φ.swapColour a b S x = φ.colour x := by
  have hx : x ∉ S := fun hx => (hS.1 hx).2.elim ha hb
  simp [swapColour, hx]

theorem swapColour_eq_iff (φ : PartialColouring K H F) {a b c : (Fin K)} {S : Set W}
    (ha : c ≠ a) (hb : c ≠ b) (x : W) :
    φ.swapColour a b S x = c ↔ φ.colour x = c := by
  simp only [swapColour]
  split
  · rw [Equiv.swap_apply_eq_iff]
    simp [Equiv.swap_apply_of_ne_of_ne ha hb]
  · rfl

/-- Swap any union of whole components, preserving properness on exactly `F`. -/
def swap (φ : PartialColouring K H F) (a b : (Fin K)) (S : Set W)
    (hS : φ.KempeClosed a b S) : PartialColouring K H F where
  colour := φ.swapColour a b S
  proper := by
    intro x y hx hy hxy heq
    by_cases hxs : x ∈ S <;> by_cases hys : y ∈ S
    · exact φ.proper hx hy hxy ((Equiv.swap a b).injective (by simpa [swapColour, hxs, hys] using heq))
    · have hc : φ.colour y = a ∨ φ.colour y = b := by
        rcases (hS.1 hxs).2 with hxa | hxb
        · right; simpa [swapColour, hxs, hys, hxa] using heq.symm
        · left; simpa [swapColour, hxs, hys, hxb] using heq.symm
      exact hys (hS.2 hxs ⟨hy, hc⟩ hxy)
    · have hc : φ.colour x = a ∨ φ.colour x = b := by
        rcases (hS.1 hys).2 with hya | hyb
        · right; simpa [swapColour, hxs, hys, hya] using heq
        · left; simpa [swapColour, hxs, hys, hyb] using heq
      exact hxs (hS.2 hys ⟨hx, hc⟩ hxy.symm)
    · exact φ.proper hx hy hxy (by simpa [swapColour, hxs, hys] using heq)

/-- Union of the components containing an `a`-neighbour of some member of `B`. -/
def touching (φ : PartialColouring K H F) (B : Set W) (a b : (Fin K)) : Set W :=
  {y | ∃ f ∈ B, ∃ x, φ.Neighbour f a x ∧ φ.SameComponent a b x y}

theorem touching_closed (φ : PartialColouring K H F) (B : Set W) (a b : (Fin K)) :
    φ.KempeClosed a b (φ.touching B a b) := by
  constructor
  · rintro y ⟨f, hf, x, hx, hxy⟩
    exact hxy.choose_spec.choose
  · rintro y z ⟨f, hf, x, hx, hxy⟩ hz hyz
    exact ⟨f, hf, x, hx, hxy.trans (φ.sameComponent_of_adj hxy.choose_spec.choose hz hyz)⟩

/-- Joint separability frees `a` simultaneously at every member of `B`. -/
theorem jointSeparable_frees (φ : PartialColouring K H F) {B : Set W} {a b : (Fin K)}
    (hab : a ≠ b) (hsep : φ.JointSeparable B a b) :
    ∀ f ∈ B, (φ.swap a b (φ.touching B a b) (φ.touching_closed B a b)).Free f a := by
  intro f hf
  rintro ⟨y, hy, hfy, hcol⟩
  change φ.swapColour a b (φ.touching B a b) y = a at hcol
  by_cases hys : y ∈ φ.touching B a b
  · have hyb : φ.colour y = b := by
      simpa [swapColour, hys, Equiv.swap_apply_eq_iff] using hcol
    obtain ⟨g, hg, x, hx, hxy⟩ := hys
    exact hsep g hg f hf x y hx ⟨hy, hfy, hyb⟩ hxy
  · have hya : φ.colour y = a := by simpa [swapColour, hys] using hcol
    exact hys ⟨f, hf, y, ⟨hy, hfy, hya⟩, φ.sameComponent_refl ⟨hy, Or.inl hya⟩⟩

theorem separable_frees (φ : PartialColouring K H F) {e : W} {a b : (Fin K)}
    (hab : a ≠ b) (hsep : φ.Separable e a b) :
    ∃ ψ : PartialColouring K H F, ψ.Free e a := by
  refine ⟨φ.swap a b (φ.touching {e} a b) (φ.touching_closed {e} a b), ?_⟩
  apply φ.jointSeparable_frees hab _ e (Set.mem_singleton e)
  simpa [JointSeparable, Separable] using hsep

/-- Insert a vertex with a free colour; in applications vertices are edges of `G`. -/
def insertFree [DecidableEq W] (φ : PartialColouring K H F) (e : W) (a : (Fin K))
    (hfree : φ.Free e a) : PartialColouring K H (insert e F) where
  colour x := if x = e then a else φ.colour x
  proper := by
    intro x y hx hy hxy heq
    by_cases hxe : x = e
    · subst x
      have hye : y ≠ e := hxy.ne.symm
      have hyF : y ∈ F := (Finset.mem_insert.mp hy).resolve_left hye
      exact hfree ⟨y, hyF, hxy, by simpa [hye] using heq.symm⟩
    · have hxF : x ∈ F := (Finset.mem_insert.mp hx).resolve_left hxe
      by_cases hye : y = e
      · subst y
        exact hfree ⟨x, hxF, hxy.symm, by simpa [hxe] using heq⟩
      · have hyF : y ∈ F := (Finset.mem_insert.mp hy).resolve_left hye
        exact φ.proper hxF hyF hxy (by simpa [hxe, hye] using heq)

theorem insert_of_separable [DecidableEq W] (φ : PartialColouring K H F) {e : W}
    {a b : (Fin K)} (hab : a ≠ b) (hsep : φ.Separable e a b) :
    Nonempty (PartialColouring K H (insert e F)) := by
  obtain ⟨ψ, hψ⟩ := φ.separable_frees hab hsep
  exact ⟨ψ.insertFree e a hψ⟩

def restrict (φ : PartialColouring K H F) (F' : Finset W) (h : F' ⊆ F) : PartialColouring K H F' where
  colour := φ.colour
  proper := by
    intro x y hx hy hxy
    exact φ.proper (h hx) (h hy) hxy

theorem erase_single_free [DecidableEq W] (φ : PartialColouring K H F) {e f : W} {p : (Fin K)}
    (hs : φ.Single e p f) :
    (φ.restrict (F.erase f) (Finset.erase_subset _ _)).Free e p := by
  rintro ⟨x, hx, hex, hc⟩
  have hxf := hs.2 x ⟨Finset.mem_of_mem_erase hx, hex, hc⟩
  exact (Finset.mem_erase.mp hx).1 hxf

/-- The legal hole move: erase the unique `p`-neighbour and colour the hole `p`. -/
def holeMove [DecidableEq W] (φ : PartialColouring K H F) {e f : W} {p : (Fin K)}
    (hs : φ.Single e p f) : PartialColouring K H (insert e (F.erase f)) :=
  (φ.restrict (F.erase f) (Finset.erase_subset _ _)).insertFree e p (φ.erase_single_free hs)

theorem holeMove_colour [DecidableEq W] (φ : PartialColouring K H F) {e f : W} {p : (Fin K)}
    (hs : φ.Single e p f) (x : W) :
    (φ.holeMove hs).colour x = if x = e then p else φ.colour x := rfl

theorem single_count (φ : PartialColouring K H F) (N : Finset W) (A : Finset (Fin K))
    (hblocked : ∀ c ∈ A, ∃ x ∈ N, φ.colour x = c) :
    2 * A.card ≤ N.card + (A.filter (fun c => (N.filter (φ.colour · = c)).card = 1)).card := by
  have hfib : ∑ c ∈ A, (N.filter (φ.colour · = c)).card ≤ N.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  have heach : ∀ c ∈ A,
      2 ≤ (N.filter (φ.colour · = c)).card +
        (if (N.filter (φ.colour · = c)).card = 1 then 1 else 0) := by
    intro c hc
    have hp : 0 < (N.filter (φ.colour · = c)).card := by
      obtain ⟨x, hx, hxc⟩ := hblocked c hc
      exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxc⟩⟩
    split <;> omega
  have hsum := Finset.sum_le_sum heach
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hsum
  have hones : (∑ c ∈ A, if (N.filter (φ.colour · = c)).card = 1 then 1 else 0) =
      (A.filter (fun c => (N.filter (φ.colour · = c)).card = 1)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hones] at hsum
  omega

def colouredNeighbours (φ : PartialColouring K H F) (e : W) : Finset W := F.filter (H.Adj e)

theorem free_or_separable_or_stuck (φ : PartialColouring K H F) (e : W) :
    (∃ a, φ.Free e a) ∨ (∃ a b, a ≠ b ∧ φ.Separable e a b) ∨ φ.Stuck e := by
  by_cases hf : ∃ a, φ.Free e a
  · exact Or.inl hf
  right
  by_cases hs : ∃ a b, a ≠ b ∧ φ.Separable e a b
  · exact Or.inl hs
  right
  constructor
  · simpa [Free, not_exists, not_not] using hf
  · intro a b hab hsep
    exact hs ⟨a, b, hab, hsep⟩


/-- Existential tangling, including the actual two-colour component. -/
def TangledAt (φ : PartialColouring K H F) (v : W) (a b : (Fin K)) : Prop :=
  ∃ x y, φ.Neighbour v a x ∧ φ.Neighbour v b y ∧ φ.SameComponent a b x y

theorem tangledAt_iff_not_separable (φ : PartialColouring K H F) (v : W) (a b : (Fin K)) :
    φ.TangledAt v a b ↔ ¬ φ.Separable v a b := by
  simp [TangledAt, Separable]

def AllTangled (φ : PartialColouring K H F) (Y : Finset (Fin K)) (v : W) : Prop :=
  ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → φ.TangledAt v a b

/-- All degrees in this file are restricted to the specified finite domain. -/
def domainNeighbours (H : SimpleGraph W) (D : Finset W) (v : W) : Finset W :=
  D.filter (H.Adj v)

def yNeighbours (φ : PartialColouring K H F) (Y : Finset (Fin K)) (v : W) : Finset W :=
  F.filter (fun x => H.Adj v x ∧ φ.colour x ∈ Y)

def colourSetS (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) : Finset W :=
  (insert h F).filter (fun v => (v ∈ F → φ.colour v ∉ Y) ∧ φ.AllTangled Y v)

/-- Integer threshold: no truncated natural subtraction. -/
def colourSetThreshold (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) (v : W) : ℤ :=
  2 * ((K : Int) - (Y.card : Int)) + (φ.yNeighbours Y v).card -
    (domainNeighbours H (insert h F) v).card

def IsColourCore (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) (C : Finset W) : Prop :=
  C ⊆ φ.colourSetS h Y ∧ ∀ v ∈ C,
    φ.colourSetThreshold h Y v ≤ (domainNeighbours H C v).card

/-- The largest subset of S satisfying the local threshold inequalities. -/
def colourSetCore (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) : Finset W :=
  (φ.colourSetS h Y).filter (fun v => ∃ C, φ.IsColourCore h Y C ∧ v ∈ C)

theorem colourSetCore_greatest (φ : PartialColouring K H F) {h : W} {Y : Finset (Fin K)}
    {C : Finset W} (hc : φ.IsColourCore h Y C) : C ⊆ φ.colourSetCore h Y := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨hc.1 hv, C, hc, hv⟩

theorem colourSetCore_isCore (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) :
    φ.IsColourCore h Y (φ.colourSetCore h Y) := by
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro v hv
  obtain ⟨_, C, hc, hvc⟩ := Finset.mem_filter.mp hv
  exact (hc.2 v hvc).trans (by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (φ.colourSetCore_greatest hc)))

theorem not_mem_colourSetCore_iff (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) :
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
def SameYClasses {F' : Finset W} (φ : PartialColouring K H F) (ψ : PartialColouring K H F')
    (Y : Finset (Fin K)) : Prop :=
  ∀ a ∈ Y, ∀ x, (x ∈ F ∧ φ.colour x = a) ↔ (x ∈ F' ∧ ψ.colour x = a)

theorem SameYClasses.symm {F' : Finset W} {φ : PartialColouring K H F}
    {ψ : PartialColouring K H F'} {Y : Finset (Fin K)} (hs : φ.SameYClasses ψ Y) :
    ψ.SameYClasses φ Y := fun a ha x => (hs a ha x).symm

theorem SameYClasses.trans {F' F'' : Finset W} {φ : PartialColouring K H F}
    {ψ : PartialColouring K H F'} {χ : PartialColouring K H F''} {Y : Finset (Fin K)}
    (hs : φ.SameYClasses ψ Y) (ht : ψ.SameYClasses χ Y) : φ.SameYClasses χ Y :=
  fun a ha x => (hs a ha x).trans (ht a ha x)

theorem SameYClasses.neighbour {F' : Finset W} {φ : PartialColouring K H F}
    {ψ : PartialColouring K H F'} {Y : Finset (Fin K)} (hs : φ.SameYClasses ψ Y)
    {a : (Fin K)} (ha : a ∈ Y) (v x : W) : φ.Neighbour v a x ↔ ψ.Neighbour v a x := by
  have := hs a ha x
  simp only [Neighbour]
  tauto

theorem SameYClasses.bicoloured {F' : Finset W} {φ : PartialColouring K H F}
    {ψ : PartialColouring K H F'} {Y : Finset (Fin K)} (hs : φ.SameYClasses ψ Y)
    {a b : (Fin K)} (ha : a ∈ Y) (hb : b ∈ Y) : φ.Bicoloured a b = ψ.Bicoloured a b := by
  ext x
  have := hs a ha x
  have := hs b hb x
  simp only [Bicoloured, Set.mem_setOf_eq]
  tauto

theorem SameYClasses.sameComponent {F' : Finset W} {φ : PartialColouring K H F}
    {ψ : PartialColouring K H F'} {Y : Finset (Fin K)} (hs : φ.SameYClasses ψ Y)
    {a b : (Fin K)} (ha : a ∈ Y) (hb : b ∈ Y) (x y : W) :
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

theorem SameYClasses.allTangled {F' : Finset W} {φ : PartialColouring K H F}
    {ψ : PartialColouring K H F'} {Y : Finset (Fin K)} (hs : φ.SameYClasses ψ Y) (v : W) :
    φ.AllTangled Y v ↔ ψ.AllTangled Y v := by
  unfold AllTangled TangledAt
  constructor <;> intro ht a ha b hb hab <;>
    obtain ⟨x, y, hx, hy, hc⟩ := ht a ha b hb hab
  · exact ⟨x, y, (hs.neighbour ha v x).mp hx, (hs.neighbour hb v y).mp hy,
      (hs.sameComponent ha hb x y).mp hc⟩
  · exact ⟨x, y, (hs.neighbour ha v x).mpr hx, (hs.neighbour hb v y).mpr hy,
      (hs.sameComponent ha hb x y).mpr hc⟩

theorem SameYClasses.yNeighbours {F' : Finset W} {φ : PartialColouring K H F}
    {ψ : PartialColouring K H F'} {Y : Finset (Fin K)} (hs : φ.SameYClasses ψ Y) (v : W) :
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

theorem holeMove_sameYClasses (φ : PartialColouring K H F) {v f : W} {p : (Fin K)}
    {Y : Finset (Fin K)} (hv : v ∉ F) (hs : φ.Single v p f) (hp : p ∉ Y) :
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
theorem outside_single_bound (φ : PartialColouring K H F) (v : W) (Y : Finset (Fin K))
    (C : Finset W) (hb : ∀ a, ∃ f, φ.Neighbour v a f)
    (hc : ∀ a ∉ Y, ∀ f, φ.Single v a f → f ∈ C) :
    2 * ((K : Int) - (Y.card : Int)) + (φ.yNeighbours Y v).card -
      (φ.colouredNeighbours v).card ≤ (domainNeighbours H C v).card := by
  let N := (φ.colouredNeighbours v).filter (fun f => φ.colour f ∉ Y)
  let A := (Finset.univ : Finset (Fin K)) \ Y
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
  have hA : A.card = K - Y.card := by simp [A, Finset.card_sdiff]
  have hY : Y.card ≤ K := by simpa using Finset.card_le_univ Y
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
def fixedClassHoles (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) : Finset W :=
  (insert h F).filter (fun v => ∃ ψ : PartialColouring K H ((insert h F).erase v),
    φ.SameYClasses ψ Y)

theorem colourSetInsertion (φ : PartialColouring K H F) (h : W) (hh : h ∉ F)
    (Y : Finset (Fin K)) (_hY : 2 ≤ Y.card)
    (hcore : h ∉ φ.colourSetCore h Y) : Nonempty (PartialColouring K H (insert h F)) := by
  by_contra hno
  let D := insert h F
  let C := φ.fixedClassHoles h Y
  have hhC : h ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, ?_⟩
    have heq : (insert h F).erase h = F := Finset.erase_insert hh
    refine ⟨φ.restrict _ (by rw [heq]), ?_⟩
    intro a ha x
    simp [restrict, heq]
  have hst : ∀ v ∈ D, ∀ ψ : PartialColouring K H (D.erase v), ψ.Stuck v := by
    intro v hv ψ
    have hD : insert v (D.erase v) = D := Finset.insert_erase hv
    rcases ψ.free_or_separable_or_stuck v with ⟨a, ha⟩ | ⟨a, b, hab, hs⟩ | hs
    · exfalso
      apply hno
      change Nonempty (PartialColouring K H D)
      rw [← hD]
      exact ⟨ψ.insertFree v a ha⟩
    · exfalso
      apply hno
      change Nonempty (PartialColouring K H D)
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

theorem colourSetInsertion_of_subsets (φ : PartialColouring K H F) (h : W) (hh : h ∉ F)
    (Y : Finset (Fin K)) (hY : 2 ≤ Y.card)
    (hc : ∀ C ⊆ φ.colourSetS h Y, h ∈ C →
      ∃ v ∈ C, (domainNeighbours H C v).card < φ.colourSetThreshold h Y v) :
    Nonempty (PartialColouring K H (insert h F)) :=
  φ.colourSetInsertion h hh Y hY ((φ.not_mem_colourSetCore_iff h Y).mpr hc)


end PartialColouring
end Se20Insertion.Parametric
