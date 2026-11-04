import Se20Insertion.DoubleHole

noncomputable section
open scoped Classical
namespace Se20Insertion

theorem sum_filter_card_comm {X : Type*} (S : Finset X) (P : X → X → Prop) :
    (∑ x ∈ S, (S.filter (P x)).card) = ∑ y ∈ S, (S.filter (fun x => P x y)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem card_filter_partition {X : Type*} {S F : Finset X} (hSF : S ⊆ F) (P : X → Prop) :
    (F.filter P).card = (S.filter P).card + (F.filter (fun x => P x ∧ x ∉ S)).card := by
  have heq : (F.filter P).filter (· ∈ S) = S.filter P := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · exact fun h => ⟨⟨hSF h.1, h.2⟩, h.1⟩
  have hh := Finset.card_filter_add_card_filter_not (s := F.filter P) (· ∈ S)
  rw [heq] at hh
  simpa only [Finset.filter_filter] using hh.symm

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- Condition (a), including all twenty colours at an uncoloured vertex. -/
def SaturatedOn (φ : PartialColouring H F) (R : Finset W) : Prop :=
  ∀ x ∈ R, ∀ a : Colour, (x ∉ F ∨ a ≠ φ.colour x) → ∃ z, φ.Neighbour x a z

/-- Condition (b); `Single` includes colouredness and adjacency. -/
def SingleClosed (φ : PartialColouring H F) (R : Finset W) : Prop :=
  ∀ x ∈ R, ∀ y, φ.Single x (φ.colour y) y → y ∈ R

/-- Condition (c), entirely in `φ`; it does not assert a movable hole. -/
def NoDoubleHole (φ : PartialColouring H F) (R : Finset W) : Prop :=
  ∀ g ∈ R, ∀ f w, ¬ φ.DoubleHoleConfig g f w

def MutualSingle (φ : PartialColouring H F) (x y : W) : Prop :=
  φ.Single x (φ.colour y) y ∧ φ.Single y (φ.colour x) x

def singleTargets (φ : PartialColouring H F) (S : Finset W) (x : W) : Finset W :=
  S.filter (fun y => H.Adj x y ∧ φ.Single y (φ.colour x) x)

def partners (φ : PartialColouring H F) (S : Finset W) (x : W) : Finset W :=
  S.filter (φ.MutualSingle x)

/-- At a saturated coloured vertex, the number of neighbours whose colour is
not single, plus 38, is at most twice the coloured degree. -/
theorem nonsingle_budget (φ : PartialColouring H F) (x : W)
    (hsat : ∀ a : Colour, a ≠ φ.colour x → ∃ z, φ.Neighbour x a z) :
    ((φ.colouredNeighbours x).filter (fun y => ¬ φ.Single x (φ.colour y) y)).card + 38 ≤
      2 * (φ.colouredNeighbours x).card := by
  let N := φ.colouredNeighbours x
  let A : Finset Colour := Finset.univ.erase (φ.colour x)
  let K := A.filter (fun a => (N.filter (φ.colour · = a)).card = 1)
  let B := N.filter (fun y => φ.Single x (φ.colour y) y)
  have hcount : 38 ≤ N.card + K.card := by
    have hh := φ.single_count N A (by
      intro a ha
      obtain ⟨z, hz, hxz, hza⟩ := hsat a (Finset.mem_erase.mp ha).1
      exact ⟨z, Finset.mem_filter.mpr ⟨hz, hxz⟩, hza⟩)
    simpa [A] using hh
  have hK : K ⊆ B.image φ.colour := by
    intro a ha
    have ha' : a ∈ φ.singleColours x :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    obtain ⟨z, hz⟩ := (φ.mem_singleColours x a).mp ha'
    have hB : z ∈ B := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hz.1.1, hz.1.2.1⟩, ?_⟩
      simpa [hz.1.2.2] using hz
    exact Finset.mem_image.mpr ⟨z, hB, hz.1.2.2⟩
  have hKB : K.card ≤ B.card :=
    (Finset.card_le_card hK).trans Finset.card_image_le
  have hp := Finset.card_filter_add_card_filter_not
    (s := N) (p := fun y => φ.Single x (φ.colour y) y)
  dsimp [B] at hKB
  dsimp [N] at *
  omega

/-- The global counting argument, isolated from the local geometry.
`hlocal` is the consequence of the absence of a double-hole configuration.
All degrees here are coloured degrees; no regularity or exact-degree identity
is used in this abstract lemma. -/
theorem counting_contradiction (φ : PartialColouring H F) (S : Finset W)
    (hSF : S ⊆ F) (hne : S.Nonempty) (hsat : φ.SaturatedOn S)
    (hclosed : φ.SingleClosed S)
    (hdegree : ∀ x ∈ S, (φ.colouredNeighbours x).card ≤ 24)
    (hlocal : ∀ x ∈ S, (φ.singleTargets S x).card + 3 * (φ.partners S x).card ≤ 24) :
    False := by
  let d := fun x => (φ.colouredNeighbours x).card
  let t := fun x => (F.filter (fun y => H.Adj x y ∧ y ∉ S)).card
  let r := fun x => (S.filter (H.Adj x)).card
  let y := fun x => (S.filter (fun z => H.Adj x z ∧ ¬ φ.Single z (φ.colour x) x)).card
  let b := fun x => (S.filter (fun z => H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z)).card
  let c := fun x => (φ.partners S x).card
  let ns := fun x => ((φ.colouredNeighbours x).filter (fun z => ¬ φ.Single x (φ.colour z) z)).card
  have hdr : ∀ x, d x = r x + t x := fun x => card_filter_partition hSF (H.Adj x)
  have hns : ∀ x ∈ S, ns x = b x + t x := by
    intro x hx
    have hh := card_filter_partition hSF (fun z => H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z)
    have heq : F.filter (fun z => (H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z) ∧ z ∉ S) =
        F.filter (fun z => H.Adj x z ∧ z ∉ S) := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1, h.2.1.1, h.2.2⟩
      · intro h
        exact ⟨h.1, ⟨h.2.1, fun hs => h.2.2 (hclosed x hx z hs)⟩, h.2.2⟩
    have hh' : (F.filter (fun z => H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z)).card =
        b x + t x := by
      convert hh using 1
      · congr 1
        ext z
        simp only [Finset.mem_filter]
      · dsimp [b, t]
        congr 1
        · congr 1
          ext z
          simp only [Finset.mem_filter]
        · convert (congrArg Finset.card heq).symm using 1
          congr 1
          ext z
          simp only [Finset.mem_filter]
    simpa [ns, b, t, colouredNeighbours, Finset.filter_filter] using hh'
  have hbudget : ∀ x ∈ S, ns x + 38 ≤ 2 * d x := by
    intro x hx
    exact φ.nonsingle_budget x (fun a ha => hsat x hx a (.inr ha))
  have hr : ∀ x, r x ≤ c x + y x + b x := by
    intro x
    have hsub : S.filter (H.Adj x) ⊆ φ.partners S x ∪
        S.filter (fun z => H.Adj x z ∧ ¬ φ.Single z (φ.colour x) x) ∪
        S.filter (fun z => H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z) := by
      intro z hz
      obtain ⟨hzS, hxz⟩ := Finset.mem_filter.mp hz
      by_cases ho : φ.Single z (φ.colour x) x
      · by_cases hi : φ.Single x (φ.colour z) z
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzS, hi, ho⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzS, hxz, hi⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzS, hxz, ho⟩))
    have hh := Finset.card_le_card hsub
    have h1 := Finset.card_union_le (φ.partners S x)
      (S.filter (fun z => H.Adj x z ∧ ¬ φ.Single z (φ.colour x) x))
    have h2 := Finset.card_union_le
      (φ.partners S x ∪ S.filter (fun z => H.Adj x z ∧ ¬ φ.Single z (φ.colour x) x))
      (S.filter (fun z => H.Adj x z ∧ ¬ φ.Single x (φ.colour z) z))
    dsimp [r, c, y, b]
    omega
  have hby : (∑ x ∈ S, b x) = ∑ x ∈ S, y x := by
    dsimp [b, y]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro z hz
    have heq : H.Adj z x ↔ H.Adj x z := ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩
    simp only [heq]
  have htargets : ∀ x, r x = (φ.singleTargets S x).card + y x := by
    intro x
    have hh := Finset.card_filter_add_card_filter_not
      (s := S.filter (H.Adj x)) (fun z => φ.Single z (φ.colour x) x)
    simpa [r, y, singleTargets, Finset.filter_filter] using hh.symm
  have hloc : ∀ x ∈ S, 3 * c x + d x ≤ y x + t x + 24 := by
    intro x hx
    have hl := hlocal x hx
    have hd := hdr x
    have ht := htargets x
    dsimp [c]
    omega
  have hglob := Finset.sum_le_sum hloc
  have hbud := Finset.sum_le_sum hbudget
  have hdeg := Finset.sum_le_sum hdegree
  have hrglob := Finset.sum_le_sum (fun x (_hx : x ∈ S) => hr x)
  have hnsum : (∑ x ∈ S, ns x) = (∑ x ∈ S, b x) + ∑ x ∈ S, t x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hns
  have hdrsum : (∑ x ∈ S, d x) = (∑ x ∈ S, r x) + ∑ x ∈ S, t x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hdr x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, smul_eq_mul] at hglob hbud hdeg hrglob
  rw [hnsum, hby] at hbud
  rw [hby] at hrglob
  have hn := Finset.card_pos.mpr hne
  change (∑ x ∈ S, d x) ≤ _ at hdeg
  omega

end PartialColouring
end Se20Insertion
