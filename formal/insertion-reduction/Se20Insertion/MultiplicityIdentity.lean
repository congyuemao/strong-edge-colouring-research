import Se20Insertion.CriticalLists

noncomputable section
open scoped Classical
set_option maxHeartbeats 2000000
namespace Se20Insertion

/-- Exact multiplicity identity, allowing absent colours and multiplicities above two. -/
theorem multiplicity_identity {W : Type*} (N : Finset W) (c : W → Colour) :
    (N.filter (fun x => (N.filter (fun y => c y = c x)).card ≠ 1)).card +
      2 * (N.image c).card + (∑ a : Colour, ((N.filter (fun y => c y = a)).card - 2)) = 2 * N.card := by
  let μ := fun a => (N.filter (fun y => c y = a)).card
  let R := N.filter (fun x => μ (c x) ≠ 1)
  have all : (∑ a : Colour, μ a) = N.card := by
    simpa [μ] using Finset.sum_card_fiberwise_eq_card_filter N (Finset.univ : Finset Colour) c
  have repeated : R.card = ∑ a : Colour, if μ a = 1 then 0 else μ a := by
    have hfib := Finset.sum_card_fiberwise_eq_card_filter R (Finset.univ : Finset Colour) c
    have heq (a : Colour) : R.filter (fun y => c y = a) = if μ a = 1 then ∅ else N.filter (fun y => c y = a) := by
      ext y
      by_cases ha : μ a = 1 <;> simp only [ha,ite_true,ite_false,Finset.mem_filter,Finset.notMem_empty,R]
      · constructor
        · rintro ⟨⟨_,hn⟩,hy⟩; exact hn (hy ▸ ha)
        · exact False.elim
      · constructor
        · exact fun h => ⟨h.1.1,h.2⟩
        · rintro ⟨hy,hya⟩; exact ⟨⟨hy,hya ▸ ha⟩,hya⟩
    simp only [heq,Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _)] at hfib
    rw [← hfib]
    apply Finset.sum_congr rfl; intro a _
    by_cases ha : μ a = 1 <;> simp [ha,μ]
  have seen : (N.image c).card = ∑ a : Colour, if μ a = 0 then 0 else 1 := by
    have heq : N.image c = Finset.univ.filter (fun a => μ a ≠ 0) := by
      ext a
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro ha
        obtain ⟨y,hy,hya⟩ := Finset.mem_image.mp ha
        exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hya⟩⟩)
      · intro ha
        obtain ⟨y,hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero ha)
        exact Finset.mem_image.mpr ⟨y,(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩
    rw [heq,Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_congr rfl; intro a _; by_cases h : μ a = 0 <;> simp [h]
  have each (a : Colour) : (if μ a = 1 then 0 else μ a) + 2 * (if μ a = 0 then 0 else 1) + (μ a - 2) = 2 * μ a := by
    split_ifs <;> omega
  have hh := Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset Colour)) => each a)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hh
  rw [← repeated,← seen,all] at hh
  exact hh

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def seenColours (φ : PartialColouring H F) (x : W) : Finset Colour :=
  (φ.colouredNeighbours x).image φ.colour

def deficit (φ : PartialColouring H F) (x : W) : ℕ := 19 - (φ.seenColours x).card

def excess (φ : PartialColouring H F) (x : W) : ℕ :=
  ∑ a : Colour, (((φ.colouredNeighbours x).filter (fun y => φ.colour y = a)).card - 2)

theorem single_iff_multiplicity_one (φ : PartialColouring H F) {x y : W}
    (hy : y ∈ φ.colouredNeighbours x) :
    φ.Single x (φ.colour y) y ↔ ((φ.colouredNeighbours x).filter (fun z => φ.colour z = φ.colour y)).card = 1 := by
  constructor
  · intro hs
    have hh := (φ.mem_singleColours x (φ.colour y)).mpr ⟨y,hs⟩
    exact (Finset.mem_filter.mp hh).2
  · intro hm
    obtain ⟨z,hz⟩ := (φ.mem_singleColours x (φ.colour y)).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩)
    have hyz := hz.2 y ⟨(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2,rfl⟩
    simpa [hyz] using hz

theorem seenColours_le_nineteen (φ : PartialColouring H F) {x : W} (hx : x ∈ F) :
    (φ.seenColours x).card ≤ 19 := by
  have hs : φ.seenColours x ⊆ Finset.univ.erase (φ.colour x) := by
    intro a ha
    obtain ⟨y,hy,hya⟩ := Finset.mem_image.mp ha
    exact Finset.mem_erase.mpr ⟨fun h => φ.proper hx (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hy).2 (hya.trans h).symm,Finset.mem_univ _⟩
  simpa using Finset.card_le_card hs

theorem nonsingle_exact (φ : PartialColouring H F) {x : W} (hx : x ∈ F) :
    ((φ.colouredNeighbours x).filter (fun y => ¬ φ.Single x (φ.colour y) y)).card +
      38 + φ.excess x = 2 * (φ.colouredNeighbours x).card + 2 * φ.deficit x := by
  have heq : (φ.colouredNeighbours x).filter (fun y => ¬ φ.Single x (φ.colour y) y) =
      (φ.colouredNeighbours x).filter (fun y => ((φ.colouredNeighbours x).filter (fun z => φ.colour z = φ.colour y)).card ≠ 1) := by
    apply Finset.filter_congr
    intro y hy; exact not_congr (φ.single_iff_multiplicity_one hy)
  have hi := multiplicity_identity (φ.colouredNeighbours x) φ.colour
  rw [← heq] at hi
  have hs := φ.seenColours_le_nineteen hx
  change _ + 2 * (φ.seenColours x).card + φ.excess x = _ at hi
  dsimp [deficit]
  omega

end PartialColouring
end Se20Insertion
