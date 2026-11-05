import Se20Part.RouteQ
import Se20Part.Greedy
import Mathlib.Combinatorics.SimpleGraph.Clique

noncomputable section
open scoped Classical BigOperators
namespace Se20Part

theorem fibre_value_heq {W C : Type*} (π : W → C) (d : C → ℕ)
    (f : ∀ c, {x // π x = c} → Fin (d c)) {a b : C} (hab : a = b)
    (x : W) (hx : π x = a) : HEq (f a ⟨x,hx⟩) (f b ⟨x,hx.trans hab⟩) := by
  subst b
  rfl

theorem fibre_fun_heq {W C : Type*} (P : C → W → Prop) (d : C → ℕ)
    (f : ∀ c, {x // P c x} → Fin (d c)) {a b : C} (hab : a = b)
    (x : W) (ha : P a x) (hb : P b x) : HEq (f a ⟨x,ha⟩) (f b ⟨x,hb⟩) := by
  subst b
  rfl

/-- Disjoint palettes assemble colourings of the actual induced classes. -/
theorem colourable_of_partition {W C : Type*} [Fintype C]
    (H : SimpleGraph W) (π : W → C) (d : C → ℕ)
    (hc : ∀ c, (H.induce {x | π x = c}).Colorable (d c)) :
    H.Colorable (∑ c, d c) := by
  let colours : ∀ c, (H.induce {x | π x = c}).Coloring (Fin (d c)) := fun c => (hc c).some
  let f : W → Σ c, Fin (d c) := fun x => ⟨π x, colours (π x) ⟨x,rfl⟩⟩
  have hf : ∀ ⦃x y⦄, H.Adj x y → f x ≠ f y := by
    intro x y hxy heq
    have hclass : π x = π y := congrArg Sigma.fst heq
    have hcxy : colours (π y) ⟨x,hclass⟩ = colours (π y) ⟨y,rfl⟩ := by
      have h := (Sigma.mk.inj_iff.mp heq).2
      have ht := fibre_value_heq π d (fun c => colours c) hclass x rfl
      exact eq_of_heq (ht.symm.trans h)
    exact (colours (π y)).valid (show (H.induce {x | π x = π y}).Adj
      ⟨x,hclass⟩ ⟨y,rfl⟩ from hxy) hcxy
  have c := SimpleGraph.Coloring.mk (G := H) f (fun {_ _} hxy => hf hxy)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using c.colorable

def PropertyQ {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ π : G.edgeSet → Fin 10,
    (∀ e, Partition.degreeIn (L2 G) π e (π e) ≤ 2) ∧
    ∀ c, ((L2 G).induce {e | π e = c}).Colorable 2

theorem propertyQ_twenty {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hQ : PropertyQ G) : StrongColourable G 20 := by
  obtain ⟨π,_,hc⟩ := hQ
  simpa [StrongColourable] using colourable_of_partition (L2 G) π (fun _ => 2) hc

/-- The cited finite Brooks theorem in the ≥3 case. Degree at most k makes
every (k+1)-clique a whole connected component, so `CliqueFree` is equivalent
to excluding the complete-component exception here. -/
def Brooks : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W) (k : ℕ),
    3 ≤ k → (∀ x, H.degree x ≤ k) → H.CliqueFree (k+1) → H.Colorable k

def brooksPalette (c : Fin 12) : ℕ := if c.val < 4 then 3 else 1

theorem brooksPalette_sum : (∑ c : Fin 12, brooksPalette c) = 20 := by
  decide +kernel

/-- The colouring-assembly step of Theorem 4.11. Clique exclusion and
independence are explicit inputs; deriving them from the lexicographic
minimum and absence of remote marks is not asserted here. -/
theorem brooks_partition_twenty (hBrooks : Brooks) {W : Type} [Fintype W]
    (H : SimpleGraph W) (π : W → Fin 12)
    (hdeg : ∀ c, ∀ x : {v // π v = c}, (H.induce {v | π v = c}).degree x ≤ brooksPalette c)
    (hclique : ∀ c, c.val < 4 → (H.induce {v | π v = c}).CliqueFree 4)
    (hind : ∀ c, 4 ≤ c.val → ∀ x y : {v // π v = c}, ¬ H.Adj x.val y.val) :
    H.Colorable 20 := by
  rw [← brooksPalette_sum]
  apply colourable_of_partition H π brooksPalette
  intro c
  by_cases hc : c.val < 4
  · simp only [brooksPalette, hc, ite_true]
    apply hBrooks _ _ 3 (by omega)
    · intro x
      have hh := hdeg c x
      simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hh ⊢
      simpa [brooksPalette,hc] using hh
    · exact hclique c hc
  · simp only [brooksPalette, hc, ite_false]
    exact ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 1))
      (fun {x y} hxy => False.elim (hind c (by omega) x y hxy))⟩

/-- The last step of Proposition 1.1: nine bipartite classes off an independent
defect set, plus one new colour for that set. -/
theorem nine_classes_one_defect {W : Type*} (H : SimpleGraph W) (π : W → Fin 9)
    (D : Set W) (hind : ∀ x ∈ D, ∀ y ∈ D, ¬ H.Adj x y)
    (hc : ∀ c, (H.induce {x | x ∉ D ∧ π x = c}).Colorable 2) : H.Colorable 19 := by
  let colours : ∀ c, (H.induce {x | x ∉ D ∧ π x = c}).Coloring (Fin 2) := fun c => (hc c).some
  let f : W → Option (Fin 9 × Fin 2) := fun x =>
    if hx : x ∈ D then none else some (π x, colours (π x) ⟨x,hx,rfl⟩)
  have hf : ∀ ⦃x y⦄, H.Adj x y → f x ≠ f y := by
    intro x y hxy heq
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
    · exact hind x hx y hy hxy
    · simp [f,hx,hy] at heq
    · simp [f,hx,hy] at heq
    · have hpair := Option.some.inj (show
        some (π x, colours (π x) ⟨x,hx,rfl⟩) =
        some (π y, colours (π y) ⟨y,hy,rfl⟩) by simpa [f,hx,hy] using heq)
      have hclass := congrArg Prod.fst hpair
      change π x = π y at hclass
      have hcol := congrArg Prod.snd hpair
      apply (colours (π y)).valid (show (H.induce {v | v ∉ D ∧ π v = π y}).Adj
        ⟨x,hx,hclass⟩ ⟨y,hy,rfl⟩ from hxy)
      have ht := fibre_fun_heq (fun c x => x ∉ D ∧ π x = c) (fun _ => 2)
        (fun c => colours c) hclass x ⟨hx,rfl⟩ ⟨hx,hclass⟩
      exact (eq_of_heq ht).symm.trans hcol
  simpa using (SimpleGraph.Coloring.mk (G := H) f (fun {_ _} hxy => hf hxy)).colorable

end Se20Part
