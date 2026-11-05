import Se20Part.CycleLength
import Se20Part.ConflictBounds
import Se20Part.ColourAssembly

noncomputable section
open scoped Classical
namespace Se20Part

/-- Haxell's independent-transversal theorem, the citation actually used by
NEW_DIRECTIONS §1.3. Nonempty parts are required also when Δ = 0. -/
def Haxell : Prop :=
  ∀ (W I : Type) [Fintype W] [Fintype I] (H : SimpleGraph W)
    (Δ : ℕ) (parts : I → Finset W),
    (∀ v, H.degree v ≤ Δ) →
    (∀ i, (parts i).Nonempty) →
    (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) →
    (∀ i, 2 * Δ ≤ (parts i).card) →
    ∃ f : I → W, (∀ i, f i ∈ parts i) ∧
      ∀ i j, i ≠ j → ¬ H.Adj (f i) (f j)

def InducedCycle.vertices {W : Type*} {H : SimpleGraph W} {n : ℕ}
    (C : InducedCycle H n) : Finset W := (Finset.range n).image C.vertex

theorem InducedCycle.card_vertices {W : Type*} {H : SimpleGraph W} {n : ℕ}
    (C : InducedCycle H n) : C.vertices.card = n := by
  rw [InducedCycle.vertices, Finset.card_image_iff.mpr]
  · exact Finset.card_range n
  · intro i hi j hj he
    exact C.injective i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) he

/-- The independent-representative step of Proposition 1.1, with the 96/48
constants verified and Cameron eliminated. Construction of the cycle family
from a degree-two partition is not an input hidden in the cited theorem. -/
theorem long_cycles_independent_transversal (hHaxell : Haxell)
    {V I : Type} [Fintype V] [Fintype I] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (hg : 96 ≤ G.egirth)
    (n : I → ℕ) (C : ∀ i, InducedCycle (L2 G) (n i))
    (hn : ∀ i, 4 ≤ n i)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i).vertices (C j).vertices) :
    ∃ f : I → G.edgeSet, (∀ i, f i ∈ (C i).vertices) ∧
      ∀ i j, i ≠ j → ¬ (L2 G).Adj (f i) (f j) := by
  apply hHaxell G.edgeSet I (L2 G) 24 (fun i => (C i).vertices)
  · intro e
    have hset : (L2 G).neighborFinset e = conflicts G e := by ext f; simp
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hset]
    exact card_conflicts_le_twentyFour G hΔ e
  · intro i
    apply Finset.card_pos.mp
    rw [InducedCycle.card_vertices]
    have := hn i
    omega
  · exact hdis
  · intro i
    have h := induced_cycle_length_bound G (g := 96) hg (C i) (hn i)
    rw [InducedCycle.card_vertices]
    omega

end Se20Part
