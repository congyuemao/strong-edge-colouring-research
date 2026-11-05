import Se20Part.TriangleInsertion
import Se20Part.Greedy

noncomputable section
open scoped Classical
namespace Se20Part

/-- Vertex-critical 21-colourability in the fixed ambient conflict graph. -/
def Critical21 {V : Type*} (G : SimpleGraph V) (F : Finset G.edgeSet) : Prop :=
  ((L2 G).induce (F : Set G.edgeSet)).Colorable 21 ∧
  ¬ ((L2 G).induce (F : Set G.edgeSet)).Colorable 20 ∧
  ∀ e ∈ F, ((L2 G).induce (F.erase e : Set G.edgeSet)).Colorable 20

/-- G09: a 21-critical edge set contains no edge of an ambient triangle. -/
theorem critical21_no_triangle {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet} (hF : Critical21 G F)
    {e : G.edgeSet} (he : e ∈ F) : ¬ OnTriangle G e := by
  intro ht
  obtain ⟨φ⟩ := (partialColouring_iff_colourable (L2 G) (F.erase e)).mpr (hF.2.2 e he)
  obtain ⟨ψ,_⟩ := triangle_insertion G hΔ φ e (Finset.notMem_erase e F) ht
  apply hF.2.1
  apply (partialColouring_iff_colourable (L2 G) F).mp
  exact ⟨Finset.insert_erase he ▸ ψ⟩

/-- The extension conclusion behind G09, for any family of triangle edges.
The conflicts are still tested in G, including edges outside F. -/
theorem triangle_reducibility {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (F T : Finset G.edgeSet) (hTF : T ⊆ F)
    (hT : ∀ e ∈ T, OnTriangle G e)
    (hc : ((L2 G).induce ((F \ T : Finset G.edgeSet) : Set G.edgeSet)).Colorable 20) :
    ((L2 G).induce (F : Set G.edgeSet)).Colorable 20 := by
  apply (partialColouring_iff_colourable (L2 G) F).mp
  apply triangle_edges_last G hΔ F T hTF hT
  exact (partialColouring_iff_colourable (L2 G) (F \ T)).mpr hc

theorem critical21_min_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    {F : Finset G.edgeSet} (hF : Critical21 G F) {e : G.edgeSet} (he : e ∈ F) :
    20 ≤ (F.filter ((L2 G).Adj e)).card := by
  obtain ⟨φ⟩ := (partialColouring_iff_colourable (L2 G) (F.erase e)).mpr (hF.2.2 e he)
  have blocked (a : Colour) : ∃ f, φ.Neighbour e a f := by
    by_contra ha
    have hfree : φ.Free e a := ha
    have ψ := φ.insertFree e a hfree
    apply hF.2.1
    apply (partialColouring_iff_colourable (L2 G) F).mp
    exact ⟨Finset.insert_erase he ▸ ψ⟩
  have himage : (F.filter ((L2 G).Adj e)).image φ.colour = Finset.univ := by
    ext a
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨f,hf,hef,hfa⟩ := blocked a
    exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr
      ⟨(Finset.mem_erase.mp hf).2,hef⟩,hfa⟩
  have h := Finset.card_image_le (s := F.filter ((L2 G).Adj e)) (f := φ.colour)
  simpa [himage] using h

end Se20Part
