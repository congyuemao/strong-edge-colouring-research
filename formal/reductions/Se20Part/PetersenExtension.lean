import Se20Part.PetersenKernel
import Se20Part.GraphBasics
import Se20Part.DiffuseSaturation

noncomputable section
open scoped Classical
namespace Se20Part
local instance petersenExtensionDecEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- An induced original-graph embedding preserves and reflects conflicts. -/
def conflictEmbedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) : L2 G ↪g L2 H where
  toFun := f.mapEdgeSet
  inj' := SimpleGraph.Hom.mapEdgeSet.injective f.toHom f.injective
  map_rel_iff' := L2_embedding_adj_iff f _ _

def embeddingFinsetIso {U W : Type*} [Fintype U] {Q : SimpleGraph U} {H : SimpleGraph W}
    (f : Q ↪g H) : Q ≃g H.induce (↑(Finset.univ.image f) : Set W) := by
  have hr : (↑(Finset.univ.image f) : Set W) = Set.range f := by
    ext w
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
  rw [hr]
  exact f.isoInduceRange

def petersenInternalEdges {V : Type*} {G : SimpleGraph V}
    (f : PetersenGraph ↪g G) : Finset G.edgeSet := Finset.univ.image f.mapEdgeSet

def embeddingOnFinsetIso {U W : Type*} {Q : SimpleGraph U} {H : SimpleGraph W}
    (f : Q ↪g H) (B : Finset W) (hB : ∀ w, w ∈ B ↔ ∃ u, f u = w) :
    Q ≃g H.induce (B : Set W) := by
  have hr : (B : Set W) = Set.range f := by ext w; exact hB w
  rw [hr]
  exact f.isoInduceRange

/-- Every induced Petersen block extends an arbitrary fixed colouring of
edges outside its fifteen internal edges. No ambient girth is needed. -/
theorem induced_petersen_extension {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (f : PetersenGraph ↪g G)
    (A : Finset G.edgeSet) (hdis : Disjoint A (petersenInternalEdges f))
    (φ : PartialColouring (L2 G) A) :
    ∃ θ : PartialColouring (L2 G) (A ∪ petersenInternalEdges f),
      ∀ a ∈ A, θ.colour a = φ.colour a := by
  have hi := embeddingOnFinsetIso (conflictEmbedding f) (petersenInternalEdges f)
    (by intro e; simp only [petersenInternalEdges, Finset.mem_image, Finset.mem_univ, true_and]; rfl)
  apply threePart_five_block_extension (L2 G) (conflict_degree_le_twentyFour G hΔ)
    A (petersenInternalEdges f) hdis
    (petersenConflictIso.trans hi) φ

/-- A reducible block is disjoint from every critical edge set. -/
theorem critical21_disjoint_of_extension {V : Type*} [Fintype V] (G : SimpleGraph V)
    (B : Finset G.edgeSet)
    (hext : ∀ A : Finset G.edgeSet, Disjoint A B →
      ∀ φ : PartialColouring (L2 G) A, Nonempty (PartialColouring (L2 G) (A ∪ B)))
    {F : Finset G.edgeSet} (hF : Critical21 G F) : Disjoint F B := by
  apply Finset.disjoint_left.mpr
  intro e heF heB
  obtain ⟨φ⟩ := (partialColouring_iff_colourable (L2 G) _).mpr (hF.2.2 e heF)
  let ψ : PartialColouring (L2 G) (F \ B) :=
    ⟨φ.colour,by
      intro x y hx hy hxy
      obtain ⟨hxF,hxB⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hyF,hyB⟩ := Finset.mem_sdiff.mp hy
      apply φ.proper (y := y) (x := x) _ _ hxy
      · simp only [Finset.mem_erase]
        exact ⟨fun h => hxB (h ▸ heB),hxF⟩
      · simp only [Finset.mem_erase]
        exact ⟨fun h => hyB (h ▸ heB),hyF⟩⟩
  obtain ⟨θ⟩ := hext (F \ B) Finset.sdiff_disjoint ψ
  apply hF.2.1
  apply (partialColouring_iff_colourable (L2 G) F).mp
  have hcover : F ⊆ (F \ B) ∪ B := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_right _ hxB
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx,hxB⟩)
  exact ⟨⟨θ.colour,fun _ _ hx hy hxy => θ.proper (hcover hx) (hcover hy) hxy⟩⟩

theorem critical21_disjoint_induced_petersen {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (f : PetersenGraph ↪g G)
    {F : Finset G.edgeSet} (hF : Critical21 G F) : Disjoint F (petersenInternalEdges f) := by
  apply critical21_disjoint_of_extension G _ _ hF
  intro A hA φ
  obtain ⟨θ,_⟩ := induced_petersen_extension G hΔ f A hA φ
  exact ⟨θ⟩

end Se20Part
