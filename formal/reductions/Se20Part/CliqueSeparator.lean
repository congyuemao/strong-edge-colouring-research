import Se20Part.GallaiLowBlocks
import Mathlib.Logic.Equiv.Fintype

noncomputable section
open scoped Classical
namespace Se20Part

/-- Colourings of two sides agree after a palette permutation on their
complete intersection. All adjacency tests remain in the original graph. -/
theorem colourable_of_clique_separator {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (A B : Finset W)
    (hcover : A ∪ B = Finset.univ) (hcl : H.IsClique (↑(A ∩ B) : Set W))
    (hsep : ∀ a ∈ A, a ∉ B → ∀ b ∈ B, b ∉ A → ¬ H.Adj a b)
    (hA : (H.induce (A : Set W)).Colorable k)
    (hB : (H.induce (B : Set W)).Colorable k) : H.Colorable k := by
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  let f : (A ∩ B : Finset W) → Fin k := fun x => cB ⟨x.val,(Finset.mem_inter.mp x.prop).2⟩
  let g : (A ∩ B : Finset W) → Fin k := fun x => cA ⟨x.val,(Finset.mem_inter.mp x.prop).1⟩
  have hf : Function.Injective f := by
    intro x y he
    by_contra hn
    have hadj : (H.induce (B : Set W)).Adj
        ⟨x.val,(Finset.mem_inter.mp x.prop).2⟩ ⟨y.val,(Finset.mem_inter.mp y.prop).2⟩ :=
      hcl x.prop y.prop (fun h => hn (Subtype.ext h))
    exact cB.valid hadj he
  have hg : Function.Injective g := by
    intro x y he
    by_contra hn
    have hadj : (H.induce (A : Set W)).Adj
        ⟨x.val,(Finset.mem_inter.mp x.prop).1⟩ ⟨y.val,(Finset.mem_inter.mp y.prop).1⟩ :=
      hcl x.prop y.prop (fun h => hn (Subtype.ext h))
    exact cA.valid hadj he
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have inB : ∀ x, x ∉ A → x ∈ B := by
    intro x hx
    have h : x ∈ A ∪ B := hcover ▸ Finset.mem_univ x
    exact (Finset.mem_union.mp h).resolve_left hx
  have hagree (x : W) (hxA : x ∈ A) (hxB : x ∈ B) :
      p (cB ⟨x,hxB⟩) = cA ⟨x,hxA⟩ := hp ⟨x,Finset.mem_inter.mpr ⟨hxA,hxB⟩⟩
  let c : W → Fin k := fun x => if hx : x ∈ A then cA ⟨x,hx⟩ else p (cB ⟨x,inB x hx⟩)
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro x y hxy
  dsimp only [c]
  split_ifs with hx hy hy
  · exact cA.valid hxy
  · have hxB : x ∈ B := by
      by_contra hn
      exact hsep x hx hn y (inB y hy) hy hxy
    rw [← hagree x hx hxB]
    exact fun he => cB.valid
      (show (H.induce (B : Set W)).Adj ⟨x,hxB⟩ ⟨y,inB y hy⟩ from hxy) (p.injective he)
  · have hyB : y ∈ B := by
      by_contra hn
      exact hsep y hy hn x (inB x hx) hx hxy.symm
    rw [← hagree y hy hyB]
    exact fun he => cB.valid
      (show (H.induce (B : Set W)).Adj ⟨x,inB x hx⟩ ⟨y,hyB⟩ from hxy) (p.injective he)
  · exact fun he => cB.valid
      (show (H.induce (B : Set W)).Adj ⟨x,inB x hx⟩ ⟨y,inB y hy⟩ from hxy) (p.injective he)

/-- A vertex-minimal non-k-colourable graph has no complete separator.
This supplies the palette-gluing step used in the S08 ball argument. -/
theorem minimal_noncolourable_no_clique_separator {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hmin : VertexMinimalNoncolourable H k)
    (A B : Finset W) (hA : (B \ A).Nonempty) (hB : (A \ B).Nonempty)
    (hcover : A ∪ B = Finset.univ) (hcl : H.IsClique (↑(A ∩ B) : Set W))
    (hsep : ∀ a ∈ A, a ∉ B → ∀ b ∈ B, b ∉ A → ¬ H.Adj a b) : False := by
  have smaller (T : Finset W) (hT : ∃ x, x ∉ T) : T.card < Fintype.card W := by
    by_contra! hn
    have he : T = Finset.univ := Finset.eq_univ_of_card _
      (Nat.le_antisymm (Finset.card_le_univ T) hn)
    obtain ⟨x,hx⟩ := hT
    exact hx (he ▸ Finset.mem_univ x)
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  exact hmin.1 (colourable_of_clique_separator H k A B hcover hcl hsep
    (hmin.2 A (smaller A ⟨a,(Finset.mem_sdiff.mp ha).2⟩))
    (hmin.2 B (smaller B ⟨b,(Finset.mem_sdiff.mp hb).2⟩)))

end Se20Part
