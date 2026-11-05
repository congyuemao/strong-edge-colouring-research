import Se20Part.Balls
import Se20Part.External

noncomputable section
open scoped Classical
namespace Se20Part

theorem EdgeWithin.symm {V : Type*} {G : SimpleGraph V} {k : ℕ} {e f : G.edgeSet}
    (h : EdgeWithin G k e f) : EdgeWithin G k f e := by
  obtain ⟨x,hx,y,hy,p,hp⟩ := h
  exact ⟨y,hy,x,hx,p.reverse,by simpa using hp⟩

def separationGraph {V I : Type*} (G : SimpleGraph V) (E : Set G.edgeSet)
    (part : E → I) (k : ℕ) : SimpleGraph E where
  Adj e f := part e ≠ part f ∧ EdgeWithin G k e.val f.val
  symm := ⟨by intro e f h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem separationGraph_degree {V I : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (E : Set G.edgeSet) (part : E → I) (k : ℕ) :
    DegreeLE (separationGraph G E part k) (3^(k+2)-3) := by
  intro e
  let f : (separationGraph G E part k).neighborSet e → edgeBall G e.val k := fun a =>
    ⟨a.val.val, (fun he => a.property.1 (congrArg part (Subtype.ext he.symm))), a.property.2⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : edgeBall G e.val k => x.val) h))
  have hc : Nat.card ((separationGraph G E part k).neighborSet e) ≤
      Nat.card (edgeBall G e.val k) := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf
  exact hc.trans (edgeBall_card_le hd e.val k)

/-- The Haxell step for any partition of candidate edges; odd-cycle geometry is not assumed. -/
theorem sparse_transversal {V I : Type} [Fintype V] [Fintype I]
    (hax : Haxell) {G : SimpleGraph V} (hd : MaxDegreeFour G)
    (E : Set G.edgeSet) (part : E → I) (hsurj : Function.Surjective part) (k : ℕ)
    (hsize : ∀ i, 2*(3^(k+2)-3) ≤ Fintype.card {e // part e = i}) :
    ∃ f : I → E, (∀ i, part (f i) = i) ∧
      ∀ i j, i ≠ j → ¬ EdgeWithin G k (f i).val (f j).val := by
  obtain ⟨f,hf,hi⟩ := hax E I (separationGraph G E part k) part (3^(k+2)-3)
    hsurj (separationGraph_degree hd E part k) hsize
  refine ⟨f,hf,?_⟩
  intro i j hij hclose
  exact hi i j hij ⟨by simpa [hf] using hij, hclose⟩

theorem sparse_transversal_eight {V I : Type} [Fintype V] [Fintype I]
    (hax : Haxell) {G : SimpleGraph V} (hd : MaxDegreeFour G)
    (E : Set G.edgeSet) (part : E → I) (hsurj : Function.Surjective part)
    (hsize : ∀ i, 39360 ≤ Fintype.card {e // part e = i}) :
    ∃ f : I → E, (∀ i, part (f i) = i) ∧
      ∀ i j, i ≠ j → ¬ EdgeWithin G 7 (f i).val (f j).val := by
  apply sparse_transversal hax hd E part hsurj 7
  norm_num
  exact hsize

theorem sparse_transversal_five {V I : Type} [Fintype V] [Fintype I]
    (hax : Haxell) {G : SimpleGraph V} (hd : MaxDegreeFour G)
    (E : Set G.edgeSet) (part : E → I) (hsurj : Function.Surjective part)
    (hsize : ∀ i, 1452 ≤ Fintype.card {e // part e = i}) :
    ∃ f : I → E, (∀ i, part (f i) = i) ∧
      ∀ i j, i ≠ j → ¬ EdgeWithin G 4 (f i).val (f j).val := by
  apply sparse_transversal hax hd E part hsurj 4
  norm_num
  exact hsize

/-- The transversal remark is valid when the parts really are fibers of a partition. -/
theorem haxell_degree_one {W I : Type} [Fintype W] [Fintype I] (hax : Haxell)
    (H : SimpleGraph W) (part : W → I) (hs : Function.Surjective part)
    (hd : DegreeLE H 1) (hp : ∀ i, 2 ≤ Fintype.card {v // part v = i}) :
    ∃ f : I → W, (∀ i, part (f i) = i) ∧
      ∀ i j, i ≠ j → ¬ H.Adj (f i) (f j) := by
  exact hax W I H part 1 hs hd (by simpa using hp)

end Se20Part
