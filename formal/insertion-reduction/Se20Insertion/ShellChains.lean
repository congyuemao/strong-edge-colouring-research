import Se20Insertion.TreePattern
import Se20Insertion.ForestSeparation

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- 11.4(1), in a form that also allows overlapping ambient shells:
a colour absent from the inner cover must be supplied by the outer shell. -/
theorem single_shell_cover {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    {e f : G.edgeSet} {u v : V} (hf : f.val = s(u,v))
    (hs : φ.Single e (φ.colour f) f)
    (hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b)
    {c : Colour} (hc : c ≠ φ.colour f)
    (hinner : c ∉ (((incident G u).erase f ∪ starBase G u).image φ.colour)) :
    ∃ x ∈ shell G u v, x ∈ F ∧ φ.colour x = c := by
  obtain ⟨x,hx⟩ := φ.single_saturated_of_no_trivial hs hnt c hc
  have hm := (mem_conflicts G f x).mpr hx.2.1
  rw [conflicts_star_decomposition G f hf] at hm
  exact ⟨x,(Finset.mem_union.mp hm).resolve_left (fun h => hinner (Finset.mem_image.mpr ⟨x,h,hx.2.2⟩)),hx.1,hx.2.2⟩

/-- 11.4(2): every shell edge conflicts with each edge at its branch root. -/
theorem shell_branch_conflicts {u v : V} (huv : G.Adj u v)
    {s f : G.edgeSet} (hs : s ∈ shell G u v) (hf : v ∈ f.val) : (L2 G).Adj f s := by
  apply shell_conflicts_branch G huv hs hf
  intro h
  obtain ⟨w,_,hs⟩ := Finset.mem_biUnion.mp hs
  exact (Finset.mem_sdiff.mp hs).2 ((mem_incident G v s).mpr (h ▸ hf))

end Se20Insertion

namespace Se20Insertion.PartialColouring
variable {V : Type*} {G : SimpleGraph V} {F : Finset G.edgeSet}

/-- An internal edge of a two-colour chain between single representatives
avoids the closed vertex neighbourhood of both endpoints of the hole. -/
theorem single_chain_avoids_closed_neighbourhood (φ : PartialColouring (L2 G) F)
    {e f g z : G.edgeSet} {u v : V} (he : e.val = s(u,v)) (heF : e ∉ F)
    {a b : Colour} (hf : φ.Single e a f) (hg : φ.Single e b g)
    (hz : z ∈ φ.Bicoloured a b) (hzf : z ≠ f) (hzg : z ≠ g) :
    ∀ w ∈ z.val, w ≠ u ∧ w ≠ v ∧ ¬ G.Adj u w ∧ ¬ G.Adj v w := by
  have hze : z ≠ e := fun h => heF (h ▸ hz.1)
  have hnot : ¬ (L2 G).Adj e z := by
    intro h
    rcases hz.2 with ha | hb
    · exact hzf (hf.2 z ⟨hz.1,h,ha⟩)
    · exact hzg (hg.2 z ⟨hz.1,h,hb⟩)
  intro w hw
  refine ⟨?_,?_,?_,?_⟩
  · intro h; exact hnot ⟨hze.symm,u,he ▸ Sym2.mem_mk_left u v,w,hw,Or.inl h.symm⟩
  · intro h; exact hnot ⟨hze.symm,v,he ▸ Sym2.mem_mk_right u v,w,hw,Or.inl h.symm⟩
  · intro h; exact hnot ⟨hze.symm,u,he ▸ Sym2.mem_mk_left u v,w,hw,Or.inr h⟩
  · intro h; exact hnot ⟨hze.symm,v,he ▸ Sym2.mem_mk_right u v,w,hw,Or.inr h⟩

theorem stuck_single_chain (φ : PartialColouring (L2 G) F)
    {e f g : G.edgeSet} (hs : φ.Stuck e) {a b : Colour} (hab : a ≠ b)
    (hf : φ.Single e a f) (hg : φ.Single e b g) : φ.SameComponent a b f g := by
  by_contra hn
  apply hs.2 a b hab
  intro x y hx hy
  simpa [hf.2 x hx,hg.2 y hy] using hn

end Se20Insertion.PartialColouring
