import Se20Insertion.LocalRepairs

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Se20Insertion.PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

/-- The manuscript's static chain: each next colour is single in the original
colouring, and the moved colours are pairwise distinct. -/
def SingleChain (φ : PartialColouring H F) : W → List (Colour × W) → Prop
  | _, [] => True
  | e, (p,f)::l => φ.Single e p f ∧ p ∉ l.map Prod.fst ∧ φ.SingleChain f l

def chainEnd : W → List (Colour × W) → W
  | e, [] => e
  | _, (_,f)::l => chainEnd f l

theorem singleChain_end_mem (φ : PartialColouring H F) {e : W} {l : List (Colour × W)}
    (hc : φ.SingleChain e l) : chainEnd e l = e ∨ chainEnd e l ∈ F := by
  induction l generalizing e with
  | nil => exact Or.inl rfl
  | cons t l ih =>
    rcases t with ⟨p,f⟩
    rcases ih hc.2.2 with h | h
    · right; change chainEnd f l ∈ F; rw [h]; exact hc.1.1.1
    · exact Or.inr h

theorem singleChain_congr {F' : Finset W} (φ : PartialColouring H F)
    (ψ : PartialColouring H F') {e : W} {l : List (Colour × W)}
    (hc : φ.SingleChain e l)
    (hclasses : ∀ c ∈ l.map Prod.fst, ∀ x v, φ.Neighbour v c x ↔ ψ.Neighbour v c x) :
    ψ.SingleChain e l := by
  induction l generalizing e with
  | nil => trivial
  | cons t l ih =>
    rcases t with ⟨p,f⟩
    have hp := hclasses p (by simp)
    refine ⟨⟨(hp f e).mp hc.1.1, ?_⟩, hc.2.1, ?_⟩
    · intro x hx; exact hc.1.2 x ((hp x e).mpr hx)
    · exact ih hc.2.2 (fun c h => hclasses c (by simp [h]))

/-- Execute the whole static chain as legal hole moves. The conclusion retains
every originally coloured edge except the final hole. -/
theorem singleChain_transport (φ : PartialColouring H F) {e : W}
    (he : e ∉ F) {l : List (Colour × W)} (hc : φ.SingleChain e l) :
    ∃ ψ : PartialColouring H ((insert e F).erase (chainEnd e l)),
      φ.SameYClasses ψ (Finset.univ \ l.toFinset.image Prod.fst) := by
  induction l generalizing F e with
  | nil =>
    refine ⟨φ.restrict _ (by simp [chainEnd, he]), ?_⟩
    intro a ha x; simp [restrict, chainEnd, he]
  | cons t l ih =>
    rcases t with ⟨p,f⟩
    let χ := φ.holeMove hc.1
    have hf : f ∉ insert e (F.erase f) := by simp [hc.1.1.2.1.ne.symm]
    have hm : φ.SameYClasses χ (Finset.univ.erase p) := by
      intro a ha x
      have hpa : p ≠ a := (Finset.mem_erase.mp ha).1.symm
      by_cases hxe : x = e
      · subst x; simp [χ, he, holeMove_colour, hpa]
      · by_cases hxf : x = f
        · subst x; simp [χ, holeMove_colour, hxe, hc.1.1.2.2, hpa]
        · simp [χ, holeMove_colour, hxe, hxf]
    have hc' : χ.SingleChain f l := φ.singleChain_congr χ hc.2.2 (by
      intro a ha x v
      exact hm.neighbour (by simp only [Finset.mem_erase, Finset.mem_univ, and_true]
                             exact fun h => hc.2.1 (h ▸ ha)) v x)
    obtain ⟨ψ, hψ⟩ := ih χ hf hc'
    have hd : insert f (insert e (F.erase f)) = insert e F := by
      rw [Finset.insert_comm, Finset.insert_erase hc.1.1.1]
    refine ⟨ψ.restrict _ (by simp only [chainEnd, hd]; exact Finset.Subset.refl _), ?_⟩
    intro a ha x
    have hap : a ≠ p := by
      intro h; subst a
      exact (Finset.mem_sdiff.mp ha).2 (by simp)
    have hal : a ∈ Finset.univ \ l.toFinset.image Prod.fst := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hm
      exact (Finset.mem_sdiff.mp ha).2 (by simpa using Finset.mem_insert_of_mem hm)
    have h₁ := hm a (by simp [hap]) x
    have h₂ := hψ a hal x
    change (x ∈ F ∧ φ.colour x = a) ↔
      (x ∈ (insert e F).erase (chainEnd f l) ∧ ψ.colour x = a)
    rw [← hd]
    exact h₁.trans h₂

/-- Corollary 11.23, including at most one further recolouring after transport. -/
theorem singleChain_triangle {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    {e : G.edgeSet} (he : e ∉ F) {l : List (Colour × G.edgeSet)}
    (hc : φ.SingleChain e l) (ht : OnTriangle G (chainEnd e l)) :
    ∃ ψ : PartialColouring (L2 G) ((insert e F).erase (chainEnd e l)),
      ∃ θ : PartialColouring (L2 G) (insert e F),
        (((insert e F).erase (chainEnd e l)).filter
          (fun x => θ.colour x ≠ ψ.colour x)).card ≤ 1 := by
  classical
  obtain ⟨ψ, _⟩ := φ.singleChain_transport he hc
  obtain ⟨θ, hθ⟩ := triangle_insertion G hΔ ψ (chainEnd e l) (by simp) ht
  have hmem : chainEnd e l ∈ insert e F :=
    Finset.mem_insert.mpr (φ.singleChain_end_mem hc)
  have hd := Finset.insert_erase hmem
  refine ⟨ψ, θ.restrict _ (by rw [hd]), ?_⟩
  exact hθ

end Se20Insertion.PartialColouring
