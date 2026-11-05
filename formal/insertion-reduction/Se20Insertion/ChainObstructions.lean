import Se20Insertion.SingleChains
import Se20Insertion.SupportCounts

noncomputable section
open scoped Classical
namespace Se20Insertion.PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

theorem chainEnd_append (e : W) (l r : List (Colour × W)) :
    chainEnd e (l ++ r) = chainEnd (chainEnd e l) r := by
  induction l generalizing e with
  | nil => rfl
  | cons t l ih => exact ih t.2

theorem singleChain_append (φ : PartialColouring H F) {e f : W} {p : Colour}
    {l : List (Colour × W)} :
    φ.SingleChain e (l ++ [(p,f)]) ↔
      φ.SingleChain e l ∧ φ.Single (chainEnd e l) p f ∧ p ∉ l.map Prod.fst := by
  induction l generalizing e with
  | nil => simp [SingleChain,chainEnd]
  | cons t l ih =>
    rcases t with ⟨q,g⟩
    simp only [List.cons_append,SingleChain,chainEnd,List.map_append,List.map_cons,
      List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or,ih]
    tauto

theorem singleChain_colours_nodup (φ : PartialColouring H F) {e : W}
    {l : List (Colour × W)} (hc : φ.SingleChain e l) : (l.map Prod.fst).Nodup := by
  induction l generalizing e with
  | nil => simp
  | cons t l ih => exact List.nodup_cons.mpr ⟨hc.2.1,ih hc.2.2⟩

/-- Theorem 11.7 for every chain length, using actual legal transport. -/
theorem singleChain_insertion (φ : PartialColouring H F) {e : W} (he : e ∉ F)
    {l : List (Colour × W)} (hc : φ.SingleChain e l) {a b : Colour}
    (hab : a ≠ b) (ha : a ∉ l.map Prod.fst) (hb : b ∉ l.map Prod.fst)
    (hs : φ.Separable (chainEnd e l) a b) :
    Nonempty (PartialColouring H (insert e F)) := by
  obtain ⟨ψ,hψ⟩ := φ.singleChain_transport he hc
  have haY : a ∈ Finset.univ \ l.toFinset.image Prod.fst := by simpa using ha
  have hbY : b ∈ Finset.univ \ l.toFinset.image Prod.fst := by simpa using hb
  have hsep : ψ.Separable (chainEnd e l) a b := by
    intro x y hx hy hxy
    exact hs x y ((hψ.neighbour haY _ _).mpr hx) ((hψ.neighbour hbY _ _).mpr hy)
      ((hψ.sameComponent haY hbY _ _).mpr hxy)
  obtain ⟨θ⟩ := ψ.insert_of_separable hab hsep
  have hmem : chainEnd e l ∈ insert e F := Finset.mem_insert.mpr (φ.singleChain_end_mem hc)
  exact ⟨θ.restrict _ (by rw [Finset.insert_erase hmem])⟩

def NoChainRepair (φ : PartialColouring H F) (e : W) (k : ℕ) : Prop :=
  ∀ l : List (Colour × W), l.length ≤ k → φ.SingleChain e l →
    ∀ a b, a ≠ b → a ∉ l.map Prod.fst → b ∉ l.map Prod.fst →
      ¬ φ.Separable (chainEnd e l) a b

/-- Corollary 11.8(1). The last-colour boundary is repaired by using the
preceding prefix and the pair (last moved colour, missing colour). -/
theorem chain_obstruction_saturated (φ : PartialColouring H F) {e : W} {k : ℕ}
    (hno : φ.NoChainRepair e k) {l : List (Colour × W)}
    (hl : l.length ≤ k) (hc : φ.SingleChain e l) :
    ∀ c, c ∉ l.map Prod.fst → ∃ x, φ.Neighbour (chainEnd e l) c x := by
  intro c hcl
  by_contra hfree
  cases l using List.reverseRecOn with
  | nil =>
    obtain ⟨b,hb⟩ := exists_ne c
    apply hno [] (by simp) hc c b hb.symm (by simp) (by simp)
    intro x y hx hy hxy
    exact hfree ⟨x,hx⟩
  | append_singleton l t =>
    rcases t with ⟨p,f⟩
    obtain ⟨hpref,hs,hp⟩ := φ.singleChain_append.mp hc
    have hcp : c ≠ p := by
      intro h; subst c; exact hcl (by simp)
    have hcpref : c ∉ l.map Prod.fst := fun h => hcl (by simp [h])
    apply hno l (by simp only [List.length_append,List.length_singleton] at hl; omega) hpref p c hcp.symm hp hcpref
    apply φ.triviallySeparable_separable hcp.symm
    intro x hx
    have hxf := hs.2 x hx
    subst x
    simpa only [Free,chainEnd_append,chainEnd] using hfree

theorem chain_obstruction_nonseparable (φ : PartialColouring H F) {e : W} {k : ℕ}
    (hno : φ.NoChainRepair e k) {l : List (Colour × W)}
    (hl : l.length ≤ k) (hc : φ.SingleChain e l) {a b : Colour}
    (hab : a ≠ b) (ha : a ∉ l.map Prod.fst) (hb : b ∉ l.map Prod.fst) :
    ¬ φ.Separable (chainEnd e l) a b := hno l hl hc a b hab ha hb

/-- Each unused single colour really extends the original static chain. -/
theorem chain_extend (φ : PartialColouring H F) {e f : W} {l : List (Colour × W)}
    (hc : φ.SingleChain e l) {c : Colour} (hcY : c ∉ l.map Prod.fst)
    (hs : φ.Single (chainEnd e l) c f) : φ.SingleChain e (l ++ [(c,f)]) :=
  φ.singleChain_append.mpr ⟨hc,hs,hcY⟩

/-- Lemma 11.10, allowing a different free target at each member of the class. -/
def recolourClassTargets (φ : PartialColouring H F) (B : Set W) (y : Colour)
    (hB : ∀ x ∈ B, x ∈ F ∧ φ.colour x = y) (c : W → Colour)
    (hf : ∀ x ∈ B, φ.Free x (c x)) : PartialColouring H F where
  colour x := if x ∈ B then c x else φ.colour x
  proper := by
    intro x z hx hz hxz heq
    by_cases hxB : x ∈ B <;> by_cases hzB : z ∈ B
    · exact φ.proper hx hz hxz ((hB x hxB).2.trans (hB z hzB).2.symm)
    · exact hf x hxB ⟨z,hz,hxz,by simpa [hxB,hzB] using heq.symm⟩
    · exact hf z hzB ⟨x,hx,hxz.symm,by simpa [hxB,hzB] using heq⟩
    · exact φ.proper hx hz hxz (by simpa [hxB,hzB] using heq)

end Se20Insertion.PartialColouring

namespace Se20Insertion
open PartialColouring

/-- Corollary 11.8(2), now with saturation derived from chain obstruction. -/
theorem chain_obstruction_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    {e : G.edgeSet} {k : ℕ} (hno : φ.NoChainRepair e k)
    {l : List (Colour × G.edgeSet)} (hl : l.length ≤ k) (hc : φ.SingleChain e l) :
    let Y := l.toFinset.image Prod.fst
    16 - 2 * l.length ≤ ((Finset.univ \ Y).filter (fun c =>
      ((φ.colouredNeighbours (chainEnd e l)).filter (φ.colour · = c)).card = 1)).card := by
  dsimp only
  have hY : (l.toFinset.image Prod.fst).card = l.length := by
    have heq : l.toFinset.image Prod.fst = (l.map Prod.fst).toFinset := by ext c; simp
    rw [heq, List.toFinset_card_of_nodup (φ.singleChain_colours_nodup hc)]
    simp
  have hb : ∀ c ∉ l.toFinset.image Prod.fst, ∃ x, φ.Neighbour (chainEnd e l) c x := by
    intro c h
    exact φ.chain_obstruction_saturated hno hl hc c (by simpa using h)
  have hcount := outside_colours_single_count G hΔ φ (chainEnd e l)
    (l.toFinset.image Prod.fst) hb
  rw [hY] at hcount
  omega

end Se20Insertion
