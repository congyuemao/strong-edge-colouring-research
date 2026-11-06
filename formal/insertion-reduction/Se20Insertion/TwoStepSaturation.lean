import Se20Insertion.HoleStateEquivalence
import Se20Insertion.ReachabilityCounting

noncomputable section
open scoped Classical
namespace Se20Insertion.PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

/-- Fill the current hole after at most k actual singleton hole moves. -/
inductive HoleFillWithin : {F : Finset W} → PartialColouring H F → W → ℕ → Prop
  | fill {F : Finset W} (φ : PartialColouring H F) (e : W) (k : ℕ)
      {c : Colour} (hc : φ.Free e c) : HoleFillWithin φ e k
  | move {F : Finset W} (φ : PartialColouring H F) {e f : W} {p : Colour} {k : ℕ}
      (he : e ∉ F) (hs : φ.Single e p f)
      (ht : HoleFillWithin (φ.holeMove hs) f k) : HoleFillWithin φ e (k+1)

/-- Every bounded repair produces a proper colouring of the entire extended domain. -/
theorem HoleFillWithin.insert {φ : PartialColouring H F} {e : W} {k : ℕ}
    (h : φ.HoleFillWithin e k) : Nonempty (PartialColouring H (insert e F)) := by
  induction h with
  | fill φ e k hc => exact ⟨φ.insertFree e _ hc⟩
  | @move F φ e f p k he hs ht ih =>
    obtain ⟨ψ⟩ := ih
    have hd : Insert.insert f (Insert.insert e (F.erase f)) = Insert.insert e F := by
      rw [Finset.insert_comm,Finset.insert_erase hs.1.1]
    exact ⟨ψ.restrict _ (by rw [hd])⟩

theorem holeFillWithin_blocked (φ : PartialColouring H F) {e : W} {k : ℕ}
    (hn : ¬ φ.HoleFillWithin e k) : ∀ c, ∃ x, φ.Neighbour e c x := by
  intro c
  by_contra hc
  exact hn (.fill φ e k hc)

theorem holeMove_single_other (φ : PartialColouring H F) {e f g v : W}
    {p q : Colour} (he : e ∉ F) (hs : φ.Single e p f)
    (hq : q ≠ p) (ht : φ.Single v q g) : (φ.holeMove hs).Single v q g := by
  have hc := (φ.holeMove_same_other_classes he hs).neighbour (a := q) (by simp [hq])
  exact ⟨(hc v g).mp ht.1, fun x hx => ht.2 x ((hc v x).mpr hx)⟩

theorem holeMove_free_other (φ : PartialColouring H F) {e f v : W}
    {p c : Colour} (he : e ∉ F) (hs : φ.Single e p f)
    (hc : c ≠ p) (hf : φ.Free v c) : (φ.holeMove hs).Free v c := by
  rintro ⟨x,hx⟩
  exact hf ⟨x,((φ.holeMove_same_other_classes he hs).neighbour (by simp [hc]) v x).mpr hx⟩

theorem one_step_static_saturated (φ : PartialColouring H F) {e f : W} {p : Colour}
    (he : e ∉ F) (hn : ¬ φ.HoleFillWithin e 2) (hs : φ.Single e p f) :
    ∀ c, c ≠ p → ∃ x, φ.Neighbour f c x := by
  intro c hcp
  by_contra hc
  exact hn (.move φ he hs (.fill _ f 1 (φ.holeMove_free_other he hs hcp hc)))

/-- P4: saturation of every static two-step target, in the original colouring.
The obstruction premise concerns filling after actual moves, not Kempe swaps. -/
theorem two_step_static_saturated (φ : PartialColouring H F) {e f g : W}
    {p q : Colour} (he : e ∉ F) (hn : ¬ φ.HoleFillWithin e 2)
    (hs : φ.Single e p f) (ht : φ.Single f q g) :
    ∀ c, c ≠ q → ∃ x, φ.Neighbour g c x := by
  have hqp : q ≠ p := by
    intro h
    exact φ.proper hs.1.1 ht.1.1 ht.1.2.1 (hs.1.2.2.trans (ht.1.2.2.trans h).symm)
  have hf : f ∉ insert e (F.erase f) := by simp [hs.1.2.1.ne.symm]
  have ht' := φ.holeMove_single_other he hs hqp ht
  intro c hcq
  by_cases hcp : c = p
  · subst c
    exact ⟨f,hs.1.1,ht.1.2.1.symm,hs.1.2.2⟩
  · by_contra hc
    have hc' := φ.holeMove_free_other he hs hcp hc
    have hc'' := (φ.holeMove hs).holeMove_free_other hf ht' hcq hc'
    exact hn (.move φ he hs (.move _ hf ht' (.fill _ g 0 hc'')))

/-- Static singleton distance at most two, without a distinct-colours convention. -/
def StaticWithinTwo (φ : PartialColouring H F) (e x : W) : Prop :=
  x = e ∨ (∃ p, φ.Single e p x) ∨
    ∃ p q f, φ.Single e p f ∧ φ.Single f q x

theorem propositionP4 (φ : PartialColouring H F) {e : W}
    (he : e ∉ F) (hn : ¬ φ.HoleFillWithin e 2) {x : W}
    (hx : φ.StaticWithinTwo e x) :
    ∀ c, (x ∉ F ∨ c ≠ φ.colour x) → ∃ y, φ.Neighbour x c y := by
  rcases hx with rfl | ⟨p,hs⟩ | ⟨p,q,f,hs,ht⟩
  · exact fun c _ => φ.holeFillWithin_blocked hn c
  · intro c hc
    apply φ.one_step_static_saturated he hn hs c
    rcases hc with h | h
    · exact (h hs.1.1).elim
    · simpa [hs.1.2.2] using h
  · intro c hc
    apply φ.two_step_static_saturated he hn hs ht c
    rcases hc with h | h
    · exact (h ht.1.1).elim
    · simpa [ht.1.2.2] using h

end Se20Insertion.PartialColouring
