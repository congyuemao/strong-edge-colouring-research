import Se20Insertion.Counting

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def TriviallySeparable (φ : PartialColouring H F) (e : W) (a b : Colour) : Prop :=
  ∀ x, φ.Neighbour e a x → φ.Free x b

theorem triviallySeparable_separable (φ : PartialColouring H F) {e : W} {a b : Colour}
    (hab : a ≠ b) (ht : φ.TriviallySeparable e a b) : φ.Separable e a b := by
  intro x y hx hy hconn
  obtain ⟨hxB, hyB, hr⟩ := hconn
  have hxy : (⟨x, hxB⟩ : φ.Bicoloured a b) ≠ ⟨y, hyB⟩ := by
    intro h
    have heq : x = y := congrArg Subtype.val h
    exact hab (hx.2.2.symm.trans ((congrArg φ.colour heq).trans hy.2.2))
  obtain ⟨z, hz⟩ := hr.nonempty_neighborSet_left hxy
  rcases z.2.2 with hza | hzb
  · exact φ.proper hx.1 z.2.1 hz (hx.2.2.trans hza.symm)
  · exact ht x hx ⟨z.val, z.2.1, hz, hzb⟩

/-- Lemma 11.6(1), with the weaker single-component hypothesis. -/
theorem single_saturated_of_no_trivial (φ : PartialColouring H F) {e f : W} {p : Colour}
    (hs : φ.Single e p f)
    (hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b) :
    ∀ q, q ≠ p → ∃ g, φ.Neighbour f q g := by
  intro q hqp
  by_contra hfree
  apply hnt p q hqp.symm
  intro x hx
  have hxf := hs.2 x hx
  subst x
  exact hfree

theorem single_saturated_of_stuck (φ : PartialColouring H F) {e f : W} {p : Colour}
    (hs : φ.Single e p f) (hst : φ.Stuck e) :
    ∀ q, q ≠ p → ∃ g, φ.Neighbour f q g :=
  φ.single_saturated_of_no_trivial hs (fun a b hab h => hst.2 a b hab (φ.triviallySeparable_separable hab h))

def restrict (φ : PartialColouring H F) (F' : Finset W) (h : F' ⊆ F) : PartialColouring H F' where
  colour := φ.colour
  proper := by
    intro x y hx hy hxy
    exact φ.proper (h hx) (h hy) hxy

theorem erase_single_free [DecidableEq W] (φ : PartialColouring H F) {e f : W} {p : Colour}
    (hs : φ.Single e p f) :
    (φ.restrict (F.erase f) (Finset.erase_subset _ _)).Free e p := by
  rintro ⟨x, hx, hex, hc⟩
  have hxf := hs.2 x ⟨Finset.mem_of_mem_erase hx, hex, hc⟩
  exact (Finset.mem_erase.mp hx).1 hxf

/-- The legal hole move: erase the unique `p`-neighbour and colour the hole `p`. -/
def holeMove [DecidableEq W] (φ : PartialColouring H F) {e f : W} {p : Colour}
    (hs : φ.Single e p f) : PartialColouring H (insert e (F.erase f)) :=
  (φ.restrict (F.erase f) (Finset.erase_subset _ _)).insertFree e p (φ.erase_single_free hs)

theorem holeMove_colour [DecidableEq W] (φ : PartialColouring H F) {e f : W} {p : Colour}
    (hs : φ.Single e p f) (x : W) :
    (φ.holeMove hs).colour x = if x = e then p else φ.colour x := rfl

theorem holeMove_single_reverse [DecidableEq W] (φ : PartialColouring H F)
    {e f : W} {p : Colour} (he : e ∉ F) (hs : φ.Single e p f) :
    (φ.holeMove hs).Single f p e := by
  have hef : e ≠ f := hs.1.2.1.ne
  refine ⟨⟨Finset.mem_insert_self _ _, hs.1.2.1.symm, by simp [holeMove_colour]⟩, ?_⟩
  intro x hx
  by_contra hxe
  have hxF : x ∈ F := Finset.mem_of_mem_erase ((Finset.mem_insert.mp hx.1).resolve_left hxe)
  have hxp : φ.colour x = p := by simpa [holeMove_colour, hxe] using hx.2.2
  exact φ.proper hs.1.1 hxF hx.2.1 (hs.1.2.2.trans hxp.symm)

theorem holeMove_reverse_domain [DecidableEq W] (φ : PartialColouring H F)
    {e f : W} {p : Colour} (he : e ∉ F) (hs : φ.Single e p f) :
    insert f ((insert e (F.erase f)).erase e) = F := by
  have hef : e ≠ f := hs.1.2.1.ne
  have he' : e ∉ F.erase f := fun h => he (Finset.mem_of_mem_erase h)
  rw [Finset.erase_insert he', Finset.insert_erase hs.1.1]

/-- Reversibility is equality on the coloured domain; unused values outside
the domain intentionally carry no mathematical meaning. -/
theorem holeMove_reverse [DecidableEq W] (φ : PartialColouring H F)
    {e f : W} {p : Colour} (he : e ∉ F) (hs : φ.Single e p f) :
    ∀ x ∈ F, ((φ.holeMove hs).holeMove (φ.holeMove_single_reverse he hs)).colour x = φ.colour x := by
  intro x hx
  have hxe : x ≠ e := fun h => he (h ▸ hx)
  by_cases hxf : x = f
  · subst x; simp [holeMove_colour, hs.1.2.2]
  · simp [holeMove_colour, hxe, hxf]

/-- Lemma 11.11: every colour class keeps its size under a hole move. -/
theorem holeMove_class_card [DecidableEq W] (φ : PartialColouring H F)
    {e f : W} {p : Colour} (he : e ∉ F) (hs : φ.Single e p f) (c : Colour) :
    ((insert e (F.erase f)).filter (fun x => (φ.holeMove hs).colour x = c)).card =
      (F.filter (φ.colour · = c)).card := by
  have hef : e ≠ f := hs.1.2.1.ne
  by_cases hcp : c = p
  · subst c
    have heq : (insert e (F.erase f)).filter (fun x => (φ.holeMove hs).colour x = p) =
        insert e ((F.filter (φ.colour · = p)).erase f) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      rw [holeMove_colour]
      by_cases hxe : x = e
      · subst x; simp
      · simp [hxe, and_assoc]
    rw [heq, Finset.card_insert_of_notMem (by simp [he])]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hs.1.1, hs.1.2.2⟩)
  · have heq : (insert e (F.erase f)).filter (fun x => (φ.holeMove hs).colour x = c) =
        F.filter (φ.colour · = c) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      rw [holeMove_colour]
      by_cases hxe : x = e
      · subst x; simp [he, Ne.symm hcp]
      · by_cases hxf : x = f
        · subst x; simp [hxe, hs.1.2.2, Ne.symm hcp]
        · simp [hxe, hxf]
    rw [heq]

theorem holeMove_blocked [DecidableEq W] (φ : PartialColouring H F)
    {e f : W} {p : Colour} (he : e ∉ F) (hs : φ.Single e p f) (hst : φ.Stuck e) :
    ∀ c, ∃ x, (φ.holeMove hs).Neighbour f c x := by
  intro c
  by_cases hcp : c = p
  · subst c
    exact ⟨e, (φ.holeMove_single_reverse he hs).1⟩
  · obtain ⟨x, hxF, hfx, hxc⟩ := φ.single_saturated_of_stuck hs hst c hcp
    have hxe : x ≠ e := fun h => he (h ▸ hxF)
    have hxf : x ≠ f := hfx.ne.symm
    exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxf, hxF⟩), hfx,
      by simpa [holeMove_colour, hxe] using hxc⟩

/-- Lemma 11.13: inseparability inherited at an adjacent single neighbour. -/
theorem inherited_inseparable (φ : PartialColouring H F) {e fp fa fb : W}
    {p a b : Colour} (hst : φ.Stuck e) (_hp : φ.Single e p fp)
    (ha : φ.Single e a fa) (hb : φ.Single e b fb) (hab : a ≠ b)
    (hpa : H.Adj fp fa) (hpb : H.Adj fp fb) : ¬ φ.Separable fp a b := by
  intro hsep
  apply hst.2 a b hab
  intro x y hx hy hconn
  have hxa := ha.2 x hx
  have hyb := hb.2 y hy
  subst x; subst y
  exact hsep fa fb ⟨ha.1.1, hpa, ha.1.2.2⟩ ⟨hb.1.1, hpb, hb.1.2.2⟩ hconn

theorem KempeClosed.component_mem {φ : PartialColouring H F} {a b : Colour} {S : Set W}
    (hS : φ.KempeClosed a b S) {x y : W} (hx : x ∈ S)
    (hxy : φ.SameComponent a b x y) : y ∈ S := by
  obtain ⟨hxB, hyB, ⟨walk⟩⟩ := hxy
  have go : ∀ {u v : φ.Bicoloured a b}, (φ.KempeGraph a b).Walk u v → u.val ∈ S → v.val ∈ S := by
    intro u v w
    induction w with
    | nil => exact fun h => h
    | @cons u z v huz w ih => exact fun hu => ih (hS.2 hu z.2 huz)
  exact go walk hx

theorem holeMove_preserves_neighbour [DecidableEq W] (φ : PartialColouring H F)
    {e f r x : W} {p c : Colour} (he : e ∉ F) (hs : φ.Single e p f)
    (hx : φ.Neighbour r c x) (hxf : x ≠ f) : (φ.holeMove hs).Neighbour r c x := by
  have hxe : x ≠ e := fun h => he (h ▸ hx.1)
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxf, hx.1⟩), hx.2.1,
    by simpa [holeMove_colour, hxe] using hx.2.2⟩

theorem holeMove_preserves_bicoloured [DecidableEq W] (φ : PartialColouring H F)
    {e f x : W} {p a b : Colour} (he : e ∉ F) (hs : φ.Single e p f)
    (hx : x ∈ φ.Bicoloured a b) (hxf : x ≠ f) :
    x ∈ (φ.holeMove hs).Bicoloured a b := by
  have hxe : x ≠ e := fun h => he (h ▸ hx.1)
  refine ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxf, hx.1⟩), ?_⟩
  simpa [holeMove_colour, hxe] using hx.2

/-- Lemma 11.12: a pair involving the moved colour cannot free the new hole. -/
theorem holeMove_inseparable_moved_colour [DecidableEq W] (φ : PartialColouring H F)
    {e f : W} {p q : Colour} (he : e ∉ F) (hs : φ.Single e p f)
    (hst : φ.Stuck e) (hpq : p ≠ q) : ¬ (φ.holeMove hs).Separable f p q := by
  intro hsep
  let ψ := φ.holeMove hs
  have hfout : f ∉ insert e (F.erase f) := by simp [hs.1.2.1.ne.symm]
  have heB : e ∈ ψ.Bicoloured p q :=
    ⟨Finset.mem_insert_self _ _, Or.inl (by simp [ψ, holeMove_colour])⟩
  let S : Set W := {x | x ∈ φ.Bicoloured p q ∧ ψ.SameComponent p q e x}
  have hclosed : φ.KempeClosed p q S := by
    refine ⟨fun _ hx => hx.1, ?_⟩
    intro x y hx hy hxy
    have hxnew : x ∈ ψ.Bicoloured p q := hx.2.choose_spec.choose
    have hxf : x ≠ f := fun h => hfout (h ▸ hxnew.1)
    by_cases hyf : y = f
    · subst y
      have hxq : φ.colour x = q := hx.1.2.resolve_left (by
        intro hxp
        exact φ.proper hx.1.1 hs.1.1 hxy (hxp.trans hs.1.2.2.symm))
      have hnew : ψ.Neighbour f q x := φ.holeMove_preserves_neighbour he hs
        ⟨hx.1.1, hxy.symm, hxq⟩ hxf
      exact False.elim (hsep e x (φ.holeMove_single_reverse he hs).1 hnew hx.2)
    · have hynew := φ.holeMove_preserves_bicoloured he hs hy hyf
      exact ⟨hy, hx.2.trans (ψ.sameComponent_of_adj hxnew hynew hxy)⟩
  apply hst.2 p q hpq
  intro x y hx hy hconn
  have hxf := hs.2 x hx
  subst x
  have hyf : y ≠ f := by
    intro h
    exact hpq (hs.1.2.2.symm.trans (h ▸ hy.2.2))
  have hyB : y ∈ φ.Bicoloured p q := ⟨hy.1, Or.inr hy.2.2⟩
  have hynew := φ.holeMove_preserves_bicoloured he hs hyB hyf
  have hyS : y ∈ S := ⟨hyB, ψ.sameComponent_of_adj heB hynew hy.2.1⟩
  have hfS := hclosed.component_mem hyS hconn.symm
  exact hfout hfS.2.choose_spec.choose.1

end PartialColouring
end Se20Insertion
