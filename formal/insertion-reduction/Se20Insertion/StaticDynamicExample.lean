import Se20Insertion.ParametricCore
import Se20Insertion.ReachabilityCounting
import Se20Insertion.TwoStepSaturation

namespace Se20Insertion.StaticDynamicExample
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The seven-vertex P3 graph, with the manuscript's hub numbered 6. -/
def graph : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet
  ({s(0,1),s(1,2),s(2,3),s(3,4),s(4,0),s(6,0),s(6,1),s(6,2),s(6,3),s(6,4),s(5,3),s(5,4)} :
    Finset (Sym2 (Fin 7)))

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def colour : Fin 7 → Fin 3 := ![0,1,2,0,2,1,0]
def domain : Finset (Fin 7) := Finset.univ.erase 6

def colouring : Parametric.PartialColouring 3 graph domain where
  colour := colour
  proper := by decide

theorem saturated : ∀ x : Fin 7, ∀ a : Fin 3,
    (x = 6 ∨ a ≠ colour x) → ∃ y, colouring.Neighbour x a y := by
  unfold Parametric.PartialColouring.Neighbour colouring
  decide

/-- Taking R to be all seven vertices makes static closure automatic. -/
theorem static_double :
    colouring.Single 0 1 1 ∧ colouring.Single 2 1 1 ∧
    colouring.Single 1 2 2 ∧ ¬ graph.Adj 0 2 := by
  unfold Parametric.PartialColouring.Single Parametric.PartialColouring.Neighbour colouring
  decide

theorem first_single : colouring.Single 6 1 1 := by
  unfold Parametric.PartialColouring.Single Parametric.PartialColouring.Neighbour colouring
  decide

def afterFirst := colouring.holeMove first_single

theorem second_single : afterFirst.Single 1 0 0 := by
  unfold Parametric.PartialColouring.Single Parametric.PartialColouring.Neighbour
  decide

def afterSecond := afterFirst.holeMove second_single

/-- The root 0 really is reached, but the old (0,1,2) double has been destroyed. -/
theorem transported_double_destroyed :
    (6 : Fin 7) ∉ domain ∧
    (1 : Fin 7) ∉ insert 6 (domain.erase 1) ∧
    afterSecond.colour 6 = 1 ∧ afterSecond.colour 1 = 0 ∧
    ¬ afterSecond.Single 2 1 1 := by
  unfold Parametric.PartialColouring.Single Parametric.PartialColouring.Neighbour
  decide

theorem not_three_colourable : ¬ graph.Colorable 3 := by
  rintro ⟨c⟩
  have h : ∀ a b d e f z : Fin 3,
      a ≠ b → b ≠ d → d ≠ e → e ≠ f → f ≠ a →
      z ≠ a → z ≠ b → z ≠ d → z ≠ e → z ≠ f → False := by
    intro a b d e f z
    omega
  exact h (c 0) (c 1) (c 2) (c 3) (c 4) (c 6)
    (c.valid (by decide)) (c.valid (by decide)) (c.valid (by decide))
    (c.valid (by decide)) (c.valid (by decide)) (c.valid (by decide))
    (c.valid (by decide)) (c.valid (by decide)) (c.valid (by decide)) (c.valid (by decide))

/-- The P3 lift: join all old vertices to a new clique of size seventeen. -/
def liftedGraph : SimpleGraph (Fin 7 ⊕ Fin 17) where
  Adj x y := match x,y with
    | .inl i,.inl j => graph.Adj i j
    | .inr i,.inr j => i ≠ j
    | _,_ => True
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all [SimpleGraph.adj_comm,ne_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance : DecidableRel liftedGraph.Adj := by
  intro x y; cases x <;> cases y <;> dsimp only [liftedGraph] <;> infer_instance

def liftedColour : Fin 7 ⊕ Fin 17 → Colour
  | .inl x => ⟨(colour x).val,by have := (colour x).isLt; omega⟩
  | .inr j => ⟨j.val + 3,by omega⟩

def liftedDomain : Finset (Fin 7 ⊕ Fin 17) := Finset.univ.erase (.inl 6)

def liftedColouring : PartialColouring liftedGraph liftedDomain where
  colour := liftedColour
  proper := by decide

theorem lifted_saturated : liftedColouring.SaturatedOn Finset.univ := by
  unfold PartialColouring.SaturatedOn PartialColouring.Neighbour liftedColouring
  decide

theorem lifted_single_closed : liftedColouring.SingleClosed Finset.univ := by
  intro x hx y hy; exact Finset.mem_univ _

theorem lifted_double : liftedColouring.DoubleHoleConfig (.inl 0) (.inl 1) (.inl 2) := by
  unfold PartialColouring.DoubleHoleConfig PartialColouring.Single PartialColouring.Neighbour
  decide

theorem lifted_first_single : liftedColouring.Single (.inl 6) 1 (.inl 1) := by
  unfold PartialColouring.Single PartialColouring.Neighbour
  decide

noncomputable def liftedAfterFirst := liftedColouring.holeMove lifted_first_single

theorem lifted_second_single : liftedAfterFirst.Single (.inl 1) 0 (.inl 0) := by
  unfold PartialColouring.Single PartialColouring.Neighbour
  decide

noncomputable def liftedAfterSecond := liftedAfterFirst.holeMove lifted_second_single

theorem lifted_transport_destroyed :
    (.inl 6 : Fin 7 ⊕ Fin 17) ∉ liftedDomain ∧
    (.inl 1 : Fin 7 ⊕ Fin 17) ∉ insert (.inl 6) (liftedDomain.erase (.inl 1)) ∧
    (.inl 0 : Fin 7 ⊕ Fin 17) ∉ insert (.inl 1)
      ((insert (.inl 6) (liftedDomain.erase (.inl 1))).erase (.inl 0)) ∧
    ¬ liftedAfterSecond.Single (.inl 2) 1 (.inl 1) := by
  unfold PartialColouring.Single PartialColouring.Neighbour
  decide

/-- An odd cycle cannot use a two-element palette. -/
theorem five_cycle_not_two {C : Type*} [DecidableEq C] (A : Finset C)
    (hA : A.card ≤ 2) (c : Fin 5 → C) (hc : ∀ i, c i ∈ A)
    (h01 : c 0 ≠ c 1) (h12 : c 1 ≠ c 2) (h23 : c 2 ≠ c 3)
    (h34 : c 3 ≠ c 4) (h40 : c 4 ≠ c 0) : False := by
  have hsub : ({c 0,c 1} : Finset C) ⊆ A := by simp [Finset.insert_subset_iff,hc]
  have heq : ({c 0,c 1} : Finset C) = A := Finset.eq_of_subset_of_card_le hsub (by simp [h01]; exact hA)
  have hmem (i : Fin 5) : c i = c 0 ∨ c i = c 1 := by
    have hi := hc i
    rw [← heq] at hi
    simpa using hi
  have h2 : c 2 = c 0 := (hmem 2).resolve_right h12.symm
  have h3 : c 3 = c 1 := (hmem 3).resolve_left (by simpa [h2] using h23.symm)
  have h4 : c 4 = c 0 := (hmem 4).resolve_right (by simpa [h3] using h34.symm)
  exact h40 h4

theorem lifted_not_twenty_colourable : ¬ liftedGraph.Colorable 20 := by
  classical
  rintro ⟨c⟩
  let T := (Finset.univ : Finset (Fin 17)).image (fun j => c (.inr j))
  have hi : Function.Injective (fun j : Fin 17 => c (.inr j)) := by
    intro i j heq
    by_contra hn
    exact c.valid (show liftedGraph.Adj (.inr i) (.inr j) from hn) heq
  have hT : T.card = 17 := by rw [Finset.card_image_of_injective _ hi]; simp
  have hhub : c (.inl 6) ∉ T := by
    intro hm
    obtain ⟨j,hj,hjc⟩ := Finset.mem_image.mp hm
    exact c.valid (show liftedGraph.Adj (.inr j) (.inl 6) from trivial) hjc
  let A : Finset Colour := Finset.univ \ insert (c (.inl 6)) T
  have hA : A.card = 2 := by simp [A,Finset.card_sdiff,Finset.card_insert_of_notMem hhub,hT]
  let d : Fin 5 → Colour := fun i => c (.inl ⟨i.val,by omega⟩)
  have hub_adj : ∀ i : Fin 7, i.val < 5 → graph.Adj i 6 := by decide
  have hd (i : Fin 5) : d i ∈ A := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with hh | ht
    · have hadj : liftedGraph.Adj (.inl ⟨i.val,by omega⟩) (.inl 6) := by
        exact hub_adj ⟨i.val,by omega⟩ i.isLt
      exact c.valid hadj hh
    · obtain ⟨j,hj,hjc⟩ := Finset.mem_image.mp ht
      exact c.valid (show liftedGraph.Adj (.inr j) (.inl ⟨i.val,by omega⟩) from trivial) hjc
  exact five_cycle_not_two A hA.le d hd
    (c.valid (show liftedGraph.Adj (.inl 0) (.inl 1) from by decide))
    (c.valid (show liftedGraph.Adj (.inl 1) (.inl 2) from by decide))
    (c.valid (show liftedGraph.Adj (.inl 2) (.inl 3) from by decide))
    (c.valid (show liftedGraph.Adj (.inl 3) (.inl 4) from by decide))
    (c.valid (show liftedGraph.Adj (.inl 4) (.inl 0) from by decide))

theorem lifted_degree_bound (x : Fin 7 ⊕ Fin 17) : liftedGraph.degree x ≤ 23 := by
  have h := liftedGraph.degree_lt_card_verts x
  have hn : Fintype.card (Fin 7 ⊕ Fin 17) = 24 := by decide
  rw [hn] at h
  omega

/-- P3 in the same twenty-colour palette as the insertion development.
The root of the displayed double is reachable by the two checked moves above. -/
theorem propositionP3 : liftedColouring.SaturatedOn Finset.univ ∧
    liftedColouring.SingleClosed Finset.univ ∧
    liftedColouring.DoubleHoleConfig (.inl 0) (.inl 1) (.inl 2) ∧
    ¬ liftedGraph.Colorable 20 :=
  ⟨lifted_saturated,lifted_single_closed,lifted_double,lifted_not_twenty_colourable⟩

/-- A second colouring of the same graph supplies the depth-three P4 obstruction. -/
def depthThreeColour : Fin 7 ⊕ Fin 17 → Colour
  | .inl x => ⟨(![0,1,2,0,1,2,0] x : Fin 3).val,by
      have := (![0,1,2,0,1,2,0] x : Fin 3).isLt; omega⟩
  | .inr j => ⟨j.val + 3,by omega⟩

def depthThreeColouring : PartialColouring liftedGraph liftedDomain where
  colour := depthThreeColour
  proper := by decide

theorem depth_three_static :
    depthThreeColouring.Single (.inl 6) 2 (.inl 2) ∧
    depthThreeColouring.Single (.inl 2) 1 (.inl 1) ∧
    depthThreeColouring.Single (.inl 1) 0 (.inl 0) ∧
    depthThreeColouring.Free (.inl 0) 2 := by
  unfold PartialColouring.Single PartialColouring.Free PartialColouring.Neighbour
  decide

theorem depth_three_no_repair (k : ℕ) :
    ¬ depthThreeColouring.HoleFillWithin (.inl 6) k := by
  intro h
  obtain ⟨ψ⟩ := h.insert
  have hd : insert (.inl 6) liftedDomain = Finset.univ := by simp [liftedDomain]
  apply lifted_not_twenty_colourable
  refine ⟨SimpleGraph.Coloring.mk ψ.colour ?_⟩
  intro x y hxy
  exact ψ.proper (by rw [hd]; simp) (by rw [hd]; simp) hxy

noncomputable def depthAfterFirst := depthThreeColouring.holeMove depth_three_static.1

theorem depth_second_single : depthAfterFirst.Single (.inl 2) 1 (.inl 1) := by
  unfold PartialColouring.Single PartialColouring.Neighbour
  decide

noncomputable def depthAfterSecond := depthAfterFirst.holeMove depth_second_single

theorem depth_third_single : depthAfterSecond.Single (.inl 1) 0 (.inl 0) := by
  unfold PartialColouring.Single PartialColouring.Neighbour
  decide

/-- The original missing colour 2 is supplied by the recoloured hub after three moves. -/
theorem depth_three_missing_colour_changed :
    (depthAfterSecond.holeMove depth_third_single).Neighbour (.inl 0) 2 (.inl 6) := by
  unfold PartialColouring.Neighbour
  decide

end Se20Insertion.StaticDynamicExample
