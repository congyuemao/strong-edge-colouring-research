import Se20Insertion.NonseparatingPair
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace Se20Insertion.EighthPassExamples

abbrev square := SimpleGraph.cycleGraph 4

theorem square_connected : square.Connected := SimpleGraph.cycleGraph_connected

/-- C4 is two-connected: each single-vertex deletion remains connected. -/
theorem square_delete_connected (v : Fin 4) : (square.induce {x | x ≠ v}).Connected := by
  have paths : ∀ v x y : Fin 4, x ≠ v → y ≠ v →
      x = y ∨ square.Adj x y ∨ ∃ z, z ≠ v ∧ square.Adj x z ∧ square.Adj z y := by decide
  have others : ∀ v : Fin 4, ∃ x, x ≠ v := by decide
  obtain ⟨r,hr⟩ := others v
  refine { preconnected := ?_, nonempty := ⟨⟨r,hr⟩⟩ }
  intro x y
  rcases paths v x.val y.val x.prop y.prop with he | ha | ⟨z,hz,hxz,hzy⟩
  · exact Subtype.ext he ▸ SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (G := square.induce {x | x ≠ v}) ha
  · exact (SimpleGraph.Adj.reachable (G := square.induce {x | x ≠ v})
      (u := x) (v := ⟨z,hz⟩) hxz).trans
      (SimpleGraph.Adj.reachable (G := square.induce {x | x ≠ v})
        (u := ⟨z,hz⟩) (v := y) hzy)

theorem square_not_complete : ¬ square.Adj 0 2 := by decide

/-- The suggested pair-existence statement fails even for the even cycle C4. -/
theorem square_no_nonseparating_pair :
    ¬ ∃ u v r : Fin 4, u ≠ v ∧ ¬ square.Adj u v ∧ square.Adj r u ∧ square.Adj r v ∧
      (square.induce {x | x ∉ ({u,v} : Finset (Fin 4))}).Connected := by
  have noedges : ∀ u v x y : Fin 4, u ≠ v → ¬ square.Adj u v →
      x ∉ ({u,v} : Finset (Fin 4)) → y ∉ ({u,v} : Finset (Fin 4)) → ¬ square.Adj x y := by decide
  have two : ∀ u v : Fin 4, u ≠ v → ∃ x y,
      x ∉ ({u,v} : Finset (Fin 4)) ∧ y ∉ ({u,v} : Finset (Fin 4)) ∧ x ≠ y := by decide
  rintro ⟨u,v,r,huv,hn,_,_,hc⟩
  obtain ⟨x,y,hx,hy,hxy⟩ := two u v huv
  have he : square.induce {x | x ∉ ({u,v} : Finset (Fin 4))} = ⊥ := by
    ext a b
    exact iff_false_intro (noedges u v a.val b.val huv hn a.prop b.prop)
  have hr := hc ⟨x,hx⟩ ⟨y,hy⟩
  rw [he,SimpleGraph.reachable_bot] at hr
  exact hxy (congrArg Subtype.val hr)

end Se20Insertion.EighthPassExamples
