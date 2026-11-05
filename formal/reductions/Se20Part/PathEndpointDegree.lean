import Se20Part.EvenPathExchange

noncomputable section
open scoped Classical
namespace Se20Part.Partition
variable {W C : Type*} [Fintype W] [Fintype C] (H : SimpleGraph W)

theorem EvenPathClosure.endpoint_degree_one {π : W → C} {e : W} {j : C}
    (P : EvenPathClosure H π e j) (i : Fin P.size)
    (hi : i.val = 0 ∨ i.val+1 = P.size) : degreeIn H π (P.vertex i) j = 1 := by
  let k : Fin P.size := ⟨if i.val = 0 then 1 else P.size-2, by
    have hh := P.two_le
    split_ifs <;> omega⟩
  have hk : i.val+1 = k.val ∨ k.val+1 = i.val := by
    dsimp [k]
    have hh := P.two_le
    split_ifs <;> omega
  have hset : (Finset.univ.filter (fun y => H.Adj (P.vertex i) y ∧ π y = j)) = {P.vertex k} := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨hadj,hcol⟩
      obtain ⟨l,rfl⟩ := P.closed_in_class i y hadj hcol
      have hl := (P.adj_iff i l).mp hadj
      have hlk : l = k := by
        apply Fin.ext
        dsimp [k]
        have hli := l.isLt
        have hii := i.isLt
        split_ifs <;> omega
      exact congrArg P.vertex hlk
    · rintro rfl
      exact ⟨(P.adj_iff i k).mpr hk,P.in_class k⟩
  rw [degreeIn_eq_card,hset]
  simp

/-- The degree-one conclusion, now from the entire even-path result rather
than from Φ₁ alone. -/
theorem zero_class_neighbour_degree_one {π : W → C} (hπ : MinimumTwo H π)
    (hbound : ∀ σ : W → C, Minimum H σ → ∀ v, degreeIn H σ v (σ v) ≤ 2)
    (e : W) (j : C) (hj : j ≠ π e)
    (hzero : degreeIn H π e j = degreeIn H π e (π e))
    (hodd : ¬ ((monochrome H π).connectedComponentMk e).toSimpleGraph.Colorable 2)
    (y : W) (hey : H.Adj e y) (hy : π y = j) : degreeIn H π y j = 1 := by
  obtain ⟨P⟩ := zero_class_even_path H hπ hbound e j hj hzero hodd
  obtain ⟨i,rfl,hi⟩ := (P.neighbours y).mp ⟨hey,hy⟩
  exact P.endpoint_degree_one H i hi

end Se20Part.Partition
