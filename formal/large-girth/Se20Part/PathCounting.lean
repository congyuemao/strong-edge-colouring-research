import Se20Part.EmbeddingCounts

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
set_option maxHeartbeats 1000000

def forwardVertexLists {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ → V → V → Finset (List V)
  | 0, _, _ => {[]}
  | n+1, u, v => univ.biUnion (fun w : Forward G u v =>
      (forwardVertexLists G n v w.val).image (List.cons w.val))

theorem forwardVertexLists_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (n : ℕ) {u v : V} (huv : G.Adj u v) :
    (forwardVertexLists G n u v).card ≤ 3^n := by
  induction n generalizing u v with
  | zero => simp [forwardVertexLists]
  | succ n ih =>
    calc
      _ ≤ ∑ w : Forward G u v, ((forwardVertexLists G n v w.val).image (List.cons w.val)).card := card_biUnion_le
      _ ≤ ∑ _w : Forward G u v, 3^n := by
        apply sum_le_sum
        intro w _
        exact card_image_le.trans (ih w.property.1)
      _ ≤ 3 * 3^n := by
        simp only [sum_const,card_univ,nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (forward_card_le_three hd huv)
      _ = _ := by rw [pow_succ]; omega

theorem path_mem_forwardVertexLists {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v w : V} (p : G.Walk v w) (hp : p.IsPath) (hu : u ∉ p.support) :
    p.support.tail ∈ forwardVertexLists G p.length u v := by
  induction p generalizing u with
  | nil => simp [forwardVertexLists]
  | @cons v x w hvx p ih =>
    have hh := (Walk.cons_isPath_iff hvx p).mp hp
    have hxu : x ≠ u := by
      intro h
      apply hu
      simp only [Walk.support_cons,List.mem_cons]
      exact Or.inr (h ▸ p.start_mem_support)
    simp only [Walk.length_cons,forwardVertexLists,mem_biUnion,mem_univ,true_and,
      Walk.support_cons,List.tail_cons]
    refine ⟨⟨x,hvx,hxu⟩,mem_image.mpr ⟨p.support.tail,ih hh.1 hh.2,?_⟩⟩
    exact p.cons_tail_support

def walkVertexLists {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ → V → Finset (List V)
  | 0, _ => {[]}
  | n+1, u => univ.biUnion (fun v : G.neighborSet u =>
      (forwardVertexLists G n u v.val).image (List.cons v.val))

theorem walkVertexLists_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (n : ℕ) (u : V) : (walkVertexLists G n u).card ≤ 2 * 3^n := by
  cases n with
  | zero => norm_num [walkVertexLists]
  | succ n =>
    calc
      _ ≤ ∑ v : G.neighborSet u, ((forwardVertexLists G n u v.val).image (List.cons v.val)).card := card_biUnion_le
      _ ≤ ∑ _v : G.neighborSet u, 3^n := by
        apply sum_le_sum
        intro v _
        exact card_image_le.trans (forwardVertexLists_card hd n v.property)
      _ ≤ 4 * 3^n := by
        simp only [sum_const,card_univ,nsmul_eq_mul,G.card_neighborSet_eq_degree]
        exact Nat.mul_le_mul_right _ (hd u)
      _ ≤ _ := by rw [pow_succ]; omega

theorem path_mem_walkVertexLists {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.support.tail ∈ walkVertexLists G p.length u := by
  cases p with
  | nil => simp [walkVertexLists]
  | @cons u w v huw p =>
    have hh := (Walk.cons_isPath_iff huw p).mp hp
    simp only [Walk.length_cons,walkVertexLists,mem_biUnion,mem_univ,true_and,
      Walk.support_cons,List.tail_cons]
    refine ⟨⟨w,huw⟩,mem_image.mpr ⟨p.support.tail,path_mem_forwardVertexLists p hh.1 hh.2,?_⟩⟩
    exact p.cons_tail_support

def forwardEnds {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ) (u v : V) : Finset V :=
  (forwardVertexLists G n u v).image (fun l => (v::l).getLast (by simp))

theorem forwardEnds_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (n : ℕ) {u v : V} (huv : G.Adj u v) :
    (forwardEnds G n u v).card ≤ 3^n :=
  card_image_le.trans (forwardVertexLists_card hd n huv)

theorem path_end_mem_forwardEnds {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v w : V} (p : G.Walk v w) (hp : p.IsPath) (hu : u ∉ p.support) :
    w ∈ forwardEnds G p.length u v := by
  apply mem_image.mpr
  refine ⟨p.support.tail,path_mem_forwardVertexLists p hp hu,?_⟩
  simp only [Walk.cons_tail_support,Walk.getLast_support]

theorem projection_gate_mem {V : Type*} [Fintype V] {G : SimpleGraph V} {a b u v : V}
    (Y : G.Walk u v) {r : G.edgeSet} (he : r.val = s(a,b)) (P : EdgeProjection Y r) :
    Y.getVert P.pos ∈ forwardEnds G P.depth a b ∪ forwardEnds G P.depth b a := by
  have hab : G.Adj a b := by simpa [he] using r.property
  have hmem : P.endpoint = a ∨ P.endpoint = b := by simpa [he] using P.mem
  rcases hmem with h | h
  · have ho : b ∉ P.stem.support := P.other_endpoint_notMem (by simp [he]) (by simpa [h] using hab.ne.symm)
    have hh := path_end_mem_forwardEnds P.stem P.stem_isPath ho
    rw [P.length_stem] at hh
    exact mem_union_right _ (by simpa only [h] using hh)
  · have ho : a ∉ P.stem.support := P.other_endpoint_notMem (by simp [he]) (by simpa [h] using hab.ne)
    have hh := path_end_mem_forwardEnds P.stem P.stem_isPath ho
    rw [P.length_stem] at hh
    exact mem_union_left _ (by simpa only [h] using hh)

def rootedPathLists {V : Type*} [Fintype V] (G : SimpleGraph V) (n k : ℕ) (z : V) : Finset (List V) :=
  (walkVertexLists G k z).biUnion (fun l =>
    (walkVertexLists G (n-k) z).image (fun r => (z::l).reverse ++ r))

theorem rootedPathLists_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (n k : ℕ) (hk : k ≤ n) (z : V) :
    (rootedPathLists G n k z).card ≤ 4 * 3^n := by
  calc
    _ ≤ ∑ l ∈ walkVertexLists G k z,
        ((walkVertexLists G (n-k) z).image (fun r => (z::l).reverse ++ r)).card := card_biUnion_le
    _ ≤ ∑ _l ∈ walkVertexLists G k z, 2 * 3^(n-k) := by
      apply sum_le_sum
      intro l _
      exact card_image_le.trans (walkVertexLists_card hd _ _)
    _ = (walkVertexLists G k z).card * (2*3^(n-k)) := by simp
    _ ≤ (2*3^k) * (2*3^(n-k)) := Nat.mul_le_mul_right _ (walkVertexLists_card hd _ _)
    _ = _ := by rw [mul_mul_mul_comm,← pow_add,Nat.add_sub_of_le hk]; norm_num

theorem path_mem_rootedPathLists {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V}
    (Y : G.Walk u v) (hy : Y.IsPath) (k : ℕ) (hk : k ≤ Y.length) :
    Y.support ∈ rootedPathLists G Y.length k (Y.getVert k) := by
  have hl := path_mem_walkVertexLists (Y.take k).reverse (hy.take k).reverse
  have hr := path_mem_walkVertexLists (Y.drop k) (hy.drop k)
  have hlenl : (Y.take k).reverse.length = k := by simp [Walk.take_length,Nat.min_eq_left hk]
  have hlenr : (Y.drop k).length = Y.length-k := by simp
  rw [hlenl] at hl
  rw [hlenr] at hr
  apply mem_biUnion.mpr
  refine ⟨(Y.take k).reverse.support.tail,hl,mem_image.mpr ⟨(Y.drop k).support.tail,hr,?_⟩⟩
  rw [Walk.cons_tail_support,Walk.support_reverse,List.reverse_reverse]
  simpa only [Walk.support_append] using congrArg Walk.support (Y.append_take_drop_eq k)

end Se20Part
