import Se20Part.PathCounting

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
set_option maxHeartbeats 2000000

abbrev Segment {V : Type*} (G : SimpleGraph V) (n : ℕ) :=
  Σ u v : V, {p : G.Path u v // p.val.length = n}

def Segment.walk {V : Type*} {G : SimpleGraph V} {n : ℕ} (Y : Segment G n) :
    G.Walk Y.1 Y.2.1 := Y.2.2.val.val

theorem Segment.isPath {V : Type*} {G : SimpleGraph V} {n : ℕ} (Y : Segment G n) :
    Y.walk.IsPath := Y.2.2.val.property

theorem Segment.length {V : Type*} {G : SimpleGraph V} {n : ℕ} (Y : Segment G n) :
    Y.walk.length = n := Y.2.2.property

theorem Segment.support_injective {V : Type*} {G : SimpleGraph V} {n : ℕ} :
    Function.Injective (fun Y : Segment G n => Y.walk.support) := by
  rintro ⟨u,v,p,hp⟩ ⟨u',v',q,hq⟩ he
  have hu : u = u' := by
    have hh := congrArg List.head? he
    simpa only [Segment.walk,List.head?_eq_some_head (Walk.support_ne_nil _),Walk.head_support,
      Option.some.injEq] using hh
  have hv : v = v' := by
    have hh := congrArg List.getLast? he
    simpa only [Segment.walk,List.getLast?_eq_getLast (Walk.support_ne_nil _),Walk.getLast_support,
      Option.some.injEq] using hh
  subst u'
  subst v'
  have hh : p = q := Subtype.ext (Walk.ext_support he)
  subst q
  rfl

theorem walkVertexLists_card_pos {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (n : ℕ) (u : V) :
    (walkVertexLists G (n+1) u).card ≤ 4 * 3^n := by
  calc
    _ ≤ ∑ v : G.neighborSet u, ((forwardVertexLists G n u v.val).image (List.cons v.val)).card := card_biUnion_le
    _ ≤ ∑ _v : G.neighborSet u, 3^n := by
      apply sum_le_sum
      intro v _
      exact card_image_le.trans (forwardVertexLists_card hd n v.property)
    _ ≤ 4 * 3^n := by
      simp only [sum_const,card_univ,nsmul_eq_mul,G.card_neighborSet_eq_degree]
      exact Nat.mul_le_mul_right _ (hd u)

theorem rootedPathLists_card_three {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (n k : ℕ) (hk : k ≤ n) (z : V) :
    (rootedPathLists G n k z).card ≤ 3 * 3^n := by
  have hb : (rootedPathLists G n k z).card ≤
      (walkVertexLists G k z).card * (walkVertexLists G (n-k) z).card := by
    calc
      _ ≤ ∑ l ∈ walkVertexLists G k z,
          ((walkVertexLists G (n-k) z).image (fun r => (z::l).reverse ++ r)).card := card_biUnion_le
      _ ≤ ∑ _l ∈ walkVertexLists G k z, (walkVertexLists G (n-k) z).card :=
        sum_le_sum (fun _ _ => card_image_le)
      _ = _ := by simp
  cases k with
  | zero =>
    simp only [walkVertexLists,card_singleton,one_mul,Nat.sub_zero] at hb
    exact hb.trans ((walkVertexLists_card hd n z).trans (by omega))
  | succ k =>
    have hc := hb.trans (Nat.mul_le_mul (walkVertexLists_card_pos hd k z)
      (walkVertexLists_card hd (n-(k+1)) z))
    have he : k+(n-(k+1))+1 = n := by omega
    have heq : (4*3^k)*(2*3^(n-(k+1))) = 8*3^(k+(n-(k+1))) := by
      rw [pow_add]; ring
    rw [heq] at hc
    have hpow : 3^n = 3^(k+(n-(k+1)))*3 := by conv_lhs => rw [← he,pow_succ]
    rw [hpow]
    omega

abbrev RootSegment {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) (n k d : ℕ) :=
  {Y : Segment G n // e ∈ projectedCandidates G Y.walk k d}

theorem rootSegment_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (e : G.edgeSet) (n k d : ℕ) (hk : k ≤ n) :
    Fintype.card (RootSegment G e n k d) ≤ 6 * 3^d * 3^n := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep e.val
  have hab : G.Adj a b := by simpa [← he] using e.property
  let gates := forwardEnds G d a b ∪ forwardEnds G d b a
  let paths := gates.biUnion (rootedPathLists G n k)
  have hmem (Y : RootSegment G e n k d) : Y.val.walk.support ∈ paths := by
    obtain ⟨P,hpos,hdepth⟩ := Y.property
    have hg := projection_gate_mem Y.val.walk he.symm P
    rw [hpos,hdepth] at hg
    apply mem_biUnion.mpr
    refine ⟨Y.val.walk.getVert k,hg,?_⟩
    have hh := path_mem_rootedPathLists Y.val.walk Y.val.isPath k (by rw [Y.val.length]; exact hk)
    simpa only [Y.val.length] using hh
  let φ : RootSegment G e n k d → paths := fun Y => ⟨Y.val.walk.support,hmem Y⟩
  have hi : Function.Injective φ := by
    intro Y Z h
    exact Subtype.ext (Segment.support_injective (congrArg Subtype.val h))
  have hg : gates.card ≤ 2*3^d :=
    (card_union_le _ _).trans ((Nat.add_le_add (forwardEnds_card hd d hab) (forwardEnds_card hd d hab.symm)).trans (by omega))
  calc
    _ ≤ Fintype.card paths := Fintype.card_le_of_injective φ hi
    _ = paths.card := Fintype.card_coe _
    _ ≤ ∑ z ∈ gates, (rootedPathLists G n k z).card := card_biUnion_le
    _ ≤ ∑ _z ∈ gates, 3*3^n := sum_le_sum (fun z _ => rootedPathLists_card_three hd n k hk z)
    _ = gates.card * (3*3^n) := by simp
    _ ≤ (2*3^d)*(3*3^n) := Nat.mul_le_mul_right _ hg
    _ = _ := by ring

end Se20Part
