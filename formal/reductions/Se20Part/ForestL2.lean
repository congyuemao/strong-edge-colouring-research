import Se20Part.GraphBasics
import Mathlib.Combinatorics.SimpleGraph.Acyclic

noncomputable section
open scoped Classical
namespace Se20Part
namespace ForestL2
variable {V : Type*} {G : SimpleGraph V}

def root (G : SimpleGraph V) (x : V) : V :=
  (G.connectedComponentMk x).nonempty_supp.some

def depth (G : SimpleGraph V) (x : V) : ℕ := G.dist (root G x) x

theorem root_reachable (x : V) : G.Reachable (root G x) x :=
  SimpleGraph.ConnectedComponent.exact (G.connectedComponentMk x).nonempty_supp.some_mem

theorem root_eq {x y : V} (h : G.Reachable x y) : root G x = root G y := by
  exact congrArg (fun C : G.ConnectedComponent => C.nonempty_supp.some)
    (SimpleGraph.ConnectedComponent.sound h)

theorem depth_adj (hG : G.IsAcyclic) {x y : V} (hxy : G.Adj x y) :
    depth G x = depth G y + 1 ∨ depth G y = depth G x + 1 := by
  have h := hG.dist_eq_dist_add_one_of_adj_of_reachable (root G x) hxy (root_reachable x)
  simpa only [depth, root_eq hxy.reachable] using h

theorem lower_neighbour_unique (hG : G.IsAcyclic) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hy : depth G y < depth G x) (hz : depth G z < depth G x) : y = z := by
  obtain ⟨p, hp, hplen⟩ := (root_reachable (G := G) x).exists_path_of_dist
  have hmem : ∀ w, G.Adj x w → depth G w < depth G x → w ∈ p.support := by
    intro w hxw hw
    by_contra hn
    obtain ⟨q,hq,hqlen⟩ := ((root_reachable (G := G) x).trans hxw.reachable).exists_path_of_dist
    have heq := hG.subsingleton_path (root G x) w |>.elim ⟨p.concat hxw, hp.concat hn hxw⟩ ⟨q,hq⟩
    have hl := congrArg (fun t : G.Path (root G x) w => t.val.length) heq
    simp only [SimpleGraph.Walk.length_concat] at hl
    rw [hplen, hqlen, root_eq hxw.reachable] at hl
    change depth G w < G.dist (root G x) x at hw
    rw [root_eq hxw.reachable] at hw
    unfold depth at hw
    omega
  exact (hG.eq_penultimate_of_adj_end hp hxy (hmem y hxy hy)).trans
    (hG.eq_penultimate_of_adj_end hp hxz (hmem z hxz hz)).symm

def height (G : SimpleGraph V) (e : G.edgeSet) : ℕ :=
  e.val.lift ⟨fun x y => max (depth G x) (depth G y), fun _ _ => max_comm _ _⟩

theorem depth_le_height {e : G.edgeSet} {x : V} (hx : x ∈ e.val) :
    depth G x ≤ height G e := by
  obtain ⟨y,he⟩ := Sym2.mem_iff_exists.mp hx
  simp [height, he]

theorem orient (hG : G.IsAcyclic) (e : G.edgeSet) :
    ∃ p c, e.val = s(p,c) ∧ G.Adj p c ∧ depth G c = depth G p + 1 ∧
      height G e = depth G c := by
  obtain ⟨x,y,he⟩ : ∃ x y, e.val = s(x,y) := Sym2.ind (fun x y => ⟨x,y,rfl⟩) e.val
  have hxy : G.Adj x y := G.mem_edgeSet.mp (he ▸ e.prop)
  rcases depth_adj hG hxy with hd | hd
  · exact ⟨y,x,he.trans Sym2.eq_swap,hxy.symm,hd,by simp [height, he, hd]⟩
  · exact ⟨x,y,he,hxy,hd,by simp [height, he, hd]⟩

theorem neighbour_cover (hG : G.IsAcyclic) {e f : G.edgeSet} {p c : V}
    (he : e.val = s(p,c)) (hpc : G.Adj p c) (hd : depth G c = depth G p + 1)
    (hf : height G f ≤ depth G c) (hef : (L2 G).Adj e f) :
    p ∈ f.val ∨ ∃ q ∈ f.val, G.Adj p q ∧ depth G q < depth G p := by
  have hbound : ∀ x ∈ f.val, depth G x ≤ depth G c :=
    fun x hx => (depth_le_height hx).trans hf
  have hat_top : ∀ x ∈ f.val, depth G x = depth G c → G.Adj p x → p ∈ f.val := by
    intro x hx hdx hpx
    obtain ⟨y,hfxy⟩ := Sym2.mem_iff_exists.mp hx
    have hxy : G.Adj x y := G.mem_edgeSet.mp (hfxy ▸ f.prop)
    have hby := hbound y (by simp [hfxy])
    have hstep := depth_adj hG hxy
    have hyp : y = p := lower_neighbour_unique hG hxy hpx.symm (by omega) (by omega)
    simp [hfxy, hyp]
  obtain ⟨_,t,ht,x,hx,htx⟩ := hef
  rcases (show t = p ∨ t = c by simpa [he, Sym2.mem_iff] using ht) with rfl | rfl
  · rcases htx with rfl | hpx
    · exact Or.inl hx
    · rcases depth_adj hG hpx with hdx | hdx
      · exact Or.inr ⟨x,hx,hpx,by omega⟩
      · exact Or.inl (hat_top x hx (by omega) hpx)
  · rcases htx with rfl | hcx
    · exact Or.inl (hat_top _ hx rfl hpc)
    · have hbx := hbound x hx
      have hstep := depth_adj hG hcx
      have hxp : x = p := lower_neighbour_unique hG hcx hpc.symm (by omega) (by omega)
      exact Or.inl (hxp ▸ hx)

theorem lower_neighbours_clique (hG : G.IsAcyclic) {e f k : G.edgeSet}
    (hf : height G f ≤ height G e) (hk : height G k ≤ height G e)
    (hef : (L2 G).Adj e f) (hek : (L2 G).Adj e k) (hfk : f ≠ k) :
    (L2 G).Adj f k := by
  obtain ⟨p,c,he,hpc,hd,hheight⟩ := orient hG e
  rw [hheight] at hf hk
  have hfc := neighbour_cover hG he hpc hd hf hef
  have hkc := neighbour_cover hG he hpc hd hk hek
  refine ⟨hfk, ?_⟩
  rcases hfc with hpf | ⟨q,hqf,hpq,hq⟩ <;>
    rcases hkc with hpk | ⟨r,hrk,hpr,hr⟩
  · exact ⟨p,hpf,p,hpk,Or.inl rfl⟩
  · exact ⟨p,hpf,r,hrk,Or.inr hpr⟩
  · exact ⟨q,hqf,p,hpk,Or.inr hpq.symm⟩
  · exact ⟨q,hqf,r,hrk,Or.inl (lower_neighbour_unique hG hpq hpr hq hr)⟩

/-- Every finite nonempty set has a simplicial vertex, even in an infinite forest. -/
theorem exists_simplicial (hG : G.IsAcyclic) (S : Finset G.edgeSet) (hS : S.Nonempty) :
    ∃ e ∈ S, ∀ f ∈ S, ∀ k ∈ S, (L2 G).Adj e f → (L2 G).Adj e k →
      f ≠ k → (L2 G).Adj f k := by
  obtain ⟨e,he,hm⟩ := S.exists_max_image (height G) hS
  exact ⟨e,he,fun f hf k hk => lower_neighbours_clique hG (hm f hf) (hm k hk)⟩

end ForestL2
end Se20Part
