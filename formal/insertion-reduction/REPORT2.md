**One small omission was found in the written proof of Theorem 11.44.** The step “the partners all lie at one endpoint, hence `d(f) - s(f) ≤ 15`” needs a partner to exist. When `c(f) = 0`, there is no `w` from which to obtain the containment in `N[w]`. The desired bound on `c(f)` is immediate in this case. The formal proof handles it separately. This is an omitted case, not a counterexample to the theorem. No further mathematical error was found in the double move or the counting theorem.

**Parts 1, 2, and 3 are proved.** The double move works in every simple conflict graph. Theorem 11.44 holds, and the proof actually works under maximum degree at most four. The component bound `7m` and the inequality `2n₁ + n₂ ≥ 2m` are also proved for partial colourings of arbitrary finite simple conflict graphs. No conjecture is a hypothesis of these results.

`REPORT.md` was not changed. All new proofs are in new files, listed below. The only existing source/build files changed are `build.ps1` and `Se20Insertion/AxiomAudit.lean`.

| File | Contents |
|---|---|
| [DoubleHole.lean](Se20Insertion/DoubleHole.lean) | Configuration for arbitrary `g`; the double move with exactly the requested hypotheses. |
| [GirthGeometry.lean](Se20Insertion/GirthGeometry.lean) | Short-cycle exclusions from Mathlib's `egirth`; endpoint classification of common conflict neighbours. |
| [GirthBounds.lean](Se20Insertion/GirthBounds.lean) | Common-neighbour upper bounds 15 and 6; opposite-end intersection bound 6; the local partner inequality. |
| [ReachabilityCounting.lean](Se20Insertion/ReachabilityCounting.lean) | Exact conditions (a), (b), (c); non-single budget; the abstract finite counting contradiction. |
| [Theorem1144.lean](Se20Insertion/Theorem1144.lean) | Discharges the local geometric hypothesis and proves Theorem 11.44, its maximum-degree variant, and its ordinary-girth variant. |
| [ComponentBounds.lean](Se20Insertion/ComponentBounds.lean) | Vertices ≤ edges + components; the mass inequality for components of sizes 1 and 2. |
| [BicolourCounts.lean](Se20Insertion/BicolourCounts.lean) | Counts over all 190 pairs; Lemma 11.16; `2n₁ + n₂ ≥ 2m`. |

## Interpretation and proof differences

The existing `L2 G` is unchanged. All conflicts, including those witnessed through the uncoloured edge, remain conflicts in the fixed ambient graph `G`. A partial colouring has an arbitrary unused value outside its coloured set; the definitions below never treat that value as a colour of the hole.

Part 1 is stated for an arbitrary simple graph `H`, so it applies to `H = L2 G` for any `G`, including infinite graphs. It keeps the hypothesis `g ∉ F` exactly as requested. The construction gives `g` and `w` the old colour of `f`, and gives `f` the old colour of `w`; all other colour values stay the same. Neither degree nor girth is used.

For Part 2, `SaturatedOn`, `SingleClosed`, and `NoDoubleHole` are exactly (a), (b), and (c). In particular, `DoubleHoleConfig` has no hypothesis that `g` is uncoloured or reachable by hole moves. All three singleness tests use the same original `φ`. `Single` itself includes membership in `F` and adjacency, so condition (b) has not lost these requirements.

The girth hypothesis is **Mathlib's `7 ≤ G.egirth`**, with infinity for an acyclic graph. There is no custom girth definition. `theorem1144_girth` also proves the requested statement directly from Mathlib's natural-valued `7 ≤ G.girth`, using `G.natCast_girth_le_egirth`. `no_short_cycle` explicitly derives the exclusion of every cycle of length at most 6.

The formal counting proof avoids division and exact conflict degrees. Write `n = |R'|`, `D = Σd`, `T = Σt`, `Y = Σy`, and `C = Σc = 2U`. It proves:

```text
n > 0
D ≤ 24n
T + Y + 38n ≤ 2D
D ≤ C + 2Y + T
3C + D ≤ Y + T + 24n
```

The last inequality follows from `|N₁(f)| + 3c(f) ≤ 24`. The geometric proof treats the empty partner set, small `N₁(f)`, same-endpoint partners, a disjoint partner, and opposite-endpoint partners. These inequalities give `242n ≤ 10D ≤ 240n`, a contradiction. Thus neither 4-regularity nor the separate correction term `M` is needed; the 4-regular theorem is a direct specialization. The local geometric hypothesis in `counting_contradiction` is proved by `partner_bound`, not assumed in Theorem 11.44.

For Part 3, `m = F.card`. The proved hypothesis bounds **coloured** neighbours of each coloured vertex by 24; a bound of 24 on all ambient conflicts implies it by taking a subset. The ambient conflict graph is finite. Every coloured vertex occurs in 19 two-colour induced graphs. Every conflicting coloured pair occurs in exactly one of the 190 unordered colour pairs. Summing vertices ≤ edges + components and the degree sum gives `C(φ) ≥ 19m - 12m = 7m`. Summing `3 ≤ size + 2·[size=1] + [size=2]` over nonempty components gives the second inequality. Isolated vertices are included throughout.

## Exact Lean definitions and statements

The following blocks copy the declarations from the source, omitting theorem proof bodies. Namespace and section variables are shown explicitly. `Colour` is the existing abbreviation `Fin 20`.

```lean

namespace Se20Insertion

abbrev Colour := Fin 20

def L2 {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f := e ≠ f ∧ ∃ a ∈ e.val, ∃ b ∈ f.val, a = b ∨ G.Adj a b
  symm := ⟨by
    rintro e f ⟨hne, a, ha, b, hb, hab⟩
    exact ⟨hne.symm, b, hb, a, ha,
      hab.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

structure PartialColouring {W : Type*} (H : SimpleGraph W) (F : Finset W) where
  colour : W → Colour
  proper : ∀ ⦃x y⦄, x ∈ F → y ∈ F → H.Adj x y → colour x ≠ colour y

def MaxDegreeFour {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v, G.degree v ≤ 4

def FourRegular {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v, G.degree v = 4

namespace PartialColouring

variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def Neighbour (φ : PartialColouring H F) (f : W) (a : Colour) (g : W) : Prop :=
  g ∈ F ∧ H.Adj f g ∧ φ.colour g = a

def Single (φ : PartialColouring H F) (f : W) (p : Colour) (g : W) : Prop :=
  φ.Neighbour f p g ∧ ∀ g', φ.Neighbour f p g' → g' = g

def DoubleHoleConfig (φ : PartialColouring H F) (g f w : W) : Prop :=
  f ∈ F ∧ w ∈ F ∧ H.Adj g f ∧ H.Adj f w ∧ g ≠ w ∧ ¬ H.Adj g w ∧
    φ.Single g (φ.colour f) f ∧ φ.Single w (φ.colour f) f ∧
      φ.Single f (φ.colour w) w

theorem doubleHoleMove (φ : PartialColouring H F) {g f w : W}
    (_hg : g ∉ F) (hf : f ∈ F) (hw : w ∈ F)
    (hgf : H.Adj g f) (hfw : H.Adj f w) (hgw : g ≠ w) (hngw : ¬ H.Adj g w)
    (hsg : φ.Single g (φ.colour f) f)
    (hsw : φ.Single w (φ.colour f) f)
    (hsf : φ.Single f (φ.colour w) w) :
    Nonempty (PartialColouring H (insert g F))

theorem DoubleHoleConfig.insert (φ : PartialColouring H F) {g f w : W}
    (hc : φ.DoubleHoleConfig g f w) (hg : g ∉ F) :
    Nonempty (PartialColouring H (insert g F))

def SaturatedOn (φ : PartialColouring H F) (R : Finset W) : Prop :=
  ∀ x ∈ R, ∀ a : Colour, (x ∉ F ∨ a ≠ φ.colour x) → ∃ z, φ.Neighbour x a z

def SingleClosed (φ : PartialColouring H F) (R : Finset W) : Prop :=
  ∀ x ∈ R, ∀ y, φ.Single x (φ.colour y) y → y ∈ R

def NoDoubleHole (φ : PartialColouring H F) (R : Finset W) : Prop :=
  ∀ g ∈ R, ∀ f w, ¬ φ.DoubleHoleConfig g f w

def MutualSingle (φ : PartialColouring H F) (x y : W) : Prop :=
  φ.Single x (φ.colour y) y ∧ φ.Single y (φ.colour x) x

def singleTargets (φ : PartialColouring H F) (S : Finset W) (x : W) : Finset W :=
  S.filter (fun y => H.Adj x y ∧ φ.Single y (φ.colour x) x)

def partners (φ : PartialColouring H F) (S : Finset W) (x : W) : Finset W :=
  S.filter (φ.MutualSingle x)

theorem nonsingle_budget (φ : PartialColouring H F) (x : W)
    (hsat : ∀ a : Colour, a ≠ φ.colour x → ∃ z, φ.Neighbour x a z) :
    ((φ.colouredNeighbours x).filter (fun y => ¬ φ.Single x (φ.colour y) y)).card + 38 ≤
      2 * (φ.colouredNeighbours x).card

theorem counting_contradiction (φ : PartialColouring H F) (S : Finset W)
    (hSF : S ⊆ F) (hne : S.Nonempty) (hsat : φ.SaturatedOn S)
    (hclosed : φ.SingleClosed S)
    (hdegree : ∀ x ∈ S, (φ.colouredNeighbours x).card ≤ 24)
    (hlocal : ∀ x ∈ S, (φ.singleTargets S x).card + 3 * (φ.partners S x).card ≤ 24) :
    False

theorem partner_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (R S : Finset G.edgeSet) (hSR : S ⊆ R) (hSF : S ⊆ F)
    (hc : φ.NoDoubleHole R) (f : G.edgeSet) (hf : f ∈ S) :
    (φ.singleTargets S f).card + 3 * (φ.partners S f).card ≤ 24

end PartialColouring

theorem theorem1144_maxDegree {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) (h : G.edgeSet)
    (φ : PartialColouring (L2 G) (Finset.univ \ {h})) :
    ¬ ∃ R : Finset G.edgeSet, h ∈ R ∧ φ.SaturatedOn R ∧
      φ.SingleClosed R ∧ φ.NoDoubleHole R

theorem theorem1144 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hreg : FourRegular G) (hg : 7 ≤ G.egirth) (h : G.edgeSet)
    (φ : PartialColouring (L2 G) (Finset.univ \ {h})) :
    ¬ ∃ R : Finset G.edgeSet, h ∈ R ∧ φ.SaturatedOn R ∧
      φ.SingleClosed R ∧ φ.NoDoubleHole R

theorem theorem1144_girth {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hreg : FourRegular G) (hg : 7 ≤ G.girth) (h : G.edgeSet)
    (φ : PartialColouring (L2 G) (Finset.univ \ {h})) :
    ¬ ∃ R : Finset G.edgeSet, h ∈ R ∧ φ.SaturatedOn R ∧
      φ.SingleClosed R ∧ φ.NoDoubleHole R

end Se20Insertion

```

The geometric statements used in the proof are:

```lean

namespace Se20Insertion.GirthGeometry

variable {V : Type*} {G : SimpleGraph V}

theorem no_short_cycle (hg : 7 ≤ G.egirth) {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) (hlen : p.length ≤ 6) : False

variable [Fintype V] (G : SimpleGraph V)

theorem common_near_card (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {f w : G.edgeSet} {a b c : V} (hf : f.val = s(a,b)) (hw : w.val = s(a,c))
    (hfw : f ≠ w) (A : Finset G.edgeSet)
    (hA : ∀ z ∈ A, (L2 G).Adj f z ∧ (w = z ∨ (L2 G).Adj w z)) : A.card ≤ 15

theorem common_far_card (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {f w : G.edgeSet} (hfw : (L2 G).Adj f w)
    (hdis : ¬ ∃ a, a ∈ f.val ∧ a ∈ w.val) (A : Finset G.edgeSet)
    (hA : ∀ z ∈ A, (L2 G).Adj f z ∧ (w = z ∨ (L2 G).Adj w z)) : A.card ≤ 6

theorem opposite_near_card (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {f w v : G.edgeSet} {a b c d : V}
    (hf : f.val = s(a,b)) (hw : w.val = s(a,c)) (hv : v.val = s(b,d))
    (hfw : f ≠ w) (hfv : f ≠ v) (A : Finset G.edgeSet)
    (hA : ∀ z ∈ A, (L2 G).Adj f z ∧
      (w = z ∨ (L2 G).Adj w z) ∧ (v = z ∨ (L2 G).Adj v z)) : A.card ≤ 6

theorem dominator_bound (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    (f : G.edgeSet) (A C : Finset G.edgeSet)
    (hA : ∀ z ∈ A, (L2 G).Adj f z) (hCA : C ⊆ A)
    (hdom : ∀ w ∈ C, ∀ z ∈ A, w = z ∨ (L2 G).Adj w z) :
    A.card + 3 * C.card ≤ 24

end Se20Insertion.GirthGeometry

```

The component definitions and supporting statements are:

```lean

namespace Se20Insertion.ComponentBounds

variable {X : Type*} [Fintype X] (H : SimpleGraph X)

theorem vertices_le_edges_add_components :
    Nat.card X ≤ Nat.card H.edgeSet + Nat.card H.ConnectedComponent

def smallComponents (k : ℕ) : ℕ :=
  Nat.card {c : H.ConnectedComponent // Nat.card c.supp = k}

theorem small_components_mass :
    3 * Nat.card H.ConnectedComponent ≤ Nat.card X +
      2 * smallComponents H 1 + smallComponents H 2

end Se20Insertion.ComponentBounds

namespace Se20Insertion.PartialColouring

variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def Bicoloured (φ : PartialColouring H F) (a b : Colour) : Set W :=
  {g | g ∈ F ∧ (φ.colour g = a ∨ φ.colour g = b)}

def KempeGraph (φ : PartialColouring H F) (a b : Colour) :
    SimpleGraph (φ.Bicoloured a b) := H.induce (φ.Bicoloured a b)

def componentCount (φ : PartialColouring H F) : ℕ :=
  ∑ a : Colour, ∑ b : Colour,
    if a < b then Nat.card (φ.KempeGraph a b).ConnectedComponent else 0

variable [Fintype W]

def smallComponentCount (φ : PartialColouring H F) (k : ℕ) : ℕ :=
  ∑ a : Colour, ∑ b : Colour,
    if a < b then ComponentBounds.smallComponents (φ.KempeGraph a b) k else 0

def colouredEdges (_φ : PartialColouring H F) : Finset H.edgeSet :=
  Finset.univ.filter (fun e => e.val.out.1 ∈ F ∧ e.val.out.2 ∈ F)

omit [Fintype W] in
theorem bicoloured_mass (φ : PartialColouring H F) :
    (∑ a : Colour, ∑ b : Colour, if a < b then Nat.card (φ.Bicoloured a b) else 0) = 19 * F.card

theorem bicoloured_edges (φ : PartialColouring H F) :
    (∑ a : Colour, ∑ b : Colour, if a < b then Nat.card (φ.KempeGraph a b).edgeSet else 0) =
      φ.colouredEdges.card

theorem coloured_edges_le_twelve (φ : PartialColouring H F)
    (hdegree : ∀ x ∈ F, (φ.colouredNeighbours x).card ≤ 24) :
    φ.colouredEdges.card ≤ 12 * F.card

theorem lemma1116 (φ : PartialColouring H F)
    (hdegree : ∀ x ∈ F, (φ.colouredNeighbours x).card ≤ 24) :
    7 * F.card ≤ φ.componentCount

theorem small_components_at_least_twice (φ : PartialColouring H F)
    (hdegree : ∀ x ∈ F, (φ.colouredNeighbours x).card ≤ 24) :
    2 * φ.smallComponentCount 1 + φ.smallComponentCount 2 ≥ 2 * F.card

end Se20Insertion.PartialColouring

```

## Validation and exact axiom output

The final `./build.ps1` run exited with code **0**. It rebuilt every original module, all seven new modules, `AxiomAudit.lean`, and the root module, sequentially against the existing local Mathlib oleans. The full output is [BUILD2.log](BUILD2.log). The toolchain remains `leanprover/lean4:v4.35.0-rc4`.

The source scan below returned no matches (the normal ripgrep exit status 1):

```powershell
rg -n '\b(sorry|admit|axiom|native_decide|ofReduceBool)\b' Se20Insertion -g '*.lean'
```

Every one of the 37 audited declarations, including the original results and all new main results, uses only `propext`, `Classical.choice`, and `Quot.sound`. The following is the exact `#print axioms` output from the final build, also saved as [AXIOMS2.txt](AXIOMS2.txt):

```text
'Se20Insertion.strongColourable_of_conj119Star' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.conj119Star_of_conj119' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_conj1115' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_conj1126' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_starInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_conj119' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.triangle_insertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.triangle_edges_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_all_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.regularCompletion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.at_least_sixteen_add_uncoloured_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.groupedColourClassInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeMove_class_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeMove_inseparable_moved_colour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.inherited_inseparable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.single_neighbour_at_least_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.AuditExamples.example_overlap_conflicts_e' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.doubleHoleMove' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.DoubleHoleConfig.insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.GirthGeometry.no_short_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.GirthGeometry.common_near_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.GirthGeometry.common_far_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.GirthGeometry.opposite_near_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.GirthGeometry.dominator_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.nonsingle_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.counting_contradiction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.partner_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.theorem1144_maxDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.theorem1144' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.theorem1144_girth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentBounds.vertices_le_edges_add_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.ComponentBounds.small_components_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.bicoloured_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.bicoloured_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.coloured_edges_le_twelve' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.lemma1116' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.small_components_at_least_twice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## What remains unproved or was not done

No requested result in Parts 1 and 2, or the finite-graph supporting results in Part 3, remains unproved or conjectural. All new proof files are in both the build and the import path used by the axiom audit. There are no unfinished proof files.

The formalization proves the upper bounds 15 and 6 needed for the argument. It does not separately prove the document's exact common-neighbour equalities or the exact conflict degree 24 in a 4-regular graph; the stronger maximum-degree proof avoids needing these equalities. It also does not formalize the claimed girth-six example or show that girth seven is necessary for the theorem itself.

Theorem 11.44 does not close the document's stated reachability gap. No theorem here turns a configuration in the original colouring at an arbitrary coloured `g` into an actual sequence that transports the hole to `g` while preserving that configuration. Conjecture 11.45 and the original unconditional 20-colour bound remain outside this result. The computational claims and k-colour-repair experiments elsewhere in section 11.24 were not formalized or rerun.

Part 3 is stated for a finite ambient conflict graph, which includes the requested finite-graph setting. It was not extended to an infinite ambient graph with only finitely many coloured vertices. The optional Part 3 work was completed well within the additional two-hour allowance.
