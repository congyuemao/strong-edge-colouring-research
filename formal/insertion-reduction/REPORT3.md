# Third pass: colour-set cores (section 11.26)

## Findings and corrections

**Two numerical overstatements need qualification.** The sentence that girth at least 7 makes `|E(L²[N(v)])|` “exactly 87” omits regularity. For example, label the edges of the cycle `C₈` cyclically by `e₀,…,e₇`. Its girth is 8, but the conflict neighbourhood of `e₀` is `{e₁,e₂,e₆,e₇}`, with only three internal conflict edges: `e₁e₂`, `e₁e₇`, and `e₆e₇`. The appropriate general claim for maximum degree 4 is an upper bound of 87; equality needs the full local degree pattern, supplied by 4-regularity. This is in optional Part 4, whose corrected geometric statement is **not formalized in this pass**. Neither this equality nor Lemma 11.48 is used by any theorem proved below.

There is a short mathematical proof of the corrected upper bound using results already in the library. Write `n = |N(v)| ≤ 24`, and let `t ≤ 6` count neighbours sharing an endpoint with the original edge `v`. The existing `GirthGeometry.common_near_card` and `common_far_card` bound the intersection of `N(v)` with a neighbour's **closed** conflict neighbourhood by 15 and 6 respectively. Subtracting that neighbour itself bounds its degree in `L²[N(v)]` by 14 or 5. The degree sum is therefore at most `14t + 5(n−t) = 5n + 9t ≤ 174`, so there are at most 87 edges. This final counting assembly is explained here, but is not a newly checked Lean theorem; the formal work stops at Parts 1–3.

The text's description of the `k = 19` obstruction as “exactly 16 single edges” should say **at least 16**, and require every single neighbour to have all its 171 eligible pairs tangled. The corrected lower bound is proved as `allGroupsFail_at_least_sixteen_single`. For a concrete counterexample to “exactly 16” in the requested general finite-conflict-graph setting, take a complete 20-partite coloured graph with colour-class sizes `5,1,1,...,1`, and add a universal uncoloured vertex `h`. Then `deg(h)=24`, the partial colouring is proper, all 190 pairs are tangled at `h`, and there are **19** single colours. For a singleton colour `u`, the two vertices `{h,f_u}` form a core for the other 19 colours: both thresholds are 1. For the fivefold colour, `τ(h)=2−5=−3`, so `{h}` itself is a core. Thus all 19-colour groups fail, with 19 single neighbours. This example is an abstract `H`, not asserted to be `L2 G` for a subquartic graph; it shows that the numerical counting hypotheses do not imply exactly 16.

No gap was found in Theorem 11.47, the properly restricted 19-colour equivalence, or Proposition 11.49(1–4). They have been proved in Lean with the requested domain convention. Three scope details are essential:

- “Extends” means a proper colouring of **all of `insert h F`**, with recolouring allowed. It does not promise agreement with `φ` on `F`.
- Degrees count only neighbours in `insert h F`. The arbitrary unused value `φ.colour h` never contributes to a `Y` colour class. Other uncoloured vertices do not count.
- The 171 pairs at a coloured neighbour exclude its own colour. `separablePairCount` counts only these pairs. The threshold 1368 is proved for that count, as in the document's `24 × 171` calculation.

## Result and files

Parts 1–3 are implemented without changing any pre-existing theorem statement. The underlying `Colour := Fin 20`, `PartialColouring`, `SameComponent`, `Separable`, `Single`, `holeMove`, `L2`, `StarInsertion`, and star reduction are reused.

| File | Contents |
|---|---|
| [ColourSetCore.lean](Se20Insertion/ColourSetCore.lean) | Tangling, integer thresholds, maximal core, the subset characterization, equality of `Y` classes, and Theorem 11.47. |
| [ColourSetPeeling.lean](Se20Insertion/ColourSetPeeling.lean) | Simultaneous peeling; equality with the maximal core after at most `|S_Y|+1` rounds. |
| [ColourSetSpecialCases.lean](Se20Insertion/ColourSetSpecialCases.lean) | Core degree inequalities, two-colour criterion, 19-colour equivalence, Theorem 11.7 via the core theorem, and the conjecture-to-colourability chain. |
| [ColourSetCounting.lean](Se20Insertion/ColourSetCounting.lean) | All-group failure, Proposition 11.49, clique/separable-pair counts, and the 1368 implication. |
| [AxiomAudit.lean](Se20Insertion/AxiomAudit.lean) | Existing audits plus 28 new declarations. |
| [build.ps1](build.ps1) | Adds the four modules in dependency order before the audit. |

The results about a finite coloured domain are slightly more general than requested: they need no `Fintype W`. The finite set `insert h F` supplies all finiteness needed even if the ambient graph is infinite.

## Proof and hypothesis review

The proof of 11.47 uses the proposed set of possible hole positions. Assuming no colouring of `insert h F` exists, `fixedClassHoles` contains each `v` admitting a proper colouring of `(insert h F).erase v` with exactly the same `Y` colour classes as `φ`. It contains `h`. A possible hole cannot originally belong to a `Y` colour class. Equality of classes preserves the actual two-colour reachability relation, and a separable pair would supply a complete colouring by the existing Kempe-swap theorem. Thus every possible hole belongs to `S_Y`.

The existing pigeonhole lemma `single_count` gives at least `τ_Y(v)` single neighbours carrying colours outside `Y`. Moving the hole to any such neighbour preserves every `Y` class. All those neighbours are therefore possible holes, making `fixedClassHoles` a core and contradicting `h ∉ C_Y`. No claim that singleness itself survives an arbitrary sequence of moves is needed.

The core is defined as the largest subset of `S_Y` satisfying its degree thresholds. `not_mem_colourSetCore_iff` is exactly the user-requested universal-subset criterion, with integer comparisons. `colourPeel_stabilizes` proves that simultaneous peeling computes this same set. The proof uses containment invariants and a strict cardinality decrease at every nonstationary round. Sequential deletion orders are not separately formalized.

For two distinct colours the threshold is exactly `36 + d_Y(v) − deg(v)`. For 19 colours excluding `u`, a single `u`-neighbour `f` gives outside-`Y` neighbour sets `{f}` at `h` and `{h}` at `f`; both thresholds are 1. When every pair at `h` is tangled, `h` lies in the core iff all eligible pairs at `f` are tangled. Negating this is the requested equivalence with a separable pair whose two colours differ from `u`. `singleInsertion_from_colourSetCore` also removes the no-separable-pair assumption at `h`: if that assumption fails, the two-colour criterion already inserts `h`.

`Conj1150` is a definition, not an axiom. It quantifies over the exact restricted star states used by the existing reduction: a graph on `Fin n`, 4-regularity, a nonexceptional centre, a nonempty star `U`, no triangle edge in `U`, and an arbitrary proper colouring of `univ \ U`. For each specified `h ∈ U`, it asks for `2 ≤ |Y| ≤ 19` and `h ∉ C_Y`. The separately defined **weaker** `ColourSetStarInsertion` only asks for some `h ∈ U` and some `Y` with `|Y| ≥ 2`. That existential version is all `StarInsertion` needs. There is no stuckness, local-maximality, girth, or degree-24 assumption in this chain. The existing `strongColourable_of_starInsertion` then yields `StrongColourable G 20` for every finite simple graph of maximum degree at most 4.

For Proposition 11.49, `AllGroupsFail φ h k` means that every `k`-element subset of the fixed 20 colours has `h` in its core. Any two distinct colours can be enlarged to such a subset, so all 190 pairs are tangled. The existing `single_saturated_of_stuck` proves that a single neighbour sees every other colour.

For the main sum, put `N = N(h)` in the restricted domain and let `A_Y` count its neighbours whose colours avoid `Y` and at which all pairs of `Y` are tangled. Core membership gives

```text
2(20−k) ≤ |{f ∈ N : φ(f) ∉ Y}| + A_Y.
```

Every neighbour colour avoids exactly `C(19,k)` groups. Double counting gives `Σ_Y |{f ∈ N : φ(f) ∉ Y}| = 24 C(19,k)` and `Σ_Y A_Y = Σ_f K_k(f)`. The binomial identity `(20−k) C(20,k) = 20 C(19,k)` therefore gives `Σ_f K_k(f) ≥ 16 C(19,k)`, equivalent to the requested division-free `3 Σ ≥ 2·24·C(19,k)`. No graph geometry is used.

At every vertex of any core, `d_Y ≥ |Y|` follows because each colour in `Y` has a neighbour when `|Y| ≥ 2`. Every core neighbour is outside the `Y` classes, giving the integer inequality `2d_Y ≤ 2deg − 2(20−|Y|)`. These assertions do not require all groups to fail. In particular, the additional conclusion `d_Y ≤ 6` for `k=2` would require `deg(v) ≤ 24` at that vertex, not merely at `h`.

For `k=2`, `tangleCliqueCount 2 f + separablePairCount f = 171`. With 24 neighbours, the total is 4104. If the separable total exceeds 1368, the tangled total is below 2736, contradicting the all-failure lower bound. `good_pair_of_separable_sum` supplies a two-colour group with `h ∉ C_Y`; `insertion_of_separable_sum` then supplies a proper colouring. This local implication does not require `h` to be stuck. It does not assert Conjecture 11.51 itself or remove its degree-24 premise.

## Exact Lean definitions and statements

These blocks are copied from the source, omitting theorem proof bodies. The section is noncomputable and uses `open scoped Classical`. `Colour` is the existing `Fin 20` abbreviation.

```lean
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def TangledAt (φ : PartialColouring H F) (v : W) (a b : Colour) : Prop :=
  ∃ x y, φ.Neighbour v a x ∧ φ.Neighbour v b y ∧ φ.SameComponent a b x y

def AllTangled (φ : PartialColouring H F) (Y : Finset Colour) (v : W) : Prop :=
  ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → φ.TangledAt v a b

def domainNeighbours (H : SimpleGraph W) (D : Finset W) (v : W) : Finset W :=
  D.filter (H.Adj v)

def yNeighbours (φ : PartialColouring H F) (Y : Finset Colour) (v : W) : Finset W :=
  F.filter (fun x => H.Adj v x ∧ φ.colour x ∈ Y)

def colourSetS (φ : PartialColouring H F) (h : W) (Y : Finset Colour) : Finset W :=
  (insert h F).filter (fun v => (v ∈ F → φ.colour v ∉ Y) ∧ φ.AllTangled Y v)

def colourSetThreshold (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (v : W) : ℤ :=
  2 * (20 - (Y.card : ℤ)) + (φ.yNeighbours Y v).card -
    (domainNeighbours H (insert h F) v).card

def IsColourCore (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (C : Finset W) : Prop :=
  C ⊆ φ.colourSetS h Y ∧ ∀ v ∈ C,
    φ.colourSetThreshold h Y v ≤ (domainNeighbours H C v).card

def colourSetCore (φ : PartialColouring H F) (h : W) (Y : Finset Colour) : Finset W :=
  (φ.colourSetS h Y).filter (fun v => ∃ C, φ.IsColourCore h Y C ∧ v ∈ C)

def SameYClasses {F' : Finset W} (φ : PartialColouring H F) (ψ : PartialColouring H F')
    (Y : Finset Colour) : Prop :=
  ∀ a ∈ Y, ∀ x, (x ∈ F ∧ φ.colour x = a) ↔ (x ∈ F' ∧ ψ.colour x = a)

def fixedClassHoles (φ : PartialColouring H F) (h : W) (Y : Finset Colour) : Finset W :=
  (insert h F).filter (fun v => ∃ ψ : PartialColouring H ((insert h F).erase v),
    φ.SameYClasses ψ Y)

theorem tangledAt_iff_not_separable (φ : PartialColouring H F) (v : W) (a b : Colour) :
    φ.TangledAt v a b ↔ ¬ φ.Separable v a b

theorem colourSetCore_greatest (φ : PartialColouring H F) {h : W} {Y : Finset Colour}
    {C : Finset W} (hc : φ.IsColourCore h Y C) : C ⊆ φ.colourSetCore h Y

theorem colourSetCore_isCore (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    φ.IsColourCore h Y (φ.colourSetCore h Y)

theorem not_mem_colourSetCore_iff (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    h ∉ φ.colourSetCore h Y ↔ ∀ C ⊆ φ.colourSetS h Y, h ∈ C →
      ∃ v ∈ C, (domainNeighbours H C v).card < φ.colourSetThreshold h Y v

theorem colourSetInsertion (φ : PartialColouring H F) (h : W) (hh : h ∉ F)
    (Y : Finset Colour) (_hY : 2 ≤ Y.card)
    (hcore : h ∉ φ.colourSetCore h Y) : Nonempty (PartialColouring H (insert h F))

theorem colourSetInsertion_of_subsets (φ : PartialColouring H F) (h : W) (hh : h ∉ F)
    (Y : Finset Colour) (hY : 2 ≤ Y.card)
    (hc : ∀ C ⊆ φ.colourSetS h Y, h ∈ C →
      ∃ v ∈ C, (domainNeighbours H C v).card < φ.colourSetThreshold h Y v) :
    Nonempty (PartialColouring H (insert h F))

end Se20Insertion.PartialColouring
```

```lean
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def colourPeelStep (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (R : Finset W) : Finset W :=
  R.filter (fun v => φ.colourSetThreshold h Y v ≤ (domainNeighbours H R v).card)

def colourPeel (φ : PartialColouring H F) (h : W) (Y : Finset Colour) : ℕ → Finset W
  | 0 => φ.colourSetS h Y
  | n + 1 => φ.colourPeelStep h Y (φ.colourPeel h Y n)

theorem colourPeel_stabilizes (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    φ.colourPeel h Y ((φ.colourSetS h Y).card + 1) = φ.colourSetCore h Y

theorem not_mem_core_iff_peeled (φ : PartialColouring H F) (h : W) (Y : Finset Colour) :
    h ∉ φ.colourSetCore h Y ↔ h ∉ φ.colourPeel h Y ((φ.colourSetS h Y).card + 1)

end Se20Insertion.PartialColouring
```

```lean
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def outsideYNeighbours (φ : PartialColouring H F) (h : W) (Y : Finset Colour) (v : W) : Finset W :=
  domainNeighbours H (insert h F) v \ φ.yNeighbours Y v

theorem core_degree_bound (φ : PartialColouring H F) (h : W) (Y : Finset Colour)
    {v : W} (hv : v ∈ φ.colourSetCore h Y) :
    2 * ((φ.yNeighbours Y v).card : ℤ) ≤
      2 * (domainNeighbours H (insert h F) v).card - 2 * (20 - (Y.card : ℤ))

theorem core_yDegree_lower (φ : PartialColouring H F) (h : W) (Y : Finset Colour)
    (hY : 2 ≤ Y.card) {v : W} (hv : v ∈ φ.colourSetCore h Y) :
    Y.card ≤ (φ.yNeighbours Y v).card

theorem twoColourCoreInsertion (φ : PartialColouring H F) (h : W) (hh : h ∉ F)
    {a b : Colour} (hab : a ≠ b) (hc : h ∉ φ.colourSetCore h {a, b}) :
    Nonempty (PartialColouring H (insert h F))

theorem twoColour_threshold (φ : PartialColouring H F) (h v : W)
    {a b : Colour} (hab : a ≠ b) :
    φ.colourSetThreshold h {a, b} v = 36 + ((φ.yNeighbours {a, b} v).card : ℤ) -
      (domainNeighbours H (insert h F) v).card

theorem nineteen_core_iff (φ : PartialColouring H F) {h f : W} {u : Colour}
    (hh : h ∉ F) (hs : φ.Single h u f)
    (ht : ∀ a b, a ≠ b → φ.TangledAt h a b) :
    h ∈ φ.colourSetCore h (Finset.univ.erase u) ↔
      φ.AllTangled (Finset.univ.erase u) f

theorem nineteen_not_core_iff_separable (φ : PartialColouring H F) {h f : W} {u : Colour}
    (hh : h ∉ F) (hs : φ.Single h u f)
    (ht : ∀ a b, a ≠ b → ¬ φ.Separable h a b) :
    h ∉ φ.colourSetCore h (Finset.univ.erase u) ↔
      ∃ a b, a ≠ b ∧ a ≠ u ∧ b ≠ u ∧ φ.Separable f a b

theorem singleInsertion_from_colourSetCore (φ : PartialColouring H F) {h f : W} {u a b : Colour}
    (hh : h ∉ F) (hs : φ.Single h u f)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) (hsep : φ.Separable f a b) :
    Nonempty (PartialColouring H (insert h F))

end Se20Insertion.PartialColouring
```

```lean
namespace Se20Insertion

def Conj1150 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), FourRegular G →
    ∀ v, Nonexceptional G v → ∀ U : Finset G.edgeSet,
      StarSet G v U → (∀ e ∈ U, ¬ OnTriangle G e) →
      ∀ φ : PartialColouring (L2 G) (Finset.univ \ U), ∀ h ∈ U,
        ∃ Y : Finset Colour, 2 ≤ Y.card ∧ Y.card ≤ 19 ∧ h ∉ φ.colourSetCore h Y

def ColourSetStarInsertion : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), FourRegular G →
    ∀ v, Nonexceptional G v → ∀ U : Finset G.edgeSet,
      StarSet G v U → (∀ e ∈ U, ¬ OnTriangle G e) →
      ∀ φ : PartialColouring (L2 G) (Finset.univ \ U),
        ∃ h ∈ U, ∃ Y : Finset Colour, 2 ≤ Y.card ∧ h ∉ φ.colourSetCore h Y

theorem colourSetStarInsertion_of_conj1150 (hc : Conj1150) : ColourSetStarInsertion

theorem starInsertion_of_colourSetStarInsertion (hc : ColourSetStarInsertion) : StarInsertion

theorem starInsertion_of_conj1150 (hc : Conj1150) : StarInsertion

theorem strongColourable_of_conj1150 (hc : Conj1150) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : MaxDegreeFour G) : StrongColourable G 20

end Se20Insertion
```

```lean
namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def colourGroups (k : ℕ) : Finset (Finset Colour) := Finset.univ.powersetCard k

def tangleCliqueCount (φ : PartialColouring H F) (k : ℕ) (f : W) : ℕ :=
  ((colourGroups k).filter (fun Y => φ.colour f ∉ Y ∧ φ.AllTangled Y f)).card

def AllGroupsFail (φ : PartialColouring H F) (h : W) (k : ℕ) : Prop :=
  ∀ Y ∈ colourGroups k, h ∈ φ.colourSetCore h Y

def separablePairCount (φ : PartialColouring H F) (f : W) : ℕ :=
  ((colourGroups 2).filter (fun Y => φ.colour f ∉ Y ∧ ¬ φ.AllTangled Y f)).card

theorem allGroupsFail_tangled (φ : PartialColouring H F) {h : W} {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 20) (hf : φ.AllGroupsFail h k) :
    ∀ a b, a ≠ b → φ.TangledAt h a b

theorem allGroupsFail_single_saturated (φ : PartialColouring H F) {h f : W} {k : ℕ}
    {u : Colour} (hk : 2 ≤ k) (hk' : k ≤ 19) (hf : φ.AllGroupsFail h k)
    (hs : φ.Single h u f) : ∀ a, a ≠ u → ∃ x, φ.Neighbour f a x

theorem allGroupsFail_at_least_sixteen_single (φ : PartialColouring H F) {h : W} {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 19) (hf : φ.AllGroupsFail h k)
    (hd : (domainNeighbours H (insert h F) h).card = 24) :
    16 ≤ (φ.singleColours h).card

theorem sum_groups_avoiding (φ : PartialColouring H F) (N : Finset W) (k : ℕ) :
    (∑ Y ∈ colourGroups k, (N.filter (fun f => φ.colour f ∉ Y)).card) =
      N.card * Nat.choose 19 k

theorem allGroupsFail_clique_sum (φ : PartialColouring H F) (h : W) {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 19) (hf : φ.AllGroupsFail h k)
    (hd : (domainNeighbours H (insert h F) h).card = 24) :
    3 * (∑ f ∈ domainNeighbours H (insert h F) h, φ.tangleCliqueCount k f) ≥
      2 * 24 * Nat.choose 19 k

theorem not_allTangled_iff_separable (φ : PartialColouring H F) (Y : Finset Colour) (f : W) :
    ¬ φ.AllTangled Y f ↔ ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧ φ.Separable f a b

theorem clique_pair_partition (φ : PartialColouring H F) (f : W) :
    φ.tangleCliqueCount 2 f + φ.separablePairCount f = 171

theorem good_pair_of_separable_sum (φ : PartialColouring H F) (h : W)
    (hd : (domainNeighbours H (insert h F) h).card = 24)
    (hsep : 1368 < ∑ f ∈ domainNeighbours H (insert h F) h, φ.separablePairCount f) :
    ∃ Y ∈ colourGroups 2, h ∉ φ.colourSetCore h Y

theorem insertion_of_separable_sum (φ : PartialColouring H F) (h : W) (hh : h ∉ F)
    (hd : (domainNeighbours H (insert h F) h).card = 24)
    (hsep : 1368 < ∑ f ∈ domainNeighbours H (insert h F) h, φ.separablePairCount f) :
    Nonempty (PartialColouring H (insert h F))

end Se20Insertion.PartialColouring
```

## Validation and exact axiom output

The final `./build.ps1` run exited with code **0**. It rebuilt all original modules, the four new modules, `AxiomAudit.lean`, and the root import, using the existing local Mathlib dependencies. The full output is [BUILD3.log](BUILD3.log). The toolchain remains `leanprover/lean4:v4.35.0-rc4`. The log contains linter/deprecation warnings, but no errors.

The source scan

```powershell
rg -n '\b(sorry|admit|axiom|native_decide|ofReduceBool)\b' Se20Insertion -g '*.lean'
```

returned no matches (ripgrep exit code 1). All **65** audited declarations, including all 28 additions, depend only on `propext`, `Classical.choice`, and `Quot.sound`. There are no new axiom declarations. Below is the exact `#print axioms` output, also saved in [AXIOMS3.txt](AXIOMS3.txt).

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
'Se20Insertion.PartialColouring.tangledAt_iff_not_separable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.colourSetCore_isCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.colourSetCore_greatest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.not_mem_colourSetCore_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.colourSetInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.colourSetInsertion_of_subsets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.colourPeel_stabilizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.not_mem_core_iff_peeled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.twoColourCoreInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.twoColour_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.nineteen_core_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.nineteen_not_core_iff_separable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.singleInsertion_from_colourSetCore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.colourSetStarInsertion_of_conj1150' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.starInsertion_of_colourSetStarInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.starInsertion_of_conj1150' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_conj1150' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.core_degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.core_yDegree_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.allGroupsFail_tangled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.allGroupsFail_single_saturated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.allGroupsFail_at_least_sixteen_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.sum_groups_avoiding' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.allGroupsFail_clique_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.not_allTangled_iff_separable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.clique_pair_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.good_pair_of_separable_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.insertion_of_separable_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What remains unproved and what was not done

No required result in Parts 1–3 remains unproved. No existing theorem statement was changed. Conjectures 11.50 and 11.51 remain conjectures; only the requested conditional implications are proved. No unconditional new 20-colour theorem is claimed.

Following the instruction to stop once Parts 1–3 build, Part 4 was not formalized: no Lean proof of chordality of `L2` of a tree, Lemma 11.48's fan conclusion, the local 87 upper bound/equality, or the long-chain girth lower bound was added. The cycle counterexample diagnoses the unqualified equality. The short proof of the corrected upper bound in the findings uses existing geometric lemmas, but its final degree-sum argument remains outside the Lean formalization.

The counterexamples in the findings are mathematical descriptions, not additional Lean examples or computational experiments. No empirical claims or GPU experiments in the reference document were rerun. There was no outside reviewer or delegated agent.
