# Fourth-pass report

## Flaws found and corrected

**`hfinite` is discharged.** The graph encoding, canonical relabelling, profile
coverage, six root certificates, and the applications to Proposition D and
Theorem F all compile. The corrected exploratory and engineering issues are
listed first below; none is an outstanding mathematical gap.

**A single large kernel reduction was not practical in the tested form.**
The 1,919-node test described below exceeded a 6,000 MB Lean memory limit.
Splitting the computation into separately checked transition and branch lemmas
first completed the same test in 198.8433097 seconds. Checking only rejections
and actual transitions reduced this to 31.6469958 seconds. A larger test with
41,934 selection nodes also passed. These are real kernel results; the C++
runs below are exploratory measurements only.

**An undocumented exploratory pruning condition was removed.** The first C++
generator capped zero-type vertices at three. That bound was not among the
formal hypotheses used by its generator. The cutoff was removed; one additional
profile appeared and was rejected by the root local test. The current counts
below come from the corrected generator. No Lean theorem relied on the cutoff.

**One shell worker encountered a scheduling collision.** It reached a log file
already held by another worker and stopped before launching Lean. The owning
compiler completed the certificate successfully. The helper scripts now use
atomic claim files. Completion was checked from all 85 compiled groups and
the assembled theorems, not merely from worker exit statuses.

No flaw has been found in the earlier Lean reductions. No existing statement
has been changed. The necessary local condition is still used in its correct
direction; unselected graph edges are retained as possible conflict witnesses.

## Exact final statements

File: `fourth_pass/Unconditional.lean`, namespace
`Se20Fractional.FourthPass`:

```lean
theorem no_obstruction14 :
    ∀ H : SimpleGraph (Fin 14), ∀ Q : Finset H.edgeSet,
      ¬ Obstruction14 H Q

theorem propositionD_unconditional {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : PropositionD G

theorem theorem_F_unconditional {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) :
    FractionalColourable (L2 G) 20
```

The last two apply the existing `propositionD_of_no_obstruction14` and
`theorem_F_of_no_obstruction14`. All three report exactly
`[propext, Classical.choice, Quot.sound]`.

## New structural theorems

Files: `fourth_pass/RootDegreeThree.lean`, `fourth_pass/SelectedTriangle.lean`.
All the following statements concern a finite simple graph `G`, maximum degree
at most four, and a selected conflict clique `Q` with at least sixteen edges.

* `tip_sum_le_three_degree`: for any finite `U` excluding the root,
  `∑ x ∈ U, (tip G r x).card ≤ 3 * G.degree r`.
* `selected_triangle_region_empty`: if a selected root edge belongs to a
  triangle, its endpoint region has no internal edges, under `LocallyLow`.
* `selected_triangle_tip_singleton`: outside the root's closed neighbourhood,
  a type containing that selected triangle label is exactly its singleton.
* `selected_labels_independent`: if the root has at least three selected
  neighbours, no two of those selected neighbours are adjacent.
* `root_internal_card_le_one`: under `LocallyLow`, a root with at least three
  selected neighbours has at most one edge inside its neighbourhood.
* `degree_three_endpoint_le_ten`: under `LocallyLow`, a degree-three root with
  at least three selected neighbours implies `(endpoints Q).card <= 10`.

The selected-label independence proof is short: if two selected labels are
adjacent, types containing either label are singleton. An outer selected edge
cannot cover those two labels and a third selected label. All selected edges
then touch the root neighbourhood, which contains an internal edge; the
degree-sum bound gives at most fifteen selected edges.

## Verified search and semantic interface

`fourth_pass/SelectionSearch.lean` defines `selectionSearch`, with structural
recursion on explicit fuel. It filters impossible selections, checks the
remaining cardinality, and branches on including or excluding an element.
Fuel exhaustion returns `false`, never a purported refutation.

`selectionSearch_sound` proves: if the result is `true`, any model compatible
with the current state has fewer than `need` good elements among the remaining
candidates. Its hypotheses require that pruning retain every good model
element and that adding such an element preserve compatibility.

`fourth_pass/SmallAnalogue.lean` instantiates this interface on the five-cycle.
`cycle_search` is checked by `decide`, and `cycle_clique_card_le_two` derives
the mathematical clique bound from search soundness.

`fourth_pass/PackedSearch.lean` implements adjacency matrices as `Nat` masks.
`BitCount.lean` proves the clear-lowest-bit counter correct:

```lean
theorem pop_eq_min (fuel x : Nat) :
  pop fuel x = min fuel x.bitIndices.length
```

`BitGraph.lean` proves bit inclusion, degree and local-test monotonicity,
strict degree increase from a missing actual edge, and edge-insertion facts.
`PackedSoundness.lean` proves completeness of possible witness lists and
soundness of forced witnesses, propagation, selection filtering, and branching.
Its main theorem is:

```lean
theorem packed_search_sound (n d fuel need : Nat)
    (st : Option State) (cs : List Edge)
    (hcheck : selectionSearch (possible n d) (step n d)
      fuel need st cs = true) :
  ∀ full, Realizes n d st full →
    (cs.filter (fun e => decide (e ∈ full.chosen))).length < need
```

`Model n full` explicitly requires the full graph's degree/local checks,
selected endpoint bounds, actual selected edges, graph symmetry and
irreflexivity, and all selected conflicts. `Realizes` requires a partial graph
contained in that full graph, completeness on edges incident to fixed root
labels, symmetry, and selected-edge containment. These requirements are not
silently assumed to follow from the profile generator.

`GraphEncoding.lean` now proves:

```lean
theorem encodeSelected_model {n : Nat} (G : SimpleGraph (Fin n))
    (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (hLow : DReduction.LocallyLow G Q) :
  Model n (encodeSelected G Q)

theorem encodeSelected_length {n : Nat}
    (G : SimpleGraph (Fin n)) (Q : Finset G.edgeSet) :
  (encodeSelected G Q).chosen.length = Q.card
```

The encoding proofs include the local rim count: lower neighbours count each
internal undirected edge once. The computed local quantity is bounded by the
graph's actual quantity, which is the direction needed for model extension.

`CanonicalRoot.lean` proves existence of a duplicate-free listing of all
fourteen vertices, with the root first, selected neighbours first within the
neighbour block, and the outside block sorted by its type mask. `Relabel.lean`,
`CanonicalProfile.lean`, and `RootProfile.lean` complete the transport and
candidate-coverage proofs. `ProfileEnumeration.lean` proves that branching over
all sorted types covers every completion, and that an invalid partial root
profile cannot extend to a model.

`SixCases.lean` proves `no_obstruction_of_six`: the six premises are
`CompletionFree d s m [] 0 (13-d)` for `(d,s,m)` equal to
`(3,3,0)`, `(4,3,0)`, `(4,3,4)`, `(4,3,16)`, `(4,3,32)`, `(4,4,0)`.
Together they imply exactly `∀ G Q, ¬ Obstruction14 G Q`. The masks 4, 16,
and 32 represent edges `(1,4)`, `(2,4)`, and `(3,4)`. The finite mask tables
are checked by `decide +kernel`, using selected-label independence and the
root local condition.

## Kernel computation and measured search sizes

`SplitSearch.lean` is an untrusted proof generator. Runtime evaluation proposes
concrete intermediate states. Each filter equality and transition equality is
independently checked by the kernel. Each branch theorem follows from the
proved `selectionSearch_split` or `selectionSearch_prune`. It does not call
native reflection and does not declare axioms.

The later `SplitSafe.lean` / `SplitProfiles.lean` route proves `Safe` directly
using the same proved transition soundness, cardinality pruning, and explicit
branching rules. This avoids reducing one giant closed Boolean expression.
The untrusted tactic may choose the tree, but each generated lemma is submitted
to the kernel via `mkAuxLemma`; proposed arithmetic and state equalities are
checked by reduction. The final proof does not trust either native evaluation
or the C++ planner.

The representative profile has root degree four, three selected root edges,
independent root neighbourhood, and outer types `[6,6,6,9,9,9]`. Its 21 candidate
edges require 13 more selected edges.

| Measurement | Result |
|---|---:|
| Binary selection nodes, including pruning leaves | 1,919 |
| Unsplit `decide +kernel`, memory limit 6,000 MB | failed: excessive memory |
| Unsplit run total time including failure diagnosis | 287.1380983 s |
| Split, kernel-checked run | 198.8433097 s |
| Whole-run rate for this profile | about 9.65 nodes/s |
| Axioms of `frozen_checked` | `[propext]` |

The timing includes importing and the small initial checks, so this is a
whole-run measurement, not a pure per-node microbenchmark. Logs are
`fourth_pass/frozen-unchunked.log` and `fourth_pass/frozen-split.log`.

The corrected C++ root-type search gives:

| Root degree / selected root degree | Type profiles | Root-valid profiles | Profiles with enough individually viable candidates | Selection nodes |
|---|---:|---:|---:|---:|
| 3 / 3 | 1,104 | 638 | 94 | 1,551 |
| 4 / 3 | 50,410 | 19,150 | 6,750 | 151,282 |
| 4 / 4 | 30,959 | 11,600 | 2,907 | 49,898 |
| Total | 82,473 | 31,388 | 9,751 | 202,731 |

These runs use sorted type multisets, the incidence capacities, at most nine
outer selected endpoints, and zero/triple pruning. They find no model and
reach no final witness-completion leaf. They are **not proofs**, and their
node ordering differs from the Lean binary search.

The full compiled diagnostic evaluation of the **Lean** enumerator has now
finished (`fourth_pass/lean-statistics.log`). It reports 4,470 / 484,102 /
118,246 binary nodes in the three cases, respectively: **606,818 nodes total**,
with zero open profiles. Evaluation times were 7.308 / 1,023.743 / 265.307
seconds. A C++ transcription matches these three counts exactly
(`fourth_pass/lean-order33.log`, `lean-order43.log`, `lean-order44.log`). This
is not a kernel acceptance theorem. At the certified test profile's measured
rate, the rough sequential extrapolation is about **17.5 hours with the first certificate format**, with the
same limitations about variable profile cost.

A second exploratory route keeps all fourteen labelled slots, includes
isolated padding as zero types, and drops zero/triple pruning. This simplifies
the relabelling obligation. A C++ transcription of the Lean binary branching
and ten-pass propagation order measures:

| Root degree / selected root degree | Profiles | Binary nodes |
|---|---:|---:|
| 3 / 3 | 904 | 42,519 |
| 4 / 3 | 30,959 | 516,382 |
| 4 / 4 | 30,959 | 118,246 |
| Total | 62,822 | 677,147 |

These are exploratory transcription counts, not certified Lean node totals.
Applying the one measured profile's rate gives about 19.5 hours sequentially with the first certificate format,
**only as a rough extrapolation**: profiles have different sizes and costs.
Further label symmetries, stronger reductions, parallel compilation, and
cheaper proofs of individual transitions have not been included in that
estimate. The positive control at fifteen selected edges finds a model; see
`fourth_pass/control15.log`.

## Axioms and validation status

The newer `CutSearch.lean` / `SplitSafe.lean` certificate checks only discarded
candidates and actual transitions; retained candidates need no reduction.
It proves the semantic `Safe` predicate directly. On the same 1,919-node
profile it took **31.6469958 seconds** (about 60.6 nodes/second), with axioms
`[propext, Classical.choice, Quot.sound]`; see `safe-bench.log`.

A larger complete profile-enumeration test has also passed: `profile_bench`
proves `CompletionFree 3 3 0 [0,0,0,0] 0 6`. Its **1,972 profile-tree nodes
and 41,934 selection nodes** were checked in **515.1937798 seconds**, with
the same standard axiom list. See `profile-bench.log`.

The six-case certificate schedule (`certificates/plan.log`) has the following
untrusted planning counts. Every scheduled file is independently checked by
Lean, and the root aggregation theorem checks that no branch was omitted.

| d | s | Inner mask | Selection nodes | Profile-tree nodes | Compilation groups |
|---:|---:|---:|---:|---:|---:|
| 3 | 3 | 0 | 42,411 | 6,418 | 3 |
| 4 | 3 | 0 | 512,150 | 164,923 | 45 |
| 4 | 3 | 4 | 1,099 | 18,036 | 3 |
| 4 | 3 | 16 | 1,109 | 19,377 | 3 |
| 4 | 3 | 32 | 1,217 | 22,293 | 3 |
| 4 | 4 | 0 | 116,632 | 163,379 | 28 |

These counts use all fourteen slots, including zero-type padding, and the six
proved root cases. They differ from the earlier diagnostic generator, which
also included internal-root patterns now excluded by the structural proof.

`ForcedTypes.lean` adds a proved suffix rule: take the bitwise intersection of
all types in `[lower, 2^d)`. Every remaining sorted type contains those bits.
Adding just these forced incidences for all remaining slots gives a subgraph
of every completion; if it violates `valid`, no completion exists. The
`completion_forced_invalid` theorem has only the standard axiom list.
On `group_4_4_0_27`, this reduced 1,501 planned profile nodes to 76 checked nodes
and completed in 8.1217623 seconds. A fresh planning run with this rule gives
119,265 profile-tree nodes instead of 394,426, and the same 674,618 selection
nodes (`certificates/forced-plan.log`). Earlier accepted groups need no rerun;
the final compiled node total therefore reflects both certificate versions.

The later search also tries candidates in a proved-permitted order: the oracle
chooses a candidate whose inclusion leaves few individually possible choices.
`ReorderSafe.lean` proves that moving this pivot to the front preserves `Safe`;
the kernel checks the concrete list decomposition. No rejection is accepted
from the lookahead score. The oracle plans 128,404 selection nodes for the
largest `(4,3,0)` case with this pivot order, compared with 512,150 originally.
This is not a uniform timing improvement: the 1,919-node small benchmark becomes
1,049 nodes but takes 35.7271984 seconds, versus 31.6469958 seconds before
lookahead. A full later group took 163.8007129 seconds. The final counts below
are the actual accepted certificates, including earlier branch orders.

The structural results, search soundness, graph encoding, canonical coverage,
pruning and reordering rules, all six root cases, and the final theorems have
compiled using only the existing toolchain and Mathlib. Their axiom outputs
are subsets of:

```text
[propext, Classical.choice, Quot.sound]
```

The completed split computation `frozen_checked` reports only `[propext]`.
All six root certificates and the three final theorems report exactly
`[propext, Classical.choice, Quot.sound]`. Logs are in
`fourth_pass/certificates/`, `fourth_pass/unconditional.log`, and
`fourth_pass/axioms.txt`.

There is no `sorry`, new axiom declaration, `native_decide`, or `bv_decide`
in the fourth-pass Lean sources. No external SAT solver was run in this pass. The local
C++ programs are exploratory searches, never proof dependencies.
No installation or fetch was performed.
All new files and temporary build outputs are on E:. Existing source statements
and previous reports were preserved.

## Accepted certificate sizes and reproduction

These are actual accepted group logs, not oracle estimates:

| d / s / mask | Groups | Checked profile nodes | Checked selection nodes |
|---|---:|---:|---:|
| 3 / 3 / 0 | 3 | 6,411 | 42,411 |
| 4 / 3 / 0 | 45 | 58,289 | 258,234 |
| 4 / 3 / 4 | 3 | 18,032 | 1,099 |
| 4 / 3 / 16 | 3 | 19,373 | 1,109 |
| 4 / 3 / 32 | 3 | 22,289 | 1,217 |
| 4 / 4 / 0 | 28 | 75,793 | 116,632 |
| **Total** | **85** | **200,187** | **420,702** |

The six root assemblies add 99 profile nodes and no selection nodes. These
counts measure certificate-generation calls, including pruning leaves; they
are not primitive kernel reductions or a minimum proof size. Some earlier
certificates can be bypassed by a later prefix-pruning rule.

The 85 successful group compilers total **13,030.9987651 seconds** of cumulative
process elapsed time (about 3.62 hours). They ran concurrently; this is not
session wall time. Timing rows are `certificates/times_*.tsv`. The 91 group/root
`.olean` files total **842,637,680 bytes**. The fourth-pass directory contains
123 Lean source files, including diagnostics and benchmarks.

The consolidated build rebuilds local mathematical dependencies and the root
assemblies, reuses the 85 certificates already checked individually, and runs
the axiom audit:

```powershell
.\fourth_pass\build.ps1 -ReuseCompiledCertificates
```

This completed successfully in **241.006148 seconds**: 40 modules rebuilt,
85 previously checked certificate groups reused, and the final axiom audit
passed. Only linter/deprecation warnings were emitted.

To regenerate every certificate with the final pruning and pivot rules:

```powershell
.\fourth_pass\build.ps1
```

The build calls the existing Lean executable directly and uses the existing
Mathlib package path. Logs: `fourth_pass/build.log`, `fourth_pass/axioms.txt`,
and `fourth_pass/consolidated-time.txt`. No fetch or installation is needed.

## What is not done

* No SAT/DRAT certificate has been formalized. None is needed by this proof.
* The C++ scheduler and diagnostics are not verified; their output is checked
  or superseded by the Lean coverage and certificate proofs.
* The certificate tree is not optimized to minimum size. The endpoint-ten
  reduction and further label symmetries offer possible future savings.

There is no remaining finite premise, open search leaf, or unproved case in
`no_obstruction14`, `propositionD_unconditional`, or `theorem_F_unconditional`.
