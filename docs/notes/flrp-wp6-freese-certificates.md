<!-- File: docs/notes/flrp-wp6-freese-certificates.md -->

# FLRP design note: certificate checking via Freese traces (WP-6)

This note fixes the certificate format and checker obligations for work package WP-6 (#457) of the FLRP program: how externally computed facts about congruence lattices of finite finitary algebras enter the library as machine-checked results.  The design is built on two short works of Ralph Freese — the algorithms underlying his Universal Algebra Calculator (https://uacalc.org) — and its guiding principle is that **the checker never searches**: all fixpoint iteration and combinatorial work happens in the external engine, and Agda verifies a linear-size witness.  Companion documents: ADR-008 (`docs/adr/008-two-layer-congruence-discipline.md`), the two-layer note (`docs/notes/flrp-two-layer-congruences.md`), and the Layer-D modules of #467/#468 (`Setoid.Congruences.Presented{,.Decidable}`, `Setoid.Congruences.Finite.Decidable`).

## 1. Sources

+  R. Freese, *Partition algorithms*, 3-page note (1997), https://math.hawaii.edu/~ralph/Notes/Partitions/partitions.pdf — partitions as union-find forests (parent vectors, roots carrying negative block size), the Weight Rule and Collapsing Rule, a normal form for partition vectors, `O(n log n)` join, and a root-pair-hashing meet (its Algorithm 4); cites Tarjan's `O(m·α(m,n))` amortized analysis [Tarjan, *Efficiency of a good but not linear set union algorithm*, J. ACM 22 (1975), 215–225] — this is the union-find data structure, which is what "Tarjan's algorithm" refers to in this context.
+  R. Freese, *Computing congruences efficiently*, 6-page preprint, https://math.hawaii.edu/~ralph/Preprints/cg2.pdf — the worklist algorithm for `Cg(a, b)`: seed the partition with `[[a, b]]`, pop a pair, apply every unary polynomial translate, join and enqueue whenever roots differ; correctness (its Theorem 1) and a **linear time bound** `O(r·‖A‖)` in the operation-table size for any fixed nonunary similarity type (its Corollaries 5–6), via the reduction to unary polynomial translates; § 5 extends the seeding to an arbitrary generating partition.
+  Supersession nuance: `cg2` supersedes the 3-page note **only for congruence generation**; it contains no join/meet algorithms, so the 3-pager remains the reference for the lattice-structure computations (join, meet, normal form) used in § 4 below.

## 2. Why the checker must not compute

The Layer-D decision procedure of #467 (`Cg-dec`, the Bool-matrix closure) is specification-grade: it makes `Cg`-membership decidable under `--safe` with a small auditable proof, and it is kept `abstract` so it stays symbolic in goals.  Executing it during type-checking costs on the order of `card²` global rescans per query — workable for the seven-element frontier, prohibitive beyond, and never the point.  Freese's worklist algorithm is the efficient counterpart (rank-bounded: at most `h ≤ n − 1` joins ever occur), but reimplementing it *verified* in Agda is real work (see § 6).  The resolution is the classic proof-certificate move: the engine computes **and emits a witness**; the checker verifies the witness in linear time.

## 3. The key observation: Freese's algorithm is a derivation generator

Each `join-blocks(r, s)` step of the `cg2` worklist algorithm is justified by "unary polynomial translate `p` applied to the previously merged pair `(x, y)`", and the seeding merges are justified by membership in the generating pair list.  The full run therefore produces an ordered list of at most `n − 1` *justified merges* — and that list is literally a skeleton of a `Gen`-derivation in the sense of `Setoid.Congruences.Generation`: seed justifications map to the `base` rule, translate justifications to operation-compatibility, and the forest bookkeeping to symmetry and transitivity.  The engine's execution trace **is** the proof object.

## 4. The certificate format and checker obligations

**Per-congruence certificate**, for a claim `θ ≑ Cg(fromPairs P)`:

+  the claimed partition as a parent vector in Freese **normal form** (each root is the least element of its block; every non-root points directly at its root), which makes equality of claimed partitions a syntactic vector comparison and makes `root` lookups constant-time in the checker;
+  the **Freese trace**: the ordered merge list, each entry a pair together with its justification — a seed pair (index into `P`) or a translate application (operation-symbol index, coordinate, frozen-argument vector, index of an earlier merge).

**Checker obligations**, each free of search and linear in the trace and table size:

+  **C1 (trace soundness)**.  Every merge is derivable: seed entries appear in `P`; translate entries apply one `Gen` compatibility constructor to an earlier entry.  Conclusion: every merged pair lies in `Cg(fromPairs P)`.
+  **C2 (claimed ⊆ generated)**.  Every parent edge of the claimed normal-form forest is covered by the trace's derived pairs (up to the symmetry/transitivity bookkeeping).  Two implementation options, to be settled during implementation: (a) require the trace to derive each forest edge explicitly and check by list membership, or (b) replay the trace's unions with a small verified union-find and compare normal forms; option (a) needs no new verified data structure and is the default.  *Settled during implementation (#457): option (b), in its simplest eager form* — a raw `cg2` trace's merged pairs need not contain the normal-form edges at all, since normal form re-roots every block at its least element after the run, so (a) as stated is unattainable without extending the justification grammar.  The checker (`Setoid.Congruences.Certificates.Congruence`) replays the merges through an eager re-pointing root vector (no ranks, no path compression — those remain engine-side devices) carrying a `Gen`-proof invariant, then aligns the replayed roots with the claimed vector by one linear sweep; cost `O(n·|trace|)`, one pass, no search.
+  **C3 (generated ⊆ claimed)**.  The claimed partition contains `P` and is a congruence.  Being a partition, it is an equivalence for free; operation-compatibility need only be checked on the **forest edges**: if `p(i)` and `root(i)` land in the same claimed block for each of the `≤ n − 1` edges and each of the `k` unary translates, compatibility for arbitrary related pairs follows by symmetry and transitivity through the roots.  Cost: `O(k·n)` root comparisons — linear in the table size.

C1–C3 together give `θ ≑ Cg(fromPairs P)` by `base`/`Cg-least`, with zero fixpoint iteration in the checker.

**Whole-lattice certificate**, for a claim about `Con(𝑨)` at Layer D (a `FiniteCongruencesᵈ` instance, or downstream `Representableᵈ` for a target lattice `L`):

+  the list of claimed congruences (normal-form vectors), each with a per-congruence certificate for its principal presentation where needed;
+  for every carrier index pair `(i, j)`, a pointer to the list entry claimed to be `Cg(enum i, enum j)`, with its Freese trace — this is what pins the list against all principal congruences;
+  the order and structure data: `θ ≤ ψ` is verified by root lookups (each block of `θ` inside a block of `ψ`); the **meet** of two listed congruences is claimed by pointer and verified directly — the meet of partitions is the pointwise root-pair intersection, so the checker confirms `i, j` related in the claimed meet iff related in both arguments, with no hashing; joins are claimed by pointer and verified through the principal-congruence pointers.  The 3-pager's root-pair-hashing meet (Algorithm 4) and union-find join are **engine-side** devices for producing these tables quickly; the checker's verification is definitional and linear-per-pair.

## 5. The engine

Any producer of Freese traces will do; two candidates, either satisfying WP-6's emitter deliverable:

+  **UACalc itself**, instrumented to emit the merge trace its congruence-generation code already performs — the library's checked results would then ride on the same algorithms that produced the field's computational folklore, which is a fitting provenance;
+  a standalone reimplementation of the `cg2` worklist algorithm (on the order of a hundred lines in any of the project's approved script languages), which may be simpler to wire into the certificate pipeline than instrumenting Java.

## 6. Parked as an explicit non-goal: verified union-find in Agda

A verified implementation of the worklist algorithm (Weight Rule, rank-bounded termination via `h ≤ n − 1`, correctness as in `cg2` Theorem 1) would give fast *in-Agda* congruence computation.  It is deliberately **not** part of WP-6: the certificate design above removes the need, and the Layer-D abstraction boundary (`Cg-dec` is a `Dec`-valued interface with an `abstract` implementation) means a fast decider can be swapped in later without touching any theorem.  Revisit only if a concrete consumer needs in-Agda computation at scale.

## 7. Side observation for WP-3

The unary-polynomial-translate reduction that powers `cg2` (congruences of `𝑨` = congruences of its translate unary algebra) is the same reduction Pálfy–Pudlák use; the translate machinery of `Setoid.Signatures.Finite` (#467) is positioned to express it, and WP-3 (#454) may want it stated as a lemma.

## 8. Impact on WP-6 (#457)

The issue's four tasks are refined as follows: the *schema* is the normal-form vector plus Freese trace of § 4; the *checker* discharges obligations C1–C3 and the whole-lattice pointers; the *emitter* is § 5; the *pilot* re-verifies one thesis-era small-lattice representation end-to-end through this pipeline.  The issue text is updated to match this note.
