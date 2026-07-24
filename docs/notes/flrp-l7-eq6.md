<!-- File: docs/notes/flrp-l7-eq6.md -->

# FLRP session note: `L7` inside `Eq(6)`, and closure obstructions through eight points

This note records the results of a 2026-07-22 working session on `L7`, the distinguished open instance of the FLRP program (issue #484, part of the #483 campaign; roadmap § 5.A.1): its minimal representation as a sublattice of a finite partition lattice, the classification of all such representations, and machine-checked closure obstructions showing that no algebra on at most eight elements has `L7` as its congruence lattice.  All computations are reproducible with the search tooling of issue #486 (`scripts/python/flrp/eqsearch.py`, landing on top of the WP-6 pipeline of PR #482), where the census figures below are pinned as regression tests.

**Naming**.  `L7` is this library's name for the lattice (`Examples.Classical.Lattices.L7`).  In the DeMeo–Freese–Jipsen manuscript *Representing Finite Lattices as Congruence Lattices of Finite Algebras* (`SmallLatticeReps.tex`, https://github.com/UniversalAlgebra/fin-lat-rep) the same lattice is `L10`, and the manuscript's `L7` is a different lattice; every artifact of the #483 campaign states which numbering it uses.

## 1. The lattice

`L7` has seven elements: a `2 × 3` grid — the product of a two-chain and a three-chain — together with one doubly irreducible element `x` satisfying `⊥ < x < ⊤` and incomparable to every nontrivial grid element.  We use the element numbering of `Examples.Classical.Lattices.L7`:

```text
0 = ⊥,   1 = (1,0),   2 = (0,1),   3 = x,   4 = (1,1),   5 = (0,2),   6 = ⊤
```

so the atoms are `1`, `2`, `3`, the coatoms are `4`, `5`, `3`, and the covers are `0 ≺ 1, 2, 3`;  `1, 2 ≺ 4`;  `2 ≺ 5`;  `4, 5, 3 ≺ 6`.

One structural fact does real work below: `L7` is **simple** — collapsing any covering pair propagates to the total congruence.  (Routine check; for instance from `1 ≡ 0`: joining with `2` gives `4 ≡ 2`, joining with `5` gives `6 ≡ 5`, meeting with `3` gives `3 ≡ 0`, joining with `1` gives `6 ≡ 1`, and meeting with `2` gives `2 ≡ 0` — total collapse.  The other eight covers are similar, and all nine were machine-checked.)

## 2. The minimal sublattice representation

By Pudlák–Tůma every finite lattice embeds in `Eq(X)` for some finite set `X`; the session determined the minimal `X` for `L7` and all embeddings up to symmetry.  Two normalizations cost nothing in a minimum-size representation: the bottom must be the diagonal `Δ` (otherwise quotient by it — the interval above it in `Eq(X)` is a smaller partition lattice), and the top must be the total relation `∇` (otherwise the representation lives in a direct product of smaller partition lattices, and simplicity of `L7` forces a faithful projection to one factor).  These are also exactly the bounds a congruence lattice must have, which is what § 4 exploits.

Exhaustive search shows `Eq(4)` and `Eq(5)` contain no copy of `L7`, while `Eq(6)` does.  An explicit embedding, with partitions of `{0, …, 5}` in bar notation (singleton blocks suppressed; a fenced block rather than a table, since GitHub and python-markdown disagree about pipes inside table cells):

```text
⊤     = 6      ∇ = |0,1,2,3,4,5|
(1,1) = 4      |0,1,2|3,4,5|
(0,2) = 5      |0,1|2,3|4,5|
x     = 3      |0,4|1,3|2,5|
(1,0) = 1      |0,2|3,4|
(0,1) = 2      |0,1|4,5|
⊥     = 0      Δ = |0|1|2|3|4|5|
```

The two squares of the grid are visible directly: `|0,2|3,4| ∨ |0,1|4,5| = |0,1,2|3,4,5|` with meet `Δ`, and `|0,1,2|3,4,5| ∧ |0,1|2,3|4,5| = |0,1|4,5|` with join `∇`; the matching `|0,4|1,3|2,5|` meets every other nontrivial element at `Δ` and joins it to `∇`.  The full `7 × 7` meet and join tables were machine-verified.

## 3. Classification of the `Eq(6)` copies

`Eq(6)` contains exactly **1080** labelled copies of `L7` (with bounds at `Δ`/`∇`), and exactly **two** up to relabeling of the six points:

+  the **symmetric class** — the copy above, invariant under the involution `(0 4)(1 5)(2 3)`; orbit size 360;
+  the **rigid class** — obtained from the same six other partitions by replacing `x ↦ |0,3|1,4|2,5|`; trivial stabilizer, orbit size 720.

The two representatives share six of their seven partitions, differing only in the matching assigned to `x`; no relabeling of the points carries one class to the other.

## 4. The closure test on six points

A copy of `L7` in `Eq(6)` is the congruence lattice of an algebra on those six points iff it is **closed** in the Snow sense: since the congruence lattice of an arbitrary algebra is determined by its unary polynomials, the minimal candidate congruence lattice containing the copy is `Inv(M)`, the relations preserved by the monoid `M` of *all* unary maps preserving the copy's five nontrivial relations, and the copy is a congruence lattice — of the unary algebra `⟨X, M⟩`, and of nothing smaller — exactly when `Inv(M)` adds nothing.

Neither class is closed, and the failure is emphatic — `M` contains **no non-bijective non-constant map at all** in either class:

| class | preserving group | monoid size | proper maps | size of Inv(M) | closed |
|---|---|---|---|---|---|
| symmetric | `⟨(0 4)(1 5)(2 3)⟩`, order 2 | 8 | 0 | 31 | no |
| rigid | trivial | 7 | 0 | 203 | no |

For the symmetric class `Inv(M)` is the lattice of all partitions invariant under the involution (31 of the 203 partitions of a six-set); for the rigid class it is all of `Eq(6)`.  Consequently **no algebra on six elements has congruence lattice isomorphic to `L7`** — through either class, and there are no other classes.

## 5. Seven and eight points

The same sweep one size up: `Eq(7)` contains **55,440** labelled copies of `L7` in **12** classes up to relabeling — two with a stabilizer of order 2, ten rigid.  Again no class admits any non-bijective non-constant preserving map; `|Inv(M)|` is 59 for the two symmetric classes (the involution-invariant partitions of a seven-set) and 877 (all of `Eq(7)`) for the ten rigid ones.  No class is closed, so **no algebra on at most seven elements has congruence lattice isomorphic to `L7`**.

The eight-point sweep (run 2026-07-22 with the vectorized engine, about five minutes of compute) settles the next size as well.  `Eq(8)` contains **4,112,640** labelled copies of `L7` in **108** classes up to relabeling: 12 classes with a stabilizer of order 2 (orbit size 20,160) and 96 rigid classes (orbit size 40,320).  Two qualitatively new things happen at eight points.

+  **Proper preserving maps finally appear**: seven of the rigid classes admit between one and four non-bijective non-constant maps, and there `|Inv(M)|` drops to 864 (four classes), 337, 131, and once as low as **50**.  The endomorphism wall of the smaller sweeps is a small-carrier artifact, not a structural feature of `L7`.
+  They are still nowhere near enough: the remaining rigid classes have `|Inv(M)| = 4140` (all of `Eq(8)`), the symmetric classes have 164 (the involution-invariant partitions of an eight-set), and even the best class stops at 50 against the required 7.

No class is closed, so **no algebra on at most eight elements has congruence lattice isomorphic to `L7`**.

## 6. Consequences and next steps

+  Combined with the manuscript's § 5 theorem that a minimal representation of `L10 = L7` cannot come from an intransitive permutation group: a minimal representation, if one exists, is the congruence lattice of a **transitive G-set on at least nine points**.
+  The nine-point frontier: the algebra side is an `Eq(9)` closure sweep (`Bell(9) = 21,147`; the tables alone are ~1.8 GB at `int16`, so the vectorized engine needs blocking before this is comfortable), while the group side — the transitive-degree scan of #487 (`TransitiveGroup(n, k)` with point stabilizer `H`, testing `[H, G] ≅ L7`) — becomes the cheaper attack from here out, with degrees 8 and below now serving only as cross-validation of the sweeps.  (Settled 2026-07-24: under this transitivity reduction only the *uniform* copies matter, the tables shrink to nothing, and § 8's sweeps find no copy on nine or ten points — the frontier now stands at twelve; the group side confirms this through degree twelve — § 9.)
+  The proper-maps phenomenon at eight points suggests a heuristic for larger carriers: classes whose monoids acquire non-bijective maps are the ones to watch, and the gap `|Inv(M)| − 7` is a measure of how far a class is from closure; tracking its minimum across sizes gives the campaign a progress metric.
+  A closed class at any size yields a finite algebra with `Con ≅ L7` and flows directly into the certificate pipeline of PR #482 for an Agda-checked `Representableᵈ` witness — the headline outcome, if it exists.
+  The positive fact of § 2 is formalized in `FLRP.L7EqSix`: the seven listed partitions, as normal-form parent vectors, with decided meets, decided join upper bounds, and join least-ness over arbitrary equivalence relations via bounded alternating chains (fuel four suffices, and the module's decisions re-verify it).  How much of the *negative* sweeps is worth certifying in Agda — the per-class `Inv(M)` computations are plain finite checks, the exhaustiveness of the embedding census is the hard part — is an open task on #484; the decision will be recorded here.

## 7. Reproduction

With the #486 tooling in place (branch `486-m6-14c-flrp-search-tooling`, on top of PR #482):

```sh
make flrp-test                          # pins the Eq(6) census and closure verdicts
FLRP_EQSEARCH_SLOW=1 make flrp-test     # adds the Eq(7) sweep (about five minutes)
```

or directly, with a target file holding the `L7` meet and join tables:

```sh
python3 scripts/python/flrp/eqsearch.py l7.json 6 --json l7-eq6-report.json
```

The report format (`flrp-eqsearch v1`) lists every class with its representative partitions (as Freese normal-form parent vectors), orbit size, preserving-group order, monoid size, `|Inv(M)|`, and closure verdict; output is deterministic, so re-runs are byte-identical.

The eight-point sweep used a numpy-vectorized engine (partitions as an `int8` parent-vector matrix, first-occurrence normal forms for meets, alternating block-min label propagation for joins, and per-class vectorized orbit generation).  That backend is now in the repository as `scripts/python/flrp/eqfast.py` (`--fast` on the `eqsearch.py` CLI), pinned byte-identical to the pure engine where both run, and the `Eq(8)` result is committed as the citable report `scripts/python/flrp/out/l7_eq8_report.json`, reproducible with

```sh
python3 scripts/python/flrp/eqsearch.py scripts/python/flrp/inputs/l7_lattice.json 8 --fast --json report.json
```

(about three hours with numpy installed — the generic engine trades the session engine's schedule-specific constraint order for generality, and a constraint-density-guided order is follow-up on #486; the `Eq(8)` figures have now been produced by two independent implementations — the session's schedule-specific engine and the repository's generic one — agreeing exactly, on top of both reproducing every smaller census).

## 8. Addendum (2026-07-24): nine, ten, and eleven points fall to the uniform sweep

The `--group-rep` restriction of issue #494 (`eqsearch.py`, either engine) sweeps only **uniform** copies — every member partition with all blocks of one size — mechanizing remark iv of the manuscript's closure-algorithm discussion (§ 6.1): the congruences of a transitive permutation group action are its systems of imprimitivity, whose blocks are cosets of intermediate subgroups and hence all of equal size.  By § 6's reduction (the manuscript's § 5: `L10` = library `L7` satisfies conditions (A) and (B″), so a minimal representation, if one exists, must be by a transitive permutation group) and with §§ 4–5 placing the minimal size at nine or beyond, the nine-point question *is* the uniform question, and the restriction's weakened negative verdict ("no algebra whose congruence lattice consists of uniform partitions" — README, uniform-restriction note) costs nothing here.

The machine answer is emphatic: on nine and on ten points there is **no uniform copy of `L7` at all** — not merely no closed class, but an empty census.

+  **`Eq(9)`: zero uniform copies**, from a nontrivial pool of 280 (all of shape `3³`).  Fast engine 0.65 s, pure engine 1.87 s, byte-identical reports; committed as `scripts/python/flrp/out/l7_eq9_uniform_report.json` and re-derived by `make flrp-test` on every run.
+  **`Eq(10)`: zero uniform copies**, from a nontrivial pool of 1,071 (shapes `2⁵` and `5²`).  Pure engine 6 m 59 s, fast engine 24 m 12 s — at a pool this narrow the constant per-prefix cost of mask arithmetic outweighs the vectorization, so the pure engine wins — byte-identical reports; committed as `out/l7_eq10_uniform_report.json`, re-derived under `FLRP_EQSEARCH_SLOW=1`.

The emptiness is structural, and the sweeps verify it exhaustively.  Any copy of `L7` embeds the cover `(0,1) ≺ (1,1)` of the grid, so it needs two *comparable* nontrivial uniform partitions, and comparability of uniform partitions forces block sizes `1 < a < b < n` with `a | b` (each larger block is a disjoint union of smaller ones) and `b | n`.  No such divisor chain exists at `n = 9` (the only nontrivial size is 3, so the 280 pool members form an antichain) or at `n = 10` (sizes 2 and 5, and `2 ∤ 5`); at `n = 11` the pool is empty outright — a transitive action of prime degree is primitive.  The first ground-set size where a uniform copy of `L7` is even conceivable is `n = 12`, whose pool (32,032 nontrivial members of shapes `2⁶`, `3⁴`, `4³`, `6²`) has genuine chains `2 | 4`, `2 | 6`, `3 | 6`.

Chaining the manuscript's transitivity theorem through the sizes:

+  a nine-point representation would be minimal (§§ 4–5), hence transitive, hence a uniform copy of `L7` in `Eq(9)` — and there is none: **no algebra on nine points has `Con ≅ L7`**;
+  a ten-point representation would then be minimal, hence transitive — and `Eq(10)` has no uniform copy: **none on ten points**;
+  an eleven-point representation would then be minimal, hence transitive of prime degree, hence primitive with the two-element congruence lattice: **none on eleven points**.

**The minimal representation of library `L7` (manuscript `L10`), if one exists, has at least twelve elements**.  The machine-checked steps are the two empty censuses, each produced independently by the pure and the vectorized engine with byte-identical reports; the reduction to the transitive case is the manuscript's § 5 theorem, cited here, not re-proved; the step at eleven is the empty prime pool itself.

Next steps, sharpened by this addendum:

+  The decisive computation is now the `Eq(12)` uniform sweep — the first size with candidate copies.  The current engines need real work there: pool² tables reach ~4.1 GB at `int16`, `12! ≈ 4.8 × 10⁸` makes materialized per-class orbits hours apiece, and the `Eq(10)` timings above calibrate the per-prefix costs.  Orbit–stabilizer classification (count the stabilizer, divide `12!`) and blocked or on-the-fly meet/join membership are the known fixes — follow-up on #494/#486.
+  The cross-validating attack is #487's transitive-degree scan (`scripts/gap/flrp/`): degrees 9–11 must come back empty for `L7` intervals by the divisor argument above, and degree 12 is where the two methods first probe genuinely new ground together; disagreement in either direction is a bug or a discovery.

Reproduction (the `--fast` flag is optional; at these pool widths the pure engine is competitive or faster, and reports are byte-identical either way):

```sh
python3 scripts/python/flrp/eqsearch.py scripts/python/flrp/inputs/l7_lattice.json 9 --group-rep --json l7-eq9u.json
python3 scripts/python/flrp/eqsearch.py scripts/python/flrp/inputs/l7_lattice.json 10 --group-rep --json l7-eq10u.json
```

## 9. Group-side cross-check: the transitive-degree scan (#487)

The uniform sweeps of § 8 are the algebra side of the transitivity reduction; the group side is #487's degree-by-degree scan.  By the manuscript's § 5 theorem a minimal representation of `L7` is a transitive `G`-set, and a transitive `G`-set of degree `n` is `G` acting on the cosets of a point stabilizer `H` of index `n`, with `Con(G ↷ G/H) ≅ [H, G]`.  So testing `[H, G] ≅ L7` over every `TransitiveGroup(n, k)` is exactly the group-realizable half of the `Eq(n)` uniform question — and, being over actual groups, it needs no closure test.  The GAP engine (`scripts/gap/flrp/`, A. Hulpke's `IntermediateSubgroups`) carries it out; prime degrees are free negatives (transitive ⇒ primitive ⇒ two-element interval) and are skipped.

Every degree through twelve comes back **negative**:

| degree | transitive groups | size-7 point-stabilizer intervals | ≅ L7 |
|---|---|---|---|
| 8 | 50 | 0 | — |
| 9 | 34 | 0 | — |
| 10 | 45 | 0 | — |
| 11 | prime | primitive: two-element interval | — |
| 12 | 301 | 18 | 0 |

Degrees 8, 9, 10 have no size-7 interval at all (at degree 8 the interval sizes are `{2, 3, 4, 6, 8, 10, 16}`); degree 12 is the first with size-7 intervals — 18 of them — but none is `L7`.  Degree 8 **cross-validates the `Eq(8)` closure sweep** of § 5, and the scan matches the § 8 uniform sweeps degree for degree.

The degree-12 verdict *sharpens* the § 8 frontier.  Section 8 leaves the `Eq(12)` uniform sweep as the decisive open computation; the group side settles its minimality-relevant part directly.  Chaining the transitivity theorem: § 8 rules out a representation on nine, ten, or eleven points, so a **twelve**-point representation would be of minimal size, hence transitive, hence a degree-12 interval `≅ L7` — and the scan finds none among all 301.  Therefore **no algebra represents `L7` on twelve points either, and a minimal representation, if one exists, has at least thirteen elements** — one past the § 8 bound.  (The full `Eq(12)` uniform closure sweep of #494 would confirm this on the algebra side; degree twelve is where the two methods first meet genuinely new ground, and they agree.)

Reproduction (inside `nix develop .#gap`, GAP 4.15.1, transgrp 3.6.5; committed reports `scripts/gap/flrp/out/l7_transitive_deg{8,9,10,12}.search.json`, format `flrp-gap-search v1`):

```sh
for d in 8 9 10 12; do
  gap -A -q -c "FLRP_DEGREE := $d;;" -b scripts/gap/flrp/bin/scan_transitive.g
  python3 scripts/python/flrp/gap_search.py \
      scripts/gap/flrp/out/l7_transitive_deg$d.raw.json \
      --target scripts/python/flrp/inputs/l7_lattice.json \
      --out scripts/gap/flrp/out/l7_transitive_deg$d.search.json --date 2026-07-24
done
```
