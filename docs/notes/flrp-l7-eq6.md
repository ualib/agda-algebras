<!-- File: docs/notes/flrp-l7-eq6.md -->

# FLRP session note: `L7` inside `Eq(6)`, and closure obstructions through seven points

This note records the results of a 2026-07-22 working session on `L7`, the distinguished open instance of the FLRP program (issue #484, part of the #483 campaign; roadmap § 5.A.1): its minimal representation as a sublattice of a finite partition lattice, the classification of all such representations, and machine-checked closure obstructions showing that no algebra on at most seven elements has `L7` as its congruence lattice.  All computations are reproducible with the search tooling of issue #486 (`scripts/python/flrp/eqsearch.py`, landing on top of the WP-6 pipeline of PR #482), where the census figures below are pinned as regression tests.

**Naming**.  `L7` is this library's name for the lattice (`Examples.Classical.Lattices.L7`).  In the DeMeo–Freese–Jipsen manuscript *Representing Finite Lattices as Congruence Lattices of Finite Algebras* (`SmallLatticeReps.tex`, https://github.com/UniversalAlgebra/fin-lat-rep) the same lattice is `L10`, and the manuscript's `L7` is a different lattice; every artifact of the #483 campaign states which numbering it uses.

## 1. The lattice

`L7` has seven elements: a `2 × 3` grid — the product of a two-chain and a three-chain — together with one doubly irreducible element `x` satisfying `⊥ < x < ⊤` and incomparable to every nontrivial grid element.  We use the element numbering of `Examples.Classical.Lattices.L7`:

```text
0 = ⊥,   1 = (1,0),   2 = (0,1),   3 = x,   4 = (1,1),   5 = (0,2),   6 = ⊤
```

so the atoms are `1`, `2`, `3`, the coatoms are `4`, `5`, `3`, and the covers are `0 ⋖ 1, 2, 3`;  `1, 2 ⋖ 4`;  `2 ⋖ 5`;  `4, 5, 3 ⋖ 6`.

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
| symmetric | `⟨(0 4)(1 5)(2 3)⟩`, order 2 | 9 | 0 | 31 | no |
| rigid | trivial | 7 | 0 | 203 | no |

For the symmetric class `Inv(M)` is the lattice of all partitions invariant under the involution (31 of the 203 partitions of a six-set); for the rigid class it is all of `Eq(6)`.  Consequently **no algebra on six elements has congruence lattice isomorphic to `L7`** — through either class, and there are no other classes.

## 5. Seven points

The same sweep one size up: `Eq(7)` contains **55,440** labelled copies of `L7` in **12** classes up to relabeling — two with a stabilizer of order 2, ten rigid.  Again no class admits any non-bijective non-constant preserving map; `|Inv(M)|` is 59 for the two symmetric classes (the involution-invariant partitions of a seven-set) and 877 (all of `Eq(7)`) for the ten rigid ones.  No class is closed, so **no algebra on at most seven elements has congruence lattice isomorphic to `L7`**.

## 6. Consequences and next steps

+  Combined with the manuscript's § 5 theorem that a minimal representation of `L10 = L7` cannot come from an intransitive permutation group: a minimal representation, if one exists, is the congruence lattice of a **transitive G-set on at least eight points**.
+  The eight-point frontier is attackable from both sides, and the two attacks cross-validate: the algebra side is the `Eq(8)` closure sweep (needs the vectorized tooling of #486 — `Bell(8) = 4140`), and the group side is the transitive-degree scan of #487 (`TransitiveGroup(8, k)` with point stabilizer `H`, testing `[H, G] ≅ L7`), which by the transitivity theorem settles minimal representations degree by degree.
+  A closed class at any size yields a finite algebra with `Con ≅ L7` and flows directly into the certificate pipeline of PR #482 for an Agda-checked `Representableᵈ` witness — the headline outcome, if it exists.
+  The positive fact of § 2 deserves formalization on its own: the seven listed partitions form a sublattice of `Eq(6)` isomorphic to `L7`, checkable by decision over the finite carrier in the style of `Examples.Classical.Lattices.L7` (task on #484).  How much of the *negative* sweeps is worth certifying in Agda — the per-class `Inv(M)` computations are plain finite checks, the exhaustiveness of the embedding census is the hard part — is an open task on #484; the decision will be recorded here.

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
