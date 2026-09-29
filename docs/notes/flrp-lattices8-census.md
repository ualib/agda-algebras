<!-- File: docs/notes/flrp-lattices8-census.md -->

# The eight-element lattices: what the formal closure properties cover

Kjos-Hanssen's September 2026 note on the eight-element congruence lattices
(`CLFA8.pdf`, William's copy) sorts the 222 lattices with eight elements into
those representable "for formal reasons" and 54 that are not, and reports a
representation, or none, for each of the 54.  The formal reasons are three:
the lattice is distributive; it is an *adjoined ordinal sum*, an element
other than the bounds being comparable with everything; or it is a *parallel
sum*, "identifying the tops and the bottoms of `L₁` and `L₂`", which the
note tests by the comparability graph on the proper part being disconnected.
The first two are theorems (Dilworth; Snow 2000, Lemma 3.6).  The third is
not, and this note records what it does and does not cover, by a census of
the 222 lattices (`scripts/python/flrp/lattices8.py`), and what the
searches of the same day say about the lattices left uncovered.  It was
written on 2026-09-28 during the M6-27 pass ([issue #578]), after the first
version of the pass's notes had adopted the note's classification of the
parachute `P(2×2, 2×2)`; William caught the error ("parachutes are not
parallel sums") on the day.

## 1.  Snow's parallel sum, read in the text

Snow's *A constructive approach to the finite congruence lattice
representation problem* (Algebra Universalis 43, 2000, pp. 279–293) was
obtained on 2026-09-28 (`2000-Snow-ConstructiveApproach.pdf`, supplied by
William) and read in full.  The relevant definitions and lemmas, with their
proofs checked, are these.

+  **Definition** (p. 286).  For lattices `L` and `N`, the parallel sum
   `L ∓ N` has as universe the disjoint union of `L` and `N` *together with
   two new elements* `0` and `1`; `x ≤ y` when `x ≤ y` in `L`, or in `N`,
   or `y = 1`, or `x = 0`.  So `L ∓ N` has `|L| + |N| + 2` elements, and the
   tops of `L` and `N` are coatoms of it, not its top.
+  **Lemma 3.2** (p. 282).  For a finite algebra `A` and *any* equivalence
   relations `α`, `β` on its carrier there is an algebra `A′` on the same
   carrier with `Con A′ = {x ∈ Con A : x ≤ α or x ≥ β}`.  (The proof is by
   primitive positive definitions and the path lemma 3.1.)  With Lemma 3.3
   (`Con C = Con A ∩ Con B` for the algebra `C` carrying the operations of
   both) this gives **Corollary 3.8**: if `α ≤ β` and `γ ≤ δ` are
   congruences of `A` with `α ∨ γ = 1` and `β ∧ δ = 0`, some algebra on the
   carrier has congruence lattice `{0} ∪ [α, β] ∪ [γ, δ] ∪ {1}`.  (Take the
   two unions `{x ≤ β} ∪ {x ≥ γ}` and `{x ≤ δ} ∪ {x ≥ α}` and intersect;
   the four pieces are `{x ≤ β ∧ δ} = {0}`, `[α, β]`, `[γ, δ]`, and
   `{x ≥ α ∨ γ} = {1}`.)
+  **Lemma 3.9** (p. 287).  If `L` is representable, so is `L ∓ 1`, where
   `1` is the one-element lattice.  *Construction*: take `A` unary with
   `Con A ≅ L`, double the carrier to `B = C ⊔ A` with `C` a copy of `A`,
   and let `α` collapse `C` and nothing else, `β` have the two blocks `C`
   and `A`, and `γ` match each element of `C` with its copy in `A`.  Then
   `β ∧ γ = 0` and `α ∨ γ = 1`, so Corollary 3.8 applied to the algebra
   with no operations gives `B₁` with `Con B₁ = {0, 1, γ} ∪ [α, β]`, and
   `[α, β] ≅ Eq(A)` by `θ ↦ θ ∪ C²`.  Adding the operations `p̄` (each
   basic operation `p` of `A` acting on `A` and on its copy `C` alike)
   preserves `γ` and cuts `[α, β]` down to `{θ ∪ C² : θ ∈ Con A}`, so
   `Con B = {0, 1, γ} ∪ {θ̄ : θ ∈ Con A} ≅ L ∓ 1`.
+  **Lemma 3.10** (p. 287).  `L₁ ∓ L₂` is representable if and only if `L₁`
   and `L₂` are.  *Construction*: in `(L₁ ∓ 1) × (L₂ ∓ 1)`, representable by
   Lemma 3.9 and the product closure (Lemma 3.5), let `aᵢ` be the point of
   `Lᵢ ∓ 1` beside `Lᵢ`; the intervals `[⟨0₁, a₂⟩, ⟨1₁, a₂⟩] ≅ L₁` and
   `[⟨a₁, 0₂⟩, ⟨a₁, 1₂⟩] ≅ L₂` (with `0ᵢ`, `1ᵢ` the bounds of `Lᵢ`) have
   tops meeting to the bottom of the product and bottoms joining to its top,
   so Corollary 3.8 yields `{0, 1} ∪ L₁ ∪ L₂ ≅ L₁ ∓ L₂`.  The "only if" is
   Lemma 3.4 (intervals of representable lattices are representable).
+  **Two remarks on the proofs**, neither affecting the statements.  Lemma
   3.9's construction needs `|A| ≥ 2`: for the one-element lattice the
   matching `γ` is the total relation and the construction returns the
   two-element lattice, while `1 ∓ 1` is the four-element Boolean lattice,
   which is distributive and representable anyway.  Lemma 3.10's displayed
   equations `⟨1₁, a₂⟩ ∧ ⟨a₁, 1₂⟩ = ⟨0₁, 0₂⟩` and `⟨0₁, a₂⟩ ∨ ⟨a₁, 0₂⟩ =
   ⟨1₁, 1₂⟩` use `0ᵢ`, `1ᵢ` for the bounds of `Lᵢ` in the second and for the
   bounds of `Lᵢ ∓ 1` in the first; read as "the meet is the bottom of the
   product and the join is its top", which is what Corollary 3.8 needs,
   both hold.

## 2.  What the glued sum would give

Write `L₁ ∥ L₂` for the operation Kjos-Hanssen's note describes: the
disjoint union of `L₁` and `L₂` with the two tops identified and the two
bottoms identified, `|L₁| + |L₂| − 2` elements.  Its proper part is the
disjoint union of the proper parts, so the note's criterion (a disconnected
comparability graph on `L ∖ {0, 1}`) characterizes the lattices of the form
`L₁ ∥ L₂` with both `Lᵢ` smaller than `L`, exactly as the note says.

+  **Closure under `∥` is not a theorem.**  `Mₙ`, the lattice of height two
   with `n` atoms, is `3 ∥ 3 ∥ ⋯ ∥ 3` (`n` copies of the three-element
   chain), so a class closed under `∥` and containing the three-element
   chain contains every `Mₙ`.  Whether every `Mₙ` is a congruence lattice
   is open; `M₁₆` is the least case not settled by Pálfy–Pudlák, Köhler,
   Feit, Pálfy, and Lucchini (`docs/notes/flrp-m6-27-paths.md` § 4;
   `FLRP.Reductions.Lucchini`).  So no published theorem gives closure under
   `∥`, and none can without settling `M₁₆`.
+  **Nor does Snow's lemma cover the flat sum of three or more lattices**,
   the disjoint union of `L₁, …, Lₙ` with one new top and one new bottom:
   `Mₙ` is the flat sum of `n` one-element lattices.  Lemma 3.10 iterated
   gives the *nested* sums `(L₁ ∓ L₂) ∓ L₃`, in which the bounds of
   `L₁ ∓ L₂` survive as elements.  (The obvious attempt, the union of the
   `n` intervals `⟨a, …, Lᵢ, …, a⟩` in `∏ (Lᵢ ∓ 1)` with the bounds, is
   not the congruence lattice of any algebra for `n = 3`: the primitive
   positive definition `(r₂ ∘ r₃) ∧ (r₃ ∘ r₁) ∧ (r₁ ∘ r₂)` from one element
   `rᵢ` of each interval defines the equivalence relation
   `⟨a₁, a₂, a₃⟩`, which is not in the union.)
+  **What Snow's lemma does give.**  `L₁ ∥ L₂` is representable whenever
   the proper parts of `L₁` and `L₂` are both intervals, that is, whenever
   `L₁` and `L₂` each have a unique atom and a unique coatom: then
   `L₁ ∥ L₂ = L₁° ∓ L₂°` for the intervals `Lᵢ°` between the atom and the
   coatom, which are representable by Lemma 3.4 when the `Lᵢ` are.  In the
   note's terms: a lattice whose proper part has *exactly two* components,
   *each an interval*, is a parallel sum in Snow's sense.

**Parachutes are not parallel sums.**  The parachute `𝒫(L₁, …, Lₙ)` of the
RP-1 note identifies the *tops* of the canopies and adjoins one new bottom
below their bottoms: it is `(2 ⊕a L₁) ∥ ⋯ ∥ (2 ⊕a Lₙ)`, a glued sum, and a
Snow sum only when `n = 2` and both canopies have a unique coatom, in which
case `𝒫(L₁, L₂) = L₁⁻ ∓ L₂⁻` for the canopies with their tops removed.  The
hexagon `P(3, 3) = 2 ∓ 2` and `P(3, 4) = 2 ∓ 3` are Snow sums; `P(3, 3, 2)`
(three canopies), `P(3, 2×2)` (a canopy with two coatoms), and `P(2×2, 2×2)`
are not.  The first two of those three have seven elements and are
representable by the seven-element census (roadmap § 3); `P(2×2, 2×2)` has
eight, and § 3 below is about it and its sixty companions.

## 3.  The census

`scripts/python/flrp/lattices8.py` (`make flrp-lat8`; pinned by
`test_lattices8.py` in `make flrp-test`) enumerates the lattices with eight
elements up to isomorphism (222, agreeing with OEIS A006966, and with the
counts 1, 1, 1, 2, 5, 15, 53 below eight), classifies each by the note's
three kinds, matches the note's Table 1 lattice for lattice through its
transcribed cover lists, and splits the note's parallel sums by Snow's
criterion.  The record is `scripts/python/flrp/out/lattices8_census.json`.

| Count | Lattices with eight elements |
| ---: | --- |
| 222 | all, up to isomorphism |
| 15 | distributive |
| 96 | adjoined ordinal sums |
| 69 | disconnected proper part (the note's "parallel sums") |
| 168 | of at least one of the three kinds |
| 54 | of none, and these are exactly the 54 of the note's Table 1, duals included |
| 8 | of the 69: proper part with two components, each an interval (Snow's Lemma 3.10 applies) |
| 61 | of the 69: not so, and not distributive either (no formal reason stands) |
| 15 | simple as lattices (the note's `#35`, represented in `Eq(4)` in its Table 1, and 14 of the 61) |

The note's counts are reproduced exactly, which fixes the reading of its
definitions; its Theorem 1, "at least 212 of the 222 are congruence
lattices", is established by its arguments for `222 − 10 − 61 = 151` of them,
the 61 being the lattices its parallel-sum clause was carrying.  The 61 are
closed under duality (28 pairs and 5 self-dual lattices), so the theorem of
Kurzweil and Netter halves the work of settling them.

The 61, in the census's numbering (`L8.k`; the covers are on `0..7` with `0`
the bottom and `7` the top, in the note's format), with the number of lattice
congruences (`|Con|`; `2` means simple) and the shape of the proper part
(components: `1` a point, `[k]` a `k`-element chain, `s(m·M)` an `s`-element
component with `m` minimal and `M` maximal elements).  A *parachute* is a
glued sum every component of whose proper part has a least element; the RP-1
note's `P(2×2, 2×2)` is `L8.122` and its dual `L8.56`.

| `k` | dual | `|Con|` | covers | proper part | shape |
| ---: | ---: | ---: | --- | --- | --- |
| 1 | 1 | 2 | `0<1 0<2 0<3 0<4 0<5 0<6 1<7 2<7 3<7 4<7 5<7 6<7` | 1 ⊔ 1 ⊔ 1 ⊔ 1 ⊔ 1 ⊔ 1 | `M₆` |
| 2 | 2 | 3 | `0<1 0<2 0<3 0<4 0<5 1<7 2<7 3<7 4<7 5<6 6<7` | 1 ⊔ 1 ⊔ 1 ⊔ 1 ⊔ [2] | both |
| 3 | 4 | 2 | `0<1 0<2 0<3 0<4 0<5 1<7 2<7 3<7 4<6 5<6 6<7` | 1 ⊔ 1 ⊔ 1 ⊔ 3(2m1M) | dual parachute |
| 4 | 3 | 2 | `0<1 0<2 0<3 0<4 1<7 2<7 3<7 4<5 4<6 5<7 6<7` | 1 ⊔ 1 ⊔ 1 ⊔ 3(1m2M) | parachute `P(2×2, 2, 2, 2)` |
| 5 | 5 | 5 | `0<1 0<2 0<3 0<4 1<7 2<7 3<7 4<5 5<6 6<7` | 1 ⊔ 1 ⊔ 1 ⊔ [3] | both |
| 6 | 11 | 2 | `0<1 0<2 0<3 0<4 0<5 1<7 2<7 3<6 4<6 5<6 6<7` | 1 ⊔ 1 ⊔ 4(3m1M) | dual parachute |
| 7 | 7 | 5 | `0<1 0<2 0<3 0<4 1<7 2<7 3<6 4<5 5<7 6<7` | 1 ⊔ 1 ⊔ [2] ⊔ [2] | both |
| 8 | 8 | 2 | `0<1 0<2 0<3 0<4 1<7 2<7 3<6 4<5 4<6 5<7 6<7` | 1 ⊔ 1 ⊔ 4(2m2M) | |
| 9 | 12 | 3 | `0<1 0<2 0<3 0<4 1<7 2<7 3<6 4<5 5<6 6<7` | 1 ⊔ 1 ⊔ 4(2m1M) | dual parachute |
| 10 | 14 | 3 | `0<1 0<2 0<3 0<4 1<7 2<7 3<5 4<5 5<6 6<7` | 1 ⊔ 1 ⊔ 4(2m1M) | dual parachute |
| 11 | 6 | 2 | `0<1 0<2 0<3 1<7 2<7 3<4 3<5 3<6 4<7 5<7 6<7` | 1 ⊔ 1 ⊔ 4(1m3M) | parachute `P(M₃, 2, 2)` |
| 12 | 9 | 3 | `0<1 0<2 0<3 1<7 2<7 3<4 3<5 4<7 5<6 6<7` | 1 ⊔ 1 ⊔ 4(1m2M) | parachute |
| 13 | 13 | 5 | `0<1 0<2 0<3 1<7 2<7 3<4 3<5 4<6 5<6 6<7` | 1 ⊔ 1 ⊔ [4] | both |
| 14 | 10 | 3 | `0<1 0<2 0<3 1<7 2<7 3<4 4<5 4<6 5<7 6<7` | 1 ⊔ 1 ⊔ 4(1m2M) | parachute |
| 15 | 15 | 9 | `0<1 0<2 0<3 1<7 2<7 3<4 4<5 5<6 6<7` | 1 ⊔ 1 ⊔ [4] | both |
| 16 | 39 | 3 | `0<1 0<2 0<3 0<4 0<5 1<7 2<6 3<6 4<6 5<6 6<7` | 1 ⊔ 5(4m1M) | dual parachute |
| 17 | 22 | 3 | `0<1 0<2 0<3 0<4 1<7 2<6 3<6 4<5 5<7 6<7` | 1 ⊔ [2] ⊔ 3(2m1M) | dual parachute |
| 18 | 24 | 2 | `0<1 0<2 0<3 0<4 1<7 2<6 3<6 4<5 4<6 5<7 6<7` | 1 ⊔ 5(3m2M) | |
| 19 | 40 | 4 | `0<1 0<2 0<3 0<4 1<7 2<6 3<6 4<5 5<6 6<7` | 1 ⊔ 5(3m1M) | dual parachute |
| 20 | 31 | 2 | `0<1 0<2 0<3 0<4 1<7 2<6 3<5 4<5 4<6 5<7 6<7` | 1 ⊔ 5(3m2M) | |
| 21 | 42 | 3 | `0<1 0<2 0<3 0<4 1<7 2<6 3<5 4<5 5<6 6<7` | 1 ⊔ 5(3m1M) | dual parachute |
| 22 | 17 | 3 | `0<1 0<2 0<3 1<7 2<6 3<4 3<5 4<7 5<7 6<7` | 1 ⊔ [2] ⊔ 3(1m2M) | parachute `P(2×2, 3, 2)` |
| 23 | 23 | 9 | `0<1 0<2 0<3 1<7 2<4 3<5 4<7 5<6 6<7` | 1 ⊔ [2] ⊔ [3] | both |
| 24 | 18 | 2 | `0<1 0<2 0<3 1<7 2<6 3<4 3<5 3<6 4<7 5<7 6<7` | 1 ⊔ 5(2m3M) | |
| 25 | 25 | 2 | `0<1 0<2 0<3 1<7 2<6 3<4 3<5 4<7 5<6 6<7` | 1 ⊔ 5(2m2M) | |
| 26 | 41 | 3 | `0<1 0<2 0<3 1<7 2<6 3<4 3<5 4<6 5<6 6<7` | 1 ⊔ 5(2m1M) | dual parachute |
| 27 | 32 | 3 | `0<1 0<2 0<3 1<7 2<6 3<4 3<6 4<5 5<7 6<7` | 1 ⊔ 5(2m2M) | |
| 28 | 34 | 3 | `0<1 0<2 0<3 1<7 2<6 3<4 4<5 4<6 5<7 6<7` | 1 ⊔ 5(2m2M) | |
| 29 | 43 | 6 | `0<1 0<2 0<3 1<7 2<6 3<4 4<5 5<6 6<7` | 1 ⊔ 5(2m1M) | dual parachute |
| 30 | 49 | 4 | `0<1 0<2 0<3 0<4 1<7 2<5 3<5 4<5 5<6 6<7` | 1 ⊔ 5(3m1M) | dual parachute |
| 31 | 20 | 2 | `0<1 0<2 0<3 1<7 2<5 2<6 3<4 3<6 4<7 5<7 6<7` | 1 ⊔ 5(2m3M) | |
| 32 | 27 | 3 | `0<1 0<2 0<3 1<7 2<5 3<4 3<6 4<7 5<6 6<7` | 1 ⊔ 5(2m2M) | |
| 33 | 45 | 6 | `0<1 0<2 0<3 1<7 2<5 3<4 4<6 5<6 6<7` | 1 ⊔ 5(2m1M) | dual parachute |
| 34 | 28 | 3 | `0<1 0<2 0<3 1<7 2<5 3<4 3<5 4<7 5<6 6<7` | 1 ⊔ 5(2m2M) | |
| 35 | 46 | 4 | `0<1 0<2 0<3 1<7 2<5 3<4 3<5 4<6 5<6 6<7` | 1 ⊔ 5(2m1M) | dual parachute |
| 36 | 50 | 6 | `0<1 0<2 0<3 1<7 2<5 3<4 4<5 5<6 6<7` | 1 ⊔ 5(2m1M) | dual parachute |
| 37 | 37 | 2 | `0<1 0<2 0<3 1<7 2<4 3<4 4<5 4<6 5<7 6<7` | 1 ⊔ 5(2m2M) | |
| 38 | 52 | 6 | `0<1 0<2 0<3 1<7 2<4 3<4 4<5 5<6 6<7` | 1 ⊔ 5(2m1M) | dual parachute |
| 39 | 16 | 3 | `0<1 0<2 1<7 2<3 2<4 2<5 2<6 3<7 4<7 5<7 6<7` | 1 ⊔ 5(1m4M) | parachute `P(M₄, 2)` |
| 40 | 19 | 4 | `0<1 0<2 1<7 2<3 2<4 2<5 3<7 4<7 5<6 6<7` | 1 ⊔ 5(1m3M) | parachute |
| 41 | 26 | 3 | `0<1 0<2 1<7 2<3 2<4 2<5 3<7 4<6 5<6 6<7` | 1 ⊔ 5(1m2M) | parachute |
| 42 | 21 | 3 | `0<1 0<2 1<7 2<3 2<4 3<7 4<5 4<6 5<7 6<7` | 1 ⊔ 5(1m3M) | parachute |
| 43 | 29 | 6 | `0<1 0<2 1<7 2<3 2<4 3<7 4<5 5<6 6<7` | 1 ⊔ 5(1m2M) | parachute |
| 45 | 33 | 6 | `0<1 0<2 1<7 2<3 2<4 3<6 4<5 5<7 6<7` | 1 ⊔ 5(1m2M) | parachute |
| 46 | 35 | 4 | `0<1 0<2 1<7 2<3 2<4 3<6 4<5 4<6 5<7 6<7` | 1 ⊔ 5(1m2M) | parachute |
| 49 | 30 | 4 | `0<1 0<2 1<7 2<3 3<4 3<5 3<6 4<7 5<7 6<7` | 1 ⊔ 5(1m3M) | parachute |
| 50 | 36 | 6 | `0<1 0<2 1<7 2<3 3<4 3<5 4<7 5<6 6<7` | 1 ⊔ 5(1m2M) | parachute |
| 52 | 38 | 6 | `0<1 0<2 1<7 2<3 3<4 4<5 4<6 5<7 6<7` | 1 ⊔ 5(1m2M) | parachute |
| 55 | 88 | 4 | `0<1 0<2 0<3 0<4 1<6 2<6 3<6 4<5 5<7 6<7` | [2] ⊔ 4(3m1M) | dual parachute |
| 56 | 122 | 2 | `0<1 0<2 0<3 0<4 1<6 2<6 3<5 4<5 5<7 6<7` | 3(2m1M) ⊔ 3(2m1M) | dual of `P(2×2, 2×2)` |
| 60 | 60 | 9 | `0<1 0<2 0<3 1<6 2<5 3<4 4<7 5<7 6<7` | [2] ⊔ [2] ⊔ [2] | both |
| 62 | 62 | 3 | `0<1 0<2 0<3 1<6 2<6 3<4 3<5 4<7 5<7 6<7` | 3(2m1M) ⊔ 3(1m2M) | |
| 63 | 63 | 3 | `0<1 0<2 0<3 1<6 2<5 3<4 3<6 4<7 5<7 6<7` | [2] ⊔ 4(2m2M) | |
| 64 | 89 | 6 | `0<1 0<2 0<3 1<6 2<4 3<5 4<7 5<6 6<7` | [2] ⊔ 4(2m1M) | dual parachute |
| 65 | 123 | 6 | `0<1 0<2 0<3 1<6 2<6 3<4 4<5 5<7 6<7` | 3(2m1M) ⊔ [3] | dual parachute |
| 79 | 91 | 6 | `0<1 0<2 0<3 1<4 2<5 3<5 4<7 5<6 6<7` | [2] ⊔ 4(2m1M) | dual parachute |
| 88 | 55 | 4 | `0<1 0<2 1<6 2<3 2<4 2<5 3<7 4<7 5<7 6<7` | [2] ⊔ 4(1m3M) | parachute `P(M₃, 3)` |
| 89 | 64 | 6 | `0<1 0<2 1<4 2<3 2<5 3<7 4<7 5<6 6<7` | [2] ⊔ 4(1m2M) | parachute |
| 91 | 79 | 6 | `0<1 0<2 1<3 2<4 3<7 4<5 4<6 5<7 6<7` | [2] ⊔ 4(1m2M) | parachute `P(3, 2 ⊕a 2×2)` |
| 122 | 56 | 2 | `0<1 0<2 1<5 1<6 2<3 2<4 3<7 4<7 5<7 6<7` | 3(1m2M) ⊔ 3(1m2M) | `P(2×2, 2×2)` |
| 123 | 65 | 6 | `0<1 0<2 1<5 2<3 2<4 3<7 4<7 5<6 6<7` | [3] ⊔ 3(1m2M) | parachute `P(4, 2×2)` |

`L8.1` is `M₆`, representable as the subspace lattice of the plane over the
field with five elements (the subgroup lattice of `C₅ × C₅`); it is the one
lattice of the 61 whose representability is classical.  For the fourteen
simple ones the question is a group question: a simple lattice whose coatoms
meet to `0` has, by the theorem of Pálfy–Pudlák and McKenzie (fin-lat-rep
manuscript § 5), a minimal congruence representation all of whose nonconstant
operations are permutations, so it is representable if and only if it is the
congruence lattice of a finite `G`-set; and the coatoms of every glued sum
meet to `0`, two coatoms from different components meeting in the bottom.

## 4.  Searches

The four instruments of the RP-3 sweeps were run over the 61 on 2026-09-28,
after the census.  Every verdict below is a negative over a finite range or a
positive with a witness; none is a non-representability claim.

+  **The closure search in `Eq(n)`, `n ≤ 7`** (`eqsearch.py --fast`, all 61
   stanzas of `scripts/python/flrp/inputs/lat8/`, one lattice per process,
   five minutes per run).  Complete through six points for all 61: two
   closed classes, `L8.3` (240 copies in `Eq(6)`, one class, closed) and
   `L8.35` (likewise), so both are congruence lattices of six-element
   algebras, and by duality so are `L8.4` and `L8.46`.  At seven points the
   generic assignment plan finished for 22 lattices (all negative, `L8.60`
   with 423360 copies in 18 classes none closed) and timed out for 36; `M₆`
   was not run at seven (it stalls the plan, and it is classical).  A
   timed-out run is recorded as such, not as a negative.
+  **The SmallGroups sweep, orders 2 through 300** (`hunt_parachutes.g` with
   the size-8 gate opened to every shape, `FLRP_S8_ATOMS := [1 .. 7]`;
   `scripts/gap/flrp/out/lat8_s8.raw.json`, git-ignored like the other raw
   reports).  The sweep enumerates the bottoms of core-free intervals as
   intersections of two maximal subgroups, which is complete for every
   glued sum (two coatoms of different components meet in the bottom), and
   skips `p`-groups, which costs only intervals over the trivial subgroup
   (in a `p`-group two maximal subgroups are normal, so their intersection
   is core-free only when trivial), that is, subgroup lattices of
   `p`-groups of order at most 300 with eight subgroups, of which
   `M₆ = Sub(C₅ × C₅)` is the one on the list.  Five eight-element core-free
   intervals in all: `M₆` over the trivial subgroup of `D₁₀`, over a `C₂` in
   `(C₅ × C₅) : C₂`, and over a `C₄` in `(C₅ × C₅) : C₄`; `L8.2` over a `C₂`
   in `(C₃ × C₃) : C₄` (order 36, index 18); and `L8.16` over a `C₂` in `A₅`
   (index 30), whence its dual `L8.39 = P(M₄, 2)` by Kurzweil–Netter.
+  **The tables-of-marks scan** (`tomscan.g`, the 414 tables of TomLib) over
   the twelve simple lattices other than `P(2×2, 2×2)` and its dual, which
   the second pass had scanned already (RP-3 note § 5).  Positive: `M₆`
   (five explicit confirmations), `L8.3` (ten marks-exact hits and two
   explicit), `L8.4` (four explicit), `L8.8` (five explicit, two tables
   unresolved above the bound), `L8.20` (six marks-exact hits), whence
   `L8.31` by duality.  Negative, every ambiguous case resolved: `L8.6`,
   `L8.11`, `L8.18`, `L8.24`.  Not completed: `L8.25`, `L8.31`, `L8.37`; the
   scan of `L8.25` (97 ambiguous survivors) sat for forty minutes on one
   table below the default resolution bound of `2·10⁷`, and a rerun at the
   bound `10⁶` stalled at the same table, so the three are the follow-up,
   one table at a time as `make gap-tomscan` does for `He.2` (`L8.31` is
   settled by duality regardless).
+  **The transitive groups by degree** (`scan_transitive.g`), for
   `P(2×2, 2×2)` only: no point-stabilizer interval of composite degree 8
   through 22 (`pm2m2_transitive_deg*.search.json`); degree 24 was still
   running when this note was written.

**Standing**.  Of the 61, eleven are settled positively by these runs
(`L8.1, 2, 3, 4, 8, 16, 20, 31, 35, 39, 46`) and fifty are open, among them
eight simple lattices: `L8.6` and `L8.11` (a dual pair), `L8.18` and
`L8.24` (a dual pair), the self-dual `L8.25` and `L8.37` (marks scans
incomplete), and `P(2×2, 2×2)` with its dual.  For a simple lattice every instrument above is exhaustive
on its range, since a representation, if one exists, is a `G`-set; the
range is what is small.

Kjos-Hanssen's note reports (its § 2.3) that its three group-library scans,
the groups of order at most 255 except 128, 192, and 256, every transitive
group of degree at most 47, and TomLib, identified *every* eight-element
interval they met as one of the 222 lattices; Table 1 prints the hits for
the 54 only.  The hits for the 61 exist in his data and are the cheapest
way to settle most of them.

## 5.  What this changes in the program's notes

+  `P(2×2, 2×2)` is not known to be representable.  The theorem note's § 7.1,
   the RP-2 catalog's Entry 13 row and § 4.13, the RP-3 dossier's last item
   and its row F13, the roadmap's § 3 closure list and § 4 update, and the
   paths note's §§ 1, 5, 6 said otherwise for part of 2026-09-28, on the
   strength of the glued reading; all are corrected in the same commit as
   this note, and each now points here.
+  Theorem E of the theorem note stands as stated: a simple parachute that
   *is* a congruence lattice is a group interval.  Its corollary is gone,
   and its content is reversed in use: a simple parachute that is not a
   group interval is not a congruence lattice at all, so for the simple
   parachutes the RP-3 hunt for a group interval is the representation
   problem itself, with no strategy meta-theorem in between.  Entry 13's
   class, the coatomistic parachutes with two big canopies, has no member
   known to be representable; its vacuity datum is "unknown".
+  The fourteen simple lattices of the list, thirteen once `M₆` is set
   aside, are the eight-element lattices on which a negative answer to the
   FLRP could be decided by group theory alone, and `P(2×2, 2×2)` is the one
   the parachute reduction (Entry 13) already constrains: any core-free
   representation of it with a monolith is almost simple, or has `H`
   complementing the monolith, or is not minimal.

## 6.  Verification status

`verified` means read in the cited text; `computed` means checked by the
named script with a committed record.

| Claim | Source | Status | How |
| --- | --- | --- | --- |
| The definition of `L ∓ N`, Lemmas 3.2, 3.3, 3.4, 3.5, 3.6, 3.9, 3.10, Corollary 3.8 | Snow 2000, pp. 282–288 | **verified** | the published text, supplied by William, read in full; the proofs of 3.9 and 3.10 checked as summarized in § 1 |
| Kjos-Hanssen's definition of the parallel sum, his criterion, and his counts 15, 96, 69, 168, 54 | `CLFA8.pdf` § 2.1, Table 1 | **verified** as his statements | read in full; the counts reproduced by the census |
| The 222 eight-element lattices and their classification; the split 8 / 61; the 15 simple ones; the duals | `scripts/python/flrp/lattices8.py` | **computed** | `scripts/python/flrp/out/lattices8_census.json`; the enumerator pinned to OEIS A006966 through eight elements and the Table 1 match pinned lattice for lattice by `test_lattices8.py` |
| Closure under `∥` would make every `Mₙ` representable | this note, § 2 | argument written here | `Mₙ = 3 ∥ ⋯ ∥ 3` |
| The three-interval union in `∏ (Lᵢ ∓ 1)` is not closed under primitive positive definitions | this note, § 2 | argument written here | the displayed definition |
| `M₆` is the subgroup lattice of `C₅ × C₅` | classical | **verified** (elementary) | six subgroups of order five, all maximal |
| The Pálfy–Pudlák–McKenzie theorem, conditions (A) and (B″) | the fin-lat-rep manuscript § 5 | **verified** as stated there | the 1980 and 1983 originals not read |

## 7.  Records

+  `scripts/python/flrp/lattices8.py`, `test_lattices8.py`; the record
   `scripts/python/flrp/out/lattices8_census.json`; the 61 target stanzas
   `scripts/python/flrp/inputs/lat8/l8_<k>.json`; `make flrp-lat8`.
+  `scripts/gap/flrp/bin/hunt_parachutes.g`: the `FLRP_S8_ATOMS` and
   `FLRP_S8_OUT` globals that open the size-8 gate to every shape.
+  `scripts/python/flrp/lat8_search.py` and its record
   `scripts/python/flrp/out/lat8_search_summary.json`: the SmallGroups
   confirmations for all 61 targets, the closure-search counts per lattice
   and number of points, and the marks-scan verdicts, in one file; the
   per-run reports it folds are re-derivable from the stanzas (the skill
   `hunting-lattice-intervals-in-tomlib` records the pipeline).

[issue #578]: https://github.com/ualib/agda-algebras/issues/578
