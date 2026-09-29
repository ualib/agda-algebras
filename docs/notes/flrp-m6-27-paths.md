<!-- File: docs/notes/flrp-m6-27-paths.md -->

# M6-27: the five paths, and where each stands

Issue M6-27 asks for one of two terminal states: a solution of the Finite
Lattice Representation Problem, or a path to one described concretely enough
to check step by step.  This note records the outcome of the first pass over
the issue's five paths (2026-09-28), in the issue's own terms, with the
verification discipline of the RP-2 catalog: every literature claim is
`verified`, `secondary`, or `unverified`, and only verified claims are
consumed.  Neither terminal state was reached.  What the pass produced is a
reduction theorem the program did not have (path 1), the computational
records that fix where the smallest open instances stand (paths 1 and 2), a
correction to the issue's description of the known representations (path 3),
and a precise statement of what stands between the program and a terminal
state (§ 6).  The mathematics of path 1 is in
`docs/notes/flrp-parachute-theorem3.md`; the review-scaffold entry is in
`docs/notes/flrp-rp3-hunt.md` § 6.

## 1.  Path 1: the parachute analog of Aschbacher's Theorem 3

**Verdict: a theorem, for coatomistic parachutes; F10 not reopened.**

+  The RP-2 survey's conclusion that both C-dependent steps of Aschbacher's
   Section 6 fail for parachutes rested on a dropped symbol: the extracted
   text of the 2008 paper lost every `≠`, and (6.6)(3)'s "two coatoms of one
   component with `M₂ ∩ M′ ≠ H`" was read as `= H`.  The page image settles
   it.  Two coatoms of one canopy meet above the canopy's atom, so a canopy
   with two coatoms supplies the step outright.  The other step, (6.5),
   needs the parachute coatomistic, as the survey said.
+  **Theorem** (`docs/notes/flrp-parachute-theorem3.md` § 4).  For a
   coatomistic parachute `Λ` with two big canopies and a core-free finite
   representation `(H, G)`: `G` is almost simple; or `H` is a complement to
   the monolith `D = F*(G)` and `[H, G]` is a signalizer lattice; or `Λ` is
   an interval in the smaller almost simple group `Aut_G(L)`; or the dual of
   `Λ` is an interval in a group of order below `|G|`.  Over Aschbacher's
   dual-closed minimality the first two remain, which is his Theorem 3's
   conclusion.  The proof is his, with the two substitutions; (5.3) uses the
   classification of finite simple groups, as in the original.
+  **Theorem A** (ibid. § 3), which needs no minimality: in every core-free
   representation of a parachute two of whose canopies have two coatoms,
   with non-simple monolith, the maximal overgroups of `H` are all of
   product type or all of diagonal type.  This is an enforcement statement
   at the level RP-3's F10 asked for.  It does not separate: both polarities
   are realized, product type by the wreathed almost simple representations
   `Ḡ ≀ C₂`, diagonal type by the Kurzweil wreaths.
+  **Theorem D** (ibid. § 4.1, from the 2009 signalizer paper, read the same
   day): in the signalizer alternative of a minimal representation, `τ` is
   faithful, `H = H(τ)`, and `F*(H)` is a transitive product of nonabelian
   simple groups.  Only the coatomistic half of "CD" and disconnectedness
   enter (his 1.2, 2.13 through 2.15, 4.10, 4.11).  The further descent of
   his Section 5 to `Aut_H(E)` does not transfer: 5.8 needs components
   without least elements and 5.10 needs atomicity.
+  **Caveat**: the dual of a parachute is never coatomistic, so on the dual
   side the all-product-type case is not excluded, and Aschbacher's
   dual-closed minimality cannot be used as freely as in his theorem
   (ibid. § 5).  The formal entry states all four alternatives for
   representations of `Λ` and derives both minimality corollaries.
+  **Formal**: `Classical.Structures.Lattice.Disconnected` gains coatoms and
   the `C*`-condition, and the same-canopy meet lemma;
   `FLRP.Reductions.Coatomistic` is Entry 13 of the catalog, the theorem
   imported as `ParachuteTheorem3` with `theorem3-dualMinimal` and
   `theorem3-minimal` derived.
+  **Smallest instance**: `P(2×2, 2×2)`, eight elements.  Neither it nor its
   dual is an upper interval in any of TomLib's 414 tables
   (`scripts/gap/flrp/out/tomscan_pm2m2*.json`; the two ambiguous cases for
   each resolved negative, `He.2` with a 12 GB heap), in any group of order
   at most 300 (the SmallGroups sweep, extended to eight elements), in
   `Eq(n)` for `n ≤ 7`, or over a point stabilizer of a transitive group of
   composite degree at most 22.  No representation of it is known, of any
   kind: see the next bullet.
+  **Theorem E, and the parallel-sum correction** (theorem note § 7.1;
   `docs/notes/flrp-lattices8-census.md`).  `P(2×2, 2×2)` is a simple
   lattice whose coatoms meet to `0` (computed; the hexagon and the three
   seven-element sweep targets are not simple), so by the theorem of
   Pálfy–Pudlák and McKenzie and DeMeo–Freese's theorem on intransitive
   actions (both in the fin-lat-rep manuscript § 5) it is a congruence
   lattice if and only if it is a group interval, and then its least
   congruence representation is a transitive `G`-set (Theorem E).  For
   part of the day the pass believed it *was* a congruence lattice, on
   Kjos-Hanssen's classification of it as a "parallel sum": his note
   describes the parallel sum as identifying the tops and the bottoms of
   two lattices, and a parachute identifies the tops of its canopies.  But
   Snow's parallel sum (Snow 2000, Lemmas 3.9 and 3.10, now read in the
   text) adjoins a *new* top and bottom, and closure under the glued
   operation would make every `Mₙ` a congruence lattice, `M₁₆` included;
   William caught the error.  So `P(2×2, 2×2)` is not known to be
   representable, Entry 13 has no member known to be representable at
   all, and the census of the eight-element lattices shows the same gap
   under 61 of the 168 lattices the note calls formally representable,
   fourteen of them simple.  The hexagon, by contrast, is a Snow sum,
   `2 ∓ 2`, and the congruence lattice of a six-element algebra
   (`FLRP.Certificates.Parachute.HexagonEq6`, from the closure search)
   while its least known group carrier has order 25920: for a non-simple
   parachute the congruence and the group questions live at different
   scales.
+  **What the path did not give**: a reduction to almost simple groups or
   signalizer lattices *was* obtained, but it imports Aschbacher's program
   rather than shortening it, and it produces no F10 invariant.  The issue's
   other hoped-for outcome, a proof that no reduction exists, is refuted for
   coatomistic parachutes and remains open for the others (a parachute with
   a chain canopy is not coatomistic, and there Case A is not excluded; the
   hexagon is such a parachute, and it is representable, so nothing is lost
   there).

## 2.  Path 2: Conjecture D at `DΔ(3,3)`

**Verdict: data only; the almost simple case is untouched.**

+  The scan of 2026-09-28 finds `DΔ(3,3)` in none of the 414 tables of marks,
   and no ambiguous case at all: of the 3396 upper intervals of size fourteen
   in the library, none has its up-count profile
   (`scripts/gap/flrp/out/tomscan_dd33.json`).  Since a table of marks lists
   every conjugacy class of subgroups, this is a complete negative for those
   414 groups, which include the alternating and symmetric groups up to
   degree 13, the sporadic groups whose tables the library has, and many
   groups of Lie type of small order.  It is consistent with Conjecture D
   and with Aschbacher–Shareshian's theorem, and it adds nothing to either
   beyond the groups covered.
+  Aschbacher's reduction (Theorem 2 of the 2009 Michigan paper, `verified`
   in RP-2) leaves the almost simple case and the lower-signalizer case.
   The almost simple case is the classification-driven casework his 2012
   and 2013 papers begin; nothing in this pass advances it.  The
   scan's isomorphism test was rewritten for the purpose (a backtracking
   matcher in place of the brute force over `12!` permutations) and
   validated against the committed hexagon record.
+  A proof for one `DΔ`-lattice would be a negative answer to the FLRP; no
   step toward one was found here beyond the data.

## 3.  Path 3: the labeled interval

**Verdict: the labels are known in every case; they do not separate; and
the issue's description of the Kurzweil wreaths was wrong.**

+  In an almost simple representation every coatom action has O'Nan–Scott
   type "almost simple", so the known parachute representations (the
   hexagon in `U₄(2)`, `A₁₁`, `U₃(7)`; `P(3,3,2)` in `PΓL(2,8)`,
   `PSL(2,25)`; `P(3,4)` in `U₄(3).2₁`) carry no information in the label.
+  In a Kurzweil wreath `[Diag × G, S ≀ G]`, the coatoms are the partition
   subgroups `S^{π_K} ⋊ G` over the atoms `K` of `[H, G]`, each meeting the
   socle in a product of full diagonal subgroups: Aschbacher's **diagonal**
   type, not product type as the issue states.  Checked in GAP on
   `A₅ ≀ C₄` over `Diag × C₄` (`scripts/gap/flrp/out/wreath_coatom_type_a5_c4.json`,
   `make gap-wreath-labels`): the coatom meets the socle in `60²` elements
   and every coordinate trivially.  The double Kurzweil wreath is the same
   shape one level up.  Aschbacher's Section 8 examples are diagonal type as
   well (his (6.7)(1) with `L̄_H = L̄`).  Product type is realized by
   `Ḡ ≀ C₂` over `H̄ ≀ C₂` for any almost simple representation `[H̄, Ḡ]`.
+  The transfer rule the parachute shape forces is Theorem A: with two
   two-coatom canopies the type is constant across all coatoms of the
   interval, whatever the canopy.  The rules between canopies are
   Aschbacher's (4.11)(1) and (4.14)(5), used in its proof.
+  A class "some coatom action of `G` has type X" is therefore not an F10
   candidate: the type is homogeneous, and each of its two values is taken
   by a wreath-rich family (the double Kurzweil wreaths are diagonal; the
   wreathed almost simple representations are product type and, being
   themselves wreath-like, are again present in every cf-IE class via the
   note's Lemma 3.3 argument only if the class contains them, which the
   RP-3 pinned-invariant caution says to check before stating anything).
   Nothing was stated.
+  The imprimitive, intransitive, and prime-degree cases of a parachute
   analog of Aschbacher–Shareshian's theorem in alternating and symmetric
   groups (RP-2 residue (iv)) were not attempted.

## 4.  Path 4: `M₁₆` through Baddeley–Lucchini

**Verdict: read; the reduction does not reach `M₁₆`; Entry 14 records the
dichotomy it rests on.**

+  The paper (J. Algebra 196 (1997), 1–100) was supplied by William and read
   in the published text (`verified`): the introduction, Section 2 (the
   results diagram, read as an image), the definitions and reduction
   theorems of Sections 4 through 7, and Section 8.  Two scanned papers in
   the research folder named "Lucchini" are the two halves of Lucchini's
   1994 *Intervals in subgroup lattices of finite groups* (Comm. Algebra
   22, 529–549), whose theorem is the input Baddeley–Lucchini start from;
   its statement and first reduction were read from the scan's page images
   (`verified`).
+  **What the two papers prove.**  Write `Ω` for the set of `n` with `Mₙ` a
   group interval and `K` for the known set (`n = 1, 2, q + 1, q + 2,
   (qᵗ + 1)/(q + 1) + 1`).  Lucchini 1994: for `n − 1` not a prime power and
   `n` large enough ("for example `n ≥ 50`"), a group `G` of least order with
   an `Mₙ` interval over `T` is almost simple, or `T ∩ Soc G = 1`, or `n ∈ K`.
   Baddeley–Lucchini split `T ∩ Soc G = 1` by whether `G = T · Soc G` (the
   `T`-complement case) and reduce each side to tuples over finite simple
   groups: `Ω(2.D) = Ω(4.7)`, the not-`T`-complement case, is realized by
   `(4.1)`-tuples with an almost simple `H` (Theorems 4.2 and 4.8,
   Proposition 4.9); `Ω(2.E) = Ω(5.1) ∪ Ω(5.2)` (Theorem 5.3), with
   `Ω(5.1) ⊆ Δ(6.9) ∪ {n : n − 1 ∈ Δ(6.9)}` through sections of simple
   groups (Corollaries 6.11 and 6.20) and `Ω(5.2) = Ω(7.13) ⊆ Δ(7.6(a)) ∪
   Ω(7.18)` through tuples of monomorphisms between simple groups (Theorem
   7.7, Corollaries 7.16 and 7.19).  Their final inclusion (Section 8) is
   `Ω ⊆ Ω(4.7) ∪ {n ≤ 50 : n ∈ Ω} ∪ Δ(6.9) ∪ {n : n − 1 ∈ Δ(6.9)} ∪ Δ(7.6(a))
   ∪ Ω(7.18) ∪ K ∪ S`, `S` the almost simple case, and they pose four
   problems on the four unknown sets, resting on two general ones: describe
   the maximal nonabelian simple sections of the nonabelian simple groups,
   and describe the pairs `(F, L)`, `F` simple, `L ≤ Aut F`, with
   `[F/1]_L ≅ M₁`.  They report `Ω(4.7)` free of alternating, sporadic, and
   exceptional `H`, and `Ω(7.18)` unbounded (Examples 8.3 and 8.4, all in
   `K`).
+  **What this means for `M₁₆`.**  Lucchini's dichotomy is proved for `n`
   large, and the 1997 paper keeps `{n ≤ 50 : n ∈ Ω}` as a separate,
   unreduced term of (2.F); `16` is the least integer outside `K` and lies
   inside that window.  So for `M₁₆` the case "`Soc G` non-simple and
   `T ∩ Soc G ≠ 1`" is excluded by nothing in either paper, and the issue's
   premise that Baddeley–Lucchini reduce `M₁₆` to almost simple groups and
   twisted wreath products is right only above `50`.  To use the reduction
   on `M₁₆` one would first have to push Lucchini's crucial case (his
   Sections 2 and 3, on `T = PSL(l, q)` and `PSU(l, q²)`) down to `n = 16`.
   Not attempted.
+  **What is consumed.**  The dichotomy is imported as Entry 14 of the
   catalog, `FLRP.Reductions.Lucchini`: over `Mₙ` with `50 ≤ n` and `n − 1`
   not a prime power, a minimal representation is almost simple, or `H`
   meets the monolith trivially, or `n` is in one of the two families
   (stated over the standard library's primes, the second family as
   `(n − 1)(q + 1) = qᵗ + 1`); its composition with Köhler's Entry 6, which
   supplies the monolith, is derived.  The 1997 tree is prose only: its
   vocabulary (twisted wreath products, sections, the tuple conditions) is
   beyond the library.
+  **What it teaches the parachute path.**  Lucchini's first reduction (his
   1.1 through 1.8) is the `Mₙ` prototype of Aschbacher's Section 4 and of
   Entry 13's argument: the interval inside the socle, the dual in a smaller
   group when `T ∩ Soc G` projects onto a component, the smaller almost
   simple `N_G(T)/C_G(T)` when every maximal `H`-invariant subgroup is of
   product type.  And Baddeley–Lucchini's "key step", that the socle of the
   complement `H` is nonabelian and unique minimal normal, is what Theorem D
   of the theorem note now gives for coatomistic parachutes.  Their residual
   problems, on maximal simple sections of simple groups, are the shape the
   parachute path's open lemmas should be expected to take.

## 5.  Path 5: the positive direction

**Verdict: not pursued as a path, but the pass's largest correction lands
here.**

+  The representable class is closed under Snow's parallel sum `L ∓ N`,
   the disjoint union with a new top and a new bottom (Snow 2000, Lemmas
   3.9 and 3.10, read in the text; `docs/notes/flrp-lattices8-census.md`
   § 1), which the roadmap's closure list had omitted.  It is *not* known
   to be closed under the glued sum that identifies the tops and the
   bottoms, the operation Kjos-Hanssen's note uses to classify 168 of the
   222 eight-element lattices as representable for formal reasons: `Mₙ` is
   a glued sum of chains.  The census of that note's classification
   (`scripts/python/flrp/lattices8.py`) reproduces its counts and finds
   that Snow's lemma covers 8 of its 69 "parallel sums"; the other 61,
   `P(2×2, 2×2)` and its dual among them, have no formal reason left, and
   fourteen of them are simple lattices, for which representability is a
   group question outright.  Formalizing Snow's lemma in `FLRP.Closure`,
   beside products, ordinal sums, duality, and the filter-ideal gluing,
   remains a natural formal target, now with the text in hand.
+  Theorem E (theorem note § 7.1): a simple parachute that is a congruence
   lattice is a group interval, its minimal congruence representation being
   a transitive `G`-set.  Read the other way, which is the way that
   matters now: a simple parachute that is not a group interval is not a
   congruence lattice, and the FLRP has a negative answer with it as the
   witness.  Aschbacher's Section 8 makes the parachutes of unique-coatom
   canopies of dual-interval form group intervals; the simple parachutes
   (canopies with two coatoms and no top-alone congruence) and the mixed
   ones (a unique-coatom canopy beside a multi-coatom one) are the two
   shapes a two-canopy parachute can have that nothing covers.
   `P(2×2, 2×2)` is the least simple one, and `P(3, 2×2)`, a congruence
   lattice by the seven-element census whose group-interval status is
   open, the least mixed one.
+  One observation from path 1: an interval `[H̄, Ḡ]` in an almost simple
   group with `H̄ ∩ F*(Ḡ) = 1` yields the same lattice as an interval of
   `Ḡ ≀ C₂`, so a lattice representable in an almost simple group is also
   representable with a non-simple socle of product type.
+  Kjos-Hanssen's ten open eight-element lattices (six up to duality,
   chains with one or two bypasses) are the census frontier's live cases;
   none is a parachute, and his `L7` bound (no algebra with fewer than 48
   elements) supersedes the range 16 to 34560 quoted in the roadmap § 3.

## 6.  What stands between the program and a terminal state

Stated as the issue asks, as open lemmas with their status.

+  **Negative answer through a coatomistic parachute: open, and direct.**
   By Theorem E a simple parachute is a congruence lattice if and only if
   it is a group interval, and the coatomistic parachutes of Entry 13 are
   simple whenever their canopies have no congruence keeping the top alone.
   So if `P(2×2, 2×2)` is not a group interval, it is not a congruence
   lattice, and the FLRP is settled negatively by it alone, without the
   strategy meta-theorem.  (For part of 2026-09-28 this item read
   "closed", on the belief that `P(2×2, 2×2)` was a congruence lattice as a
   parallel sum; `docs/notes/flrp-lattices8-census.md` records why that
   was wrong.)  The open lemmas listed next are therefore about whether a
   representation exists, and the reduction of path 1 describes what a
   minimal one would have to look like.
+  **What the reduction asks about `P(2×2, 2×2)`**.  By the theorem of
   path 1 a minimal representation, if there is one, satisfies one of the
   following, each a statement that a search could confirm or a proof
   could exclude; excluding all four excludes the representation.
   (a) No almost simple group has an upper interval isomorphic to `Λ`.
   This is classification casework of the Aschbacher–Shareshian kind;
   `Λ` is not on Theorem D's list of *Overgroups of primitive groups II*,
   so a primitive subgroup of non-prime degree in an alternating or
   symmetric group is excluded (`verified`, RP-2), and the 414 groups of
   TomLib are excluded by computation.  (b) No signalizer lattice `Λ(τ)`,
   `τ ∈ T(L)`, is isomorphic to `Λ`.  Aschbacher's 2009 paper reduces the
   analogous statement for `D(m₁, …, mₜ)`-lattices to lower signalizer
   lattices in almost simple groups; the same reduction for parachutes has
   not been attempted.  (c) No almost simple group has an upper interval
   isomorphic to the dual of `Λ`, and (d) no representation of the dual
   with every coatom of product type exists outside those; the dual side is
   where the parachute analog is weaker than Theorem 3 (path 1, caveat).
   Evidence of tractability: (a) at the TomLib scale is a minute of
   computation and could be pushed to the primitive groups library by
   degree; (b) is now sharper: Theorem D (theorem note § 4.1) gives `τ`
   faithful and `F*(H)` a transitive product of simple groups, so (b) splits
   into (b1) `F*(H)` simple, a question about signalizer lattices in almost
   simple groups, the parachute form of the 2009 paper's condition (SA),
   and (b2) `F*(H) = Eᵐ`, `m ≥ 2`, where the descent to `Aut_H(E)` of his
   Section 5 fails at 5.8 and 5.10 and needs a new argument or a
   counterexample.  Neither is a special case proved.
+  **Negative answer through an F10 family**.  A pair of cf-IE classes
   separated by an invariant that varies across the Kurzweil wreaths, whose
   parachute is *mixed* (§ 5): a canopy with a unique coatom or a top-alone
   congruence beside a canopy with several coatoms, since a simple
   parachute needs no family (previous item) and the parachutes of
   unique-coatom canopies of dual-interval form are group intervals by
   Aschbacher's Section 8.  `P(3, 2×2)` is the least such parachute and
   the natural first question: it is a congruence lattice (seven
   elements); is it a group interval?  Theorem A shows coatom type is homogeneous but two-valued
   across the wreath-rich families, so it is not the separating invariant;
   no candidate was found.  The next finer invariants Aschbacher's Section 4 offers are the
   partition `Γ(M)` of the components attached to a diagonal-type coatom
   and the subgroup `L̄_H`, both constant across the double Kurzweil wreaths
   of one lattice and varying only with the lattice, which is exactly the
   correlation an F10 pair needs and exactly what has not been shown to
   force anything.
+  **Positive answer**.  Statement (B) for all finite lattices; no path.  Two
   pointwise questions are where the parachute program now lives: whether
   the simple parachutes, `P(2×2, 2×2)` first, are group intervals, which
   is their representability; and whether the mixed parachutes,
   `P(3, 2×2)` first, which are congruence lattices, are group intervals.

## 7.  Records of this pass

+  Notes: this file; `docs/notes/flrp-parachute-theorem3.md`; the
   corrections to `docs/notes/flrp-rp2-catalog.md` § 4.12 and § 6, and the
   review entry in `docs/notes/flrp-rp3-hunt.md` § 6; and
   `docs/notes/flrp-lattices8-census.md`, the parallel-sum correction with
   the census of the eight-element lattices and the sweeps over the 61 it
   leaves open (`scripts/python/flrp/lattices8.py`, `lat8_search.py`).
+  Formal: `Classical.Structures.Lattice.Disconnected` (coatoms, the
   `C*`-condition, the same-canopy meet lemma);
   `FLRP.Reductions.Coatomistic` (Entry 13); `FLRP.Reductions.Lucchini`
   (Entry 14); `FLRP.Certificates.Parachute.HexagonEq6` (the hexagon on six
   points).
+  Computation: `scripts/gap/flrp/out/tomscan_pm2m2.json`,
   `tomscan_pm2m2_big.json`, `tomscan_pm2m2d.json`, `tomscan_dd33.json`
   (targets `pm2m2`, `pm2m2d`, `dd33` under `scripts/gap/flrp/inputs/`,
   generated by `scripts/python/flrp/parachute_targets.py`);
   `wreath_coatom_type_a5_c4.json` (`make gap-wreath-labels`); the scan's
   isomorphism test in `scripts/gap/flrp/bin/tomscan.g`; the eight-element
   slice of the SmallGroups sweep (`rp3_pm2m2.search.json`,
   `rp3_pm2m2d.search.json`); the transitive-groups scans
   `pm2m2_transitive_deg*.search.json`; the hexagon claim file
   `scripts/python/flrp/inputs/hexagon_eq6.json` and its audit
   `out/HexagonEq6.cert.json`.
