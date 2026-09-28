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
   each resolved negative, `He.2` with a 12 GB heap).  Its representability
   is open, and with it the entry's vacuity datum.
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

**Verdict: blocked on the text.**

+  The paper (J. Algebra 196 (1997), 1–100; DOI `10.1006/jabr.1997.7069`) is
   in Elsevier's open archive, which answers `curl` with a challenge page;
   Unpaywall lists the publisher as the only location; the Chrome extension
   was not connected.  William must supply the PDF.  Two scanned papers in
   the research folder named "Lucchini" are the two halves of Lucchini's
   1994 *Intervals in subgroup lattices of finite groups* (Comm. Algebra
   22, 529–549), not this paper.
+  What the zbMATH review says (`secondary`): the paper reduces the question
   of which `Mₙ` are intervals to questions about finite simple groups,
   through a generalized wreath product construction of B. H. Neumann
   (Arch. Math. 14 (1963)), using the classification in the reduction
   itself; the residual questions fall under two general tasks, to describe
   the subgroups of `Aut(F)`, `F` simple, that leave invariant exactly one
   subgroup other than `1` and `F`, and to determine the maximal simple
   sections of nonabelian simple groups in a technical sense.  Nothing of
   this is consumed.

## 5.  Path 5: the positive direction

**Verdict: not attempted beyond one observation.**

+  The negative paths did not die in this pass, so the positive direction
   was not pursued as the issue orders.  One observation from path 1
   belongs here: an interval `[H̄, Ḡ]` in an almost simple group with
   `H̄ ∩ F*(Ḡ) = 1` yields the same lattice as an interval of `Ḡ ≀ C₂`, so a
   lattice representable in an almost simple group is also representable
   with a non-simple socle of product type; this is a closure-like fact
   about the representable class, not a new representation.
+  For the smallest open coatomistic parachute `P(2×2, 2×2)`, no formalized
   closure construction produces it: products and ordinal sums do not
   produce parachutes with two big canopies, Kurzweil–Netter duality relates
   it to its dual, which is equally unrepresented, and a filter-ideal
   gluing stacks its two summands, whereas the two canopies are
   incomparable.  Aschbacher's Section 8 machine realizes only parachutes
   whose canopies have a unique coatom.

## 6.  What stands between the program and a terminal state

Stated as the issue asks, as open lemmas with their status.

+  **Negative answer through a coatomistic parachute** `Λ`, say
   `P(2×2, 2×2)`.  By the theorem of path 1, `Λ` is not a group interval as
   soon as the following four statements hold, each an open lemma.
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
   degree; (b) has a worked model in the 2009 paper.  Neither is a special
   case proved.
+  **Negative answer through an F10 family**.  A pair of cf-IE classes
   separated by an invariant that varies across the Kurzweil wreaths.
   Theorem A shows coatom type is homogeneous but two-valued across the
   wreath-rich families, so it is not that invariant; no candidate was
   found.  The next finer invariants Aschbacher's Section 4 offers are the
   partition `Γ(M)` of the components attached to a diagonal-type coatom
   and the subgroup `L̄_H`, both constant across the double Kurzweil wreaths
   of one lattice and varying only with the lattice, which is exactly the
   correlation an F10 pair needs and exactly what has not been shown to
   force anything.
+  **Positive answer**.  Statement (B) for all finite lattices; no path.  A
   representation of `P(2×2, 2×2)` would extend the census and give Entry
   13 its vacuity datum; the theorem of path 1 says where to look: an
   almost simple group, a signalizer lattice, or the dual.

## 7.  Records of this pass

+  Notes: this file; `docs/notes/flrp-parachute-theorem3.md`; the
   corrections to `docs/notes/flrp-rp2-catalog.md` § 4.12 and § 6, and the
   review entry in `docs/notes/flrp-rp3-hunt.md` § 6.
+  Formal: `Classical.Structures.Lattice.Disconnected` (coatoms, the
   `C*`-condition, the same-canopy meet lemma);
   `FLRP.Reductions.Coatomistic` (Entry 13).
+  Computation: `scripts/gap/flrp/out/tomscan_pm2m2.json`,
   `tomscan_pm2m2_big.json`, `tomscan_pm2m2d.json`, `tomscan_dd33.json`
   (targets `pm2m2`, `pm2m2d`, `dd33` under `scripts/gap/flrp/inputs/`,
   generated by `scripts/python/flrp/parachute_targets.py`);
   `wreath_coatom_type_a5_c4.json` (`make gap-wreath-labels`); the scan's
   isomorphism test in `scripts/gap/flrp/bin/tomscan.g`.
