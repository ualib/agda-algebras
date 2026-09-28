<!-- File: docs/notes/flrp-parachute-theorem3.md -->

# The parachute analog of Aschbacher's Theorem 3

This note records the outcome of the first path of issue M6-27: the attempt
to redo Section 6 of Aschbacher's *On intervals in subgroup lattices of
finite groups* (J. Amer. Math. Soc. 21 (2008), 809–830) for parachutes.  The
outcome is a theorem, not a no-go: for **coatomistic** parachutes with two big
canopies, Aschbacher's argument transfers with one substitution and one
caveat, and the RP-2 survey's conclusion that it fails was based on a
misreading of a single symbol.  The note states the theorem with every step
tied to a numbered lemma of the paper, records the caveat (the dual), and
says what the result does and does not give the program.  The formal
companion is `src/FLRP/Reductions/Coatomistic.lagda.md` (Entry 13 of the
enforcement catalog); the lattice-side vocabulary it uses is in
`src/Classical/Structures/Lattice/Disconnected.lagda.md`.

Every reference of the form (m.n) below is to the 2008 paper, read in the
published text; where the extracted text was ambiguous the page image was
read (§ 7 records what was checked how).

## 1.  Setting

Throughout, `Λ = 𝒫(L₁, …, Lₙ)` is a parachute with `n ≥ 2` canopies, at
least two of them **big** (more than two elements).  Its proper part `Λ′` is
the disjoint union of the canopies with the shared top removed, its
connected components are the canopies, and by the RP-2 dictionary it is one
of Aschbacher's D-lattices, hence an A-lattice.  The following two conditions
on `Λ` are the ones this note is about.

+  **Coatomistic** (Aschbacher's condition (C), his `C*`-lattices): every
   proper element is a meet of coatoms.  A parachute is coatomistic exactly
   when every canopy is coatomistic *including its bottom*, so that its atom
   is a meet of that canopy's coatoms.  A chain canopy fails this; a Boolean
   or `Mₖ` canopy (`k ≥ 2`) satisfies it.
+  **Two two-coatom canopies**: at least two canopies each contain two
   distinct coatoms of `Λ`.  A big coatomistic canopy has two coatoms (its
   atom is a meet of the canopy's coatoms and is not itself a coatom), so a
   coatomistic parachute with two big canopies has this property.

A **representation** of `Λ` is a pair `(H, G)`, `G` a finite group, `H ≤ G`,
with `O_G(H) = [H, G] ≅ Λ`; it is **core-free** when `ker_H(G) = 1`.  The
paper's minimality is over `G(Λ)`, the representations of `Λ` **or of its
dual**; `G*(Λ)` is the set of those with `|G|` least.

Aschbacher's Proposition 2 applies to every core-free representation of an
A-lattice, so to every core-free representation of `Λ`: `G` has a unique
minimal normal subgroup `D`, `G = HD`, `D = ∏_{X ∈ 𝓛} X` is the direct
product of the components of `G`, which are nonabelian simple groups
permuted transitively by `H`, and `U ↦ U ∩ D` is a poset isomorphism of
`O_G(H)` onto the `H`-invariant subgroups of `D` containing `H ∩ D`.  Since
`D` is nonabelian and unique minimal normal, `C_G(D) = 1` and `D = F*(G)`,
which is his Hypothesis 4.6.  `G` is **almost simple** exactly when `D` is
simple, that is, `|𝓛| = 1`; everything below assumes `|𝓛| ≥ 2` and fixes a
component `L` with `Ḡ = Aut_G(L)`, `H̄ = Aut_H(L)`, `L̄ = Inn(L)`,
`L̄_H = H̄ ∩ L̄`, and `D_H = H ∩ D`, `D̄_H` its image in `Aut(L)`, as in his
Notation 4.3.

## 2.  The two C-dependent steps, and what was misread

The proof of Theorem 3 uses the condition (C) in exactly two places, and the
RP-2 survey (§ 4.12) said both fail for parachutes.  The first reading was
right, the second was wrong.

+  **(6.5)**, the step that rules out the case where every maximal overgroup
   of `H` is of product type: it passes to `Ḡ`, which carries the same
   interval by (4.12)(7), and (4.12)(7) needs `O_G(H)` coatomistic.  A
   parachute has this exactly when it is coatomistic in the sense of § 1.
   The survey said so.
+  **(6.6)(3)**, the step that, when maximal overgroups of both types occur,
   shows `L̄_H = 1` and `M^III(H) = ∅`.  Its proof reads: "As `O₂` contains
   an edge, we may assume `M′ ∈ O₂ ∩ M(H) − {M₂}` with `M₂ ∩ M′ ≠ H`."  The
   extracted text of the paper had dropped the `≠` (as it dropped every
   `≠` and `≰` in Sections 4 and 6), and the survey read the step as
   needing two coatoms of one component meeting **in** `H`, which two
   coatoms of one canopy never do.  The published page (p. 825) has
   `M₂ ∩ M′ ≠ H`: two coatoms of one component meeting **above** `H`.  The
   condition (C) supplies such a pair from an edge `K < M₂` of `O₂`, since
   `K` is a meet of coatoms and is not `M₂`, so a second coatom lies above
   `K`; a canopy with two coatoms supplies such a pair outright, because two
   elements of one canopy meet above that canopy's atom.  This last fact is
   `same-canopy-meet-≢⊥` of the lattice module: two lines.

So the second step needs, not (C), but a canopy on the side `O₂` with two
coatoms, and the parachutes of § 1 have one on every side that matters.

## 3.  The trichotomy on the maximal overgroups

Let `(H, G)` be a core-free representation of `Λ` with `|𝓛| ≥ 2`.  His (4.7)
(which rests on Theorem 1 of Aschbacher–Scott, the case (C) of maximal
subgroups not containing `F*(G)`) sorts the maximal overgroups `M ∈ M(H)`
into two kinds:

+  **product type** (his `M^I(H)`): `M ∩ D = ∏_X M_X` with `M_X = M ∩ X`
   nontrivial and `M̄_L` a maximal proper `H̄`-invariant subgroup of `L̄`
   containing `D̄_H`;
+  **diagonal type** (his `M^II(H)`): `M ∩ D = ∏_{γ ∈ Γ(M)} M_γ` over a
   maximal `G`-invariant partition `Γ(M)` of `𝓛`, each `M_γ` a full diagonal
   subgroup of `D_γ`; in particular `M ∩ X = 1` for every component.  Among
   these, `M^III(H)` are those with `Inn(M_γ) ≤ Aut_H(M_γ)` and `M^IV(H)`
   the rest.

The maximal overgroups of `H` are the coatoms of `[H, G]`, one or more in
each canopy (a canopy has at least two elements, so it has a maximal proper
element), and two coatoms lie in the same canopy exactly when they meet
above `H`.

**Theorem A (homogeneity of type; no minimality).**  Let `Λ` have two big
canopies and two two-coatom canopies, and let `(H, G)` be a core-free
representation with `|𝓛| ≥ 2`.  Then the coatoms of `[H, G]` are all of
product type or all of diagonal type.

*Proof.*  Suppose both types occur.  Since every canopy has a coatom and
there are at least two canopies, some product-type `M₁` and some
diagonal-type `M₂` lie in different canopies, so `M₁ ∩ M₂ = H`; this is the
hypothesis of (4.11), and (6.2)'s partition is taken with `M₁ ∈ O₁`,
`M₂ ∈ O₂`.  By (6.6)(1) and (2), whose proofs use nothing about `Λ` beyond
its being a D-lattice satisfying Hypothesis 4.6, either `L̄_H = 1` or
`M^III(H) ≠ ∅`, and `D_H = 1`.

Assume `L̄_H ≠ 1`.  By (4.11)(1) any two product-type coatoms meet above `H`,
so all of `M^I(H)` lies in one canopy `C₁`.  Take a canopy `C ≠ C₁` with two
coatoms `M, M′` (the hypothesis, used here).  Both are of diagonal type, and
`M ∩ M′` lies above the atom of `C`, so `H` is maximal in neither; by
(4.11)(2), applied to `M₁` and each of them, neither is in `M^IV(H)`, so both
are in `M^III(H)`.  Now (4.14)(5), whose hypotheses `M^I(H) ≠ ∅ ≠ M^III(H)`
hold, says that distinct `M, M′ ∈ M^III(H)` either meet in `H` or lie with
`M₁` in one connected component of `O_G(H)′`; they meet above `H` and `M₁`
lies in another canopy.  This contradiction gives `L̄_H = 1`, and then
(4.14)(2), which says `L̄_H ≠ 1` whenever `M^I(H)` and `M^III(H)` are both
nonempty, gives `M^III(H) = ∅`.  This is (6.6)(3) for `Λ`.

The rest is the body of (6.8).  With `L̄_H = 1` and `D_H = 1`, all of `M^I(H)`
lies in one connected component of `O_G(H)′`: if `H̄ = 1` through the full
diagonal subgroup `F = C_D(H)` of (3.6), every product-type coatom meeting
`HF` above `H`; if `H̄ ≠ 1` because `H̄` is a nontrivial complement to `L̄` in
`Ḡ` and (5.3) makes the lattice of `H̄`-invariant subgroups of `L̄` connected,
which by (4.9)(4) connects the product-type coatoms.  Let `C₁` be that
canopy.  Some other canopy is big; take a coatom `M₂` of it, so `H < K₂ < M₂`
for its atom `K₂`.  `M₂` is of diagonal type, hence in `M^IV(H)`, and `H` is
not maximal in it, so (4.11)(2)(ii) produces a product-type `M` with
`M ∩ M₂ ≠ H`; but `M` lies in `C₁` and `M₂` does not.  ∎

Two remarks.  The minimality of `G` is used nowhere; Theorem A constrains
*every* core-free representation, which is the level at which the RP-3 hunt
works.  And (5.3) is the one step that uses the classification of the finite
simple groups (through the structure of `Out(L)`), exactly as in the paper.

## 4.  The theorem

**Theorem B (product type).**  Let `Λ` be coatomistic with two big canopies,
and `(H, G)` a core-free representation with `|𝓛| ≥ 2` in which every coatom
is of product type.  Then `O_Ḡ(H̄) ≅ Λ`, and `|Ḡ| < |G|`.

*Proof.*  Two coatoms from different canopies meet in `H`, so (4.12)
applies, and (4.12)(7) makes `η : O_Ḡ(H̄) → O_G(H)` an isomorphism because
`O_G(H)` is coatomistic.  The conjugation map `N_G(L) → Ḡ` is onto with
kernel `C_G(L) ⊇ ∏_{X ≠ L} X ≠ 1`, so `|Ḡ| < |N_G(L)| ≤ |G|`.  ∎

**Theorem C (diagonal type).**  Let `Λ` have two big canopies and `(H, G)`
be a core-free representation with `|𝓛| ≥ 2` in which every coatom is of
diagonal type.  Then `L̄_H = L̄` (`H` induces every inner automorphism of a
component), and one of the following holds.

+  (C1) `H ∩ D = 1`, so `H` is a complement to `D = F*(G)`; Hypothesis 3.1
   holds; `H` acts faithfully on `𝓛`; and `O_G(H)` is the signalizer lattice
   `Λ(τ)` of `τ = (H, N_H(L), C_H(L)) ∈ T(L)`.
+  (C2) `H ∩ D = ∏_{γ ∈ Γ₀} D_{H,γ}` is a product of full diagonal subgroups
   over an `H`-invariant partition `Γ₀` of `𝓛` with blocks of size at least
   two, and `O_G(H)` is anti-isomorphic to the interval `[N_H*, H₀*]` of the
   permutation group `H* ≤ Sym(𝓛)` induced by `H`, where `H₀` stabilizes the
   block of `Γ₀` containing `L`.  In particular the dual of `Λ` is an
   interval in a group of order at most `|H| < |G|`.

*Proof.*  `M^I(H) = ∅` gives `L̄_H = L̄` by (4.10)(1), and then `D̄_H ∈ {1, L̄}`
by (4.5)(6).  If `D̄_H = 1` then `D_H = 1`, and (6.7)(4) through (8) give
(C1); the proof of (6.7) uses the minimality of `G` only in the other case.
If `D̄_H = L̄`, (4.13)(2) through (4) give (C2); the blocks have size at least
two because a block of size one would put a component inside `H ∩ D`,
against `ker_H(G) = 1` and the transitivity of `H`.  ∎

**Theorem (Aschbacher's Theorem 3 for parachutes).**  Let `Λ` be a
coatomistic parachute with two big canopies, and `(H, G)` a core-free finite
representation of `Λ`, with `D` the monolith of `G`.  Then one of the
following holds.

1.  `D` is simple, so `G` is almost simple.
2.  `H` is a complement to `D`, and `O_G(H) ≅ Λ(τ)` as in (C1).
3.  `Λ ≅ O_Ḡ(H̄)` for the almost simple group `Ḡ = Aut_G(L)`, with
    `|Ḡ| < |G|`.
4.  The dual of `Λ` is an interval in a group of order less than `|G|`.

If `|G|` is least among the representations of `Λ` and of its dual, only 1
and 2 remain, which is the conclusion of Theorem 3; if `|G|` is least among
the representations of `Λ` alone, 4 remains as well.

*Proof.*  If `|𝓛| = 1` we are in 1.  Otherwise `Λ` satisfies the hypotheses
of Theorem A (§ 1), so the coatoms are homogeneous in type; product type is
Theorem B, alternative 3; diagonal type is Theorem C, alternatives 2 and 4.
The two minimality statements follow because 3 and 4 each exhibit a smaller
group with an interval isomorphic to `Λ` or to its dual.  ∎

## 5.  The caveat: the dual

Aschbacher's minimality ranges over `Λ` and its dual, and his class of
CD-lattices is closed under duality, so his Theorem 3 says the same thing
whichever of the two a minimal pair realizes.  A parachute with a big canopy
is never atomistic, so its dual is never coatomistic, and Theorem B has no
counterpart for a representation of the dual: in the all-product-type case
the retraction `η` of (4.12) only shows that `O_Ḡ(H̄)` is the sub-poset of
product-type members, a dual parachute whose canopies are lattice-closed
subsets of the `Lᵢ`, and no contradiction with minimality follows unless
every member is of product type.  Theorem A does transfer to the dual, since
the dual of a parachute with two two-coatom canopies has two components each
containing two *atoms* whose join is proper, but (6.6)(3) is about coatoms
and the dual's coatoms pairwise meet in `H`; so the mixed case is not
excluded on the dual side either, though (6.6)(2) still makes `H` a
complement to `D` there.  What can be said about a minimal pair in
Aschbacher's sense that realizes the dual is: `G` is almost simple, or `H`
complements `D` (cases (6.6)(2) and (C1)), or every coatom is of product
type with some member of the interval not of product type.  This is the
honest form of the reduction over `G*(Λ)`, and the formal entry states the
theorem for representations of `Λ` itself with all four alternatives
explicit, leaving the minimality to two derived corollaries.

## 6.  What the alternatives look like

Each alternative of the theorem is realized by a known construction, which
is the reason the theorem yields no separating invariant by itself.

+  **Alternative 3** is the "wreathed almost simple" shape.  If `Λ ≅ [H̄, Ḡ]`
   with `Ḡ` almost simple and `H̄ ∩ L̄ = 1`, then `G = Ḡ ≀ C₂` with
   `H = H̄ ≀ C₂` is a core-free representation of `Λ` with `D = L²` and every
   coatom of product type: the `H`-invariant subgroups of `D` are the
   products `V × V^h` for `V` an `H̄`-invariant subgroup of `L`, no full
   diagonal being invariant under `H̄ × H̄`.  So an almost simple
   representation always comes with non-almost-simple ones of alternative 3.
+  **Alternative 4** is the shape of the Kurzweil wreaths.  For the wreath
   `U = S ≀ G` over the cosets of a core-free `H ≤ G`, the interval
   `[Diag × G, U]` is the dual of `[H, G]` (Kurzweil, Entry 5 of the
   registry), its coatoms correspond to the atoms `K` of `[H, G]` and are
   `S^{π_K} ⋊ G` with `π_K` the partition of `G/H` into `K`-cosets, so each
   coatom meets the socle in a product of full diagonal subgroups, and
   `H ∩ D = Diag ≠ 1` is the full diagonal over the one-block partition.
   This is (C2) with `Γ₀ = {𝓛}`, `H* = G`, `N_H* = H`, and (4.13)(4) is then
   Kurzweil's theorem itself.  The double Kurzweil wreath, which represents
   `Λ` again, is (C2) with `H₀* = U`.  The claim in the issue that these
   coatoms "label product-action" is therefore not right: they are of
   diagonal type.  Checked in GAP on the smallest instance, `A₅ ≀ C₄` over
   `Diag × C₄` (index 216000, core-free): the interval is a chain of three,
   its coatom meets the socle in `60²` elements and each coordinate `A₅`
   trivially, and its coset action on `3600` points is primitive
   (`scripts/gap/flrp/bin/wreath_coatom_type.g`, record
   `scripts/gap/flrp/out/wreath_coatom_type_a5_c4.json`).  GAP's
   `ONanScottType` returns the code `4b` for that action, which its manual
   glosses as a product action with an almost simple factor; the direct
   computation of the stabilizer in the socle is what this note relies on.
+  **Alternative 2** is realized by Aschbacher's Section 8 for parachutes
   whose canopies each have a *unique* coatom (his (8.4): the components of
   `Λ(τ)` are the duals of `[Kᵢ, Hᵢ]` with a top adjoined), the hexagon
   among them; for a coatomistic parachute with big canopies no example of
   alternative 2 is known, and none of alternative 1 either.

The known almost simple representations of parachutes (the hexagon in
`U₄(2)`, `A₁₁`, `U₃(7)`; `P(3,3,2)` in `PΓL(2,8)` and `PSL(2,25)`; `P(3,4)` in
`U₄(3).2₁`) are alternative 1 and carry no type label (the socle is simple);
in the vocabulary of the issue's third path, every coatom action of an
almost simple group is of O'Nan–Scott type "almost simple".

## 7.  What this gives the program, and what it does not

+  **Theorem A is an enforcement theorem** in the RP-3 sense, at the level
   the hunt asked for: it constrains the monolith and the action on it in
   *every* core-free representation of a parachute with two two-coatom
   canopies.  But its two polarities are both realized (alternatives 3 and
   4 above), so "homogeneous of product type" and "homogeneous of diagonal
   type" are each a class that omits representations the other contains,
   and neither is a candidate cf-IE class on its own; the RP-3 caution on
   pinned invariants applies.
+  **The reduction imports the almost simple machinery** for coatomistic
   parachutes exactly as Theorem 3 does for CD-lattices: to show such a
   parachute is not a group interval one must exclude an almost simple
   representation of it or of its dual, a signalizer-lattice representation,
   and the two dual-side cases of § 5.  That is the shape of Aschbacher's
   program for the `DΔ`-lattices (2009, 2012, 2013), which after fifteen
   years has settled the alternating and symmetric groups and started the
   Lie-type case.  Nothing here shortens it.
+  **The smallest target** is `P(2×2, 2×2)`, the parachute of two
   four-element Boolean lattices, eight elements, the least coatomistic
   parachute with two big canopies.  Whether it is a group interval is open.
   The tables-of-marks scan of 2026-09-28 (`scripts/gap/flrp/out/tomscan_pm2m2.json`,
   `tomscan_pm2m2_big.json`, `tomscan_pm2m2d.json`) finds neither it nor
   its dual in any of the 414 tables: no marks-exact hit, and the two
   ambiguous cases for each resolved negative explicitly (for the lattice,
   `M12.2` and `He.2`, the latter with a 12 GB heap; both intervals have
   three atoms).  So its minimal carrier, if any, lies outside TomLib; the
   SmallGroups sweep has not been run for eight-element targets.
+  **The parachute of two rank-3 Boolean lattices** `P(2³, 2³)` is the
   coatomistic parachute closest to Shareshian's `DΔ(3,3)`, which is that
   parachute with its two atoms deleted.  The scan of the same day finds
   `DΔ(3,3)` in none of the 414 tables either, with no ambiguous case at all
   (`scripts/gap/flrp/out/tomscan_dd33.json`): among the 3396 upper
   intervals of size fourteen in the library, none has its up-count profile.

## 8.  Verification status

`verified` means read in the cited text; `secondary` means read in a source
about it; `computed` means checked in GAP with a committed record.

| Claim | Source | Status | How |
| --- | --- | --- | --- |
| Proposition 2; (1.2); (2.1)–(2.3); (4.2)–(4.14); (5.2), (5.3); (6.2)–(6.8); (7.1); (8.4) | Aschbacher 2008 | **verified** | the published text in full; the page images of pp. 818–822 and 825–826 for every `≠` and `≰` in (4.5), (4.7), (4.9)–(4.14), (6.5)–(6.8) |
| (6.6)(3)'s proof needs two coatoms of `O₂` with `M₂ ∩ M′ ≠ H` | Aschbacher 2008, p. 825 | **verified** | the page image; the extracted text drops the symbol |
| (4.7) rests on Theorem 1, case (C), of Aschbacher–Scott 1985 | cited by Aschbacher 2008 | **secondary** | not read; consumed only through (4.7) as stated in the 2008 text |
| The Kurzweil wreath's coatom over `Diag × Ū` is of diagonal type | this note, § 6 | **computed** at `A₅ ≀ C₄` | `scripts/gap/flrp/out/wreath_coatom_type_a5_c4.json`; the general statement is the identification of the coatoms with the partition subgroups `S^{π_K} ⋊ G`, an elementary reading of Kurzweil's isomorphism |
| `P(2×2, 2×2)`, its dual, and `DΔ(3,3)` are upper intervals in none of TomLib's 414 tables | this repository | **computed** | `tomscan_pm2m2.json`, `tomscan_pm2m2_big.json`, `tomscan_pm2m2d.json`, `tomscan_dd33.json` |
| The isomorphism test of the scan agrees with the brute-force one | this repository | **computed** | the hexagon re-scan reproduced the committed sixteen hits and 143 ambiguous cases |

## 9.  Formal artifacts

+  `Classical.Structures.Lattice.Disconnected`: `IsCoatom`, `IsCoatomistic`
   (Aschbacher's `C*`-condition), and `same-canopy-meet`,
   `same-canopy-meet-≢⊥` (two elements of one canopy meet above its atom).
+  `FLRP.Reductions.Coatomistic`: the hypotheses `TwoBigCanopiesᴸ`,
   `TwoCoatoms`, `TwoCoatomCanopies`; the alternatives `MonolithSimple`,
   `ComplementsMonolith`, `SmallerRepresentation`; the imported theorem
   `ParachuteTheorem3` with the four alternatives; the minimality notions
   `Minimal`, `DualMinimal`; and the two derived corollaries
   `theorem3-dualMinimal` and `theorem3-minimal`.
+  Not formalized, recorded here: Theorem A (it needs the component
   decomposition of the monolith to state "type"), the signalizer-lattice
   clause of alternative 2, and the structure of alternative 4.
