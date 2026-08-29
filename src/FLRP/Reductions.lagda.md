---
layout: default
file: "src/FLRP/Reductions.lagda.md"
title: "FLRP.Reductions module (The Agda Universal Algebra Library)"
date: "2026-07-26"
author: "the agda-algebras development team"
---

### The enforcement catalog

This is the [FLRP.Reductions][] module of the [Agda Universal Algebra Library][].

The catalog of research phase RP-2: the literature's "an interval of this shape forces
a group of this kind" theorems, each recast as a precise (cf-/min-)interval
enforceability statement in the vocabulary of [FLRP.Enforceable][].  It is the
machine-readable inventory the hunt of RP-3 runs over, and the survey note
`docs/notes/flrp-rp2-catalog.md` is its human-readable companion — the entry table,
the verification status of every literature claim, and the entries considered and
rejected as too vague to state.

Every entry records, in prose above its statements:

+  the **property** and its enforcing **lattice**;
+  the **source**, with a precise citation;
+  whether the enforcement is **IE**, **cf-IE**, or **min-IE**;
+  whether the proof is **formalized here** or **imported as a named hypothesis**;
+  the **group representability status** of the enforcing lattice — the vacuity
   discipline below.

**Vacuity discipline**.  If no group realizes `𝑳` as an upper interval then *every*
property is enforced via `𝑳`, vacuously — and deciding that emptiness is the original
problem.  `not-representable→IE`{.AgdaFunction} below makes this formal, in two
lines, and it is the reason group representability of an enforcing lattice is tracked
explicitly by every entry rather than quantified away.  An entry whose lattice is not
known to be group representable is still a legitimate entry (Entry 7, whose lattice
is `L7`, is the extreme case); it just has to say so, and it does.

**No postulates**.  A theorem whose proof stays on paper becomes a *named, cited
hypothesis*: a type defined here, threaded as an ordinary argument by the results that
consume it, exactly as [FLRP.Assumptions][] does for the program's standing classical
imports.  Nothing in this module is asserted that is not proved.

**Two group-theoretic predicates the library does not have**.  Solvability and being
an alternating or symmetric group are not definable in the library today, so Entries 4,
5, 7, and 8 are parameterized by an abstract predicate together with the facts their
sources supply about it.  The statements are therefore *schemas*, honest about what
they assume; when the predicates land, the schemas instantiate unchanged.

#### Contents

+  **Vocabulary** — vacuity and non-vacuity, Lemma 3.1 (proved here), refutation of
   enforcement from a witness, the min-IE repair, and the enforcing lattices `Mₙ`.
+  **Entries 1–3** — `𝒢₂` (subdirectly irreducible), `𝒢₃` (no nontrivial abelian
   normal subgroup), `𝒢₄` (trivial centralizers): cf-IE via parachutes, *derived*
   from RP-1 ([FLRP.Parachute][]), modulo the minimal-normal-subgroup hypothesis.
+  **Composition** — Corollary 3.8 and the strategy meta-theorem as catalog
   operations, with the observation that cf-IE composes while representability does
   not.
+  **Entry 4** — `𝒢₀` (nonsolvable), IE via `M₇`; Pálfy–Pudlák, Pálfy, Feit.
+  **Entry 5** — `𝒢₁` (neither alternating nor symmetric), IE via `M₆`; Basile,
   after Pálfy.
+  **Entry 6** — min-IE via `Mₙ` for `n − 1` not a prime power; Köhler,
   Pálfy–Pudlák, Feit.
+  **Entry 7** — the four structural restrictions on a core-free representation of
   `L7`; DeMeo's thesis, Theorem 6.3.1.
+  **Entry 8** — a *negative* entry: rank-three Boolean lattices do not enforce
   `𝒢₁`; Lucchini–Moscatiello–Palcoux–Spiga.
+  **Entry 9**: the two-element chain enforces exactly on the class of groups with
   a core-free maximal subgroup; elementary, both directions derived, closing the
   two-element corner of the RP-4 reduction.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Reductions where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using  ( ⊥-elim )
open import Data.Fin.Base                          using  ( Fin )
open import Data.Fin.Patterns                      using  ( 0F ; 1F )
open import Data.Fin.Properties                    using  ( _≟_ )
open import Data.Nat.Base renaming ( _≤_ to _≤ⁿ_ ) using  ( ℕ ; zero ; suc ; _+_ )
open import Data.Nat.Properties                    using  ( ≤-refl )
open import Data.Product                           using  ( _×_ ; _,_ ; Σ-syntax
                                                          ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using  ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit.Base                         using  ( tt )
open import Level                                  using  ( Level ; 0ℓ ; _⊔_ ; lift )
                                                   renaming ( suc to lsuc )
open import Relation.Binary                        using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; refl )
open import Relation.Nullary                       using  ( ¬_ ; Dec )
open import Relation.Unary                         using  ( Pred ; _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice            using  ( TopOf ; BottomOf
                                                           ; module Lattice-Order )
open import Classical.Small.Structures              using  ( Lattice )
open import Classical.Structures.Group              using  ( Group ; IsSubgroup
                                                           ; module Centralizer
                                                           ; module Conjugate
                                                           ; module MaximalSubgroup
                                                           ; module MinimalNormal
                                                           ; fullSubgroup )
open import Classical.Structures.Lattice.Parachute   using  ( module LatticeParachute )
open import Classical.Structures.Lattice.Product     using  ( _×ˡ_ )
open import Examples.Classical.Lattices.L7           using  ( L7-lattice )
open import FLRP.Closure.Basic  using  ( chain₂-top ; chain₂-bot )
open import FLRP.Enforceable    using  ( ComplementHClosed ; CoreFree
                                       ; CoreFreeReduction ; GroupProperty
                                       ; GroupRepresentable ; IE ; IE→cfIE
                                       ; IntervalIso ; PropertyStable ; cfIE
                                       ; cfIE→IE-Statement ; minIE
                                       ; module UpperInterval )
open import FLRP.Parachute      using  ( module GroupParachute )

import Classical.Structures.Group.MinimalNormalDescent as Descent
open import FLRP.Parachute.Theorems  using  ( module ParachuteTheorems )
open import FLRP.Problem        using  ( chain₂-lattice ; OrderIso )
open import Setoid.Algebras     using  ( 𝕌[_] ; 𝔻[_] ; FiniteAlgebra )
open import Setoid.Homomorphisms  using  ( _IsHomImageOf_ )
```
-->

#### Vacuity, and what an entry is worth

The two-line theorem the vacuity discipline rests on: a lattice that is *no* interval
in any finite subgroup lattice enforces everything.  So "`P` is IE via `𝑳`" carries no
information at all until `𝑳` is known to be group representable, and deciding that
for an arbitrary `𝑳` is precisely statement (B) of Pálfy–Pudlák.

```agda
-- If `𝑳` is not group representable then every group property is IE via `𝑳`.
not-representable→IE : {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice)
  →  ¬ GroupRepresentable 𝑳 → IE P 𝑳
not-representable→IE P 𝑳 no-rep 𝒢 H H-sg iso = ⊥-elim (no-rep record
  { grp           = 𝒢
  ; sub           = H
  ; isSubgroup    = H-sg
  ; interval-iso  = iso
  })
```

Note what that proof does: it *builds* the representability witness the hypothesis
denies, from the very interval isomorphism the enforcement statement quantifies over.
Vacuous enforcement is not an edge case to be excluded by fiat; it is what
enforcement degenerates to in the absence of a witness.

Conversely, an entry whose enforcing lattice *is* group representable really does
constrain a group.  The core-free reduction is what turns an arbitrary representation
into a core-free one, which is what cf-IE consumes; it is
`CoreFreeReduction`{.AgdaRecord} of [FLRP.Enforceable][], the same named hypothesis
RP-1 threads.

```agda
-- Non-vacuity: a cf-IE entry over a representable lattice exhibits a group with
-- the property.
cfIE-nonvacuous : {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice)
  →  cfIE P 𝑳 → GroupRepresentable 𝑳 → CoreFreeReduction
  →  Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ] P 𝒢
cfIE-nonvacuous P 𝑳 enf rep cfr =
  𝒬 , enf 𝒬 J J-sg J-cf (transport 𝑳 interval-iso)
  where
  open GroupRepresentable rep
  open CoreFreeReduction cfr

  reduced    = reduce grp sub isSubgroup
  𝒬          = proj₁ reduced
  J          = proj₁ (proj₂ reduced)
  J-sg       = proj₁ (proj₂ (proj₂ reduced))
  J-cf       = proj₁ (proj₂ (proj₂ (proj₂ reduced)))
  transport  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ reduced))))
```

For an **IE** entry the reduction is not needed at all: the representation witness is
already a group with the property, core-free or not.  So IE entries are the cheap ones
to make non-vacuous, which is one reason Entries 4 and 5 are stated at that level.

```agda
-- Non-vacuity for an IE entry, with no reduction hypothesis.
IE-nonvacuous : {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice)
  →  IE P 𝑳 → GroupRepresentable 𝑳 → Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ] P 𝒢
IE-nonvacuous P 𝑳 ie rep = grp , ie grp sub isSubgroup interval-iso
  where open GroupRepresentable rep

-- Entries compose at the cf-IE level, so a family of entries drawn from the
-- catalog at mixed levels is weakened family-wise by `IE→cfIE` first.  (The
-- property and lattice are passed explicitly: `IE` is a defined function, so an
-- implicit argument under it is never inferred from the proof.)
IE-family→cfIE-family : {ℓP : Level} {n : ℕ}
  (Ps : Fin n → GroupProperty ℓP) (𝑳s : Fin n → Lattice)
  →  (∀ i → IE (Ps i) (𝑳s i)) → ∀ i → cfIE (Ps i) (𝑳s i)
IE-family→cfIE-family Ps 𝑳s ies i = IE→cfIE {P = Ps i} {𝑳 = 𝑳s i} (ies i)
```

The mirror image of vacuity: a representation of `𝑳` over a group that *fails* `P`
refutes enforcement outright.  This is how the catalog records a *negative* entry —
that a given lattice does **not** enforce a given property (Entry 8).

```agda
-- A representation over a group without `P` refutes IE of `P` via `𝑳`.
witness→¬IE : {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice)
  (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  →  IntervalIso 𝒢 H H-sg 𝑳 → ¬ P 𝒢 → ¬ IE P 𝑳
witness→¬IE P 𝑳 𝒢 H H-sg iso ¬P ie = ¬P (ie 𝒢 H H-sg iso)

-- Over a *core-free* subgroup it refutes cf-IE as well.
witness→¬cfIE : {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice)
  (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  →  CoreFree 𝒢 H H-sg → IntervalIso 𝒢 H H-sg 𝑳 → ¬ P 𝒢 → ¬ cfIE P 𝑳
witness→¬cfIE P 𝑳 𝒢 H H-sg cf iso ¬P enf = ¬P (enf 𝒢 H H-sg cf iso)
```

#### Lemma 3.1, proved

[FLRP.Enforceable][] states the note's Lemma 3.1 as the type
`cfIE→IE-Statement`{.AgdaFunction} and leaves it uninhabited.  The catalog needs it —
Entries 4 and 5 upgrade their sources' core-free facts to plain IE through it — so
here it is, proved.[^1]

The constructive core first.  Given a representation `[H , G] ≅ 𝑳`, the core-free
reduction produces a core-free representation of the same lattice over a homomorphic
image `Q` of `G`; cf-IE gives `P Q`; and if `G` failed `P` then H-closure of the
complementary class would give `¬ P Q`.  So every representation forces `¬ ¬ P G`,
with no classical hypothesis whatsoever.

```agda
-- Lemma 3.1, constructive form: enforcement of `¬ ¬ P`.
cfIE→¬¬ : {ℓP : Level} (P : GroupProperty ℓP)
  →  CoreFreeReduction → ComplementHClosed P → (𝑳 : Lattice) → cfIE P 𝑳
  →  ∀ 𝒢 H H-sg → IntervalIso 𝒢 H H-sg 𝑳 → ¬ ¬ P 𝒢
cfIE→¬¬ P cfr hcl 𝑳 enf 𝒢 H H-sg iso ¬P𝒢 =
  hcl 𝒢 𝒬 hom ¬P𝒢 (enf 𝒬 J J-sg J-cf (transport 𝑳 iso))
  where
  open CoreFreeReduction cfr

  reduced    = reduce 𝒢 H H-sg
  𝒬          = proj₁ reduced
  J          = proj₁ (proj₂ reduced)
  J-sg       = proj₁ (proj₂ (proj₂ reduced))
  J-cf       = proj₁ (proj₂ (proj₂ (proj₂ reduced)))
  transport  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ reduced))))
  hom        = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ reduced))))
```

Stability of `P` under double negation closes the gap, which is exactly the third
hypothesis of `cfIE→IE-Statement`{.AgdaFunction}.

```agda
-- Lemma 3.1 (`lemma-wjd-2` of the note), inhabiting the RP-1 statement type.
cfIE→IE : {ℓP : Level} (P : GroupProperty ℓP) → cfIE→IE-Statement P
cfIE→IE P cfr hcl stable 𝑳 enf 𝒢 H H-sg iso =
  stable 𝒢 (cfIE→¬¬ P cfr hcl 𝑳 enf 𝒢 H H-sg iso)
```

Now the observation that makes Lemma 3.1 free of classical content *for the catalog's
entries*.  Every cf-IE property the literature supplies is the **negation** of a
common group property — "not solvable", "not alternating or symmetric", "not almost
simple" — as the note itself remarks, and a negation is double-negation stable with no
assumption at all.

```agda
-- A negated property is stable under double negation, unconditionally.
negation-Stable : {ℓQ : Level} (Q : GroupProperty ℓQ) → PropertyStable (λ 𝒢 → ¬ Q 𝒢)
negation-Stable Q 𝒢 ¬¬¬q q = ¬¬¬q (λ ¬q → ¬q q)
```

Likewise the H-closure hypothesis simplifies: for a negated property, the
complementary class is the original class, so plain closure of that class under
homomorphic images suffices.

```agda
-- A class closed under homomorphic images.
HClosed : {ℓQ : Level} → GroupProperty ℓQ → Type (lsuc 0ℓ ⊔ ℓQ)
HClosed Q = ∀ 𝒢 𝒬 → 𝒬 .proj₁ IsHomImageOf 𝒢 .proj₁ → Q 𝒢 → Q 𝒬

-- H-closure of `Q` is Lemma 3.1's hypothesis for the property `¬ Q`.
HClosed→ComplementHClosed : {ℓQ : Level} (Q : GroupProperty ℓQ)
  →  HClosed Q → ComplementHClosed (λ 𝒢 → ¬ Q 𝒢)
HClosed→ComplementHClosed Q hcl 𝒢 𝒬 hom ¬¬q ¬q𝒬 = ¬¬q (λ q𝒢 → ¬q𝒬 (hcl 𝒢 𝒬 hom q𝒢))

-- Lemma 3.1 for a negated class: cf-IE upgrades to IE with no classical
-- hypothesis beyond the core-free reduction and H-closure of the class.
cfIE→IE-negation : {ℓQ : Level} (Q : GroupProperty ℓQ)
  →  CoreFreeReduction → HClosed Q → (𝑳 : Lattice)
  →  cfIE (λ 𝒢 → ¬ Q 𝒢) 𝑳 → IE (λ 𝒢 → ¬ Q 𝒢) 𝑳
cfIE→IE-negation Q cfr hcl =
  cfIE→IE  (λ 𝒢 → ¬ Q 𝒢) cfr (HClosed→ComplementHClosed Q hcl) (negation-Stable Q)
```

#### Exclusion lattices

Entries 4 and 5 have the same shape, and it is the shape the sources deliver: a
lattice that *cannot* occur as the upper interval above a core-free subgroup of a
group in some class `Q`.  Such an **exclusion** is literally core-free enforcement of
`¬ Q`, and Lemma 3.1 lifts it to IE.

```agda
-- `𝑳` is no upper interval above a core-free subgroup of a group in the class `Q`.
CoreFreeExclusion : {ℓQ : Level} → GroupProperty ℓQ → Lattice → Type (lsuc 0ℓ ⊔ ℓQ)
CoreFreeExclusion Q 𝑳 =
  ∀ 𝒢 H H-sg → CoreFree 𝒢 H H-sg → Q 𝒢 → ¬ IntervalIso 𝒢 H H-sg 𝑳

-- An exclusion is core-free enforcement of the complementary class ...
exclusion→cfIE : {ℓQ : Level} (Q : GroupProperty ℓQ) (𝑳 : Lattice)
  →  CoreFreeExclusion Q 𝑳 → cfIE (λ 𝒢 → ¬ Q 𝒢) 𝑳
exclusion→cfIE Q 𝑳 exc 𝒢 H H-sg cf iso q = exc 𝒢 H H-sg cf q iso

-- ... and hence, by Lemma 3.1, interval enforcement of it.
exclusion→IE : {ℓQ : Level} (Q : GroupProperty ℓQ) (𝑳 : Lattice)
  →  CoreFreeReduction → HClosed Q → CoreFreeExclusion Q 𝑳 → IE (λ 𝒢 → ¬ Q 𝒢) 𝑳
exclusion→IE Q 𝑳 cfr hcl exc =
  cfIE→IE-negation Q cfr hcl 𝑳 (exclusion→cfIE Q 𝑳 exc)
```

#### min-IE, repaired

`minIE`{.AgdaFunction} of [FLRP.Enforceable][] quantifies minimality against a
*single* other representation, so instantiating that other representation with the
given one collapses it: `minIE P 𝑳`{.AgdaFunction} implies `P` of **every** finitely
presented representation of `𝑳`, which is plain IE restricted to finite groups.  The
one-line proof is the honest record of the defect.[^2]

```agda
-- `minIE` is degenerate: it forces `P` of every finite representation.
minIE-degenerate : {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice) → minIE P 𝑳
  →  ∀ 𝒢 H H-sg → FiniteAlgebra (proj₁ 𝒢) → IntervalIso 𝒢 H H-sg 𝑳 → P 𝒢
minIE-degenerate P 𝑳 m 𝒢 H H-sg fin iso = m 𝒢 𝒢 H H H-sg H-sg fin iso fin iso ≤-refl
```

The catalog therefore states its min-IE entry over the repaired notion, in which
minimality is quantified over *all* finite representations.  As with
`minIE`{.AgdaFunction}, cardinality is the certified `card`{.AgdaField} of the
`FiniteAlgebra`{.AgdaRecord} interface, which bounds the carrier from above; with
exact enumerations this is the `|G|`-minimality of the literature.

```agda
open FiniteAlgebra using ( card )

-- `P` holds of every representation of `𝑳` of least certified cardinality.
MinimallyIE : {ℓP : Level} → GroupProperty ℓP → Lattice → Type (lsuc 0ℓ ⊔ ℓP)
MinimallyIE P 𝑳 =
  ∀ 𝒢 H H-sg (fin : FiniteAlgebra (proj₁ 𝒢)) → IntervalIso 𝒢 H H-sg 𝑳
  → (∀ 𝒬 J J-sg (fin' : FiniteAlgebra (proj₁ 𝒬))
       → IntervalIso 𝒬 J J-sg 𝑳 → fin .card ≤ⁿ fin' .card)
  → P 𝒢

-- Interval enforcement is minimal enforcement, forgetting minimality.
IE→MinimallyIE : {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice)
  →  IE P 𝑳 → MinimallyIE P 𝑳
IE→MinimallyIE P 𝑳 ie 𝒢 H H-sg fin iso least = ie 𝒢 H H-sg iso

-- Minimal enforcement is closed under conjunction with no parachute: minimality
-- is a property of the representation, not of the lattice.  (Contrast
-- Corollary 3.8 below, where the enforcing lattices differ and a parachute is
-- what glues them.)
MinimallyIE-∧ : {ℓ₁ ℓ₂ : Level} (P₁ : GroupProperty ℓ₁) (P₂ : GroupProperty ℓ₂)
  (𝑳 : Lattice) → MinimallyIE P₁ 𝑳 → MinimallyIE P₂ 𝑳
  →  MinimallyIE (λ 𝒢 → P₁ 𝒢 × P₂ 𝒢) 𝑳
MinimallyIE-∧ P₁ P₂ 𝑳 m₁ m₂ 𝒢 H H-sg fin iso least =
  m₁ 𝒢 H H-sg fin iso least , m₂ 𝒢 H H-sg fin iso least
```

#### The enforcing lattices `Mₙ`

`Mₙ` is the `(n + 2)`-element lattice of height two with `n` atoms — the shape whose
representability is the classical stress test, and the enforcing lattice of Entries 4,
5, and 6.  It is available with no new construction: it is the **parachute** of `n`
two-element chains ([Classical.Structures.Lattice.Parachute][]).  The parachute's
carrier lists the shared top, the fresh bottom, and the *proper* elements of each
canopy; a two-element chain has exactly one proper element, its bottom, which is the
`n`-th atom.  So `𝒫(𝟚 , … , 𝟚)` is `Mₙ` on the nose, with `atom`{.AgdaFunction} and
`covered`{.AgdaFunction} of `ParachuteAtoms`{.AgdaModule} witnessing the height-two
shape.

Note that `Mₙ` has *no* big canopy, so none of the parachute theorems of
[FLRP.Parachute][] applies to it — the note's hypothesis "at least two `|Lᵢ| > 2`"
fails.  This is exactly why Entries 4, 5, and 6 need external theorems where
Entries 1–3 need only RP-1.

```agda
private
  -- The two-element chain's decision procedure for being the top, and the
  -- nondegeneracy its parachute needs; both are computations on `Fin 2`.
  chain₂-top? : (x : 𝕌[ proj₁ chain₂-lattice ])
    →  Dec (Setoid._≈_ 𝔻[ proj₁ chain₂-lattice ] x (proj₁ chain₂-top))
  chain₂-top? x = x ≟ 1F

  chain₂-nondeg :
    ¬ (Setoid._≈_ 𝔻[ proj₁ chain₂-lattice ] (proj₁ chain₂-bot) (proj₁ chain₂-top))
  chain₂-nondeg ()

  -- The parachute of `suc m` two-element chains.
  module Mᵃ (m : ℕ) = LatticeParachute  {m = m} (λ (_ : Fin (suc m)) → chain₂-lattice)
                                      (λ _ → chain₂-top) (λ _ → chain₂-top?)
                                      (λ _ → chain₂-bot) (λ _ → chain₂-nondeg)

-- Mₙ: the (n + 2)-element lattice with n atoms.  (M₀ is the two-element chain.)
M[_] : ℕ → Lattice
M[ zero ]   = chain₂-lattice
M[ suc m ]  = Mᵃ.⊕ᵖ-Lattice m
```

#### The note's classes `𝒢₂`, `𝒢₃`, `𝒢₄`

The three classes the parachute construction makes enforceable, as group properties.
Each quantifies over *all* normal subgroups at the program's fixed level `0ℓ`; the
notions of normal subgroup, nontriviality, minimality, monolith, and abelianness are
those of [Classical.Structures.Group.MinimalNormal][].

`𝒢₂` is subdirect irreducibility, in the group-side form: `G` has a **monolith**, a
least nontrivial normal subgroup.  For groups this is equivalent to subdirect
irreducibility in the universal-algebraic sense, which is how the note states it;
the algebra-side notion `IsSubdirectlyIrreducible`{.AgdaFunction} of
[Setoid.Congruences.Monolith][] is about the congruence lattice, and the bridge — the
correspondence between normal subgroups of `G` and congruences of `G` — is not yet
formalized (see the survey note, § 4).

```agda
-- 𝒢₂: the subdirectly irreducible groups.
𝒢₂ : GroupProperty (lsuc 0ℓ)
𝒢₂ 𝒢 = MinimalNormal.HasMonolithᵍ 𝒢 0ℓ
```

`𝒢₃` is "no nontrivial abelian normal subgroup", stated as the note's own Remark
states it: *every nontrivial normal subgroup is nonabelian*.  The two readings are
classically the same statement, and this one needs no decision — the alternative
("every abelian normal subgroup is trivial") is not derivable from the centralizer
argument without deciding triviality.

```agda
-- 𝒢₃: no nontrivial abelian normal subgroup.
𝒢₃ : GroupProperty (lsuc 0ℓ)
𝒢₃ 𝒢 = (N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsNormalSubgroup N → Nontrivial N → ¬ Abelian N
  where open MinimalNormal 𝒢 0ℓ
```

`𝒢₄` is the note's `{G : C_G(M) = 1 for all 1 ≠ M ⊴ G}`.  The macro named
`\subnormal` in the note's source expands to `⊴`, so the quantifier ranges over
*normal* subgroups, not subnormal ones.  (The thesis version of the class quantifies
over a single minimal normal subgroup; the note strengthens it to all of them, and
this is the note's form.)

```agda
-- 𝒢₄: every nontrivial normal subgroup has trivial centralizer.
𝒢₄ : GroupProperty (lsuc 0ℓ)
𝒢₄ 𝒢 = (N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsNormalSubgroup N → Nontrivial N → C[ N ] ⊆ Triv
  where  open MinimalNormal 𝒢 0ℓ
         open Centralizer 𝒢  using  ( C[_] )
```

One hypothesis is threaded through all three entries and named here rather than
smuggled in.  **Minimal-normal descent**: every nontrivial normal subgroup of a
*finite* group contains a minimal one.  RP-1 threads it as a module parameter of
`Structure.Minimal`{.AgdaModule}, and the catalog threads it as a property of the group
being constrained — so the quantifier over normal subgroups in `𝒢₃` and `𝒢₄` is *not*
silently dropped.  Classically every finite group satisfies it, so on the note's
universe of discourse the entries below say exactly what the note says; what the
formal discharge below additionally needs is recorded after the definition.

```agda
-- Minimal-normal descent: a consequence of finiteness, threaded explicitly.
MinimalNormalDescent : GroupProperty (lsuc 0ℓ)
MinimalNormalDescent 𝒢 =
  (N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsNormalSubgroup N → Nontrivial N
  → Σ[ M ∈ Pred 𝕌[ proj₁ 𝒢 ] 0ℓ ] (IsMinimalNormal M × M ⊆ N)
  where open MinimalNormal 𝒢 0ℓ
```

It is no longer an unproved fact.  [Classical.Structures.Group.MinimalNormalDescent][]
proves the descent for a finite group, by well-founded recursion on the order of a
subgroup, with normal closures of single elements as the descending chain; what remains
is a *presentation* hypothesis, not a group-theoretic one.  Minimality quantifies over
every normal subgroup, including those whose membership cannot be decided, and the
no-go `minimal→DNE`{.AgdaFunction} of that module shows the *witnessed* reading of
unrestricted minimality yields double-negation elimination — so no constructive proof
can return witnessed minimal subgroups against arbitrary predicates, and the
construction's output must be restricted somewhere.  `finite-MinimalNormalDescent`
below therefore discharges the property for a finite group *whenever* its normal
subgroups are decidably presented — the group-side reading of `complete`{.AgdaField}
of `FiniteCongruences`{.AgdaRecord}, which the two-layer note
(`docs/notes/flrp-two-layer-congruences.md`) already identifies as the library's
single Layer-S bridge.  Decidable presentation is the sufficient bridge this module
establishes, and the no-go is why the witnessed route demands *some* such datum; the
bare negative reading of the property carries no witness for the no-go to exploit,
and its unconditional derivability is left open.

```agda
-- Descent is a theorem for a finite group with decidably presented normal subgroups.
finite-MinimalNormalDescent : (𝒢 : Group 0ℓ 0ℓ)(𝑭 : FiniteAlgebra (proj₁ 𝒢))
  →  Descent.MinimalNormalDescent.DecidablyPresented 𝒢 𝑭 → MinimalNormalDescent 𝒢
finite-MinimalNormalDescent =
  Descent.MinimalNormalDescent.minimal-normal-descent-sem
```

The antecedent of Entries 1–3 is therefore no longer a *conjecture* of finite group
theory but a layer-crossing datum, and the entries retire the moment a consumer
supplies it — for a concrete certificate, by computation.

#### Entries 1–3: the parachute classes

**Property**.  `𝒢₂` (subdirectly irreducible), `𝒢₃` (no nontrivial abelian normal
subgroup), `𝒢₄` (trivial centralizers).

**Enforcing lattice**.  Any parachute `𝒫(L₁ , … , Lₙ)` with `n ≥ 2` canopies, at
least two of them with more than two elements.

**Source**.  The note, Lemma 3.7 (`lemma-wjd-5`) and its Remark:
`docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`.

**Level**.  cf-IE — and none of the three is IE via a *group representable* lattice:
by `IE-fattens`{.AgdaFunction} of [FLRP.Enforceable][], such an entry would force the
property on `G × K` for every `K`, and a suitable direct factor destroys each of them
(`1 × K` is a nontrivial normal subgroup centralized by `G × 1`, it is abelian for
abelian `K`, and it meets a minimal normal subgroup of `G × 1` trivially).  Via a
lattice that is *not* representable they are of course IE, vacuously
(`not-representable→IE`{.AgdaFunction}) — which is the note's remark after Lemma 3.2
read with the vacuity discipline switched on.

**Formalized here**, from RP-1 ([FLRP.Parachute][], [FLRP.Parachute.Theorems][]) —
not imported.  The one hypothesis is minimal-normal descent, as an antecedent of the
enforced property.

**Representability status**.  Unknown, and *interesting*: whether a parachute with
two big canopies is group representable is exactly what statement (C) of the note
asserts for every family, and a family whose classes have empty intersection would
settle the FLRP negatively (`strategy-meta-theorem`{.AgdaFunction} of
[FLRP.Parachute.Theorems][]).  The catalog therefore never assumes it.

```agda
module Parachutes {m : ℕ}
  (𝑳s      : Fin (2 + m) → Lattice)
  (𝒕       : ∀ i → TopOf (𝑳s i))
  (top?    : ∀ i (x : 𝕌[ proj₁ (𝑳s i) ])
           → Dec (Setoid._≈_ 𝔻[ proj₁ (𝑳s i) ] x (proj₁ (𝒕 i))))
  (𝒃       : ∀ i → BottomOf (𝑳s i))
  (nondeg  : ∀ i → ¬ (Setoid._≈_ 𝔻[ proj₁ (𝑳s i) ] (proj₁ (𝒃 i)) (proj₁ (𝒕 i))))
  where

  open ParachuteTheorems {0ℓ} 𝑳s 𝒕 top? 𝒃 nondeg

  -- The two big canopies, as Lemma 3.7 requires.
  module Enforcement
    (p q    : Fin (2 + m))
    (p≢q    : ¬ (p ≡ q))
    (big-p  : BigCanopyᴸ p)
    (big-q  : BigCanopyᴸ q)
    where
```

Inside a core-free representation of the parachute, the structural half of Lemma 3.7
is available: this is the instance `Structure37`{.AgdaModule} of
[FLRP.Parachute.Theorems][] builds, re-instantiated here without the enforced-property
parameters that module carries.

```agda
    module Rep
      (𝒢     : Group 0ℓ 0ℓ)
      (H     : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ)
      (H-sg  : IsSubgroup 𝒢 H)
      (H-cf  : CoreFree 𝒢 H H-sg)
      (iso   : IntervalIso 𝒢 H H-sg ⊕ᵖ-Lattice)
      where

      open GroupParachute 𝒢 H H-sg
      open Over 𝒢 H H-sg iso
      open MinimalNormal 𝒢 0ℓ
      open Conjugate 𝒢  using  ( fullSubgroupIsnormal )

      -- Lemma 3.7 for this representation.
      module S = Structure config H-cf p≢q (bigCanopy p big-p) (bigCanopy q big-q)
                   IsAll? (K p)
                   (K-proper p (proj₁ (companion p)) (proj₂ (companion p))) (K-⊄H p)

      -- The minimality datum of RP-1's `Minimal` module, from a minimal normal
      -- subgroup in the sense of [Classical.Structures.Group.MinimalNormal][].
      private
        minimality : {M : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ} → IsMinimalNormal M
          → {N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ} → IsSubgroup 𝒢 N → Conjugate.IsNormal 𝒢 N
          → N ⊆ M → Nontrivial N → M ⊆ N
        minimality M-min N-sg N-nrm =
          M-min .minimal _ (record { isSubgroup = N-sg ; isNormal = N-nrm })
```

**Entry 3** first, since the other two follow from it.  Lemma 3.7 (i): the
centralizer of a nontrivial normal subgroup is trivial.  Descent supplies a minimal
normal subgroup inside it, and `centralizer-of-normal`{.AgdaFunction} of
[FLRP.Parachute][] does the rest — centralizers are antitone, so the centralizer of
the larger subgroup is inside that of the minimal one, which is trivial.

```agda
      centralizers : MinimalNormalDescent 𝒢 → 𝒢₄ 𝒢
      centralizers descent N N-nsg N-nontriv =
        S.centralizer-of-normal M N
          (M-min .normalSubgroup .isSubgroup) (M-min .normalSubgroup .isNormal)
          (M-min .nontrivial) (minimality M-min) M⊆N
        where
        descended  = descent N N-nsg N-nontriv
        M          = proj₁ descended
        M-min      = proj₁ (proj₂ descended)
        M⊆N        = proj₂ (proj₂ descended)
```

**Entry 2**.  The note's Remark: an abelian normal subgroup lies inside its own
centralizer, so a nontrivial one would be trivial.

```agda
      nonabelian : MinimalNormalDescent 𝒢 → 𝒢₃ 𝒢
      nonabelian descent N N-nsg N-nontriv ab =
        N-nontriv  (abelian-centralizer-trivial ab
                   (centralizers descent N N-nsg N-nontriv))
```

**Entry 1**.  Lemma 3.7 (ii).  Descent applied to the whole group supplies a minimal
normal subgroup `M`; RP-1's `normals-meet`{.AgdaFunction} says no nontrivial normal
subgroup meets `M` trivially; and `minimal-meets→least`{.AgdaFunction} turns that
pairwise statement into the monolith property.

The group is nontrivial, as descent's hypothesis requires: were every element the
identity, the `p`-th atom subgroup would collapse into `H`, which the parachute
forbids.

```agda
      monolith : MinimalNormalDescent 𝒢 → 𝒢₂ 𝒢
      monolith descent = M , record { isMinimalNormal = M-min ; least = M-least }
        where
        open Setoid 𝔻[ proj₁ 𝒢 ]  using  ()  renaming ( sym to ≈symᵍ )

        Full : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ
        Full = proj₁ (fullSubgroup 𝒢 0ℓ)

        Full-nsg : IsNormalSubgroup Full
        Full-nsg = record  { isSubgroup  = proj₂ (fullSubgroup 𝒢 0ℓ)
                           ; isNormal    = fullSubgroupIsnormal 0ℓ }

        Full-nontriv : Nontrivial Full
        Full-nontriv triv = K-⊄H p
          (λ _ → IsSubgroup.respects H-sg (≈symᵍ (triv (lift _)))
                                          (IsSubgroup.ε-closed H-sg))

        descended  = descent Full Full-nsg Full-nontriv
        M          = proj₁ descended
        M-min      = proj₁ (proj₂ descended)

        -- No nontrivial normal subgroup meets `M` trivially (RP-1) ...
        meets : (N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsNormalSubgroup N → Nontrivial N
              → ¬ MeetTrivially M N
        meets N N-nsg N-nontriv mt = N-nontriv
          (S.Minimal.normals-meet M
             (M-min .normalSubgroup .isSubgroup) (M-min .normalSubgroup .isNormal)
             (M-min .nontrivial) (minimality M-min)
             N (N-nsg .isSubgroup) (N-nsg .isNormal) (λ w∈M w∈N → mt (w∈M , w∈N)))

        -- ... so `M` is below every one of them.
        M-least : (N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsNormalSubgroup N → Nontrivial N → M ⊆ N
        M-least = minimal-meets→least M M-min meets
```

The three entries, as cf-IE statements.  Each is core-free interval enforceability of
the corresponding class *modulo minimal-normal descent*, which is the honest reading
of "cf-IE via a parachute" in a library without well-founded descent on group order.

```agda
    -- Entry 1: 𝒢₂ is cf-IE via the parachute (modulo descent).
    entry-𝒢₂ : cfIE (λ 𝒢 → MinimalNormalDescent 𝒢 → 𝒢₂ 𝒢) ⊕ᵖ-Lattice
    entry-𝒢₂ 𝒢 H H-sg H-cf iso = Rep.monolith 𝒢 H H-sg H-cf iso

    -- Entry 2: 𝒢₃ is cf-IE via the parachute (modulo descent).
    entry-𝒢₃ : cfIE (λ 𝒢 → MinimalNormalDescent 𝒢 → 𝒢₃ 𝒢) ⊕ᵖ-Lattice
    entry-𝒢₃ 𝒢 H H-sg H-cf iso = Rep.nonabelian 𝒢 H H-sg H-cf iso

    -- Entry 3: 𝒢₄ is cf-IE via the parachute (modulo descent).
    entry-𝒢₄ : cfIE (λ 𝒢 → MinimalNormalDescent 𝒢 → 𝒢₄ 𝒢) ⊕ᵖ-Lattice
    entry-𝒢₄ 𝒢 H H-sg H-cf iso = Rep.centralizers 𝒢 H H-sg H-cf iso
```

#### Composition: the catalog composes, its witnesses do not

Corollary 3.8 is the catalog's conjunction operation: entries enforced by *different*
lattices combine into one entry enforced by the parachute of those lattices.  It is
`conjunction-cfIE`{.AgdaFunction} of [FLRP.Parachute.Theorems][], re-exported here as
catalog vocabulary together with the two theorems that make composition worth doing.

What does **not** compose is the vacuity datum.  Nothing carries
`GroupRepresentable`{.AgdaRecord} of the canopies to
`GroupRepresentable`{.AgdaRecord} of the parachute, and supplying it for every family
is precisely statement (C) — the FLRP itself.  The asymmetry is the strategy: compose
entries until the conjunction is *unsatisfiable*, at which point the parachute is not
representable and, with Pálfy–Pudlák, the FLRP has a negative answer.

Entries enter composition at the cf-IE level, so an IE entry (Entries 4 and 5) is
weakened first — `IE→cfIE`{.AgdaFunction} of [FLRP.Enforceable][], family-wise as
`IE-family→cfIE-family`{.AgdaFunction} above.  Note also what composition does *not*
require: no entry is restated as a hypothesis once it has been derived, so Entries 1–3
enter as the theorems proved above and not as assumptions.

```agda
    module Compose {ℓP : Level}
      (Ps       : Fin (2 + m) → GroupProperty ℓP)
      (Ps-cfIE  : ∀ i → cfIE (Ps i) (𝑳s i))
      where

      private module PT = ParachuteTheorems {ℓP} 𝑳s 𝒕 top? 𝒃 nondeg

      open PT.Enforced p q p≢q big-p big-q Ps Ps-cfIE public
        using  ( conjunction-cfIE
               ; empty-intersection→not-representable
               ; strategy-meta-theorem )
```

#### Entry 4: `𝒢₀`, the nonsolvable groups

**Property**.  `𝒢₀ = ¬ Solvable`.

**Enforcing lattice**.  `M₇`.  Any `Mₙ` with `n − 1` not a prime power will do; `M₇`
is the choice that makes the entry *non-vacuous*, since `M₇` is group representable
(Feit) while `M₁₆`, say, is not known to be.

**Sources**.

+  Exclusion: Pálfy–Pudlák [1980] — if `Mₙ` is an interval in the subgroup lattice of
   a finite solvable group then `n = q + 1` for a prime power `q`.  Since `6` is not a
   prime power, `M₇` is no interval in a solvable group.  The note cites Pálfy [1995]
   for "an example of a lattice that cannot occur as an upper interval in the subgroup
   lattice of a finite solvable group"; `M₇` is such an example.  `verify`: the
   Pálfy–Pudlák statement is verified against two independent secondary sources but
   not against the 1980 paper itself (see the survey note, § 3).
+  Representability: Feit [1983] — `M₇ ≅ [H , A₃₁]` with `|H| = 31 · 5`; also
   Köhler [1983].  Verified against DeMeo's thesis (arXiv:1204.4305, Ch. 8, Question 8)
   and against Pálfy's classification as quoted by Basile [2001, Prop. 5.2.1].
+  H-closure of the solvable groups is elementary (a quotient of a solvable group is
   solvable) and is asserted by the note.

**Level**.  cf-IE from the exclusion, upgraded to **IE** by Lemma 3.1 — the one piece
of reasoning in this entry that is not an import, and it is formalized above
(`exclusion→IE`{.AgdaFunction}).  Solvability itself is *not* IE, by fattening.

**Imported as hypotheses**: the exclusion, H-closure, and Feit's representation.
**Formalized here**: the upgrade and the non-vacuity conclusion.

```agda
module Entry-𝒢₀ {ℓS : Level} (Solvable : GroupProperty ℓS) where

  -- 𝒢₀: the nonsolvable groups.
  𝒢₀ : GroupProperty ℓS
  𝒢₀ 𝒢 = ¬ Solvable 𝒢

  -- Pálfy–Pudlák [1980] / Pálfy [1995]: M₇ is no interval above a core-free
  -- subgroup of a finite solvable group.
  SolvableExclusion : Type (lsuc 0ℓ ⊔ ℓS)
  SolvableExclusion = CoreFreeExclusion Solvable M[ 7 ]

  -- Elementary: homomorphic images of solvable groups are solvable.
  SolvableHClosed : Type (lsuc 0ℓ ⊔ ℓS)
  SolvableHClosed = HClosed Solvable

  -- Feit [1983], Köhler [1983]: M₇ ≅ [H , A₃₁] with |H| = 155.
  FeitM₇ : Type (lsuc 0ℓ)
  FeitM₇ = GroupRepresentable M[ 7 ]

  -- The entry, at both levels.
  nonsolvable-cfIE : SolvableExclusion → cfIE 𝒢₀ M[ 7 ]
  nonsolvable-cfIE = exclusion→cfIE Solvable M[ 7 ]

  nonsolvable-IE : CoreFreeReduction → SolvableHClosed → SolvableExclusion → IE 𝒢₀ M[ 7 ]
  nonsolvable-IE cfr hcl = exclusion→IE Solvable M[ 7 ] cfr hcl

  -- Non-vacuity: Feit's representation makes the entry bite.
  nonsolvable-nonvacuous : CoreFreeReduction → FeitM₇ → SolvableExclusion
    →  Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ] 𝒢₀ 𝒢
  nonsolvable-nonvacuous cfr feit exc =
    cfIE-nonvacuous 𝒢₀ M[ 7 ] (nonsolvable-cfIE exc) feit cfr
```

#### Entry 5: `𝒢₁`, neither alternating nor symmetric

**Property**.  `𝒢₁ = ¬ AltOrSym`, the note's
`{G : (∀ n < ω) (G ≠ Aₙ ∧ G ≠ Sₙ)}`.

**Enforcing lattice**.  `M₆`.

**Sources**.

+  Exclusion: Basile [2001], *Second maximal subgroups of the finite alternating and
   symmetric groups* (ANU thesis; arXiv:0810.3721), **Theorem D**: "A second maximal
   subgroup of a finite alternating or symmetric group of degree at least 5 is never
   contained in more than 3 maximal subgroups, unless it is one of the three examples
   of Feit and Pálfy."  Those three examples are `M₅` in `A₁₃`, `M₇` in `A₃₁`, and
   `M₁₁` in `A₃₁` (Basile, Prop. 5.2.1, quoting Pálfy [1988, Table II]), so a
   second maximal subgroup with `n` maximal overgroups has `n ∈ {1, 2, 3, 5, 7, 11}`.
   A second maximal subgroup is exactly the bottom of a height-two interval, so `M₆`
   is no interval in an alternating or symmetric group of degree at least 5.  DeMeo's
   thesis states this consequence as "`M₆ ≅ [H , G]` only if `G ∉ Gi`"
   (arXiv:1204.4305, § 5.2).  The note attributes the same *class* of results to
   Aschbacher–Shareshian [2009] as well; that paper could not be obtained, so it is
   named here for the record and this entry rests on Basile alone (`verify`).
+  Representability: `M₆ = M_{5+1}` is the subspace lattice of a two-dimensional
   vector space over `F₅`, an interval in the group of translations and scalar
   multiplications of that space.  `verify`: verified against a secondary source
   (Freese's review of Schmidt's *Subgroup Lattices of Groups*), not formalized.
+  H-closure of the alternating and symmetric groups is asserted by the note.

**Scope note, recorded rather than papered over**.  Basile's Theorem D is stated for
degree at least 5.  Degrees below 5 are covered by inspection — the alternating and
symmetric groups of degree at most 4 have order at most 24 and no interval isomorphic
to `M₆` — but that inspection is *not* machine-checked here, so the imported
hypothesis below is stated for the full class and the gap is flagged in the survey
note (§ 3).

**Level**.  cf-IE from the exclusion, upgraded to **IE** by Lemma 3.1 exactly as in
Entry 4.  Being alternating or symmetric is not IE, by fattening.

```agda
module Entry-𝒢₁ {ℓA : Level} (AltOrSym : GroupProperty ℓA) where

  -- 𝒢₁: the groups that are neither alternating nor symmetric.
  𝒢₁ : GroupProperty ℓA
  𝒢₁ 𝒢 = ¬ AltOrSym 𝒢

  -- Basile [2001, Thm D and Prop. 5.2.1]: M₆ is no interval above a core-free
  -- subgroup of an alternating or symmetric group.
  AltSymExclusion : Type (lsuc 0ℓ ⊔ ℓA)
  AltSymExclusion = CoreFreeExclusion AltOrSym M[ 6 ]

  -- The alternating and symmetric groups are closed under homomorphic images.
  AltSymHClosed : Type (lsuc 0ℓ ⊔ ℓA)
  AltSymHClosed = HClosed AltOrSym

  -- M₆ is the subspace lattice of a plane over F₅, hence group representable.
  M₆-representable : Type (lsuc 0ℓ)
  M₆-representable = GroupRepresentable M[ 6 ]

  -- The entry, at both levels.
  nongiant-cfIE : AltSymExclusion → cfIE 𝒢₁ M[ 6 ]
  nongiant-cfIE = exclusion→cfIE AltOrSym M[ 6 ]

  nongiant-IE : CoreFreeReduction → AltSymHClosed → AltSymExclusion → IE 𝒢₁ M[ 6 ]
  nongiant-IE cfr hcl = exclusion→IE AltOrSym M[ 6 ] cfr hcl

  -- Non-vacuity.
  nongiant-nonvacuous : CoreFreeReduction → M₆-representable → AltSymExclusion
    →  Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ] 𝒢₁ 𝒢
  nongiant-nonvacuous cfr rep exc =
    cfIE-nonvacuous 𝒢₁ M[ 6 ] (nongiant-cfIE exc) rep cfr
```

#### Entry 6: the min-IE entry — Köhler, Pálfy–Pudlák, and Feit's `M₇`

**Property**.  `𝒢₂` (subdirectly irreducible) and `𝒢₃` (no nontrivial abelian normal
subgroup) — the same two classes Entries 1 and 2 obtain from parachutes, here obtained
from a *minimality* hypothesis instead.

**Enforcing lattice**.  `Mₙ` for `n − 1` not a prime power; `M₇` is the instance the
program cares about, and the library's motivating min-IE example.

**Source**.  Freese's review of Schmidt, *Subgroup Lattices of Groups*, records the
two halves separately: "A minimal group whose subgroup lattice has `Mₙ` as an interval
has a unique minimal normal subgroup, Köhler [1983], and has no Abelian normal
subgroup, Pálfy and Pudlák [1980], assuming `n − 1` is not a prime power."  With
Feit [1983] and Köhler [1983] supplying `M₇ ≅ [H , A₃₁]`, the entry is non-vacuous;
Pálfy [1988] analyses those examples further.  `verify`: the two attributions come
from that review, not from the 1983 and 1980 papers themselves.

**Level**.  **min-IE** — over the repaired `MinimallyIE`{.AgdaFunction} above, not
`minIE`{.AgdaFunction}.  Neither half is IE (fattening again), and whether either is
cf-IE via `Mₙ` is *not* what these sources say: minimality and core-freeness are
different hypotheses, related only through the unformalized fact that a
minimal-order representation is core-free (see the survey note, § 4).

**Imported as hypotheses**, both halves.  **Formalized here**: their conjunction, and
the observation that min-IE conjoins with no parachute.

```agda
module Entry-Minimal where

  -- Köhler [1983]: a minimal representation of Mₙ has a unique minimal normal
  -- subgroup (n − 1 not a prime power).
  Kohler : ℕ → Type (lsuc 0ℓ)
  Kohler n = MinimallyIE 𝒢₂ M[ n ]

  -- Pálfy–Pudlák [1980]: it has no nontrivial abelian normal subgroup.
  PalfyPudlakMinimal : ℕ → Type (lsuc 0ℓ)
  PalfyPudlakMinimal n = MinimallyIE 𝒢₃ M[ n ]

  -- The two halves, conjoined.
  minimal-structure : (n : ℕ) → Kohler n → PalfyPudlakMinimal n
    →  MinimallyIE (λ 𝒢 → 𝒢₂ 𝒢 × 𝒢₃ 𝒢) M[ n ]
  minimal-structure n = MinimallyIE-∧ 𝒢₂ 𝒢₃ M[ n ]
```

#### Entry 7: `L7`, the distinguished open instance

**Property**.  `𝒢₄ ∧ 𝒢₃ ∧ 𝒢₂ ∧ 𝒢₀` — every nontrivial normal subgroup has trivial
centralizer, none is abelian, the group is subdirectly irreducible, and it is
nonsolvable.

**Enforcing lattice**.  `L7`, the seven-element lattice of
[Examples.Classical.Lattices.L7][] — the unique smallest lattice with no known
representation.

**Source**.  DeMeo, *Congruence lattices of finite algebras* (thesis, 2012;
arXiv:1204.4305), **Theorem 6.3.1**: "Suppose `H < G` are finite groups with
`core_G(H) = 1` and suppose `L7 ≅ [H , G]`.  Then (i) `G` is a primitive permutation
group; (ii) if `N ⊴ G` then `C_G(N) = 1`; (iii) `G` contains no non-trivial abelian
normal subgroup; (iv) `G` is not solvable; (v) `G` is subdirectly irreducible;
(vi) with the possible exception of at most one maximal subgroup, all proper subgroups
in the interval `[H , G]` are core-free."  Clauses (ii)–(v) are imported below;
(i) needs a primitivity predicate and (vi) a maximality predicate, neither of which
the catalog has — recorded in the survey note rather than approximated.

**Level**.  cf-IE, as stated (the hypothesis is core-freeness of `H`).

**Representability status**.  **Unknown** — and this is the entry that shows why the
discipline matters.  If `L7` is not group representable then this entry, and every
other statement about `L7`, is vacuous (`not-representable→IE`{.AgdaFunction}) — and
the FLRP has a negative answer, since a minimal algebra representing `L7` is a
transitive G-set.  So the entry's content is *conditional on the open problem*, which
is exactly its interest: it says what the group would have to look like.

```agda
module Entry-L7 {ℓS : Level} (Solvable : GroupProperty ℓS) where

  -- DeMeo [thesis, Thm 6.3.1], clauses (ii)–(v): the structure a core-free
  -- representation of L7 forces.
  L7-Structure : GroupProperty (lsuc 0ℓ ⊔ ℓS)
  L7-Structure 𝒢 = 𝒢₄ 𝒢 × 𝒢₃ 𝒢 × 𝒢₂ 𝒢 × ¬ Solvable 𝒢

  L7-Enforcement : Type (lsuc 0ℓ ⊔ ℓS)
  L7-Enforcement = cfIE L7-Structure L7-lattice

  -- What the entry says, if L7 is group representable at all.
  L7-consequence : L7-Enforcement → GroupRepresentable L7-lattice → CoreFreeReduction
    →  Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ] L7-Structure 𝒢
  L7-consequence enf rep cfr = cfIE-nonvacuous L7-Structure L7-lattice enf rep cfr
```

#### Entry 8: Boolean lattices do not enforce `𝒢₁` — a negative entry

**Property**.  `𝒢₁` — and the entry's content is that the rank-three Boolean lattice
does **not** enforce it.

**Lattice**.  `𝟚³`, the three-fold product of the two-element chain.

**Source**.  Lucchini, Moscatiello, Palcoux, and Spiga, *Boolean lattices in finite
alternating and symmetric groups* (arXiv:1911.04516), **Theorem 1.1** and §§ 3–4:
the subgroups `H` of `G = Alt(Ω)` or `Sym(Ω)` with `[H , G]` Boolean of rank at least
3 are classified into eleven families, and cases (1) and (2) — stabilizers of chains
of non-trivial regular partitions — "do occur for arbitrary values of `ℓ`".  So some
alternating (or symmetric) group carries a Boolean upper interval of rank 3.

**Level**.  A refutation, not an enforcement: with a witness inside the class,
`witness→¬IE`{.AgdaFunction} refutes IE of `𝒢₁` via `𝟚³` outright.  Negative entries
are what keep RP-3 from searching where the answer is known: no Boolean lattice of
rank at least 3 can serve as an enforcing lattice for `𝒢₁`.

**Imported as a hypothesis**: the realization.  **Formalized here**: the refutation.

```agda
module Entry-Boolean {ℓA : Level} (AltOrSym : GroupProperty ℓA) where

  -- The rank-three Boolean lattice.
  𝟚³ : Lattice
  𝟚³ = chain₂-lattice ×ˡ (chain₂-lattice ×ˡ chain₂-lattice)

  -- Lucchini–Moscatiello–Palcoux–Spiga [2019], Theorem 1.1 (1)–(2) with §§ 3–4:
  -- an alternating or symmetric group with a Boolean upper interval of rank 3.
  BooleanRealization : Type (lsuc 0ℓ ⊔ ℓA)
  BooleanRealization =
    Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ] Σ[ H ∈ Pred 𝕌[ proj₁ 𝒢 ] 0ℓ ] Σ[ H-sg ∈ IsSubgroup 𝒢 H ]
      ( AltOrSym 𝒢 × IntervalIso 𝒢 H H-sg 𝟚³ )

  -- Hence the rank-three Boolean lattice enforces neither `𝒢₁` ...
  boolean-¬IE-𝒢₁ : BooleanRealization → ¬ IE (λ 𝒢 → ¬ AltOrSym 𝒢) 𝟚³
  boolean-¬IE-𝒢₁ (𝒢 , H , H-sg , alt , iso) =
    witness→¬IE (λ 𝒢' → ¬ AltOrSym 𝒢') 𝟚³ 𝒢 H H-sg iso (λ ¬alt → ¬alt alt)

  -- ... nor, a fortiori, any property that fails of that witness.
  boolean-¬IE : {ℓP : Level} (P : GroupProperty ℓP) → BooleanRealization
    →  (∀ 𝒢 → AltOrSym 𝒢 → ¬ P 𝒢) → ¬ IE P 𝟚³
  boolean-¬IE P (𝒢 , H , H-sg , alt , iso) fails =
    witness→¬IE P 𝟚³ 𝒢 H H-sg iso (fails 𝒢 alt)
```

#### Entry 9: the two-element chain enforces exactly on the core-free-maximal class

**Property**.  Schematic, in both directions.  Forward: *every* property that is
cf-IE via a two-element chain holds of every group with a core-free maximal
subgroup.  Backward: the tautological class `HasCoreFreeMaximal`{.AgdaFunction} is
itself cf-IE via every two-element chain, so it is the *least* class such a chain
core-free enforces.

**Enforcing lattice**.  Any lattice with exactly two elements
(`IsChain₂`{.AgdaRecord} below); `chain₂-lattice`{.AgdaFunction} is the concrete
instance.

**Source**.  Elementary, and **derived** in full; nothing is imported.  The entry
exists because the RP-4 reduction of the pair question to statement (C) carries a
three-element side condition on each canopy, so a contradictory pair living on
two-element chains would evade it; this entry is the classical piece that closes
that corner (the design note `docs/notes/flrp-rp4-wreath.md` § 5 records the gap,
and `FLRP.Hunt`{.AgdaModule} assembles the closure).  Classically the content is
folklore: `[H , G]` is a two-element chain over a core-free `H` precisely when `H`
is a core-free maximal subgroup, i.e. when `G` acts faithfully and primitively on
the cosets of `H`.

**Level**.  cf-IE.  The classes so enforced are also wreath-rich, by Lemma 3.3
instantiated at the chain; that corollary lives in [FLRP.Hunt][] beside the corner
it closes, keeping this module independent of the wreath machinery.

**Constructive status**.  Both directions are proved, but the maximality datum they
exchange (`IsMaximalSubgroup`{.AgdaRecord} of
[Classical.Structures.Group.MaximalSubgroup][]) is oracle-strength, for the reason
recorded in that module: classifying an arbitrary intermediate subgroup decides an
arbitrary proposition.  This is the interval-side face of the WP-1 no-go theorem of
[FLRP.Problem][], and it is why neither direction produces concrete
`𝒢₀`{.AgdaFunction}-memberships in safe Agda: like every entry, this one is a
statement *about* representations, with the witnesses supplied classically.

A lattice **is a two-element chain** when it has a chosen bottom and top, the two
are distinct, and every element is one or the other.  The last field is the
decision the interval construction consumes; for a concrete lattice on a finite
carrier it is a pattern match.

```agda
record IsChain₂ (𝑳 : Lattice) : Type 0ℓ where
  field
    bot       : BottomOf 𝑳
    top       : TopOf 𝑳
    distinct  : ¬ (Setoid._≈_ 𝔻[ proj₁ 𝑳 ] (proj₁ bot) (proj₁ top))
    place     : ∀ x →  Setoid._≈_ 𝔻[ proj₁ 𝑳 ] x (proj₁ bot)
                    ⊎  Setoid._≈_ 𝔻[ proj₁ 𝑳 ] x (proj₁ top)

-- The concrete two-element chain is one.
chain₂-IsChain₂ : IsChain₂ chain₂-lattice
chain₂-IsChain₂ = record
  { bot       = chain₂-bot
  ; top       = chain₂-top
  ; distinct  = λ ()
  ; place     = λ { 0F → inj₁ refl ; 1F → inj₂ refl }
  }
```

The tautological class: the groups with a core-free maximal subgroup.

```agda
HasCoreFreeMaximal : GroupProperty (lsuc 0ℓ)
HasCoreFreeMaximal 𝒢@(𝑮 , _) =
  Σ[ H ∈ Pred 𝕌[ 𝑮 ] 0ℓ ] Σ[ H-sg ∈ IsSubgroup 𝒢 H ]
    ( CoreFree 𝒢 H H-sg × MaximalSubgroup.IsMaximalSubgroup 𝒢 0ℓ H )
```

The correspondence itself: over a fixed subgroup, maximality data and an interval
isomorphism with a two-element chain are interconvertible.  The forward direction
sends an interval element to the bottom or the top according to its
classification; the backward direction classifies an intermediate subgroup by
where the isomorphism sends it, using that an order isomorphism matches up the two
bottoms and the two tops.

```agda
module Chain₂Interval
  (ℒ@(𝑳 , _) : Lattice) (c₂ : IsChain₂ ℒ)
  (𝒢@(𝑮 , _) : Group 0ℓ 0ℓ) (H : Pred 𝕌[ 𝑮 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  where

  open IsChain₂ c₂
  open Setoid 𝔻[ 𝑳 ]   using ()
                        renaming ( _≈_ to _≈ᴸ_ ; sym to ≈ᴸ-sym ; trans to ≈ᴸ-trans )
  open Lattice-Order ℒ  using ( _≤_ ; ≤-antisym ; ≤-reflexive ; ≤-trans )
                        renaming ( ≤-refl to ≤ᴸ-refl )
  open UpperInterval 𝒢 H H-sg
    using  ( Interval≈ ; mk ; set ; above ; element-isSubgroup ; _≈ᵢ_ ; _≤ᵢ_ )
  open MaximalSubgroup 𝒢 0ℓ  using  ( IsMaximalSubgroup )
  open IsMaximalSubgroup

  private
    b t : 𝕌[ 𝑳 ]
    b = proj₁ bot
    t = proj₁ top

    -- The two endpoints of the interval, as interval elements.
    H↑ᵉ G↑ᵉ : Interval≈
    H↑ᵉ = mk H H-sg (λ h → h)
    G↑ᵉ = mk (fullSubgroup 𝒢 0ℓ .proj₁) (fullSubgroup 𝒢 0ℓ .proj₂) (λ _ → lift tt)
```

**Maximality yields the isomorphism.**  Each proof obligation is dispatched by a
helper taking the relevant classification as an argument, in the library's
`with`-discipline.

```agda
  module _ (H-max : IsMaximalSubgroup H) where

    private
      -- The classification of an interval element.
      Class : Interval≈ → Type 0ℓ
      Class K = (set K ⊆ H) ⊎ (∀ x → x ∈ set K)

      class : (K : Interval≈) → Class K
      class K = classify H-max (set K) (element-isSubgroup K) (above K)

      -- Where a classified element goes: bottom if it is H, top if it is G.
      -- (The subject is explicit throughout this block: the classification
      -- type mentions only the element's predicate, so an implicit subject
      -- would leave its proof components as unsolved metavariables.)
      toAux : (K : Interval≈) → Class K → 𝕌[ 𝑳 ]
      toAux _ (inj₁ _) = b
      toAux _ (inj₂ _) = t

      to′ : Interval≈ → 𝕌[ 𝑳 ]
      to′ K = toAux K (class K)

      -- Where a placed lattice element comes from.
      fromAux : (u : 𝕌[ 𝑳 ]) → (u ≈ᴸ b) ⊎ (u ≈ᴸ t) → Interval≈
      fromAux _ (inj₁ _) = H↑ᵉ
      fromAux _ (inj₂ _) = G↑ᵉ

      from′ : 𝕌[ 𝑳 ] → Interval≈
      from′ u = fromAux u (place u)

      -- Monotonicity, by cases on the two classifications; the crossed case
      -- (everything below a subgroup of H) contradicts properness.
      to-mono′ : (K K' : Interval≈) (d : Class K) (d' : Class K')
        → K ≤ᵢ K' → toAux K d ≤ toAux K' d'
      to-mono′ _ _ (inj₁ _)    (inj₁ _)     _   = ≤ᴸ-refl
      to-mono′ _ _ (inj₁ _)    (inj₂ _)     _   = proj₂ bot t
      to-mono′ _ _ (inj₂ all)  (inj₁ K'⊆H)  le  =
        ⊥-elim (proper H-max (λ x → K'⊆H (le (all x))))
      to-mono′ _ _ (inj₂ _)    (inj₂ _)     _   = ≤ᴸ-refl

      -- Monotonicity of from, by cases on the two placements; the crossed case
      -- (top below bottom) contradicts distinctness.
      from-mono′ : (u v : 𝕌[ 𝑳 ])
        (c : (u ≈ᴸ b) ⊎ (u ≈ᴸ t)) (c' : (v ≈ᴸ b) ⊎ (v ≈ᴸ t))
        → u ≤ v → fromAux u c ≤ᵢ fromAux v c'
      from-mono′ _ _ (inj₁ _)    (inj₁ _)     _   = λ z → z
      from-mono′ _ _ (inj₁ _)    (inj₂ _)     _   = λ _ → lift tt
      from-mono′ u v (inj₂ u≈t)  (inj₁ v≈b)   le  =
        ⊥-elim (distinct (≤-antisym (proj₂ bot t) t≤b))
        where
        t≤b : t ≤ b
        t≤b = ≤-trans  (≤-reflexive (≈ᴸ-sym u≈t))
                       (≤-trans le (≤-reflexive v≈b))
      from-mono′ _ _ (inj₂ _)    (inj₂ _)     _   = λ z → z

      -- Round trip on the lattice: the endpoints classify to themselves.
      to∘from-bot : (u : 𝕌[ 𝑳 ]) → u ≈ᴸ b
        → (d : Class H↑ᵉ) → toAux H↑ᵉ d ≈ᴸ u
      to∘from-bot u u≈b (inj₁ _)     = ≈ᴸ-sym u≈b
      to∘from-bot u u≈b (inj₂ allH)  = ⊥-elim (proper H-max allH)

      to∘from-top : (u : 𝕌[ 𝑳 ]) → u ≈ᴸ t
        → (d : Class G↑ᵉ) → toAux G↑ᵉ d ≈ᴸ u
      to∘from-top u u≈t (inj₁ full⊆H)  =
        ⊥-elim (proper H-max (λ x → full⊆H (lift tt)))
      to∘from-top u u≈t (inj₂ _)       = ≈ᴸ-sym u≈t

      to∘from′ : ∀ u → to′ (from′ u) ≈ᴸ u
      to∘from′ u with place u
      ... | inj₁ u≈b = to∘from-bot u u≈b (class H↑ᵉ)
      ... | inj₂ u≈t = to∘from-top u u≈t (class G↑ᵉ)

      -- Round trip on the interval: a classified element is its endpoint.
      from∘to-bot : (K : Interval≈) → set K ⊆ H
        → (c : (b ≈ᴸ b) ⊎ (b ≈ᴸ t)) → fromAux b c ≈ᵢ K
      from∘to-bot K K⊆H (inj₁ _)    = above K , K⊆H
      from∘to-bot K K⊆H (inj₂ b≈t)  = ⊥-elim (distinct b≈t)

      from∘to-top : (K : Interval≈) → (∀ x → x ∈ set K)
        → (c : (t ≈ᴸ b) ⊎ (t ≈ᴸ t)) → fromAux t c ≈ᵢ K
      from∘to-top K allK (inj₁ t≈b)  = ⊥-elim (distinct (≈ᴸ-sym t≈b))
      from∘to-top K allK (inj₂ _)    = (λ {x} _ → allK x) , (λ _ → lift tt)

      from∘to′ : ∀ K → from′ (to′ K) ≈ᵢ K
      from∘to′ K with class K
      ... | inj₁ K⊆H   = from∘to-bot K K⊆H (place b)
      ... | inj₂ allK  = from∘to-top K allK (place t)

    -- A core-free maximal subgroup carries the two-element chain.
    maximal→intervalIso : IntervalIso 𝒢 H H-sg ℒ
    maximal→intervalIso = record
      { to         = to′
      ; from       = from′
      ; to-mono    = λ {K} {K'} le → to-mono′ K K' (class K) (class K') le
      ; from-mono  = λ {u} {v} le → from-mono′ u v (place u) (place v) le
      ; to∘from    = to∘from′
      ; from∘to    = from∘to′
      }
```

**The isomorphism yields maximality.**  An order isomorphism matches the interval's
endpoints with the chain's (`to-H↑`{.AgdaFunction}, `to-G↑`{.AgdaFunction}), so an
intermediate subgroup is classified by where it lands, and properness follows from
distinctness of the two chain elements.

```agda
  module _ (iso : IntervalIso 𝒢 H H-sg ℒ) where

    private
      module I = OrderIso iso

      -- The isomorphism respects interval equality, by antisymmetry.
      to-cong : {K K' : Interval≈} → K ≈ᵢ K' → I.to K ≈ᴸ I.to K'
      to-cong (le , ge) = ≤-antisym (I.to-mono le) (I.to-mono ge)

      -- The interval's bottom lands on the chain's bottom ...
      to-H↑ : I.to H↑ᵉ ≈ᴸ b
      to-H↑ = ≤-antisym (below b) (proj₂ bot (I.to H↑ᵉ))
        where
        below : ∀ u → I.to H↑ᵉ ≤ u
        below u = ≤-trans  (I.to-mono {H↑ᵉ} {I.from u} (above (I.from u)))
                           (≤-reflexive (I.to∘from u))

      -- ... and the interval's top on the chain's top.
      to-G↑ : I.to G↑ᵉ ≈ᴸ t
      to-G↑ = ≤-antisym (proj₂ top (I.to G↑ᵉ)) (over t)
        where
        over : ∀ u → u ≤ I.to G↑ᵉ
        over u = ≤-trans  (≤-reflexive (≈ᴸ-sym (I.to∘from u)))
                          (I.to-mono {I.from u} {G↑ᵉ} (λ _ → lift tt))

    -- A subgroup carrying the two-element chain is maximal.
    intervalIso→maximal : IsMaximalSubgroup H
    intervalIso→maximal = record
      { isSubgroup  = H-sg
      ; proper      = prop
      ; classify    = decide
      }
      where
      prop : ¬ (∀ x → x ∈ H)
      prop allH = distinct
        (≈ᴸ-trans  (≈ᴸ-sym to-H↑)
        (≈ᴸ-trans  (to-cong ((λ _ → lift tt) , (λ {x} _ → allH x)))
                   to-G↑))

      decide : (K : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (K-sg : IsSubgroup 𝒢 K) → H ⊆ K
        → (K ⊆ H) ⊎ (∀ x → x ∈ K)
      decide K K-sg H⊆K = go (place (I.to k))
        where
        k : Interval≈
        k = mk K K-sg H⊆K

        go : (I.to k ≈ᴸ b) ⊎ (I.to k ≈ᴸ t) → (K ⊆ H) ⊎ (∀ x → x ∈ K)
        go (inj₁ e) = inj₁ λ x∈K →
          proj₁ (I.from∘to H↑ᵉ)
            (I.from-mono {I.to k} {I.to H↑ᵉ}
              (≤-reflexive (≈ᴸ-trans e (≈ᴸ-sym to-H↑)))
              (proj₂ (I.from∘to k) x∈K))
        go (inj₂ e) = inj₂ λ x →
          proj₁ (I.from∘to k)
            (I.from-mono {I.to G↑ᵉ} {I.to k}
              (≤-reflexive (≈ᴸ-trans to-G↑ (≈ᴸ-sym e)))
              (proj₂ (I.from∘to G↑ᵉ) (lift tt)))
```

The entry, in both directions.  Forward, the headline of the RP-4 design note's
open item: a property that is cf-IE via a two-element chain holds of every group
with a core-free maximal subgroup.

```agda
chain₂-enforces : {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice) → IsChain₂ 𝑳
  → cfIE P 𝑳
  → ∀ 𝒢 (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  → CoreFree 𝒢 H H-sg → MaximalSubgroup.IsMaximalSubgroup 𝒢 0ℓ H
  → P 𝒢
chain₂-enforces P 𝑳 c₂ enf 𝒢 H H-sg cf H-max =
  enf 𝒢 H H-sg cf (Chain₂Interval.maximal→intervalIso 𝑳 c₂ 𝒢 H H-sg H-max)
```

Backward, the tautology made formal: the core-free-maximal class is itself cf-IE
via every two-element chain, so it is exactly the least class such a chain
enforces.

```agda
chain₂-cfIE-coreFreeMaximal : (𝑳 : Lattice) → IsChain₂ 𝑳
  → cfIE HasCoreFreeMaximal 𝑳
chain₂-cfIE-coreFreeMaximal 𝑳 c₂ 𝒢 H H-sg cf iso =
  H , H-sg , cf , Chain₂Interval.intervalIso→maximal 𝑳 c₂ 𝒢 H H-sg iso
```

---

[^1]: The note's proof is by contradiction; the formalization keeps the
      contradiction where it belongs (in `cfIE→¬¬`{.AgdaFunction}) and isolates the
      classical step as the `PropertyStable`{.AgdaFunction} hypothesis, which
      `negation-Stable`{.AgdaFunction} discharges for every entry the catalog
      actually has.  See `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`,
      Lemma 3.1 (`lemma-wjd-2`).

[^2]: Reported in the survey note `docs/notes/flrp-rp2-catalog.md` § 4; retiring
      `minIE`{.AgdaFunction} in favour of `MinimallyIE`{.AgdaFunction} is a
      follow-up to WP-4, and FLRP modules are exempt from the deprecation cycle
      (roadmap § 1), so the replacement can be direct.
