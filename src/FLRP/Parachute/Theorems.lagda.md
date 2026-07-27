---
layout: default
file: "src/FLRP/Parachute/Theorems.lagda.md"
title: "FLRP.Parachute.Theorems module (The Agda Universal Algebra Library)"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### The parachute theorems and the strategy meta-theorem

This is the [FLRP.Parachute.Theorems][] module of the [Agda Universal Algebra Library][].

Everything is now in place to assemble § 3.3 of the note.[^1]  Fix `n ≥ 2` finite
lattices `L₁ , … , Lₙ`, at least two of which have more than two elements, and let
`𝒫 = 𝒫(L₁ , … , Lₙ)` be their parachute.  Then:

+  **Theorem 3.6, substantive direction**.  If `𝒫` is group representable, a single
   finite group `G` lies in *every* class core-free enforceable by a canopy, and
   realizes every canopy `Lᵢ` as an upper interval over a core-free subgroup
   (`parachute-representable`{.AgdaFunction}).
+  **Corollary 3.8**.  A finite conjunction of cf-IE properties is cf-IE — via the
   parachute of the enforcing lattices (`conjunction-cfIE`{.AgdaFunction}).  No
   representability hypothesis enters: the corollary is about enforcement, not about
   existence.
+  **Lemma 3.7**, through the `Structure37`{.AgdaModule} instance inside a core-free
   representation: `NH = G` for every nontrivial normal `N`, the centralizer of a
   minimal normal subgroup is trivial, that subgroup is nonabelian, and no
   nontrivial normal subgroup meets it trivially — `G` is subdirectly irreducible.
+  **The strategy meta-theorem**.  If the enforced classes have *empty intersection*
   then `𝒫` is not group representable
   (`empty-intersection→not-representable`{.AgdaFunction}); with Pálfy–Pudlák
   (Entry 3 of [FLRP.Assumptions][]) the FLRP then has a negative answer
   (`strategy-meta-theorem`{.AgdaFunction}).

The engine is the core-freeness propagation of [FLRP.Parachute][]: over a core-free
`H`, every proper member of `[H , G]` is core-free — in particular each atom
subgroup `Kᵢ`, above which `[Kᵢ , G] ≅ Lᵢ` by the canopy isomorphism of
[FLRP.Parachute.Representation][].  So each `Lᵢ` gets to speak, over a *core-free*
subgroup, about the same group.

**What is assumed, and where**.  Three hypotheses are threaded as ordinary
arguments, never postulated.

+  `CoreFreeReduction`{.AgdaRecord} ([FLRP.Enforceable][]) turns an arbitrary
   representation of `𝒫` into a core-free one.  It is the note's "we can assume `H`
   is core-free (else pass to `G/N`)" and needs quotient groups, which the library
   does not yet have.
+  A **finite presentation** of the parachute — a `FiniteLattice`{.AgdaRecord} whose
   lattice is isomorphic to `𝒫` — is required only by the last step, because
   statement (B) is quantified over `Fin`-presented finite lattices.  Every concrete
   instance supplies it by computation; the general transport (enumerate a finite
   setoid lattice and rebuild its tables) is routine and unformalized.
+  `PalfyPudlak`{.AgdaFunction} (Entry 3) is the classical import.

**On the converse direction of Theorem 3.6**.  (C) `⟹` (B) is immediate in the note
("obviously"), by applying (C) to a family containing the lattice to be represented
padded with two big canopies.  Formalizing it needs a concrete three-element lattice
and the padding bookkeeping, and it carries no weight in the program — the strategy
runs entirely on the direction proved here.  It is recorded as an open item in the
design note rather than assumed.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Parachute.Theorems where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base    using  ( Fin )
open import Data.Fin.Patterns using ( 0F ; 1F )
open import Data.Fin.Properties using ( _≟_ )
open import Data.Nat.Base    using  ( ℕ ; _+_ )
open import Data.Product     using  ( _,_ ; _×_ ; Σ-syntax ; ∃-syntax ; proj₁ ; proj₂ )
open import Level            using  ( Level ; 0ℓ )
open import Relation.Binary  using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; sym ; trans )
open import Relation.Nullary using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Unary   using  ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice  using  ( TopOf ; BottomOf )
open import Classical.Small.Structures    using  ( Lattice )
open import Classical.Structures.Group    using  ( Group ; IsSubgroup )
open import FLRP.Assumptions              using  ( PalfyPudlak )
open import FLRP.Enforceable  using  ( module UpperInterval ; CoreFree ; cfIE
                                     ; CoreFreeReduction ; GroupProperty
                                     ; GroupRepresentable ; IntervalIso )
open import FLRP.Parachute    using  ( module GroupParachute )
open import FLRP.Parachute.Representation
                              using  ( module ParachuteRep ; LatticeIso
                                     ; compose-IntervalIsoʳ )
open import FLRP.Problem      using  ( FiniteLattice ; toLattice ; FLRP-Statement )
open import Setoid.Algebras   using  ( 𝕌[_] ; 𝔻[_] )
```
-->

#### The setting

A family of `2 + m` canopies with the data the parachute construction needs, two
distinguished big canopies, and a property core-free enforceable by each canopy.

```agda
module ParachuteTheorems {ℓP : Level} {m : ℕ}
  (𝑳s      : Fin (2 + m) → Lattice)
  (𝒕       : ∀ i → TopOf (𝑳s i))
  (top?    : ∀ i (x : 𝕌[ proj₁ (𝑳s i) ])
           → Dec (Setoid._≈_ 𝔻[ proj₁ (𝑳s i) ] x (proj₁ (𝒕 i))))
  (𝒃       : ∀ i → BottomOf (𝑳s i))
  (nondeg  : ∀ i → ¬ (Setoid._≈_ 𝔻[ proj₁ (𝑳s i) ] (proj₁ (𝒃 i)) (proj₁ (𝒕 i))))
  where

  open ParachuteRep 𝑳s 𝒕 top? 𝒃 nondeg public
```

Every index has a companion, since there are at least two canopies; this is what
makes each atom a *proper* subgroup, which is the hypothesis the propagation theorem
needs.

```agda
  private
    0≢1 : ¬ (_≡_ {A = Fin (2 + m)} 0F 1F)
    0≢1 ()

  -- Some index other than i.
  companion : (i : Fin (2 + m)) → Σ[ j ∈ Fin (2 + m) ] (¬ (i ≡ j))
  companion i with i ≟ 0F
  ... | yes i≡0  = 1F , λ i≡1 → 0≢1 (trans (sym i≡0) i≡1)
  ... | no  i≢0  = 0F , i≢0
```

#### Theorem 3.6 and Corollary 3.8

Fix the two big canopies and the enforced properties.

```agda
  module Enforced
    (p q      : Fin (2 + m))
    (p≢q      : ¬ (p ≡ q))
    (big-p    : BigCanopyᴸ p)
    (big-q    : BigCanopyᴸ q)
    (Ps       : Fin (2 + m) → GroupProperty ℓP)
    (Ps-cfIE  : ∀ i → cfIE (Ps i) (𝑳s i))
    where
```

The heart: over a core-free representation of the parachute, every atom subgroup is
core-free and carries its canopy, so the group has every enforced property.

```agda
    module Core-Free
      (𝒢     : Group 0ℓ 0ℓ)
      (H     : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ)
      (H-sg  : IsSubgroup 𝒢 H)
      (H-cf  : CoreFree 𝒢 H H-sg)
      (iso   : IntervalIso 𝒢 H H-sg ⊕ᵖ-Lattice)
      where

      open UpperInterval 𝒢 H H-sg
      open GroupParachute 𝒢 H H-sg
      open Over 𝒢 H H-sg iso

      -- Each atom subgroup is core-free: it is a proper member of the interval,
      -- and core-freeness propagates from H to every proper member.
      K-CoreFree : (i : Fin (2 + m))
                 → CoreFree 𝒢 (set (K i)) (element-isSubgroup (K i))
      K-CoreFree i =
        proper-CoreFree config H-cf p≢q (bigCanopy p big-p) (bigCanopy q big-q)
                        (K i) (K-proper i (proj₁ (companion i)) (proj₂ (companion i)))

      -- ... so every canopy speaks about G, over a core-free subgroup.
      enforced : (i : Fin (2 + m)) → Ps i 𝒢
      enforced i = Ps-cfIE i 𝒢 (set (K i)) (element-isSubgroup (K i))
                              (K-CoreFree i) (canopyIso i)

      -- Lemma 3.7 applies to this representation: properness is decidable in a
      -- parachute (`IsAll?`), and the p-th atom is a member strictly between H
      -- and G.  What remains open in `Structure` is only the minimal normal
      -- subgroup, which the caller supplies.
      module Structure37 = Structure config H-cf p≢q
                             (bigCanopy p big-p) (bigCanopy q big-q) IsAll?
                             (K p) (K-proper p (proj₁ (companion p)) (proj₂ (companion p)))
                             (K-⊄H p)

      -- The witnesses, in the packaged form statement (C) asks for.
      canopy-witnesses : (i : Fin (2 + m))
        → ∃[ J ] ∃[ J-sg ] ( CoreFree 𝒢 J J-sg × IntervalIso 𝒢 J J-sg (𝑳s i) )
      canopy-witnesses i =
        set (K i) , element-isSubgroup (K i) , K-CoreFree i , canopyIso i
```

**Corollary 3.8**: the conjunction of finitely many cf-IE properties is cf-IE, by
the parachute of the enforcing lattices.  Note that this is literally the statement
above, read as a definition of `cfIE`{.AgdaFunction}.

```agda
    conjunction-cfIE : cfIE (λ 𝒢 → ∀ i → Ps i 𝒢) ⊕ᵖ-Lattice
    conjunction-cfIE 𝒢 H H-sg H-cf iso = Core-Free.enforced 𝒢 H H-sg H-cf iso
```

**Theorem 3.6**, substantive direction: a group representation of the parachute —
made core-free by the reduction — puts a single group in the intersection of the
enforced classes, with every canopy realized over a core-free subgroup.

```agda
    parachute-representable :
         GroupRepresentable ⊕ᵖ-Lattice
      →  CoreFreeReduction
      →  Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ]
           (  (∀ i → Ps i 𝒢)
           ×  (∀ i → ∃[ J ] ∃[ J-sg ]
                     ( CoreFree 𝒢 J J-sg × IntervalIso 𝒢 J J-sg (𝑳s i) )) )
    parachute-representable rep cfr =
      𝒬 , Core-Free.enforced 𝒬 J J-sg J-cf iso𝒬
        , Core-Free.canopy-witnesses 𝒬 J J-sg J-cf iso𝒬
      where
      open GroupRepresentable rep
      open CoreFreeReduction cfr

      reduced = reduce grp sub isSubgroup

      𝒬     = proj₁ reduced
      J     = proj₁ (proj₂ reduced)
      J-sg  = proj₁ (proj₂ (proj₂ reduced))
      J-cf  = proj₁ (proj₂ (proj₂ (proj₂ reduced)))

      iso𝒬 : IntervalIso 𝒬 J J-sg ⊕ᵖ-Lattice
      iso𝒬 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ reduced)))) ⊕ᵖ-Lattice interval-iso
```

#### The strategy meta-theorem

If the enforced classes have empty intersection, no group can carry the parachute:
the parachute is not group representable.  This is the note's Remark after
Theorem 3.6, and the whole point of the RP-3 hunt.

```agda
    empty-intersection→not-representable :
         ((𝒢 : Group 0ℓ 0ℓ) → ¬ (∀ i → Ps i 𝒢))
      →  CoreFreeReduction
      →  ¬ GroupRepresentable ⊕ᵖ-Lattice
    empty-intersection→not-representable empty cfr rep =
      empty (proj₁ witness) (proj₁ (proj₂ witness))
      where witness = parachute-representable rep cfr
```

A **finite presentation** of a lattice: a `FiniteLattice`{.AgdaRecord} isomorphic to
it.  Statement (B) is quantified over such presentations, so this is what lets the
previous theorem refute it.

```agda
    FinitePresentation : Lattice → Type 0ℓ
    FinitePresentation 𝑳 = Σ[ 𝑭 ∈ FiniteLattice ] LatticeIso (toLattice 𝑭) 𝑳
```

The meta-theorem that caps the phase: **finitely many cf-IE classes with empty
intersection give the FLRP a negative answer**.  Every step is now machine-checked
except the three explicit hypotheses.

```agda
    strategy-meta-theorem :
         ((𝒢 : Group 0ℓ 0ℓ) → ¬ (∀ i → Ps i 𝒢))   -- the classes do not all meet
      →  CoreFreeReduction                        -- core-free normalization
      →  FinitePresentation ⊕ᵖ-Lattice            -- the parachute is a finite lattice
      →  PalfyPudlak                              -- Assumptions, Entry 3
      →  ¬ FLRP-Statement
    strategy-meta-theorem empty cfr (𝑭 , liso) pp flrp =
      empty-intersection→not-representable empty cfr represented
      where
      -- Statement (B) applies to the presentation, and representability
      -- transports along the isomorphism.
      represented : GroupRepresentable ⊕ᵖ-Lattice
      represented = record
        { grp           = grp
        ; sub           = sub
        ; isSubgroup    = isSubgroup
        ; interval-iso  = compose-IntervalIsoʳ grp sub isSubgroup
                            (toLattice 𝑭) ⊕ᵖ-Lattice interval-iso liso
        }
        where open GroupRepresentable (pp flrp 𝑭)
```

---

[^1]: `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, Theorem 3.6
      (`thm-wjd-1`), its Remark, and Corollary 3.8
      (`cor:isle-prop-groups-1`); see also the design note
      `docs/notes/flrp-rp1-parachutes.md`.
