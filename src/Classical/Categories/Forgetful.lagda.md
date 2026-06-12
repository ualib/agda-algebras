---
layout: default
file: "src/Classical/Categories/Forgetful.lagda.md"
title: "Classical.Categories.Forgetful module"
date: "2026-06-09"
author: "the agda-algebras development team"
---

### Classical forgetful functors

This is the [Classical.Categories.Forgetful][] module of the [Agda Universal Algebra Library][].

The classical forgetful *projections* of [ADR-002][] §5 become forgetful *functors* simply by
giving them the morphism action — and that action is already supplied, uniformly, by the
reduct functor [`reductF`][Classical.Categories.Reduct].  Each forgetful is `reductF` of the
relevant signature inclusion, reusing the per-structure inclusion data (`X-incl` / `X-κ`).

The inaugural instance is `monoid→semigroupF`.  Since a semigroup is an algebra over
`Sig-Magma` (Semigroup reuses the magma signature), the forgetful from monoids is `reductF`
of the inclusion `Sig-Magma ↪ Sig-Monoid` — packaged from the existing `∙-incl` / `∙-κ` of
[`Classical.Structures.Monoid`][].  Its action on a monoid homomorphism keeps the underlying
setoid map on the nose, as `monoid→semigroupF-keeps-map` records by `refl`.

A forgetful functor between *theory-satisfying* structures owes a second debt beyond the
morphism action: the theory obligation.  `monoid→semigroup` must show that the magma reduct
of a monoid satisfies `Th-Semigroup`, and M3-6 paid that debt by hand (the curried-law pivot
`thm` inside [`Classical.Structures.Monoid`][], built on per-signature `interp-node`
bridges).  The last section of this module re-derives that obligation from the general
*reduct-invariance of satisfaction* theorem of [Classical.Varieties.Invariance][] — the
M4-5e regression demonstration that the bespoke per-structure pivots are instances of one
lemma.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Categories.Forgetful where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive    using ()           renaming ( Set to Type )
open import Data.Fin.Patterns using ( 0F ; 1F )
open import Data.Product      using ( proj₁ ; proj₂ )
open import Level             using ( Level )
open import Relation.Binary   using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures.Morphisms  using ( SigMorphism ; mkSigMorphism )
open import Overture.Terms.Translation     using ( _✶_ )
open import Setoid.Categories.Functor      using ( Functor )
open import Classical.Categories.Reduct    using ( reductF )
open import Classical.Signatures.Magma     using ( Sig-Magma )
open import Classical.Signatures.Monoid    using ( Sig-Monoid )
open import Classical.Structures.Monoid    using ( ∙-incl ; ∙-κ ; Monoid ; monoid→magma )
open import Classical.Structures.Semigroup using () renaming ( _⊨_ to _⊨ˢᵍ_ )
open import Classical.Theories.Monoid      using ( Th-Monoid ; assoc )
open import Classical.Theories.Semigroup   using ( Th-Semigroup ) renaming ( assoc to assocˢ )
open import Classical.Varieties.Invariance using ( ⊧-reduct )

open import Setoid.Terms.Basic               using ( _≐_ ; module Environment )
open import Setoid.Varieties.EquationalLogic using ( _⊧_≈_ )

import Setoid.Categories.Algebra as AlgCat

open import Setoid.Algebras.Basic      {𝑆 = Sig-Monoid} using ( Algebra ; 𝔻[_] )
open import Setoid.Homomorphisms.Basic {𝑆 = Sig-Monoid} using ( hom )

open _≐_ using ( rfl ; gnl )

private variable α ρ : Level
```

The inclusion `Sig-Magma ↪ Sig-Monoid`, as a signature morphism:

```agda
magma↪monoid : SigMorphism Sig-Magma Sig-Monoid
magma↪monoid = mkSigMorphism ∙-incl ∙-κ
```

The forgetful functor on algebras, `reductF` of that inclusion:

```agda
monoid→semigroupF : Functor (AlgCat.Alg {𝑆 = Sig-Monoid} α ρ) (AlgCat.Alg {𝑆 = Sig-Magma} α ρ)
monoid→semigroupF = reductF magma↪monoid
```

Its morphism action keeps the underlying setoid map of a monoid homomorphism unchanged:

```agda
monoid→semigroupF-keeps-map : {𝑴 𝑵 : Algebra α ρ} (f : hom 𝑴 𝑵)
                            → proj₁ (Functor.F₁ monoid→semigroupF f) ≡ proj₁ f
monoid→semigroupF-keeps-map _ = refl
```

#### The theory obligation, re-derived from reduct-invariance

This is the M4-5e regression demonstration.  The obligation: the magma reduct of a
monoid satisfies the semigroup theory.  The bespoke M3-6 proof (`thm` inside
`monoid→semigroup`) pivots through the monoid's curried associativity with hand-rolled
`interp-node` bridges; here the same obligation falls out of the general lemma
[`⊧-reduct`][Classical.Varieties.Invariance] in three steps:

1. the monoid itself satisfies its associativity equation (`proj₂ ℳ assoc` — already
   in hand, no term reasoning at all);
2. the `magma↪monoid`-translation of the *semigroup* associativity equation is the
   *monoid* associativity equation, up to the term equality `_≐_` (the two `bridge`
   lemmas below); and
3. `⊧-reduct` converts satisfaction of the translated equation into satisfaction of
   the original equation by the reduct.

Step 2 is where the M3-5 measurement (recorded in [Classical.Varieties.Invariance][])
becomes visible in practice.  The translated term and the theory's term are *not*
definitionally equal — both theories build their argument tuples with `Fin`-pattern
lambdas (`pair`), and the translation rebuilds the positions through `κ`, so the
position functions agree pointwise but not by `refl`; under `--safe` no propositional
equality is available.  But they are `_≐_`-equal by a finite, purely mechanical
pattern-match — compare each position, recurse — with no `refl`-matching of any
neutral arity type and no `interp-node` family.  The η-gap's only surviving shadow is
this pair of four-line bridges, and the bridges are *provable*, where the `≡`-form
would be funext-blocked.  (A cubical port erases even this residue: with funext the
bridges become `refl`-transports.)

```agda
module _ (ℳ : Monoid α ρ) where
  private 𝑴 = proj₁ ℳ
  open Setoid 𝔻[ 𝑴 ] using ( sym ; trans )
  open Environment 𝑴 using ( ≐→Equal )

  private
    -- The translated semigroup-associativity terms are the monoid-associativity
    -- terms, up to ≐.  Position by position: the outer node, its left subterm
    -- (one more node), and the variable leaves.
    bridgeˡ : (magma↪monoid ✶ proj₁ (Th-Semigroup assocˢ)) ≐ proj₁ (Th-Monoid assoc)
    bridgeˡ = gnl λ{ 0F → gnl (λ{ 0F → rfl refl ; 1F → rfl refl }) ; 1F → rfl refl }

    bridgeʳ : (magma↪monoid ✶ proj₂ (Th-Semigroup assocˢ)) ≐ proj₂ (Th-Monoid assoc)
    bridgeʳ = gnl λ{ 0F → rfl refl ; 1F → gnl (λ{ 0F → rfl refl ; 1F → rfl refl }) }

    -- The monoid satisfies the *translated* semigroup equation: rewrite both
    -- sides along the bridges and use the monoid's own associativity.
    ℳ⊧assoc✶ : 𝑴 ⊧ (magma↪monoid ✶ proj₁ (Th-Semigroup assocˢ))
                  ≈ (magma↪monoid ✶ proj₂ (Th-Semigroup assocˢ))
    ℳ⊧assoc✶ η =
      trans (≐→Equal _ _ bridgeˡ η) (trans (proj₂ ℳ assoc η) (sym (≐→Equal _ _ bridgeʳ η)))

  -- The reduct satisfies the semigroup theory, by reduct-invariance.  (The
  -- equation's two sides are pinned explicitly: the unifier cannot recover s
  -- from φ ✶ s or from ⟦ s ⟧, both being defined by recursion on s — the same
  -- implicit-pinning discipline the M4-5 handoff records.)
  Th-Semigroup-via-invariance : monoid→magma ℳ ⊨ˢᵍ Th-Semigroup
  Th-Semigroup-via-invariance assocˢ =
    ⊧-reduct magma↪monoid 𝑴
      {s = proj₁ (Th-Semigroup assocˢ)} {t = proj₂ (Th-Semigroup assocˢ)} ℳ⊧assoc✶
```

Per the issue's instruction, the bespoke proof in `Classical.Structures.Monoid` is
*not* deleted: it remains the proof `monoid→semigroup` actually uses, and this
section certifies that the general route re-proves it.  Adopting the general route
inside `monoid→semigroup` itself is deliberately deferred — it would reverse the
import order between `Classical.Structures.Monoid` and the categorical layer.

--------------------------------------

{% include UALib.Links.md %}
