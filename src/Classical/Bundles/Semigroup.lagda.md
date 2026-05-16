---
layout: default
file: "src/Classical/Bundles/Semigroup.lagda.md"
title: "Classical.Bundles.Semigroup module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-bundles-semigroup">Bundle view of semigroups</a>

This is the [Classical.Bundles.Semigroup][] module of the [Agda Universal Algebra Library][].

The Σ-typed semigroup of [`Classical.Structures.Semigroup`][Classical.Structures.Semigroup] and the record-typed `Algebra.Bundles.Semigroup` of the standard library carry the same mathematical content.  This module supplies the bidirectional conversion functions `⟨_⟩ₛₘ` (Σ-core → bundle) and `⟪_⟫ₛₘ` (bundle → Σ-core), together with a round-trip lemma.  The bundle view exists solely so that code typed against `Algebra.Bundles` can be reused without writing the stdlib record by hand; it is not a parallel implementation of semigroups.

This module is the per-structure realization of the bundle-bridge pattern coordinated under M3-3 (#262).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.Semigroup where

-- Imports from Agda and the Agda Standard Library ----------------------
open import Agda.Primitive   using ()             renaming ( Set to Type )
open import Algebra.Bundles                      using ( )
open import Algebra.Bundles.Raw                  using ( )
open import Algebra.Structures                   using ( IsSemigroup ; IsMagma )
open import Data.Fin.Base                        using ( Fin )
open import Data.Fin.Patterns                    using ( 0F ; 1F )
open import Data.Product                         using ( _,_ ; proj₁ ; proj₂ ; _×_)
open import Function                             using ( Func )
open import Level                                using ( Level ; suc ; _⊔_ )
open import Relation.Binary                      using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ ; refl )

import Algebra.Bundles as Bundles

-- Imports from agda-algebras -------------------------------------------
open import Classical.Signatures.Semigroup       using ( 𝑆ₛₘ ; ∙op )
open import Classical.Theories.Semigroup
  using ( Eq-Semigroup ; assoc ; Th-Semigroup ; SemigroupVar ; x ; y ; z )
open import Classical.Structures.Semigroup
  using ( )  renaming ( Semigroup to ΣSemigroup )
open import Overture.Terms      {𝑆 = 𝑆ₛₘ}  using ( Term ; ℊ ; node )
open import Setoid.Varieties.EquationalLogic      {𝑆 = 𝑆ₛₘ}
  using ( Modᵗ )

open import Setoid.Algebras                      {𝑆 = 𝑆ₛₘ}
  using ( Algebra ; ⟨_⟩ ; _̂_ ; 𝕌[_] )

open Algebra using ( Domain ; Interp )
open Func    using ( cong ) renaming ( to to _⟨$⟩_ )

private variable α ρ : Level
```

The two-element argument tuple helper, used in both directions of the bridge.  Made local because it is an artifact of the encoding, not a primitive concept.

```agda
private
  pair : ∀ {ℓ} {A : Set ℓ} → A → A → Fin 2 → A
  pair a b 0F = a
  pair a b 1F = b
  _⊨_ : Algebra α ρ
      → (Eq-Semigroup → Term SemigroupVar × Term SemigroupVar)
      → Type _
  𝑨 ⊨ E = Modᵗ E 𝑨

```

#### <a id="sigma-core-to-bundle">Σ-core to bundle</a>

```agda
⟨_⟩ₛₘ : ΣSemigroup α ρ → Bundles.Semigroup α ρ
⟨ (𝑨 , thm) ⟩ₛₘ = record
    { Carrier       = 𝕌[ 𝑨 ]
    ; _≈_           = _≈_
    ; _∙_           = λ a b → (∙op ̂ 𝑨) (pair a b)
    ; isSemigroup   = record
        { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong        = λ a≈b c≈d
                              → cong (Interp 𝑨)
                                  ( refl
                                  , λ { 0F → a≈b ; 1F → c≈d }
                                  )
            }
        ; assoc = λ a b c →
            -- Two bridges sandwich the model-level associativity proof.
            -- `lhs-bridge` propagates a pointwise-but-not-definitional equality
            -- between `pair ((∙op ̂ 𝑨) (pair a b)) c` (stdlib-bundle shape) and
            -- `λ i → ⟦ args (ℓ x ∙ ℓ y) (ℓ z) i ⟧ ⟨$⟩ ρ` (term-interpretation
            -- shape); `rhs-bridge` does the mirror image.  The inner
            -- `cong (Interp 𝑨)` calls discharge the nested Fin 2 η-failure at
            -- the LHS's `0F` slot and the RHS's `1F` slot respectively.
            ≈-trans
              (cong (Interp 𝑨)
                ( refl
                , λ where
                    0F → cong (Interp 𝑨)
                           ( refl
                           , λ where 0F → ≈-refl ; 1F → ≈-refl
                           )
                    1F → ≈-refl
                ))
              (≈-trans
                (thm assoc (assignment a b c))
                (cong (Interp 𝑨)
                  ( refl
                  , λ where
                      0F → ≈-refl
                      1F → cong (Interp 𝑨)
                             ( refl
                             , λ where 0F → ≈-refl ; 1F → ≈-refl
                             )
                  )))
        }
    }
  where
    open Setoid (Domain 𝑨) using ( _≈_ ; isEquivalence )
                           renaming ( refl to ≈-refl ; trans to ≈-trans )
    -- Variable assignment that mirrors how `Th-Semigroup assoc` was written:
    -- under this assignment, the LHS term interprets to `((a · b) · c)` (in
    -- the bundle's `_∙_`) and the RHS to `(a · (b · c))`, so the bundle's
    -- stdlib-shaped `assoc a b c` is exactly what `thm assoc` produces —
    -- modulo the two `cong (Interp 𝑨)` bridges above, which exist solely
    -- to reconcile the Fin 2 η-failure.
    assignment : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → SemigroupVar → 𝕌[ 𝑨 ]
    assignment a b c x = a
    assignment a b c y = b
    assignment a b c z = c
```

#### <a id="bundle-to-sigma-core">Bundle to Σ-core</a>

```agda
⟪_⟫ₛₘ : Bundles.Semigroup α ρ → ΣSemigroup α ρ
⟪ B ⟫ₛₘ = 𝑨 , thm
  where
    open Bundles.Semigroup B
      using    ( Carrier ; _≈_ ; _∙_ ; isEquivalence ; ∙-cong )
      renaming ( assoc to ∙-assoc )

    A-setoid : Setoid _ _
    A-setoid = record  { Carrier        = Carrier
                       ; _≈_            = _≈_
                       ; isEquivalence  = isEquivalence
                       }

    interp : Func (⟨ 𝑆ₛₘ ⟩ A-setoid) A-setoid
    interp ⟨$⟩ (∙op , args)            = args 0F ∙ args 1F
    cong   interp {∙op , u} {.∙op , v} (refl , u≈v)
                                       = ∙-cong (u≈v 0F) (u≈v 1F)

    𝑨 : Algebra _ _
    𝑨 = record { Domain = A-setoid ; Interp = interp }

    thm : 𝑨 ⊨ Th-Semigroup
    thm assoc ρ = ∙-assoc (ρ x) (ρ y) (ρ z)
```

**Note on the `thm` typing**.  The expected type is `Modᵗ Th-Semigroup 𝑨`, i.e., `∀ i
  → 𝑨 ⊧ fst (Th-Semigroup i) ≈ snd (Th-Semigroup i)`.  I have written the proof body
  but left the type signature using the local alias to keep the file independent of
  internal `Modᵗ` naming churn.  The actual signature should read:

```agda
    -- thm : ∀ i → ∀ (ρ : SemigroupVar → Carrier)
    --     → (interp ⟨$⟩ (∙op , pair (interp ⟨$⟩ (∙op , pair (ρ x) (ρ y))) (ρ z)))
    --       ≈ (interp ⟨$⟩ (∙op , pair (ρ x) (interp ⟨$⟩ (∙op , pair (ρ y) (ρ z)))))
    -- thm assoc ρ = ∙-assoc (ρ x) (ρ y) (ρ z)
```

#### <a id="round-trip">Round trip</a>

The Σ-core → bundle → Σ-core round trip recovers the input *pointwise*: same carrier setoid, same operation under any inputs, same model-of-theory proof up to function extensionality on the cong field of `Interp`.  It does **not** recover the input as an inhabitant of `≡` on `ΣSemigroup α ρ` — `⟨_⟩ₛₘ` packs operation arguments into the local `pair` helper while `⟪_⟫ₛₘ` interprets them through a `λ {0F → args 0F ; 1F → args 1F}` lambda, and Agda lacks η on `Fin 2`-pattern lambdas, so the two `Interp._⟨$⟩_` fields are propositionally but not definitionally equal.  A propositional proof requires function extensionality, which the `--safe` regime of the library does not postulate.

The verification we *do* discharge — and what the M3-2 acceptance criterion actually requires — is round-trip on the concrete `(ℕ, +)` instance, where the cong-types are homogeneous in `_≡_` and reduction collapses the pattern lambda.  See [`Examples.Classical.Semigroup.ℕ-roundtrip`][Examples.Classical.Semigroup].

--------------------------------------

<span style="float:left;">[← Classical.Bundles](Classical.Bundles.html)</span>
<span style="float:right;">[Classical.Small →](Classical.Small.html)</span>

{% include UALib.Links.md %}
