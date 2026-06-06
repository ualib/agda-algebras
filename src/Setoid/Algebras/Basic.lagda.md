---
layout: default
title : "Setoid.Algebras.Basic module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---

#### Basic definitions

This is the [Setoid.Algebras.Basic][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature )

module Setoid.Algebras.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda and the Agda Standard Library --------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product     using ( _,_ )
open import Function         using ( _∘_ ; _∘₂_ ; Func ; _$_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid ; IsEquivalence )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------
open import Overture           using ( proj₂ ; proj₁ ; OperationSymbolsOf ; ArityOf )
open import Setoid.Signatures  using ( EqArgs ; ⟨_⟩ ) public

private variable α ρ ι : Level

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α
```


#### Setoid Algebras

Here we define algebras over a setoid, instead of a mere type with no equivalence on it.

The operator `⟨_⟩`{.AgdaFunction} that translates an ordinary signature into a
signature over a setoid domain — together with its companion `EqArgs`{.AgdaFunction}
— is defined in the signature-generic module [Setoid.Signatures][] and re-exported
here (see the import above).  Each takes its own signature argument rather than
reading this module's `{𝑆}`, so housing them in a non-parameterized module means
the unused `{𝑆 : Signature 𝓞 𝓥}` parameter of this module does not ride along as
an unsolvable metavariable at use sites.  The `Interp`{.AgdaField} field of
`Algebra`{.AgdaRecord} applies the re-exported `⟨ 𝑆 ⟩` to this module's signature `𝑆`.

```agda
open Setoid using ( _≈_ ; Carrier )

open Func renaming ( to to _⟨$⟩_ ; cong to ≈cong )
```

A setoid algebra is just like an algebra but we require that all basic operations
of the algebra respect the underlying setoid equality. The `Func` record packs a
function (`f`, aka apply, aka `_⟨$⟩_`) with a proof (cong) that the function respects
equality.

```agda
record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
 field
  Domain : Setoid α ρ
  Interp : Func (⟨ 𝑆 ⟩ Domain) Domain
   --      ^^^^^^^^^^^^^^^^^^^^^^^ is a record type with two fields:
   --       1. a function  f : Carrier (⟨ 𝑆 ⟩ Domain)  → Carrier Domain
   --       2. a proof cong : f Preserves _≈₁_ ⟶ _≈₂_ (that f preserves the setoid equalities)
 -- Actually, we already have the following: (it's called "reflexive"; see Structures.IsEquivalence)
 ≡→≈ : ∀{x}{y} → x ≡ y → (_≈_ Domain) x y
 ≡→≈ refl = Setoid.refl Domain

open Algebra
```

The next three definitions are merely syntactic sugar, but they can be very useful
for improving readability of our code.

```agda
𝔻[_] : Algebra α ρ →  Setoid α ρ
𝔻[ 𝑨 ] = Domain 𝑨

-- forgetful functor: returns the carrier of (the domain of) 𝑨, forgetting its structure
𝕌[_] : Algebra α ρ →  Type α
𝕌[ 𝑨 ] = Carrier 𝔻[ 𝑨 ]

-- interpretation of an operation symbol in an algebra
_̂_ : (f : OperationSymbolsOf 𝑆)(𝑨 : Algebra α ρ) → (ArityOf 𝑆 f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]
f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
{-# WARNING_ON_USAGE _̂_
"The combining-caret notation `_̂_` is deprecated as of v3.0 and will be removed
in v3.1.  Use the ASCII `_^_` defined immediately below.  See ADR-002 §7."
#-}

-- ASCII canonical form of operation-symbol interpretation in an algebra.
-- Definitionally identical to `_̂_`; introduced for grep-friendliness and to
-- survive shell-pipeline tooling.  New `Classical/` code uses `_^_`
-- exclusively; existing `Setoid/` code may continue to use `_̂_` until v3.1.
-- See ADR-002 §7 for the rationale and per-tree policy.
_^_ : (f : OperationSymbolsOf 𝑆)(𝑨 : Algebra α ρ) → (ArityOf 𝑆 f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]
f ^ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
```

Sometimes we want to extract the universe level of a given algebra or its carrier.
The following functions provide that information.

```agda
-- The universe level of an algebra
Level-of-Alg : {α ρ 𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α ρ → Level
Level-of-Alg {α = α}{ρ}{𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)

-- The universe level of the carrier of an algebra
Level-of-Carrier : {α ρ 𝓞 𝓥  : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α ρ → Level
Level-of-Carrier {α = α} _ = α
```


#### Level lifting setoid algebra types

```agda
module _ (𝑨 : Algebra α ρ)(ℓ : Level) where
  open Algebra 𝑨  using ()     renaming ( Domain to A )
  open Setoid A   using (sym ; trans )  renaming ( Carrier to ∣A∣ ; _≈_ to _≈₁_ ; refl to refl₁ )
  open Level


  Lift-Algˡ : Algebra (α ⊔ ℓ) ρ
  Lift-Algˡ .Domain =
    record  { Carrier = Lift ℓ ∣A∣
            ; _≈_ = λ x y → lower x ≈₁ lower y
            ; isEquivalence = record  { refl = refl₁ ; sym = sym ; trans = trans }
            }
  Lift-Algˡ .Interp ⟨$⟩ (f , la) = lift $ (f ^ 𝑨) (lower ∘ la)
  Lift-Algˡ .Interp .≈cong (refl , la=lb) = ≈cong (Interp 𝑨) (refl , la=lb)


  Lift-Algʳ : Algebra α (ρ ⊔ ℓ)
  Lift-Algʳ .Domain =
    record  { Carrier = ∣A∣
            ; _≈_ = (Lift ℓ) ∘₂ _≈₁_
            ; isEquivalence = record  { refl = lift refl₁
                                      ; sym = lift ∘ sym ∘ lower
                                      ; trans = λ x y → lift $ trans (lower x) (lower y)
                                      }
            }
  Lift-Algʳ .Interp ⟨$⟩ (f , la) = (f ^ 𝑨) la
  Lift-Algʳ .Interp .≈cong (refl , la≡lb) = lift $ ≈cong (Interp 𝑨) (≡.refl , (lower ∘ la≡lb))

Lift-Alg : (𝑨 : Algebra α ρ)(ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀)
```

--------------------------------

<span style="float:left;">[↑ Setoid.Algebras](Setoid.Algebras.html)</span>
<span style="float:right;">[Setoid.Algebras.Products →](Setoid.Algebras.Products.html)</span>

{% include UALib.Links.md %}
