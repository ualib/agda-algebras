---
layout: default
title : "Setoid.Signatures module (Agda Universal Algebra Library)"
date : "2026-06-06"
author: "agda-algebras development team"
---

#### The signature-to-setoid functor

This is the [Setoid.Signatures][] module of the [Agda Universal Algebra Library][].

It collects the two *signature-generic* constructions that translate an ordinary
signature into a signature over a setoid domain: the polynomial-functor lifting
`⟨_⟩`{.AgdaFunction} and its companion `EqArgs`{.AgdaFunction}.  Each takes the
signature as its own argument — explicitly for `⟨_⟩`{.AgdaFunction}, as an implicit
`{𝑆}` for `EqArgs`{.AgdaFunction} — and reads no ambient signature, so they live in
a module with no `{𝑆 : Signature 𝓞 𝓥}` parameter.  It is the setoid-level companion
to [Overture.Signatures][].

Keeping them here — rather than inside the signature-parameterized
[Setoid.Algebras.Basic][] — matters for more than tidiness.  In a module
parameterized by `{𝑆 : Signature 𝓞 𝓥}`, every definition gets that module
parameter silently prepended, whether or not it uses it.  For `Algebra`, `_^_`,
`𝔻[_]`, … that is harmless: their types mention the module's `𝑆`, so it is
recovered from context at each use site.  But `⟨_⟩` and `EqArgs` take their own
signature argument and never refer to the module's parameter, so the prepended
`{𝑆}` is left unconstrained — a hand-written use site stalls on it as an
unsolvable metavariable.  Defining them in this non-parameterized module removes
the spurious parameter at the source.  [Setoid.Algebras.Basic][] re-exports both
names, so importing them from there is unaffected.

The setoid-algebra approach was inspired by Andreas Abel's formalization of
Birkhoff's completeness theorem; see:
http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Signatures where

-- Imports from the Agda and the Agda Standard Library --------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Setoid ; IsEquivalence )

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- Imports from the Agda Universal Algebra Library ----------------------
open import Overture  using ( 𝓞 ; 𝓥 ; Signature ; OperationSymbolsOf ; ArityOf )

private variable α ρ : Level

open Setoid
 using ( _≈_ ; Carrier )
 renaming ( refl to reflS ; sym to symS ; trans to transS ; isEquivalence to isEqv )
```

`EqArgs` is the equality on the argument tuples of a pair of operation symbols.
Given a proof `f ≡ g` that the two symbols agree, two tuples are `EqArgs`-related
when they are pointwise equal in the underlying setoid `A`.

```agda
EqArgs : {𝑆 : Signature 𝓞 𝓥} (A : Setoid α ρ)
  → ∀{f g} → f ≡ g → (ArityOf 𝑆 f → Carrier A) → (ArityOf 𝑆 g → Carrier A)
  → Type (𝓥 ⊔ ρ)

EqArgs A ≡.refl u v = ∀ i → u i ≈ᴬ v i
  where open Setoid A using () renaming ( _≈_ to _≈ᴬ_ )
```

`⟨ 𝑆 ⟩ A` is the setoid whose carrier is a single operation symbol paired with a
tuple of its arguments drawn from `A`, and whose equality is `EqArgs`{.AgdaFunction}.
This is the polynomial functor of the signature `𝑆`, lifted to setoids.

```agda
open IsEquivalence using( refl ; sym ; trans )

⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρ → Setoid (𝓞 ⊔ 𝓥 ⊔ α) (𝓞 ⊔ 𝓥 ⊔ ρ)
⟨ 𝑆 ⟩ A .Carrier = Σ[ f ∈ OperationSymbolsOf 𝑆 ] (ArityOf 𝑆 f → A .Carrier)
⟨ 𝑆 ⟩ A ._≈_ (f , u) (g , v) = Σ[ eqv ∈ f ≡ g ] EqArgs A eqv u v
⟨ 𝑆 ⟩ A .isEqv .refl = ≡.refl , λ _ → reflS A
⟨ 𝑆 ⟩ A .isEqv .sym (≡.refl , g) = ≡.refl , λ i → symS A (g i)
⟨ 𝑆 ⟩ A .isEqv .trans (≡.refl , g) (≡.refl , h) = ≡.refl , λ i → transS  A (g i) (h i)
```
