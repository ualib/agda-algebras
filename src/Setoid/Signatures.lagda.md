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
`⟨_⟩`{.AgdaFunction} and its companion `EqArgs`{.AgdaFunction}.  Both take the
signature as an *explicit* argument and use no ambient signature, so they live in
a module with no `{𝑆 : Signature 𝓞 𝓥}` parameter.

Keeping them here — rather than inside the signature-parameterized
[Setoid.Algebras.Basic][] — matters for more than tidiness.  In a module
parameterized by `{𝑆 : Signature 𝓞 𝓥}`, a definition whose type never mentions
the parameter still has the unused `{𝑆}` silently prepended.  For `Algebra`,
`_^_`, `𝔻[_]`, … the parameter is recovered from context because each of those
types mentions `𝑆`; but `⟨_⟩` and `EqArgs` mention it nowhere, so a hand-written
use site leaves the prepended `{𝑆}` as an unsolvable metavariable.  Defining them
in this non-parameterized module removes the spurious parameter at the source.
[Setoid.Algebras.Basic][] re-exports both names, so importing them from there is
unaffected.

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

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

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

EqArgs A refl u v = ∀ i → u i ≈ᴬ v i
  where open Setoid A using () renaming ( _≈_ to _≈ᴬ_ )
```

`⟨ 𝑆 ⟩ A` is the setoid whose carrier is a single operation symbol paired with a
tuple of its arguments drawn from `A`, and whose equality is `EqArgs`{.AgdaFunction}.
This is the polynomial functor of the signature `𝑆`, lifted to setoids.

```agda
⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρ → Setoid (𝓞 ⊔ 𝓥 ⊔ α) (𝓞 ⊔ 𝓥 ⊔ ρ)
Carrier (⟨ 𝑆 ⟩ A) = Σ[ f ∈ OperationSymbolsOf 𝑆 ] (ArityOf 𝑆 f → A .Carrier)
_≈_ (⟨ 𝑆 ⟩ A) (f , u) (g , v) = Σ[ eqv ∈ f ≡ g ] EqArgs A eqv u v

IsEquivalence.refl (isEqv (⟨ 𝑆 ⟩ A)) = refl , λ _ → reflS A
IsEquivalence.sym (isEqv (⟨ 𝑆 ⟩ A)) (refl , g) = refl , λ i → symS A (g i)
IsEquivalence.trans (isEqv (⟨ 𝑆 ⟩ A)) (refl , g) (refl , h) =
  refl , λ i → transS  A (g i) (h i)
```

--------------------------------

<span style="float:left;">[↑ Setoid](Setoid.html)</span>
<span style="float:right;">[Setoid.Subalgebras →](Setoid.Subalgebras.html)</span>

{% include UALib.Links.md %}
