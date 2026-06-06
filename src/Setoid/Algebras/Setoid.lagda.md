---
layout: default
title : "Setoid.Algebras.Setoid module (Agda Universal Algebra Library)"
date : "2026-06-06"
author: "agda-algebras development team"
---

#### The signature-to-setoid functor

This is the [Setoid.Algebras.Setoid][] module of the [Agda Universal Algebra Library][].

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

(The setoid-algebra approach is inspired by the one taken, e.g., by Andreas Abel
in his formalization of Birkhoff's completeness theorem; a
[pdf is available here](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).)

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Algebras.Setoid where

-- Imports from the Agda and the Agda Standard Library --------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
open import Level            using ( Level )
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
when they are pointwise equal in the underlying setoid `ξ`.

```agda
EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρ}
 →        ∀{f g} → f ≡ g → (ArityOf 𝑆 f → Carrier ξ) → (ArityOf 𝑆 g → Carrier ξ) → Type _

EqArgs {ξ = ξ} refl u v = ∀ i → (_≈_ ξ) (u i) (v i)
```

`⟨ 𝑆 ⟩ ξ` is the setoid whose carrier is a single operation symbol paired with a
tuple of its arguments drawn from `ξ`, and whose equality is `EqArgs`{.AgdaFunction}.
This is the polynomial functor of the signature `𝑆`, lifted to setoids.

```agda
⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρ → Setoid _ _
Carrier (⟨ 𝑆 ⟩ ξ) = Σ[ f ∈ OperationSymbolsOf 𝑆 ] (ArityOf 𝑆 f → ξ .Carrier)
_≈_ (⟨ 𝑆 ⟩ ξ) (f , u) (g , v) = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

IsEquivalence.refl   (isEqv (⟨ 𝑆 ⟩ ξ))                      = refl , λ _ → reflS   ξ
IsEquivalence.sym    (isEqv (⟨ 𝑆 ⟩ ξ))(refl , g)            = refl , λ i → symS    ξ (g i)
IsEquivalence.trans  (isEqv (⟨ 𝑆 ⟩ ξ))(refl , g)(refl , h)  = refl , λ i → transS  ξ (g i) (h i)
```

--------------------------------

<span style="float:left;">[↑ Setoid.Algebras](Setoid.Algebras.html)</span>
<span style="float:right;">[Setoid.Algebras.Basic →](Setoid.Algebras.Basic.html)</span>

{% include UALib.Links.md %}
