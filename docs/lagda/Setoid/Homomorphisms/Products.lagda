---
layout: default
title : "Setoid.Homomorphisms.Products module (The Agda Universal Algebra Library)"
date : "2021-09-21"
author: "agda-algebras development team"
---

#### <a id="products-of-homomorphisms">Products of Homomorphisms of Algebras</a>

This is the [Setoid.Homomorphisms.Products][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Products {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library --------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Function         using () renaming ( Func to _⟶_ )
open import Data.Product     using ( _,_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

-- Imports from the Agda Universal Algebras Library ----------------------
open import Overture         using ( ∣_∣ ; ∥_∥)
open import Setoid.Algebras {𝑆 = 𝑆}
                             using ( Algebra ; _̂_ ; ⨅ )
open import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}
                             using ( hom ; IsHom ; epi )

private variable a α b β 𝓘 : Level

\end{code}

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family
`ℬ : I → Algebra β 𝑆` of algebras.  We sometimes refer to the inhabitants of `I`
as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then
we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.

\begin{code}

module _ {I : Type 𝓘}{𝑨 : Algebra a α }(ℬ : I → Algebra b β)  where
 open Algebra 𝑨      using ()        renaming ( Domain to A )
 open Algebra (⨅ ℬ)  using ()        renaming ( Domain to ⨅B )
 open _⟶_            using ( cong )  renaming ( to to _⟨$⟩_ )
 open IsHom

 ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = h , hhom
  where
  h : A ⟶ ⨅B
  (h ⟨$⟩ a) i = ∣ 𝒽 i ∣ ⟨$⟩ a
  cong h xy i = cong ∣ 𝒽 i ∣ xy

  hhom : IsHom 𝑨 (⨅ ℬ) h
  compatible hhom = λ i → compatible ∥ 𝒽 i ∥

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.
The syntax we use to represent this type is available to us because of the way `-Π`
is defined in the [Type Topology][] library.  We like this syntax because it is very
close to the notation one finds in the standard type theory literature.  However, we
could equally well have used one of the following alternatives, which may be closer
to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` or `(i : I) → hom 𝑨 (ℬ i)` or `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of
a family of algebras. That is, if we are given `𝒜 : I → Algebra α 𝑆` and
`ℬ : I → Algebra β 𝑆` (two families of `𝑆`-algebras), and
`𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct
a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.

\begin{code}

 ⨅-hom : (𝒜 : I → Algebra a α) → (∀ (i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom 𝒜 𝒽 = F , isHom
  where
  open Algebra (⨅ 𝒜) using () renaming ( Domain to ⨅A )

  F : ⨅A ⟶ ⨅B
  (F ⟨$⟩ x) i = ∣ 𝒽 i ∣ ⟨$⟩ x i
  cong F xy i = cong ∣ 𝒽 i ∣ (xy i)

  isHom : IsHom (⨅ 𝒜) (⨅ ℬ) F
  compatible isHom i = compatible ∥ 𝒽 i ∥
\end{code}


#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra
onto one of its factors is a homomorphism.

\begin{code}

 ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom i = F , isHom
  where
  open Algebra (ℬ i)  using () renaming ( Domain to Bi )
  open Setoid Bi      using () renaming ( refl to reflᵢ )

  F : ⨅B ⟶ Bi
  F ⟨$⟩ x = x i
  cong F xy = xy i

  isHom : IsHom (⨅ ℬ) (ℬ i) F
  compatible isHom {f} {a} = reflᵢ

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.

---------------------------------

<span style="float:left;">[← Setoid.Homomorphisms.Kernels](Setoid.Homomorphisms.Kernels.html)</span>
<span style="float:right;">[Setoid.Homomorphisms.Noether →](Setoid.Homomorphisms.Noether.html)</span>

{% include UALib.Links.md %}
