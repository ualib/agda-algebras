---
layout: default
file: "src/Setoid/Subalgebras/Subdirect/Basic.lagda.md"
title: "Setoid.Subalgebras.Subdirect.Basic module (The Agda Universal Algebra Library)"
date: "2026-06-20"
author: "the agda-algebras development team"
---

### Subdirect product basics

This is the [Setoid.Subalgebras.Subdirect.Basic][] module of the [Agda Universal Algebra Library][].

A **subdirect product** of a family `𝒜 : I → Algebra` is a subalgebra of the product
`⨅ 𝒜` whose every coordinate projection is *surjective* — the subalgebra meets every
factor.  A **subdirect embedding** of `𝑨` is a monomorphism `𝑨 ↪ ⨅ 𝒜` exhibiting `𝑨`
as such a subdirect product.  These are the structures underlying Birkhoff's *subdirect
representation theorem*: every algebra is a subdirect product of subdirectly irreducible
algebras.


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Subalgebras.Subdirect.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Function         using ( id ) renaming ( Func to _⟶_ )
open import Level            using ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary  using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_ ) renaming ( refl to ≡refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Functions                         using ( IsInjective ; IsSurjective )

open import Setoid.Algebras                 {𝑆 = 𝑆}  using ( Algebra ; ⨅ ; 𝔻[_] )
open import Setoid.Congruences              {𝑆 = 𝑆}  using ( Con ; _╱_ )
open import Setoid.Homomorphisms            {𝑆 = 𝑆}  using  ( hom ; IsHom ; epi ; IsEpi
                                                            ; 𝒾𝒹 ; ⊙-hom ; ⨅-hom-co
                                                            ; πhom ; πepi )
open import Setoid.Subalgebras.Subalgebras  {𝑆 = 𝑆}  using ( _≤_ )
open import Setoid.Congruences.Monolith     {𝑆 = 𝑆}  using ( IsSubdirectlyIrreducible )

open _⟶_  using ( cong ) renaming ( to to _⟨$⟩_ )
open Algebra  using ( Domain )

private variable α ρ β ρᵇ ℓ ι : Level
```

#### Coordinate projections out of a product

The projection of a product algebra onto its `i`-th factor is a homomorphism.  (This is
the `⨅-projection-hom` of [Setoid.Homomorphisms.Products][], re-derived here without that
version's vestigial domain parameter so that the factor family `𝒜` determines it.)

```agda
module _ {I : Type ι}(𝒜 : I → Algebra α ρ) where
  open Algebra (⨅ 𝒜) using () renaming ( Domain to ⨅A )

  ⨅-proj : (i : I) → hom (⨅ 𝒜) (𝒜 i)
  ⨅-proj i = F , isHom
    where
    open Algebra (𝒜 i)  using () renaming ( Domain to Aᵢ )
    open Setoid Aᵢ       using ( refl )
    F : ⨅A ⟶ Aᵢ
    F = record { to = λ x → x i ; cong = λ xy → xy i }
    isHom : IsHom (⨅ 𝒜) (𝒜 i) F
    isHom = record { compatible = refl }
```

#### Subdirect products and subdirect embeddings

Fix a candidate algebra `𝑩` and a factor family `𝒜`.  The `i`-th **coordinate map** of a
homomorphism `h : 𝑩 → ⨅ 𝒜` is the composite `projᵢ ∘ h : 𝑩 → 𝒜 i`.  A homomorphism is a
**subdirect embedding** when it is injective (so `𝑩 ≤ ⨅ 𝒜`) and every coordinate map is
surjective.

```agda
module _ {I : Type ι}{𝑩 : Algebra β ρᵇ}(𝒜 : I → Algebra α ρ) where

  -- The i-th coordinate map projᵢ ∘ h of a hom into the product.
  coord : hom 𝑩 (⨅ 𝒜) → (i : I) → hom 𝑩 (𝒜 i)
  coord h i = ⊙-hom h (⨅-proj 𝒜 i)

  record IsSubdirectEmbedding (h : hom 𝑩 (⨅ 𝒜)) : Type (ι ⊔ α ⊔ ρ ⊔ β ⊔ ρᵇ) where
    field
      embed-inj  : IsInjective (proj₁ h)
      proj-onto  : (i : I) → IsSurjective (proj₁ (coord h i))

  open IsSubdirectEmbedding public

  -- A subdirect embedding of 𝑩 into ⨅ 𝒜 (equivalently: 𝑩 is a subdirect product of 𝒜).
  SubdirectEmbedding : Type (𝓞 ⊔ 𝓥 ⊔ ι ⊔ α ⊔ ρ ⊔ β ⊔ ρᵇ)
  SubdirectEmbedding = Σ[ h ∈ hom 𝑩 (⨅ 𝒜) ] IsSubdirectEmbedding h

  -- A subdirect embedding is in particular a subalgebra inclusion 𝑩 ≤ ⨅ 𝒜.
  subdirect→≤ : SubdirectEmbedding → 𝑩 ≤ ⨅ 𝒜
  subdirect→≤ (h , emb) = h , embed-inj emb
```

#### The bridge: a separating family of congruences gives a subdirect embedding

Now the constructive heart.  Fix an algebra `𝑨` and a family of congruences
`θ : I → Con 𝑨`.  Form the family of quotients `i ↦ 𝑨 ╱ θ i` and the natural map into
their product, assembled from the canonical quotient projections `πhom (θ i)`.

```agda
module _ {I : Type ι}{𝑨 : Algebra α ρ}(θ : I → Con 𝑨 ℓ) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )

  -- the family of quotient algebras and the natural map into their product
  𝑨╱ : I → Algebra α ℓ
  𝑨╱ i = 𝑨 ╱ θ i

  natmap : hom 𝑨 (⨅ 𝑨╱)
  natmap = ⨅-hom-co 𝑨╱ (λ i → πhom 𝒾𝒹 (θ i))
```

The family **separates points** when the only pairs related by *every* `θ i` are the
`≈`-equal ones — i.e. the meet `⋂ θ` is the diagonal `0ᴬ`.  This is *exactly* the
injectivity of the natural map: an element's image in the product is its tuple of
congruence classes, and two elements have the same tuple iff every `θ i` relates them.

```agda
  -- the meet ⋂ θ is the diagonal 0ᴬ: every θ i relating a,b forces a ≈ b.
  Separates : Type (ι ⊔ α ⊔ ρ ⊔ ℓ)
  Separates = ∀ {a b} → (∀ i → proj₁ (θ i) a b) → a ≈ b

  -- Injectivity of the natural map is definitionally the separation property.
  natmap-injective : Separates → IsInjective (proj₁ natmap)
  natmap-injective = id

  natmap-separates : IsInjective (proj₁ natmap) → Separates
  natmap-separates = id

  _ : IsInjective (proj₁ natmap) ≡ Separates
  _ = ≡refl
```

Each coordinate map `projᵢ ∘ natmap` *is* the canonical quotient epimorphism
`𝑨 ↠ 𝑨 ╱ θ i`, hence surjective — with no decidability or choice assumption on the index.

```agda
  natmap-proj-onto : (i : I) → IsSurjective (proj₁ (coord 𝑨╱ natmap i))
  natmap-proj-onto i = IsEpi.isSurjective (proj₂ (πepi 𝒾𝒹 (θ i)))
```

Assembling injectivity and the surjective coordinate maps gives the subdirect embedding.

```agda
  separating→subdirect : Separates → IsSubdirectEmbedding 𝑨╱ natmap
  separating→subdirect sep =
    record { embed-inj = natmap-injective sep ; proj-onto = natmap-proj-onto }

  separating→SubdirectEmbedding : Separates → SubdirectEmbedding 𝑨╱
  separating→SubdirectEmbedding sep = natmap , separating→subdirect sep
```


--------------------------------------

<span style="float:left;">[← Setoid.Subalgebras.Subdirect](Setoid.Subalgebras.Subdirect.html)</span>
<span style="float:right;">[Setoid.Subalgebras.Subdirect.BirkhoffSI →](Setoid.Subalgebras.Subdirect.BirkhoffSI.html)</span>

{% include UALib.Links.md %}
