---
layout: default
file: "src/Setoid/Subalgebras/Subdirect.lagda.md"
title: "Setoid.Subalgebras.Subdirect module (The Agda Universal Algebra Library)"
date: "2026-06-20"
author: "the agda-algebras development team"
---

### Subdirect products and Birkhoff's subdirect representation theorem

This is the [Setoid.Subalgebras.Subdirect][] module of the [Agda Universal Algebra Library][].

A **subdirect product** of a family `𝒜 : I → Algebra` is a subalgebra of the product
`⨅ 𝒜` whose every coordinate projection is *surjective* — the subalgebra meets every
factor.  A **subdirect embedding** of `𝑨` is a monomorphism `𝑨 ↪ ⨅ 𝒜` exhibiting `𝑨`
as such a subdirect product.  These are the structures underlying Birkhoff's *subdirect
representation theorem*: every algebra is a subdirect product of subdirectly irreducible
algebras.

This module proves the **choice-free core** in full:

+  *the bridge* — a family of congruences `θ : I → Con 𝑨` whose meet is the diagonal
   (`θ` *separates points*) induces a subdirect embedding `𝑨 ↪ ⨅ (λ i → 𝑨 ╱ θ i)`, with
   injectivity *exactly* the separation hypothesis and the coordinate projections
   surjective because they are the canonical quotient maps; and
+  *the reduction of Birkhoff to existence* — given a subdirect SI-representation of `𝑨`
   (a separating family whose quotients are all subdirectly irreducible), `𝑨` is a
   subdirect product of subdirectly irreducible algebras.

What is **not** choice-free is the *existence* of a subdirect SI-representation for an
arbitrary algebra: for each pair `a ≢ b` one needs a congruence maximal among those not
relating `a , b` (it is completely meet-irreducible, so its quotient is subdirectly
irreducible), and selecting it is a Zorn's-lemma step incompatible with postulate-free
`--safe`.  Following option (a) of the design brief, we take that existence as an
explicit module parameter (`SubdirectSIRep`), so the theorem is proved *relative to* a
precisely-stated assumption and nothing is postulated.  See the design note
`docs/notes/m6-2-subdirect.md` for the alternatives (finite/decidable search; deferral)
and the rationale.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Subalgebras.Subdirect {𝑆 : Signature 𝓞 𝓥} where

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
  -- ⋂ θ ≅ 0ᴬ : every θ i relating a,b forces a ≈ b.
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

#### Birkhoff's subdirect representation theorem

The conclusion of Birkhoff's theorem is that an algebra is a subdirect product of
*subdirectly irreducible* algebras: a family of SI algebras and a subdirect embedding
into their product.

```agda
SubdirectlyRepresentable : (𝑨 : Algebra α ρ) → (ℓ ι : Level) → Type (𝓞 ⊔ 𝓥  ⊔ ρ ⊔ lsuc (α ⊔ ℓ ⊔ ι))
SubdirectlyRepresentable {α}{ρ} 𝑨 ℓ ι =
  Σ[ I ∈ Type ι ] Σ[ 𝒜 ∈ (I → Algebra α ℓ) ]
    ((∀ i → IsSubdirectlyIrreducible (𝒜 i)) × SubdirectEmbedding {𝑩 = 𝑨} 𝒜)
```

A **subdirect SI-representation** of `𝑨` packages exactly the data that the bridge
consumes: an index type, a family of congruences whose quotients are subdirectly
irreducible, and a proof that the family separates points.  This is the precise
content that Zorn's lemma supplies classically (and is the only non-constructive input).

```agda
SubdirectSIRep : (𝑨 : Algebra α ρ) → (ℓ ι : Level) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ lsuc (ℓ ⊔ ι))
SubdirectSIRep 𝑨 ℓ ι =
  Σ[ I ∈ Type ι ] Σ[ θ ∈ (I → Con 𝑨 ℓ) ]
    (Separates θ × (∀ i → IsSubdirectlyIrreducible (𝑨 ╱ θ i)))
```

The choice-free reduction: a subdirect SI-representation yields a subdirect-product
representation by subdirectly irreducible algebras.  This is the whole theorem *modulo*
the existence of the representation.

```agda
SIRep→Representable : {𝑨 : Algebra α ρ}
  → SubdirectSIRep 𝑨 ℓ ι → SubdirectlyRepresentable 𝑨 ℓ ι
SIRep→Representable (I , θ , sep , si) =
  I , (λ i → _ ╱ θ i) , si , separating→SubdirectEmbedding θ sep
```

Birkhoff's theorem, relative to the choice principle that every algebra admits a
subdirect SI-representation, then says every algebra is subdirectly representable.

```agda
module _ (sirep : (𝑨 : Algebra α ρ) → SubdirectSIRep 𝑨 ℓ ι) where

  Birkhoff-subdirect : (𝑨 : Algebra α ρ) → SubdirectlyRepresentable 𝑨 ℓ ι
  Birkhoff-subdirect 𝑨 = SIRep→Representable (sirep 𝑨)
```

--------------------------------------

<span style="float:left;">[← Setoid.Subalgebras.Subalgebras](Setoid.Subalgebras.Subalgebras.html)</span>
<span style="float:right;">[Setoid.Subalgebras.Properties →](Setoid.Subalgebras.Properties.html)</span>

{% include UALib.Links.md %}
