---
layout: default
title : "Setoid.Homomorphisms.Basic module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### Homomorphisms of Algebras over Setoids

This is the [Setoid.Homomorphisms.Basic][] module of the [Agda Universal Algebra Library][].

A **homomorphism** from `𝑨` to `𝑩` is a setoid function `h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]`
between the domains of the two algebras that is *compatible* with every basic
operation: for each operation symbol `f` and each tuple `a` of arguments,
`h ⟨$⟩ (f ^ 𝑨) a` and `(f ^ 𝑩) λ x → h ⟨$⟩ a x` are related by the equality of `𝑩`.

Two things distinguish this from an ordinary type-based definition, where
compatibility is an identification `h ((f ^ 𝑨) a) ≡ (f ^ 𝑩) (h ∘ a)`.

1.  The map is a setoid function, so it carries its own congruence proof and
    cannot fail to send equal arguments to equal results.
2.  Compatibility is asserted up to the equality *of the codomain*, not up to
    propositional equality; that is what lets `𝑩` be a quotient algebra (the same
    carrier under a coarser equivalence) with no special quotient type and no
    appeal to extensionality.

This module defines the compatibility predicates, the homomorphism type
`hom`{.AgdaFunction} and its predicate form `IsHom`{.AgdaRecord}, the injective
and surjective variants (monomorphisms and epimorphisms) in both of those forms,
the translations between them, and the identity homomorphism `𝒾𝒹`{.AgdaFunction}.
Everything else the library proves about homomorphisms is built on these,
including the following:

+  **composition**, `⊙-hom`{.AgdaFunction}, and the homomorphisms that witness
   **universe lifting** in [Setoid.Homomorphisms.Properties][];
+  **the kernel** of a homomorphism as a congruence, and the **quotient** it
   determines in [Setoid.Homomorphisms.Kernels][];
+  **isomorphism**, `_≅_`{.AgdaRecord}, given by a pair of mutually inverse
   homomorphisms in [Setoid.Homomorphisms.Isomorphisms][];
+  **the first homomorphism theorem** in [Setoid.Homomorphisms.Noether][];
+  **factoring** one homomorphism through another in
   [Setoid.Homomorphisms.Factor][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Homomorphisms.Basic  where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive           using () renaming ( Set to Type )
open import Data.Product             using ( _,_ ; Σ ; Σ-syntax ; proj₁ ; proj₂ )
open import Function.Bundles         using () renaming ( Func to _⟶_ )
open import Level                    using ( Level ; _⊔_ )
open import Relation.Binary          using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( refl )

-- Imports from the Agda Universal Algebra Library ---------------------------
open import Overture                 using ( OperationSymbolsOf ; 𝓞 ; 𝓥 ; Signature )
open import Setoid.Functions         using ( IsInjective ; IsSurjective ; 𝑖𝑑 )
open import Setoid.Algebras          using ( Algebra ; _^_ ; 𝔻[_])

private variable
  α β ρᵃ ρᵇ : Level
```
-->

The homomorphism type is built in four steps.  `compatible-map-op`{.AgdaFunction}
says that a setoid function `h` commutes with *one* operation symbol `f`;
`compatible-map`{.AgdaFunction} quantifies that over all operation symbols;
`IsHom`{.AgdaRecord} packages the resulting property as a record with the single
field `compatible`{.AgdaField} and the constructor
`mkIsHom`{.AgdaInductiveConstructor}; and `hom`{.AgdaFunction} is the type of
homomorphisms proper.  An inhabitant of `hom 𝑨 𝑩` is therefore a pair `(h , p)`: a
setoid function `h` from the domain of `𝑨` to that of `𝑩`, together with a proof
that `h` is compatible.

`mkhom`{.AgdaFunction} is the smart constructor for that pair, so a caller who has
`h` and a `compatible-map`{.AgdaFunction} proof never has to write the `Σ`-pair
and the `IsHom`{.AgdaRecord} record by hand.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ)(𝑩 : Algebra β ρᵇ) where
  open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝔻[ 𝑨 ]}{To = 𝔻[ 𝑩 ]} renaming (to to _⟨$⟩_ )

  compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → OperationSymbolsOf 𝑆 → Type (𝓥 ⊔ α ⊔ ρᵇ)
  compatible-map-op h f =  ∀ {a} → h ⟨$⟩ (f ^ 𝑨) a ≈₂ (f ^ 𝑩) λ x → h ⟨$⟩ a x
    where open Setoid 𝔻[ 𝑩 ] using() renaming ( _≈_ to _≈₂_ )

  compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ)
  compatible-map h = ∀ {f} → compatible-map-op h f

  -- The property of being a homomorphism.
  record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
    constructor mkIsHom
    field compatible : compatible-map h

  hom : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
  hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom

  -- Smart constructor for a homomorphism: bundle a setoid map with its
  -- compatibility proof, hiding the Σ / IsHom plumbing.
  mkhom : (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → compatible-map h → hom
  mkhom h c = h , mkIsHom c
```

#### Monomorphisms and epimorphisms

A **monomorphism** is an injective homomorphism and an **epimorphism** is a
surjective one.  Each comes in the two forms `hom`{.AgdaFunction} does:

+  the predicates `IsMon`{.AgdaRecord} and `IsEpi`{.AgdaRecord}, whose fields pair
   the homomorphism property with `IsInjective`{.AgdaFunction} or
   `IsSurjective`{.AgdaFunction};
+  the bundled types `mon`{.AgdaFunction} and `epi`{.AgdaFunction}, which pair a
   setoid function with such a proof.

Both predicates export a `HomReduct`{.AgdaFunction} that forgets the extra
condition, and `mon→hom`{.AgdaFunction} and `epi→hom`{.AgdaFunction} apply it to
the bundled forms.

`mon→intohom`{.AgdaFunction} and `epi→ontohom`{.AgdaFunction} regroup the same
data the other way, as a `hom`{.AgdaFunction} paired with the injectivity or the
surjectivity of its underlying map.  That regrouping earns a name because the two
resulting types are, by definition, `_IsSubalgebraOf_`{.AgdaFunction} of
[Setoid.Subalgebras.Basic][] and `_IsHomImageOf_`{.AgdaFunction} of
[Setoid.Homomorphisms.HomomorphicImages][]; so these are the functions that turn a
monomorphism into a subalgebra and an epimorphism into a homomorphic image.

```agda
  record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
    field
      isHom : IsHom h
      isInjective : IsInjective h

    HomReduct : hom
    HomReduct = h , isHom

  mon : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
  mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon

  mon→hom : mon → hom
  mon→hom h = IsMon.HomReduct (proj₂ h)

  record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
    field
      isHom : IsHom h
      isSurjective : IsSurjective h

    HomReduct : hom
    HomReduct = h , isHom

  epi : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
  epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi

  epi→hom : epi → hom
  epi→hom h = IsEpi.HomReduct (proj₂ h)

module _ {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ)(𝑩 : Algebra β ρᵇ) where
  open IsEpi
  open IsMon

  mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective (proj₁ h)
  mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

  epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective (proj₁ h)
  epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
```

Finally, we define the identity homomorphism for setoid algebras.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} where
  open Setoid 𝔻[ 𝑨 ]   using ( reflexive )

  𝒾𝒹 :  hom 𝑨 𝑨
  𝒾𝒹 = 𝑖𝑑 , mkIsHom (reflexive refl)
```
