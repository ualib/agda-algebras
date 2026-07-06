---
layout: default
file: "src/Setoid/Subalgebras/Subdirect/BirkhoffSI.lagda.md"
title: "Setoid.Subalgebras.Subdirect.BirkhoffSI module (The Agda Universal Algebra Library)"
date: "2026-06-20"
author: "the agda-algebras development team"
---

### Birkhoff's subdirect representation theorem

This is the [Setoid.Subalgebras.Subdirect.BirkhoffSI][] module of the
[Agda Universal Algebra Library][].

Birkhoff's SI theorem asserts that every algebra is a subdirect product of
subdirectly irreducible algebras; this manifests as a family of SI algebras and a
subdirect embedding into their product.

This module proves the **choice-free core** in full.

+  *The bridge* — a family of congruences `θ : I → Con 𝑨` whose meet is the diagonal
   (`θ` *separates points*) induces a subdirect embedding `𝑨 ↪ ⨅ (λ i → 𝑨 ╱ θ i)`,
   with injectivity *exactly* the separation hypothesis and the coordinate
   projections surjective because they are the canonical quotient maps.
+  *The reduction of Birkhoff to existence* — given a subdirect SI-representation of
   `𝑨` (a separating family whose quotients are all subdirectly irreducible), `𝑨` is
   a subdirect product of subdirectly irreducible algebras.

What is **not** choice-free is the *existence* of a subdirect SI-representation for an
arbitrary algebra.  Indeed, for each pair `a ≢ b` one needs a congruence maximal
among those not relating `a , b` (it is completely meet-irreducible, so its quotient
is subdirectly irreducible); this is chosen by Zorn's lemma, which is incompatible with
a postulate-free, `--safe` formalization.  In the present module, we take that
existence as an explicit module parameter (`SubdirectSIRep`), so the theorem is
proved *relative to* a precisely-stated assumption and nothing is postulated.[^1]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Subalgebras.Subdirect.BirkhoffSI {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Product     using ( _×_ ; _,_ ; Σ-syntax )
open import Level            using ( Level ; _⊔_ )  renaming ( suc to lsuc )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Algebras                     {𝑆 = 𝑆}  using  ( Algebra )
open import Setoid.Congruences                  {𝑆 = 𝑆}  using  ( Con ; _╱_ )
open import Setoid.Congruences.Monolith         {𝑆 = 𝑆} using ( IsSubdirectlyIrreducible )
open import Setoid.Subalgebras.Subdirect.Basic  {𝑆 = 𝑆}
  using ( SubdirectEmbedding ; Separates ; separating→SubdirectEmbedding )

private variable α ρ ℓ ι : Level
```
-->

```agda
SubdirectlyRepresentable : (𝑨 : Algebra α ρ) (ℓ ι : Level) → Type (𝓞 ⊔ 𝓥  ⊔ ρ ⊔ lsuc (α ⊔ ℓ ⊔ ι))
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
  Σ[ I ∈ Type ι ] Σ[ θ ∈ (I → Con 𝑨 ℓ) ] (Separates θ × ∀ i → IsSubdirectlyIrreducible (𝑨 ╱ θ i))
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

-------------------------------

[^1]: This is called "option (a)" in the design brief `docs/notes/m6-2-subdirect.md`; that document also describes alternatives (finite/decidable search, and the rationale) to be explored in other submodules of [Setoid.Subalgebras.Subdirect](/Setoid/Subalgebras/Subdirect/).
