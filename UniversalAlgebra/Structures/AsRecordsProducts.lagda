---
layout: default
title : Sturctures.AsRecordsProducts module
date : 2021-05-11
author: [the ualib/agda-algebras development team][]
---

### Products for structures as records

This module is similar to Products.lagda but for structures represented using records rather than
dependent pair type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

open import Structures.AsRecordsBasic

module Structures.AsRecordsProducts where


open import Agda.Primitive         using    ( _⊔_   ;  lsuc     )
                                   renaming ( Set   to Type     )
open import Data.Product           using    ( _,_   ;  Σ-syntax
                                            ; Σ                 )
open import Level                  using    ( Level             )
open import Relation.Unary         using    ( _∈_   ;  Pred     )

open import Overture.Preliminaries using    ( ∣_∣   ; Π-syntax
                                            ; Π                 )
private variable 𝐹 𝑅 : signature

module _ {α ρ ℓ : Level} where

 ⨅ : {ℑ : Type ℓ}(𝒜 : ℑ → structure 𝐹 {α} 𝑅 {ρ} ) → structure 𝐹 {α ⊔ ℓ} 𝑅 {ρ ⊔ ℓ}
 ⨅ {ℑ = ℑ} 𝒜 = record { carrier = Π[ i ∈ ℑ ] carrier (𝒜 i)            -- domain of the product structure
                 ; op = λ 𝑓 a i → (op (𝒜 i) 𝑓) λ x → a x i       -- interpretation of  operations
                 ; rel = λ r a → ∀ i → (rel (𝒜 i) r) λ x → a x i -- interpretation of relations
                 }


module _ {α ρ ℓ : Level}
         {𝒦 : Pred (structure 𝐹 {α} 𝑅 {ρ}) ℓ} where

  ℓp : Level
  ℓp = lsuc (α ⊔ ρ) ⊔ ℓ

  ℑ : Type ℓp
  ℑ = Σ[ 𝑨 ∈ structure 𝐹 {α} 𝑅 {ρ}] 𝑨 ∈ 𝒦

  𝔄 : ℑ → structure 𝐹 {α} 𝑅 {ρ}
  𝔄 𝔦 = ∣ 𝔦 ∣

  class-product : structure 𝐹 𝑅
  class-product = ⨅ 𝔄

\end{code}

--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

















-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Unary using (Pred; _∈_)

-- Imports from the Agda Universal Algebra Library
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)
-- open import Algebras.Basic


-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Binary.PropositionalEquality.Core using (trans)

-- open import Agda.Primitive using (_⊔_; lsuc)
-- open import Relation.Unary using (Pred; _∈_)

-- open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax;  i0; i1; fst; snd; _,_)
-- open import Cubical.Foundations.Prelude using (refl; sym; _∙_; funExt; cong; _∎; _≡⟨_⟩_)
-- open import Cubical.Foundations.Function using (_∘_)
-- open import Cubical.Data.Sigma.Base using (_×_)

-- -- Imports from the Agda Universal Algebra Library
-- open import overture.preliminaries using (Π; Π-syntax; _⁻¹; id; ∣_∣)
-- open import structures.basic using (Signature; Structure; _ʳ_; _ᵒ_; signature; structure)
-- open import overture.inverses using (IsInjective; IsSurjective)
-- open import relations.discrete using (ker)


