---
layout: default
title : Structures.Products module
date : 2021-05-11
author: [the ualib/agda-algebras development team][]
---

### Product structures

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}



module Structures.Products where

open import Agda.Primitive        using    (  _⊔_ ;  lsuc    )
                                  renaming (  Set   to Type  )
open import Data.Product          using    (  _,_ ; Σ ; _×_  ;
                                              Σ-syntax       )
open import Level                 using    (  Level ; Lift   )
open import Relation.Unary        using    (  ∅ ; _∈_ ; Pred )

open import Overture.Preliminaries using ( ∣_∣ ; ∥_∥ ; Π ; Π-syntax )
open import Structures.Basic       using ( Signature ; Structure ; _ʳ_ ; _ᵒ_ )


private variable
 𝑅 𝐹 : Signature
 α ρ ι : Level

⨅ : {ℑ : Type ι}(𝒜 : ℑ → Structure  𝑅 𝐹{α}{ρ}) → Structure 𝑅 𝐹 {α ⊔ ι} {ρ ⊔ ι}
⨅ {ℑ = ℑ} 𝒜 = Π[ 𝔦 ∈ ℑ ] ∣ 𝒜 𝔦 ∣ ,                     -- domain of the product structure
         ( λ r a → ∀ 𝔦 → (r ʳ 𝒜 𝔦) λ x → a x 𝔦 ) , -- interpretations of relations
         ( λ 𝑓 a 𝔦 → (𝑓 ᵒ 𝒜 𝔦) λ x → a x 𝔦 )        -- interpretations of  operations

module _ {α ρ τ : Level}{𝒦 : Pred (Structure 𝑅 𝐹 {α}{ρ}) τ} where

 ℓp : Level
 ℓp = lsuc (α ⊔ ρ) ⊔ τ

 ℑ : Type ℓp
 ℑ = Σ[ 𝑨 ∈ Structure 𝑅 𝐹 ] (𝑨 ∈ 𝒦)

 𝔖 : ℑ → Structure 𝑅 𝐹        -- (type \MfS to get 𝔖)
 𝔖 𝔦 = ∣ 𝔦 ∣

 class-prod : Structure 𝑅 𝐹
 class-prod = ⨅ 𝔖

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.


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


