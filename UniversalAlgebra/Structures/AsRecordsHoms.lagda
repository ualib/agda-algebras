---
layout: default
title : Structures.AsRecordsHoms
date : 2021-06-22
author: [the ualib/agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

module Structures.AsRecordsHoms where

open import Axiom.Extensionality.Propositional using () renaming (Extensionality to funext)
open import Agda.Builtin.Equality  using    ( _≡_   ;  refl     )
open import Agda.Primitive         using    (  _⊔_  ;  lsuc     )
                                   renaming (  Set  to Type     )
open import Data.Product           using    (  _,_  ;  Σ
                                            ;  _×_  ;  Σ-syntax )
                                   renaming ( proj₁ to fst
                                            ; proj₂ to snd      )
open import Level                  using    ( Level ;  Lift
                                            ; lift  ;  lower    )
                                   renaming ( zero  to ℓ₀       )
open import Function.Base          using    ( _∘_   ;  id       )
open import Relation.Binary        using    ( IsEquivalence     )
open import Relation.Binary.PropositionalEquality
                                   using    ( cong  ; module ≡-Reasoning
                                            ; sym   ; trans )




open import Overture.Preliminaries    using ( ℓ₁ ; ∣_∣ ; ∥_∥ ; _⁻¹ ; _∙_ ; 𝑖𝑑 ; Π ; Π-syntax)
open import Overture.Inverses         using ( IsInjective ; IsSurjective ; Image_∋_)
open import Relations.Discrete        using ( ker ; kerlift )
open import Relations.Quotients       using ( Equivalence ; Quotient
                                            ; 0[_]Equivalence ; ker-IsEquivalence
                                            ; kerlift-IsEquivalence ; ⟪_⟫ ; ⌞_⌟
                                            ; ⟪_∼_⟫-elim ; _/_ )
open import Relations.Extensionality  using ( swelldef )

open import Structures.AsRecordsBasic using ( signature ; structure ; Sig∅
                                            ; Lift-structure ; compatible )


private variable  α β γ ρ ρ₀ ρ₁ ρ₂ : Level

open structure
open signature

-- module _ {γ : Level} (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹){𝑩 : structure {β} 𝑅 {ρ₁} 𝐹}(𝑪 : structure {γ} 𝑅 {ρ₂} 𝐹) where

module _ {𝑅 𝐹 : signature}(𝑨 : structure {α} {ρ₀} 𝑅 𝐹)(𝑩 : structure {β} {ρ₁} 𝑅 𝐹) where

 comm-rel : (symbol 𝑅) → ((carrier 𝑨) → (carrier 𝑩)) → Type (α ⊔ ρ₀ ⊔ ρ₁)
 comm-rel 𝑟 h = ∀ a → ((rel 𝑨) 𝑟 a) → ((rel 𝑩) 𝑟) (h ∘ a)

 is-hom-rel : ((carrier 𝑨) → (carrier 𝑩)) → Type (α ⊔ ρ₀ ⊔ ρ₁)
 is-hom-rel h = ∀ R →  comm-rel R h

 comm-op : (symbol 𝐹) → ((carrier 𝑨) → (carrier 𝑩)) → Type (α ⊔ β)
 comm-op f h = ∀ a → h (((op 𝑨) f) a) ≡ ((op 𝑩) f) (h ∘ a)

 is-hom-op : ((carrier 𝑨) → (carrier 𝑩)) → Type (α ⊔ β)
 is-hom-op h = ∀ f → comm-op f h

 is-hom : ((carrier 𝑨) → (carrier 𝑩)) → Type (α ⊔ ρ₀ ⊔ β ⊔ ρ₁)
 is-hom h = is-hom-rel h × is-hom-op h

 hom : Type (α ⊔ ρ₀ ⊔ β ⊔ ρ₁)
 hom = Σ[ h ∈ ((carrier 𝑨) → (carrier 𝑩)) ] is-hom h

-- EXAMPLE.  The special case when 𝑅 = ∅ (i.e., purely algebraic structures)
module _ {𝐹 : signature}(𝑨 : structure {α} {ρ₀} Sig∅ 𝐹)(𝑩 : structure {β} {ρ₁} Sig∅ 𝐹) where

 -- The type of homomorphisms from one algebraic structure to another.
 hom-alg : Type (α ⊔ β)
 hom-alg = Σ[ h ∈ ((carrier 𝑨) → (carrier 𝑩)) ] is-hom-op 𝑨 𝑩 h


module _ {𝑅 𝐹 : signature} (𝑨 : structure {α} {ρ₀} 𝑅 𝐹){𝑩 : structure {β} {ρ₁} 𝑅 𝐹}(𝑪 : structure {γ} {ρ₂} 𝑅 𝐹) where

 ∘-is-hom-rel : {f : (carrier 𝑨) → (carrier 𝑩)}{g : (carrier 𝑩) → (carrier 𝑪)}
  →             is-hom-rel 𝑨 𝑩 f → is-hom-rel 𝑩 𝑪 g → is-hom-rel 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-rel {f}{g} fhr ghr R a = λ z → ghr R (λ z₁ → f (a z₁)) (fhr R a z)

 ∘-is-hom-op : {f : (carrier 𝑨) → (carrier 𝑩)}{g : (carrier 𝑩) → (carrier 𝑪)}
  →            is-hom-op 𝑨 𝑩 f → is-hom-op 𝑩 𝑪 g → is-hom-op 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-op {f}{g} fho gho 𝑓 a = cong g (fho 𝑓 a) ∙ gho 𝑓 (f ∘ a)

 ∘-is-hom : {f : (carrier 𝑨) → (carrier 𝑩)}{g : (carrier 𝑩) → (carrier 𝑪)}
  →         is-hom 𝑨 𝑩 f → is-hom 𝑩 𝑪 g → is-hom 𝑨 𝑪 (g ∘ f)
 ∘-is-hom {f} {g} fhro ghro = ihr , iho
  where
  ihr : is-hom-rel 𝑨 𝑪 (g ∘ f)
  ihr = ∘-is-hom-rel {f}{g} (fst fhro) (fst ghro)

  iho : is-hom-op 𝑨 𝑪 (g ∘ f)
  iho = ∘-is-hom-op {f}{g} (snd fhro) (snd ghro)

 ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
 ∘-hom (f , fh) (g , gh) = g ∘ f , ∘-is-hom {f}{g} fh gh


module _ {𝑅 𝐹 : signature} where -- (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹){𝑩 : structure {β} 𝑅 {ρ₁} 𝐹}(𝑪 : structure {γ} 𝑅 {ρ₂} 𝐹) where
 𝒾𝒹 : (𝑨 : structure {α} {ρ} 𝑅 𝐹) → hom 𝑨 𝑨
 𝒾𝒹 _ = id , (λ R a z → z)  , (λ f a → refl)  -- (λ R a → refl)

module _ {𝑅 𝐹 : signature} (𝑨 : structure {α} {ρ₀} 𝑅 𝐹)(𝑩 : structure {β} {ρ₁} 𝑅 𝐹) where

 is-mon : ((carrier 𝑨) → (carrier 𝑩)) → Type (α ⊔ ρ₀ ⊔ β ⊔ ρ₁)
 is-mon g = is-hom 𝑨 𝑩 g × IsInjective g

 mon : Type (α ⊔ ρ₀ ⊔ β ⊔ ρ₁)
 mon = Σ[ g ∈ ((carrier 𝑨) → (carrier 𝑩)) ] is-mon g

 mon→hom : mon → hom 𝑨 𝑩
 mon→hom ϕ = (fst ϕ) , fst (snd ϕ )


 is-epi : ((carrier 𝑨) → (carrier 𝑩)) → Type (α ⊔ ρ₀ ⊔ β ⊔ ρ₁)
 is-epi g = is-hom 𝑨 𝑩 g × IsSurjective g

 epi : Type (α ⊔ ρ₀ ⊔ β ⊔ ρ₁)
 epi = Σ[ g ∈ ((carrier 𝑨) → (carrier 𝑩)) ] is-epi g

 epi→hom : epi → hom 𝑨 𝑩
 epi→hom ϕ = (fst ϕ) , fst (snd ϕ)

module _ {𝑅 𝐹 : signature} where
 open Lift

 𝓁𝒾𝒻𝓉 : {𝑨 : structure {α} {ρ} 𝑅 𝐹} → hom 𝑨 (Lift-structure 𝑨 β)
 𝓁𝒾𝒻𝓉 = lift , (λ R a x → x) , λ f a → refl

 𝓁ℴ𝓌ℯ𝓇 : {α β : Level}{𝑨 : structure {α} {ρ} 𝑅 𝐹} → hom (Lift-structure 𝑨 β) 𝑨
 𝓁ℴ𝓌ℯ𝓇 = lower , (λ R a x → x) , (λ f a → refl)

-- Kernels of homomorphisms


open ≡-Reasoning
module _ {𝑅 𝐹 : signature} {wd : swelldef ℓ₀ β}{𝑨 : structure {α} {β ⊔ ρ₀} 𝑅 𝐹}{𝑩 : structure {β} {ρ₁} 𝑅 𝐹} where

 homker-comp : (h : hom 𝑨 𝑩) → compatible 𝑨 (ker (fst h))
 homker-comp h f {u}{v} kuv = ((fst h) (((op 𝑨)f) u))  ≡⟨(snd (snd h)) f u ⟩
                              ((op 𝑩) f)((fst h) ∘ u) ≡⟨ wd ((op 𝑩)f) ((fst h) ∘ u) ((fst h) ∘ v) kuv ⟩
                              ((op 𝑩) f)((fst h) ∘ v) ≡⟨((snd (snd h)) f v)⁻¹ ⟩
                              (fst h)(((op 𝑨)f) v)   ∎

 kerlift-comp : (h : hom 𝑨 𝑩) → compatible 𝑨 (kerlift (fst h) (α ⊔ ρ₀) )
 kerlift-comp (h , hhom) f {u}{v} kuv = lift goal
  where
  goal : h (op 𝑨 f u) ≡ h (op 𝑨 f v)
  goal = h (op 𝑨 f u)    ≡⟨ snd hhom f u ⟩
         (op 𝑩 f)(h ∘ u) ≡⟨ wd (op 𝑩 f)(h ∘ u)(h ∘ v)(lower ∘ kuv) ⟩
         (op 𝑩 f)(h ∘ v) ≡⟨ (snd hhom f v)⁻¹ ⟩
         h (op 𝑨 f v)    ∎

 open import Structures.AsRecordsCongruences --  {𝑅 = 𝑅}{𝐹 = 𝐹}

 kercon : hom 𝑨 𝑩 → con 𝑨
 kercon (h , hhom) = ((λ x y → Lift (α ⊔ ρ₀) (h x ≡ h y)) , goal) , kerlift-comp (h , hhom)
  where
  goal : IsEquivalence (λ x y → Lift (α ⊔ ρ₀) (h x ≡ h y))
  goal = record { refl = lift refl
                ; sym = λ p → lift (sym (lower p))
                ; trans = λ p q → lift (trans (lower p)(lower q)) }

 kerquo : hom 𝑨 𝑩 → structure {lsuc (α ⊔ β ⊔ ρ₀)} {β ⊔ ρ₀} 𝑅 𝐹
 kerquo h = 𝑨 ╱ (kercon h)

module _ {𝑅 𝐹 : signature}{ρ₀ : Level}   where
 ker[_⇒_] : (𝑨 : structure {α} {β ⊔ ρ₀} 𝑅 𝐹)(𝑩 : structure {β} {ρ₁} 𝑅 𝐹){wd : swelldef ℓ₀ β}
  →         hom 𝑨 𝑩 → structure 𝑅 𝐹
 ker[_⇒_] 𝑨 𝑩 {wd} h = kerquo{ρ₀ = ρ₀}{wd = wd}{𝑨}{𝑩 = 𝑩} h


-- Canonical projections

module _ {𝑅 𝐹 : signature}{𝑨 : structure {α} {ρ} 𝑅 𝐹} where

 open Image_∋_
 open import Structures.AsRecordsCongruences

 πepi : (θ : con 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = (λ a → ⟪ a ⟫ {fst ∣ θ ∣}) , (γrel , (λ _ _ → refl)) , cπ-is-epic
  where
  γrel : is-hom-rel 𝑨 (𝑨 ╱ θ) (λ a → ⟪ a ⟫ {fst ∣ θ ∣})
  γrel R a x = x
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫ {fst ∣ θ ∣})
  cπ-is-epic (C , Relations.Quotients.R-block block-u refl) = eq block-u refl


 πhom : (θ : con 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi→hom 𝑨 (𝑨 ╱ θ) (πepi θ)

module _ {𝑅 𝐹 : signature}{wd : swelldef ℓ₀ β}{𝑨 : structure {α} {β ⊔ ρ₀} 𝑅 𝐹}{𝑩 : structure {β} {ρ₁} 𝑅 𝐹} where

 πker : (h : hom 𝑨 𝑩) → epi 𝑨 (ker[_⇒_]{ρ₀ = ρ₀} 𝑨 𝑩 {wd} h)
 πker h = πepi (kercon{ρ₀ = ρ₀} {wd = wd} {𝑨}{𝑩} h)

module _ {𝑅 𝐹 : signature}{I : Type }(ℬ : I → structure {β} {ρ₁} 𝑅 𝐹) where

 open import Structures.AsRecordsProducts

 ⨅-hom-co : funext ℓ₀ β → {α : Level}(𝑨 : structure {α} {ρ₀} 𝑅 𝐹) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ I ℬ)
 ⨅-hom-co fe 𝑨 h = ((λ a i → ∣ h i ∣ a)) , (λ R a x 𝔦 → fst ∥ h 𝔦 ∥ R a x) , (λ f a → fe (λ i → snd ∥ h i ∥ f a))

 ⨅-hom : funext ℓ₀ β → {α : Level}(𝒜 : I → structure {α} {ρ₀} 𝑅 𝐹) → Π[ i ∈ I ] hom (𝒜 i)(ℬ i) → hom (⨅ I 𝒜)(⨅ I ℬ)
 ⨅-hom fe 𝒜 h = (λ a i → ∣ h i ∣ (a i)) , (λ R a x 𝔦 → fst ∥ h 𝔦 ∥ R (λ z → a z 𝔦) (x 𝔦))
                                         , λ f a → fe (λ i → snd ∥ h i ∥ f (λ z → a z i))
-- Projection out of products

 ⨅-projection-hom : Π[ i ∈ I ] hom (⨅ I ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , (λ R a z → z x)  , λ f a → refl

\end{code}

--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
