---
layout: default
title : Structures.Homs.Records
date : 2021-06-22
author: [agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

module Structures.Homs.Records where

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

open import Structures.Records        using ( signature ; structure ; Sig∅
                                            ; Lift-struc ; compatible )


open structure
open signature

private variable 𝐹 𝑅 : signature

module _ {α ρᵃ : Level}
         (𝑨 : structure 𝐹 {α}𝑅 {ρᵃ})
         {β ρᵇ : Level}
         (𝑩 : structure 𝐹 {β}𝑅 {ρᵇ}) where

 private
  A = carrier 𝑨
  B = carrier 𝑩

 preserves : (symbol 𝑅) → (A → B) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 preserves 𝑟 h = ∀ a → ((rel 𝑨) 𝑟 a) → ((rel 𝑩) 𝑟) (h ∘ a)

 is-hom-rel : (A → B) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 is-hom-rel h = ∀ (r : symbol 𝑅) → preserves r h

 comm-op : (A → B) → (symbol 𝐹) → Type (α ⊔ β)
 comm-op h f = ∀ a → h (((op 𝑨) f) a) ≡ ((op 𝑩) f) (h ∘ a)

 is-hom-op : (A → B) → Type (α ⊔ β)
 is-hom-op h = ∀ f → comm-op h f

 is-hom : (A → B) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-hom h = is-hom-rel h × is-hom-op h

 hom : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 hom = Σ[ h ∈ (A → B) ] is-hom h


-- The special case when 𝑅 = ∅ (i.e., purely algebraic structures)
module _ {α : Level}{𝑨 : structure 𝐹 {α} Sig∅ {ℓ₀}}
         {β : Level}{𝑩 : structure 𝐹 {β} Sig∅ {ℓ₀}} where

 -- The type of homomorphisms from one algebraic structure to another.
 hom-alg : Type (α ⊔ β)
 hom-alg = Σ[ h ∈ ((carrier 𝑨) → (carrier 𝑩)) ] is-hom-op 𝑨 𝑩 h



module _ {α ρᵃ : Level}{𝑨 : structure 𝐹 {α} 𝑅 {ρᵃ}}
         {β ρᵇ : Level}{𝑩 : structure 𝐹 {β} 𝑅 {ρᵇ}}
         {γ ρᶜ : Level}{𝑪 : structure 𝐹 {γ} 𝑅 {ρᶜ}} where

 private
  A = carrier 𝑨
  B = carrier 𝑩
  C = carrier 𝑪

 ∘-is-hom-rel : (f : A → B)(g : B → C)
  →             is-hom-rel 𝑨 𝑩 f → is-hom-rel 𝑩 𝑪 g → is-hom-rel 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-rel f g fhr ghr R a = λ z → ghr R (λ z₁ → f (a z₁)) (fhr R a z)

 ∘-is-hom-op : (f : A → B)(g : B → C)
  →            is-hom-op 𝑨 𝑩 f → is-hom-op 𝑩 𝑪 g → is-hom-op 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-op f g fho gho 𝑓 a = cong g (fho 𝑓 a) ∙ gho 𝑓 (f ∘ a)

 ∘-is-hom : (f : A → B)(g : B → C)
  →         is-hom 𝑨 𝑩 f → is-hom 𝑩 𝑪 g → is-hom 𝑨 𝑪 (g ∘ f)
 ∘-is-hom f g fhro ghro = ihr , iho
  where
  ihr : is-hom-rel 𝑨 𝑪 (g ∘ f)
  ihr = ∘-is-hom-rel f g (fst fhro) (fst ghro)

  iho : is-hom-op 𝑨 𝑪 (g ∘ f)
  iho = ∘-is-hom-op f g (snd fhro) (snd ghro)

 ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪 → hom 𝑨 𝑪
 ∘-hom (f , fh) (g , gh) = g ∘ f , ∘-is-hom f g fh gh


module _ {α ρᵃ : Level}{𝑨 : structure 𝐹 {α}𝑅 {ρᵃ}} where
 𝒾𝒹 : hom 𝑨 𝑨
 𝒾𝒹 = id , (λ _ _ z → z)  , (λ _ _ → refl)


module _ {α ρᵃ : Level}{𝑨 : structure 𝐹 {α} 𝑅 {ρᵃ}}
         {β ρᵇ : Level}{𝑩 : structure 𝐹 {β} 𝑅 {ρᵇ}} where

 private
  A = carrier 𝑨
  B = carrier 𝑩

 is-mon : (A → B) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-mon g = is-hom 𝑨 𝑩 g × IsInjective g

 mon : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 mon = Σ[ g ∈ (A → B) ] is-mon g

 mon→hom : mon → hom 𝑨 𝑩
 mon→hom ϕ = (fst ϕ) , fst (snd ϕ )


 is-epi : (A → B) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-epi g = is-hom 𝑨 𝑩 g × IsSurjective g

 epi : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 epi = Σ[ g ∈ (A → B) ] is-epi g

 epi→hom : epi → hom 𝑨 𝑩
 epi→hom ϕ = (fst ϕ) , fst (snd ϕ)

module _ {𝑅 𝐹 : signature}{α ρᵃ : Level} where
 open Lift

 𝓁𝒾𝒻𝓉 : {ℓ : Level}{𝑨 : structure 𝐹 {α} 𝑅 {ρᵃ}} → hom 𝑨 (Lift-struc ℓ {𝑨})
 𝓁𝒾𝒻𝓉 = lift , (λ _ _ x → x) , λ _ _ → refl

 𝓁ℴ𝓌ℯ𝓇 : {ℓ : Level}{𝑨 : structure 𝐹 {α}𝑅 {ρᵃ}} → hom (Lift-struc ℓ {𝑨}) 𝑨
 𝓁ℴ𝓌ℯ𝓇 = lower , (λ _ _ x → x) , (λ _ _ → refl)

-- Kernels of homomorphisms


open ≡-Reasoning
module _ {α ρᵃ : Level}
         {β ρᵇ : Level}{𝑨 : structure 𝐹 {α} 𝑅 {β ⊔ ρᵃ}}{𝑩 : structure 𝐹 {β} 𝑅 {ρᵇ}}
         {wd : swelldef ℓ₀ β} where

 homker-comp : (h : hom 𝑨 𝑩) → compatible 𝑨 (ker ∣ h ∣)
 homker-comp (h , hhom) f {u}{v} kuv =
  h (((op 𝑨)f) u)    ≡⟨ ∥ hhom ∥ f u ⟩
  ((op 𝑩) f)(h ∘ u)  ≡⟨ wd ((op 𝑩)f) (h ∘ u) (h ∘ v) kuv ⟩
  ((op 𝑩) f)(h ∘ v)  ≡⟨ (∥ hhom ∥ f v)⁻¹ ⟩
  h (((op 𝑨)f) v)    ∎

 kerlift-comp : (h : hom 𝑨 𝑩) → compatible 𝑨 (kerlift ∣ h ∣ (α ⊔ ρᵃ) )
 kerlift-comp (h , hhom) f {u}{v} kuv = lift goal
  where
  goal : h (op 𝑨 f u) ≡ h (op 𝑨 f v)
  goal = h (op 𝑨 f u)    ≡⟨ snd hhom f u ⟩
         (op 𝑩 f)(h ∘ u) ≡⟨ wd (op 𝑩 f)(h ∘ u)(h ∘ v)(lower ∘ kuv) ⟩
         (op 𝑩 f)(h ∘ v) ≡⟨ (snd hhom f v)⁻¹ ⟩
         h (op 𝑨 f v)    ∎

 open import Structures.Congruences.Records

 kercon : hom 𝑨 𝑩 → con 𝑨
 kercon (h , hhom) = ((λ x y → Lift (α ⊔ ρᵃ) (h x ≡ h y)) , goal) , kerlift-comp (h , hhom)
  where
  goal : IsEquivalence (λ x y → Lift (α ⊔ ρᵃ) (h x ≡ h y))
  goal = record { refl = lift refl
                ; sym = λ p → lift (sym (lower p))
                ; trans = λ p q → lift (trans (lower p)(lower q)) }

 kerquo : hom 𝑨 𝑩 → structure 𝐹 {lsuc (α ⊔ β ⊔ ρᵃ)} 𝑅 {β ⊔ ρᵃ}
 kerquo h = 𝑨 ╱ (kercon h)

module _ {α ρᵃ β ρᵇ : Level}   where
 ker[_⇒_] : (𝑨 : structure 𝐹 {α} 𝑅 {β ⊔ ρᵃ} )(𝑩 : structure 𝐹{β} 𝑅 {ρᵇ} ){wd : swelldef ℓ₀ β}
  →         hom 𝑨 𝑩 → structure 𝐹 𝑅
 ker[_⇒_] 𝑨 𝑩 {wd} h = kerquo{ρᵃ = ρᵃ}{𝑨 = 𝑨}{𝑩}{wd = wd} h


-- Canonical projections

module _ {α ρᵃ : Level}{𝑨 : structure 𝐹 {α}𝑅 {ρᵃ} } where

 open Image_∋_
 open import Structures.Congruences.Records

 πepi : (θ : con 𝑨) → epi {𝑨 = 𝑨}{𝑩 = 𝑨 ╱ θ}
 πepi θ = (λ a → ⟪ a ⟫ {fst ∣ θ ∣}) , (γrel , (λ _ _ → refl)) , cπ-is-epic
  where
  γrel : is-hom-rel 𝑨 (𝑨 ╱ θ) (λ a → ⟪ a ⟫ {fst ∣ θ ∣})
  γrel R a x = x
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫ {fst ∣ θ ∣})
  cπ-is-epic (C , Relations.Quotients.R-block block-u refl) = eq block-u refl


 πhom : (θ : con 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi→hom {𝑨 = 𝑨} {𝑩 = (𝑨 ╱ θ)} (πepi θ)

module _ {α ρᵃ : Level}
         {β ρᵇ : Level}{𝑨 : structure 𝐹 {α} 𝑅 {β ⊔ ρᵃ}}{𝑩 : structure 𝐹 {β} 𝑅 {ρᵇ}}
         {wd : swelldef ℓ₀ β} where

 πker : (h : hom 𝑨 𝑩) → epi {𝑨 = 𝑨} {𝑩 = (ker[_⇒_]{ρᵃ = ρᵃ} 𝑨 𝑩 {wd = wd} h)}
 πker h = πepi (kercon{ρᵃ = ρᵃ} {𝑨 = 𝑨}{𝑩 = 𝑩}{wd = wd}  h)


open import Structures.Products.Records

module _ {α ρᵃ : Level}{𝑨 : structure 𝐹 {α}𝑅 {ρᵃ}}
         {ℓ : Level}{I : Type ℓ}
         {β ρᵇ : Level}{ℬ : I → structure 𝐹 {β}𝑅 {ρᵇ}} where

 ⨅-hom-co : funext ℓ β → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co fe h = ((λ a i → ∣ h i ∣ a)) , (λ R a x 𝔦 → fst ∥ h 𝔦 ∥ R a x) , (λ f a → fe (λ i → snd ∥ h i ∥ f a))


module _ {ℓ : Level}{I : Type ℓ}
         {α ρᵃ : Level}{𝒜 : I → structure 𝐹 {α}𝑅 {ρᵃ}}
         {β ρᵇ : Level}{ℬ : I → structure 𝐹 {β}𝑅 {ρᵇ}} where

 ⨅-hom : funext ℓ β → Π[ i ∈ I ] hom (𝒜 i)(ℬ i) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom fe h = (λ a i → ∣ h i ∣ (a i)) , (λ R a x 𝔦 → fst ∥ h 𝔦 ∥ R (λ z → a z 𝔦) (x 𝔦))
                                         , λ f a → fe (λ i → snd ∥ h i ∥ f (λ z → a z i))

module _ {ℓ : Level}{I : Type ℓ}
         {α ρᵃ : Level}{𝒜 : I → structure 𝐹 {α}𝑅 {ρᵃ}} where

 -- Projection out of products

 ⨅-projection-hom : Π[ i ∈ I ] hom (⨅ 𝒜) (𝒜 i)
 ⨅-projection-hom = λ x → (λ z → z x) , (λ R a z → z x)  , λ f a → refl

\end{code}

--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
