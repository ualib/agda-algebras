---
layout: default
title : Structures.Congruences module
date : 2021-05-12
author: [the ualib/agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}


module Structures.Congruences where

open import Agda.Builtin.Equality  using    ( _≡_      ; refl    )
open import Agda.Primitive         using    (  _⊔_ ;  lsuc    )
                                   renaming (  Set   to Type  )
open import Data.Product           using    (  _,_ ; Σ ; _×_  ;
                                               Σ-syntax       )
                                   renaming ( proj₁ to fst )
open import Level                  using    ( Level    ;   Lift
                                            ; lift     ;   lower )
                                   renaming ( zero to ℓ₀ )
open import Function.Base          using    ( _∘_ ) -- ; id     )
open import Relation.Unary         using    (  ∅ ; _∈_ ; Pred )
open import Relation.Binary        using    ( IsEquivalence   )
                                   renaming ( Rel   to BinRel )
open import Overture.Preliminaries using ( ∣_∣ ; ∥_∥ ; Π ; Π-syntax )
open import Structures.Basic       using ( Signature ; Structure ; _ʳ_ ; _ᵒ_ ; Compatible)
open import Relations.Discrete     using ( _|:_ ; 0[_])
open import Relations.Quotients    using ( Equivalence ; 0[_]Equivalence ; Quotient
                                         ; ⟪_⟫ ; ⌞_⌟ ; ⟪_∼_⟫-elim ; _/_ )
open import Relations.Extensionality using ( swelldef )

private variable 𝑅 𝐹 : Signature
--  α ρ τ 𝓥 : Level
--  

module _ {α ρ : Level} where

 Con : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → Type (lsuc (α ⊔ ρ))
 Con 𝑨 = Σ[ θ ∈ Equivalence ∣ 𝑨 ∣{α ⊔ ρ} ] (Compatible 𝑨 ∣ θ ∣)

 -- Example. The zero congruence of a structure.
 0[_]Compatible : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → swelldef ℓ₀ α → (𝑓 : ∣ 𝐹 ∣) → (𝑓 ᵒ 𝑨) |: (0[ ∣ 𝑨 ∣ ]{ρ})
 0[ 𝑨 ]Compatible wd 𝑓 {i}{j} ptws0  = lift γ
  where
  γ : (𝑓 ᵒ 𝑨) i ≡ (𝑓 ᵒ 𝑨) j
  γ = wd (𝑓 ᵒ 𝑨) i j (lower ∘ ptws0)

 0Con[_] : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → swelldef ℓ₀ α → Con 𝑨
 0Con[ 𝑨 ] wd = 0[ ∣ 𝑨 ∣ ]Equivalence , 0[ 𝑨 ]Compatible wd

\end{code}

#### Quotient structures

\begin{code}

 _╱_ : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → Con 𝑨 → Structure 𝑅 𝐹 {lsuc (α ⊔ ρ)}{ρ}

 𝑨 ╱ θ = (Quotient (∣ 𝑨 ∣) {α ⊔ ρ} ∣ θ ∣)        -- domain of quotient structure
          , (λ r x → (r ʳ 𝑨) λ i → ⌞ x i ⌟)      -- interpretation of relations
          , λ f b → ⟪ (f ᵒ 𝑨) (λ i → ⌞ b i ⌟)  ⟫ -- interp of operations

 /≡-elim : {𝑨 : Structure 𝑅 𝐹 {α}{ρ}}( (θ , _ ) : Con 𝑨){u v : ∣ 𝑨 ∣}
  →    ⟪ u ⟫{∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v
 /≡-elim θ {u}{v} x =  ⟪ u ∼ v ⟫-elim {R = ∣ θ ∣} x

\end{code}

Example. The zero congruence of an arbitrary structure.

\begin{code}

 𝟘[_╱_] : (𝑨 : Structure 𝑅 𝐹 {α}{ρ})(θ : Con 𝑨) → BinRel (∣ 𝑨 ∣ / (fst ∣ θ ∣)) (lsuc (α ⊔ ρ))
 𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

𝟎[_╱_] : {α ρ : Level}(𝑨 : Structure 𝑅 𝐹 {α}{ρ})(θ : Con 𝑨) → swelldef ℓ₀ (lsuc (α ⊔ ρ)) → Con (𝑨 ╱ θ)
𝟎[ 𝑨 ╱ θ ] wd = 0[ ∣ 𝑨 ╱ θ ∣ ]Equivalence , 0[ 𝑨 ╱ θ ]Compatible wd

\end{code}

--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

















<!-- NO LONGER NEEDED ----------------------------------------------------------

-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Agda.Builtin.Equality using (_≡_; refl)
-- open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Unary using (Pred; _∈_)
-- open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)

-- -- Imports from the Agda Universal Algebra Library
-- open import Algebras.Basic
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; ∣_∣; ∥_∥; fst)
-- open import Relations.Discrete using (𝟎; _|:_)
-- open import Relations.Quotients using (_/_; ⟪_⟫)

--------------------------------------------------------------------------------- -->
open _/ₜ_

_╱ₜ_ : (𝑩 : Structure 𝑅 𝐹 {β}) → Con{α} 𝑩 → Structure 𝑅 𝐹

𝑩 ╱ₜ θ = (∣ 𝑩 ∣ /ₜ ∣ fst θ ∣)                                    -- domain of the quotient algebra
, rel -- basic relations of the quotient structure
, op        -- basic operations of the quotient algebra
where
rel : (r : ∣ 𝑅 ∣)(b : ∥ 𝑅 ∥ r → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣) → Type ?
rel r b = ?
-- (λ 𝑟 [ x ] → ((𝑟 ʳ 𝑩) λ i → ∣ fst θ ∣ (x i)))
op : (f : ∣ 𝐹 ∣)(b : ∥ 𝐹 ∥ f → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣) → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣
op f b = ? -- λ 𝑓 [ 𝑎 ] → [ ((𝑓 ᵒ 𝑩)(λ i →  𝑎 i)) ]  

record IsMinBin {A : Type α} (_≣_ : BinRel A ℓ₀ ) : Typeω where -- (α ⊔ ρ) where
 field
   isequiv : IsEquivalence{α}{ℓ₀} _≣_
   ismin : {ρ' : Level}(_≋_ : BinRel A ρ'){x y : A} → x ≣ y → x ≋ y

 reflexive : _≡_ ⇒ _≣_
 reflexive refl = IsEquivalence.refl isequiv

 corefl : _≣_ ⇒ _≡_
 corefl x≣y = ismin _≡_ x≣y


-- 𝟎 : (A : Type α) → BinRel A α
-- 𝟎 A = _≡_

 𝟎-comp→𝟎-lift-comp' : {ρ : Level} → swelldef (α ⊔ ρ) → Compatible 𝑨 _≡_ → Compatible (Lift-struc 𝑨 ρ) _≡_
 𝟎-comp→𝟎-lift-comp' {ρ = ρ} wd compA 𝑓 {u}{v} uv = goal
  where
  goal : (𝑓 ᵒ Lift-struc 𝑨 ρ) u ≡ (𝑓 ᵒ Lift-struc 𝑨 ρ) v
  goal = wd (𝑓 ᵒ Lift-struc 𝑨 ρ) u v uv

 𝟎-compatible-op' : swelldef α → (𝑓 : ∣ 𝐹 ∣) → compatible-op (𝑓 ᵒ 𝑨) _≡_
 𝟎-compatible-op' wd 𝑓 u v uv = wd (𝑓 ᵒ 𝑨) u v uv

 -- 𝟘 : {ρ : Level} → swelldef α → swelldef (α ⊔ ρ) → Con{ α ⊔ ρ }{ β } (Lift-struc 𝑨 ρ)
 -- 𝟘 {ρ = ρ} wd0 wd = 𝟎-Equivalence , goal
 --  where
 --  goal : compatible (Lift-struc 𝑨 ρ) (𝟎 ∣ Lift-struc 𝑨 ρ ∣)
 --  goal 𝑓 {u}{v} uv = 𝟎-comp→𝟎-lift-comp' wd (𝟎-compatible-op' wd0) 𝑓 u v uv


-- module _ {α ρ : Level}{wd : swelldef α}{wd' : swelldef ρ}  where

 -- 𝟎[_╱_] : (𝑨 : Structure 𝑅 𝐹)(θ : Con 𝑨) → Con (𝑨 ╱ θ)
 -- 𝟎[ 𝑨 ╱ θ ] = ( R , Reqiv) , {!!}
 --  where
 --  R : BinRel ∣ 𝑨 ╱ θ ∣ ρ
 --  R (x₁ , x₂) (y₁ , y₂) = x₁ ⊆ y₁ × y₁ ⊆ x₁
 --  Reqiv : IsEquivalence R
 --  Reqiv = record { refl = (λ z → z) , (λ z → z) ; sym = λ Rxy → snd Rxy , fst Rxy ; trans = λ Rij Rjk → (⊑-trans {!!} {!!} {!!} {!!}) , (⊑-trans fst {!!} {!!} {!!}) }
 --  goal : compatible (𝑨 ╱ θ) ∣ {!!} , {!!} ∣ -- compatible (Lift-struc 𝑨 {!!}) (𝟎 ∣ Lift-struc 𝑨 {!!} ∣)
 --  goal 𝑓 {u}{v} uv = {!!} -- 𝟎-comp→𝟎-lift-comp' wd (𝟎-compatible-op' wd) 𝑓 u v uv
-- ⊆-trans : Transitive (_⊆_ {A = A} {ℓ})
-- ⊆-trans P⊆Q Q⊆R x∈P = Q⊆R (P⊆Q x∈P)

 -- 𝟘 : funext ℓ₀ α → Con 𝑨
 -- 𝟘 fe = 𝟎-Equivalence , 𝟎-compatible fe --   IsCongruence→Con 𝟎 Δ
-- 𝑨 ╱ θ : Structure 𝑅 𝐹 {α ⊔ lsuc ρ}{ρ}
