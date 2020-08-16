-- FILE: basic.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020
-- Note: This was used for the second part of my talk at JMM Special Session.

{-# OPTIONS --without-K --exact-split --safe #-}

module basic where

-- modules that import basic:
-- congruences, homomorphisms, terms, subuniverses, closure, birkhoff

open import prelude using (Universe; 𝓘; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; 𝓧; 𝓤ω; Σω; _⸲_;
  _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; _×_; Π; _≡_; Epic; Pred; _∈_) public

--The type of operations
Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Op I A = (I → A) → A

--Example. the projections
π : {I : 𝓥 ̇ } {A : 𝓤 ̇ } → I → Op I A
π i x = x i

--𝓞 is the universe in which operation symbols live
--𝓥 is the universe in which arities live
Signature : (𝓞 𝓥 : Universe) → (𝓞 ⊔ 𝓥) ⁺ ̇
Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇ )
-- -Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-- -Σ X Y = Σ Y

Algebra : (𝓤 : Universe){𝓞 𝓥 : Universe}
 →        (𝑆 : Signature 𝓞 𝓥) →  𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
Algebra 𝓤 {𝓞}{𝓥} 𝑆 = Σ A ꞉ 𝓤 ̇ , ((f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A)

--The type of operations
-- BigOp : 𝓥 ̇ → 𝓤ω → _
-- BigOp I A = (I → A) → A


--𝓞 is the universe in which operation symbols live
--𝓥 is the universe in which arities live
-- BigSignature : (𝓞 𝓥 : Universe) → 𝓞 ⁺ ⊔ 𝓥 ⁺ ̇
-- BigSignature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇  , ( F → 𝓥 ̇ )

-- data monoid-op : 𝓤₀ ̇ where
--  e : monoid-op
--  · : monoid-op

-- monoid-sig : Signature _ _
-- monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }


module _ {𝑆 : Signature 𝓞 𝓥}  where

 _̂_ : (f : ∣ 𝑆 ∣)
  →   (𝑨 : Algebra 𝓤 𝑆)
  →   (∥ 𝑆 ∥ f  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 f ̂ 𝑨 = λ x → (∥ 𝑨 ∥ f) x

 ⨅ : {I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓤 ⊔ 𝓘) 𝑆
 ⨅ {I = I} 𝒜 = ((i : I) → ∣ 𝒜 i ∣) ,
                 λ  (f : ∣ 𝑆 ∣)
                    (proj : ∥ 𝑆 ∥ f → (j : I) → ∣ 𝒜 j ∣)
                    (i : I)
                  → (f ̂ 𝒜 i) λ {args → proj args i}

 -- ⨅' : (𝒜 : (𝓢 : Universe)(I : 𝓢 ̇) → Algebra 𝓢 𝑆 ) →  𝓤ω
 -- ⨅' 𝒜 = ((𝓣 : Universe)(J : 𝓣 ̇) →  ∣ 𝒜 𝓣 J ∣)
 ⨅' : (𝒜 : (𝓢 : Universe) → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓢 ⁺) 𝑆 ) →  𝓤ω
 ⨅' 𝒜 = ((𝓣 : Universe) →  ∣ 𝒜 𝓣 ∣)

 -- Ops : (𝒜 : (𝓢 : Universe)(I : 𝓢 ̇) → Algebra 𝓢 𝑆 ) → {!!}
 -- Ops 𝒜 = λ (f : ∣ 𝑆 ∣)
 --           (proj : ∥ 𝑆 ∥ f → (𝓢 : Universe)(I : 𝓢 ̇) → ∣ 𝒜 𝓢 I ∣)
 --           (𝓣 : Universe)
 --           (J : 𝓣 ̇)
 --           → (f ̂ (𝒜 𝓣 J)) λ {args → proj args 𝓣 J}

--  -- ⨅'' : (𝒜 : (𝓘 : Universe)(I : 𝓘 ̇ ) → Algebra 𝓘 𝑆 ) → BigAlgebra _ 𝑆
--  -- ⨅'' 𝒜 =  ((𝓘 : Universe)( i : _) → ∣ 𝒜 𝓘 i ∣) ,  λ f x 𝓘 i → (f ̂ (𝒜 𝓘 i)) λ 𝓥 → x 𝓥 i
-- ((f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A)

--  infixr -1 ⨅

 --Usually we want to assume that, given an algebra 𝑨, we can
 --always find a surjective map h₀ : X → ∣ 𝑨 ∣ from an arbitrary
 --collection X of "variables" onto the universe of 𝑨.
 --Here is the type we use when making this assumption.

 _↠_ : 𝓧 ̇ → Algebra 𝓤 𝑆 → 𝓧 ⊔ 𝓤 ̇
 X ↠ 𝑨 = Σ h ꞉ (X → ∣ 𝑨 ∣) , Epic h
