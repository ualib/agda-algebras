-- FILE: basic.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020
-- Note: This was used for the second part of my talk at JMM Special Session.

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude using (Universe; 𝓘; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣;
  _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; _×_; Π; _≡_)

module basic where

--The type of operations
Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Op I A = (I → A) → A

--Example. the projections
π : {I : 𝓥 ̇ } {A : 𝓤 ̇ } → I → Op I A
π i x = x i

--𝓞 is the universe in which operation symbols live
--𝓥 is the universe in which arities live
Signature : (𝓞 𝓥 : Universe) → 𝓞 ⁺ ⊔ 𝓥 ⁺ ̇
Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇  , ( F → 𝓥 ̇ )

Algebra : (𝓤 : Universe) → {𝓞 𝓥 : Universe}
 →        (S : Signature 𝓞 𝓥) →  𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
Algebra 𝓤 {𝓞}{𝓥} S = Σ A ꞉ 𝓤 ̇ , ((𝑓 : ∣ S ∣) → Op (∥ S ∥ 𝑓) A)

data monoid-op : 𝓤₀ ̇ where
 e : monoid-op
 · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }


module _ {S : Signature 𝓞 𝓥}  where

 Π' : {I : 𝓘 ̇ }( A : I → Algebra 𝓤 S ) → Algebra (𝓤 ⊔ 𝓘) S
 Π' A =  (( ᵢ : _) → ∣ A ᵢ ∣) ,  λ 𝑓 x ᵢ → ∥ A ᵢ ∥ 𝑓 λ 𝓥 → x 𝓥 ᵢ

