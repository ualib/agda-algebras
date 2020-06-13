--FILE: UF-Basic.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 20 Feb 2020
--UPDATE: 13 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude using (Universe; 𝓘; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; ℕ; _×_; Π; _≡_)
open import UF-Singleton using (is-set)
open import UF-Extensionality using (dep-intensionality; hfunext; Π-is-set)
--open import Data.Fin using (Fin)

module UF-Basic where

-- Operations and projections
Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Op I A = (I → A) → A

π : {I : 𝓥 ̇} {A : 𝓤 ̇} → I → Op I A
π i x = x i

-- 𝓞 is the universe in which the operation symbols lives
-- 𝓥 is the universe in which the arities live
Signature : (𝓞 𝓥 : Universe) → 𝓞 ⁺ ⊔ 𝓥 ⁺ ̇
Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇  , ( F → 𝓥 ̇ )

-- 𝓤 is the universe level of carriers (or "universes") of structures
Algebra : (𝓤 : Universe) → {𝓞 𝓥 : Universe} → (S : Signature 𝓞 𝓥) →  𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
Algebra 𝓤 {𝓞} {𝓥} S = Σ A ꞉ 𝓤 ̇ ,  ( (𝓸 : ∣ S ∣ )  → Op ( ∥ S ∥ 𝓸) A )
-- Alternative notation (more in line with the lit) is also possible:
-- Algebra 𝓤 {𝓞} {𝓥} (F , ρ) = Σ A ꞉ 𝓤 ̇ ,  ( (𝓸 : F )  → Op ( ρ 𝓸) A )
-- where S = (F , ρ) is the signature with F the set of operation symbols
-- and ρ the arity function.

--We could insist that the carrier of an algebra is a *set*
--(i.e., a type with at most 1 way to prove 2 elements equal).
--The assumption `is-set A` could be included as follows:
SmallAlgebra : (𝓤 : Universe){𝓞 𝓥 : Universe}(S : Signature 𝓞 𝓥) →  𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
SmallAlgebra 𝓤 {𝓞} {𝓥} (F , ρ) = Σ A ꞉ 𝓤 ̇ , is-set A × ((𝓸 : F) → Op (ρ 𝓸) A)

module _ {S : Signature 𝓞 𝓥}  where

  --if the set X on which we wish to define an algebra is already given...
  algebra-on :  {𝓤 : Universe} (X : 𝓤 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
  algebra-on {𝓤} X = Σ A ꞉ (Algebra 𝓤 S)  , ( ∣ A ∣ ≡ X )

  Π' : {I : 𝓘 ̇}( A : I → Algebra 𝓤 S ) → Algebra (𝓤 ⊔ 𝓘) S
  Π' A =  ( ( ᵢ : _) → ∣ A ᵢ ∣ ) ,  λ 𝓸 x ᵢ → ∥ A ᵢ ∥ 𝓸 λ 𝓥 → x 𝓥 ᵢ

  -- We now want to construct a small algebra out of a product of small algebras.
  -- But for that we need that the products of "sets" is a "set".
  product-of-sets-is-set : (hfe : hfunext 𝓘 𝓤) 
                           (I : 𝓘 ̇)(X : I → 𝓤 ̇)
   →                       ((i : I) → is-set (X i))
                          --------------------------
   →                       is-set (Π X)
  product-of-sets-is-set hfe I X ∀Xset = Π-is-set hfe ∀Xset

  -- product of small algebras
  Πₛ : {hfe : hfunext 𝓘 𝓤}{I : 𝓘 ̇}(A : I → SmallAlgebra 𝓤 S) → SmallAlgebra (𝓤 ⊔ 𝓘) S
  Πₛ {hfe = hfe}{I = I} A = ((i : _) → ∣ A i ∣) ,
                             (product-of-sets-is-set hfe I (λ i → ∣ A i ∣)
                              (λ i → ∣ ∥ A i ∥ ∣)) ,   -- is-set ∣ A ᵢ ∣
                               λ 𝓸 x i → ∥ ∥ A i ∥ ∥ 𝓸 λ 𝓥 → x 𝓥 i  --same ops as Π' (Alg prod)

--Example: monoid
-- A monoid signature has two operation symbols, say, `e`  and `·`, of arities 0 and 2
-- (thus, of types `(𝟘 → A) → A` and `(𝟚 → A) → A`) resp. The types indicate that `e` is
-- nullary (i.e., takes no args, equivalently, takes args--  of type `𝟘 → A`), while `·`
-- is binary (as indicated  by argument type `𝟚 → A`).
data monoid-op : 𝓤₀ ̇ where
  e : monoid-op
  · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }

