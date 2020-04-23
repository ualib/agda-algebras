--File: UF-Basic.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 21 Feb 2020
--Notes: Based on the file `basic.agda` (24 Dec 2019).
--       Used for 1st half of talk at JMM Special Session (Jan 2020).

{-# OPTIONS --without-K --exact-split --safe #-}

--open import Preliminaries  using (Level; lzero; lsuc;_⊔_; ∃; _,_; ⊥; Bool; _×_; ∣_∣; ⟦_⟧; _≡_; _∘_; Pred; _∈_; Lift)
open import UF-Prelude using (Universe; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚 )
--; universe-of; id; 𝑖𝑑; _∘_; pr₁; pr₂; Π; -Π; domain; _×_; _≡_; refl; _∼_; transport; _≡⟨_⟩_; _∎; ap; _∙_; _⁻¹; _⇔_; _iff_; lr-implication; rl-implication

module UF-Basic where

-- -- Operations and projections
Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Op I A = (I → A) → A

π : {I : 𝓥 ̇} {A : 𝓤 ̇} → I → Op I A
π i x = x i

-- 𝓞 is the universe in which the operation symbols lives
-- 𝓥 is the universe in which the arities live
Signature : (𝓞 𝓥 : Universe) → 𝓞 ⁺ ⊔ 𝓥 ⁺ ̇
Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇  , (F → 𝓥 ̇)

-- 𝓤 is the universe level of carriers (or "universes") of structures
Algebra : (𝓤 : Universe) → {𝓞 𝓥 : Universe} → (S : Signature 𝓞 𝓥) →  𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
Algebra 𝓤 {𝓞} {𝓥} (F , ρ) = Σ A ꞉ 𝓤 ̇ ,  ( (𝓸 : F)  → Op (ρ 𝓸) A )

-- Indexed product of algebras is an algebra
-- The trick is to view the Pi-type as a dependent product i.e.
-- A i1 × A i2 × A i3 × ... = (i : I) → A i

module _ {𝓜 𝓞 𝓥 : Universe} {S : Signature 𝓞 𝓥} where

  Π' : {I : 𝓜 ̇} → (I → Algebra 𝓤 S) → Algebra (𝓤 ⊔ 𝓜) S
  Π' {I = I} 𝔄 = ( (i : I) → ∣ 𝔄 i ∣ ) ,  λ 𝓸 x i → ∥ 𝔄 i ∥ 𝓸 λ 𝓥 → x 𝓥 i

--Example: monoid
--  A monoid signature has two operation symbols, say, `e`  and `·`, of arities 0 and 2 (thus, of types `(𝟘 → A) → A`
--  and `(𝟚 → A) → A`) resp. The types indicate that `e` is nullary (i.e., takes no args, equivalently, takes args
--  of type `𝟘 → A`), while `·` is binary (as indicated  by argument type `𝟚 -> A`).

data monoid-op : 𝓤₀ ̇ where
  e : monoid-op
  · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }

