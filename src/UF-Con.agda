--FILE: UF-Con.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 22 Feb 2020
--UPDATED: 23 Apr 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude using (Universe; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓡; 𝓢; 𝓣; 𝓞; _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟙; 𝟚; _×_; _≡_; refl; _∼_; ≡-sym; _≡⟨_⟩_; _∎; ap; _⁻¹)
open import UF-Basic using (Signature; Algebra)
open import UF-Extensionality using (propext; dfunext; funext)
open import UF-Singleton using (is-subsingleton; is-set)
open import UF-Rel using (Rel; IsEquivalence; Reflexive; Symmetric; Transitive; _=[_]⇒_)
open import Relation.Unary using (Pred)

module UF-Con where

-------------------------------------------------------------------
--Equivalence relations and blocks

--For a binary relation ≈ on A, denote a single ≈-class (containing a) by `[ a ] ≈`
[_]_ : {𝓤 : Universe} {A : 𝓤 ̇} →  (a : A) → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
[ a ] _≈_ = Σ x ꞉ _ ,  a ≈ x

--...denote the collection of all ≈-classes of A by `A // ≈`.
_//_ : {𝓤 : Universe} (A : 𝓤 ̇ ) → Rel A 𝓡 → (𝓤 ⊔ 𝓡) ⁺ ̇
A // ≈ = Σ C ꞉ _ ,   Σ a ꞉ A ,  C ≡ ( [ a ] ≈ )

is-subsingleton-valued : {A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)

reflexive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
reflexive _≈_ = ∀ x → x ≈ x

symmetric : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

transitive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
is-equivalence-relation _≈_ = is-subsingleton-valued _≈_  × reflexive _≈_  × symmetric _≈_  × transitive _≈_

--The "trivial" or "diagonal" or "identity" relation.
𝟎 : {A : 𝓤 ̇} → Rel A 𝓤
𝟎 a b = a ≡ b

-- 𝟎 : {𝓤 : Universe} (A : 𝓤 ̇) → 𝓤 ̇
-- 𝟎 A = Σ a ꞉ (A × A) , pr₁ a ≡ pr₂ a

--The "universal" or "total" or "all" relation.
𝟏 : {A : 𝓤 ̇} → Rel A 𝓤₀
𝟏 a b = 𝟙

𝟎-on-set-is-equiv : propext 𝓤 → dfunext 𝓤 𝓤 → {A : 𝓤 ̇}
  →         is-set A
  →         is-equivalence-relation {𝓤} {𝓤} {A} 𝟎
𝟎-on-set-is-equiv pe fe {A} Aset =
  Aset , refl , (λ x y x≡y → ≡-sym x≡y) , λ x y z x≡y y≡z → x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎ 

𝟎-IsEquivalence : {A : 𝓤 ̇} → IsEquivalence {𝓤}{𝓤}{A} 𝟎
𝟎-IsEquivalence = record { rfl = ρ ; sym = σ ; trans = τ }
 where
  ρ : Reflexive 𝟎
  ρ {x} =  x ≡⟨ refl x ⟩ x ∎

  σ : Symmetric 𝟎
  σ {x} {y} x≡y = x≡y ⁻¹

  τ : Transitive 𝟎
  τ {x} {y} {z} x≡y y≡z = x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎

--lift a binary relation from pairs to pairs of tuples.
lift-rel :  {γ : 𝓥 ̇} {Z : 𝓤 ̇} → Rel Z 𝓦 → (γ → Z) → (γ → Z) → 𝓥 ⊔ 𝓦 ̇
lift-rel R 𝒇 𝒈 = ∀ x → R (𝒇 x) (𝒈 x)

--compatibility of a given function-relation pair
compatible-fun : {γ : 𝓥 ̇} {Z : 𝓤 ̇} ( 𝒇 : (γ → Z) → Z )  (𝑹 : Rel Z 𝓦) →  𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
compatible-fun 𝒇 𝑹 = (lift-rel 𝑹) =[ 𝒇 ]⇒ 𝑹

module _ {S : Signature 𝓞 𝓥}  where

  -- relation compatible with an operation
  compatible-op : {𝑨 : Algebra 𝓤 S} → ∣ S ∣ → Rel ∣ 𝑨 ∣ 𝓤 → 𝓥 ⊔ 𝓤 ̇
  compatible-op {𝓤} {𝑨} 𝓸 𝓻 = (lift-rel 𝓻) =[ (∥ 𝑨 ∥ 𝓸) ]⇒ 𝓻

  --The given relation is compatible with all ops of an algebra.
  compatible : (𝑨 : Algebra 𝓤 S) -> Rel ∣ 𝑨 ∣ 𝓤 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇
  compatible {𝓤} 𝑨 𝓻 = ∀ 𝓸 → compatible-op{𝓤}{𝑨} 𝓸 𝓻

  𝟎-compatible-op : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 S} → (𝓸 : ∣ S ∣) → compatible-op {𝓤}{𝑨} 𝓸 𝟎
  𝟎-compatible-op fe {𝑨} 𝓸 ptws𝟎  = ap  (∥ 𝑨 ∥ 𝓸) (fe (λ x → ptws𝟎 x))

  𝟎-compatible : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 S} → compatible 𝑨 𝟎
  𝟎-compatible fe {𝑨} = λ 𝓸 args → 𝟎-compatible-op fe {𝑨} 𝓸 args

  -- Congruence relations
  Con : {𝓤 : Universe} (𝑨 : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
  Con {𝓤} 𝑨 = Σ θ ꞉ ( Rel ∣ 𝑨 ∣ 𝓤 ) , IsEquivalence θ × compatible 𝑨 θ

  con : (𝑨 : Algebra 𝓤 S)  →  Pred (Rel ∣ 𝑨 ∣ 𝓤) _
  con 𝑨 = λ θ → IsEquivalence θ × compatible 𝑨 θ

  record Congruence (𝑨 : Algebra 𝓤 S) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
    constructor mkcon
    field
      ⟨_⟩ : Rel ∣ 𝑨 ∣ 𝓤
      Compatible : compatible 𝑨 ⟨_⟩
      IsEquiv : IsEquivalence ⟨_⟩
  open Congruence

  --The "trivial" or "diagonal" or "identity" relation.
  Δ : funext 𝓥 𝓤 → (𝑨 : Algebra 𝓤 S) → Congruence 𝑨
  Δ fe 𝑨 = mkcon 𝟎
                ( 𝟎-compatible fe {𝑨} )
                ( 𝟎-IsEquivalence )

  _╱_ : (𝑨 : Algebra 𝓤 S) → Congruence 𝑨
         ---------------------------------
   →     Algebra (𝓤 ⁺) S
  𝑨 ╱ θ = ( ( ∣ 𝑨 ∣ // ⟨ θ ⟩ ) , -- carrier
             ( λ 𝓸 args        -- operations
                 → ( [ ∥ 𝑨 ∥ 𝓸 (λ i₁ -> ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩ ) ,
                    ( ∥ 𝑨 ∥ 𝓸 (λ i₁ -> ∣ ∥ args i₁ ∥ ∣) , refl _ )
             )
           )

