\begin{code}
-- FILE: congruences.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020
-- NOTE: This file used to be called relations.agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic

module congruences where

open import prelude using (𝓡; 𝓢; is-prop; 𝟙; _≡⟨_⟩_; _∎; refl; _⁻¹; funext; ap; _∙_; 𝓇ℯ𝒻𝓁) public

REL : 𝓤 ̇ → 𝓥 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓝 ⁺) ̇
REL A B 𝓝 = A → B → 𝓝 ̇

Rel : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
Rel A 𝓝 = REL A A 𝓝

KER : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → 𝓤 ⊔ 𝓦 ̇
KER {𝓤}{𝓦}{A} g = Σ x ꞉ A , Σ y ꞉ A , g x ≡ g y

ker : {A B : 𝓤 ̇ } → (A → B) → 𝓤 ̇
ker {𝓤} = KER{𝓤}{𝓤}

KER-rel : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → Rel A 𝓦
KER-rel g x y = g x ≡ g y

-- (in the special case 𝓦 ≡ 𝓤)
ker-rel : {A B : 𝓤 ̇ } → (A → B) → Rel A 𝓤
ker-rel {𝓤} = KER-rel {𝓤} {𝓤}

KER-pred : {A : 𝓤 ̇}{B : 𝓦 ̇} → (A → B) → Pred (A × A) 𝓦
KER-pred g (x , y) = g x ≡ g y

-- (in the special case 𝓦 ≡ 𝓤)
ker-pred : {A : 𝓤 ̇ }{B : 𝓤 ̇ } → (A → B) → Pred (A × A) 𝓤
ker-pred {𝓤} = KER-pred {𝓤} {𝓤}

_⇒_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →    REL A B 𝓡 → REL A B 𝓢
 →    𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇

P ⇒ Q = ∀ {i j} → P i j → Q i j

infixr 4 _⇒_

_on_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
 →     (B → B → C) → (A → B) → (A → A → C)
_*_ on g = λ x y → g x * g y

_=[_]⇒_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →        Rel A 𝓡 → (A → B) → Rel B 𝓢
 →        𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇

P =[ g ]⇒ Q = P ⇒ (Q on g)

infixr 4 _=[_]⇒_


reflexive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
reflexive _≈_ = ∀ x → x ≈ x

symmetric : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

transitive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

[_]_ :  {A : 𝓤 ̇ } →  (a : A) → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
[ a ] ≈ = Σ x ꞉ _ ,  ≈ a x

_//_ :  (A : 𝓤 ̇ ) → Rel A 𝓡 → (𝓤 ⊔ 𝓡) ⁺ ̇
A // ≈ = Σ C ꞉ _ ,   Σ a ꞉ A ,  C ≡ ( [ a ] ≈ )

⌜_⌝ : {A : 𝓤 ̇}{≈ : Rel A 𝓡} → A // ≈  → A
⌜ 𝒂 ⌝ = ∣ ∥ 𝒂 ∥ ∣

⟦_⟧ : {A : 𝓤 ̇} → A → {≈ : Rel A 𝓡} → A // ≈
⟦ a ⟧ {≈} = ([ a ] ≈) , a , 𝓇ℯ𝒻𝓁


is-subsingleton-valued : {A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
is-subsingleton-valued  _≈_ = ∀ x y → is-prop (x ≈ y)

𝟎 : {A : 𝓤 ̇ } → 𝓤 ̇
𝟎{𝓤} {A} = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

𝟎-alg-rel : {𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝓤 𝑆} → 𝓤 ̇
𝟎-alg-rel {𝑨 = 𝑨} = Σ a ꞉ ∣ 𝑨 ∣ , Σ b ꞉ ∣ 𝑨 ∣ , a ≡ b

𝟎-rel : {A : 𝓤 ̇ } → Rel A 𝓤
𝟎-rel a b = a ≡ b

𝟎-pred : {A : 𝓤 ̇ } → Pred (A × A) 𝓤
𝟎-pred (a , a') = a ≡ a'

--...as a binary predicate:
𝟎'' : {A : 𝓤 ̇ } → 𝓤 ̇
𝟎'' {𝓤} {A} = Σ p ꞉ (A × A) , ∣ p ∣ ≡ ∥ p ∥

𝟏 : {A : 𝓤 ̇ } → Rel A 𝓤₀
𝟏 a b = 𝟙

record IsEquivalence {𝓤 : Universe} {A : 𝓤 ̇ } (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
  field
    rfl  : reflexive _≈_
    sym   : symmetric _≈_
    trans : transitive _≈_

is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
is-equivalence-relation _≈_ =
 is-subsingleton-valued _≈_
  × reflexive _≈_ × symmetric _≈_ × transitive _≈_

𝟎-IsEquivalence : {A : 𝓤 ̇ } → IsEquivalence{𝓤 = 𝓤}{A = A} 𝟎-rel
𝟎-IsEquivalence = record { rfl = λ x → 𝓇ℯ𝒻𝓁
                         ; sym = λ x y x≡y → x≡y ⁻¹
                         ; trans = λ x y z x≡y y≡z → x≡y ∙ y≡z }

lift-rel : {γ : 𝓥 ̇ } {Z : 𝓤 ̇ }
 →         Rel Z 𝓦 → (γ → Z) → (γ → Z)
 →         𝓥 ⊔ 𝓦 ̇
lift-rel R f g = ∀ x → R (f x) (g x)

compatible-fun : {γ : 𝓥 ̇ } {Z : 𝓤 ̇ }
                 (f : (γ → Z) → Z)(R : Rel Z 𝓦)
 →               𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
compatible-fun f R  = (lift-rel R) =[ f ]⇒ R

module _ {𝑆 : Signature 𝓞 𝓥}  where

  -- relation compatible with an operation
  compatible-op : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} → ∣ 𝑆 ∣ → Rel ∣ 𝑨 ∣ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  compatible-op {𝑨 = 𝑨} f R = (lift-rel R) =[ f ̂ 𝑨 ]⇒ R

  --The given relation is compatible with all ops of an algebra.
  compatible : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆) → Rel ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  compatible {𝓤 = 𝓤}{𝓦 = 𝓦} 𝑨 R = ∀ f → compatible-op{𝓤 = 𝓤}{𝓦 = 𝓦}{𝑨 = 𝑨} f R

  𝟎-compatible-op : funext 𝓥 𝓤
   →                {𝑨 : Algebra 𝓤 𝑆} (f : ∣ 𝑆 ∣)
   →                compatible-op {𝓤 = 𝓤}{𝑨 = 𝑨} f 𝟎-rel
  𝟎-compatible-op fe {𝑨 = 𝑨} f ptws0  =
   ap (f ̂ 𝑨) (fe (λ x → ptws0 x))

  𝟎-compatible : funext 𝓥 𝓤
   →             {A : Algebra 𝓤 𝑆}
   →             compatible A 𝟎-rel
  𝟎-compatible fe {A} =
   λ f args → 𝟎-compatible-op fe {A} f args

  -- Congruence relations
  Con : (A : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
  Con {𝓤} A =
   Σ θ ꞉ ( Rel ∣ A ∣ 𝓤 ) , IsEquivalence θ × compatible A θ

  con : (A : Algebra 𝓤 𝑆)  →  Pred (Rel ∣ A ∣ 𝓤) _
  con A = λ θ → IsEquivalence θ × compatible A θ

  record Congruence {𝓤 : Universe} (A : Algebra 𝓤 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
    constructor mkcon
    field
      ⟨_⟩ : Rel ∣ A ∣ 𝓤
      Compatible : compatible A ⟨_⟩
      IsEquiv : IsEquivalence ⟨_⟩
  open Congruence

  Δ : funext 𝓥 𝓤 → (A : Algebra 𝓤 𝑆) → Congruence A
  Δ fe A = mkcon 𝟎-rel
                ( 𝟎-compatible fe {A} )
                ( 𝟎-IsEquivalence )

  _╱_ : (A : Algebra 𝓤 𝑆) → Congruence A
         ---------------------------------
   →     Algebra (𝓤 ⁺) 𝑆
  A ╱ θ = (( ∣ A ∣ // ⟨ θ ⟩ ) , -- carrier
            (λ f args        -- operations
             → ([ (f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩) ,
               ((f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
            )
          )
\end{code}
