\begin{code}
-- FILE: congruences.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020
-- NOTE: This file used to be called relations.agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import prelude using (global-dfunext)
-- open import Relation.Unary using () -- Pred; _∈_; _⊆_)

module congruences {gfe : global-dfunext} where

open import prelude using (Univalence; is-prop; 𝟙; _≡⟨_⟩_; _∎; refl; _⁻¹; funext; ap; _≡_; _∙_;
 𝓇ℯ𝒻𝓁; cong-app-pred; id; _⇔_; _∈₀_; _⊆₀_; 𝓟; ∈₀-is-subsingleton; equiv-to-subsingleton;
 powersets-are-sets'; subset-extensionality'; propext; Ω; Σ-is-subsingleton; Π-is-subsingleton;
 cong-app-𝓟; fst; ≡-elim-left) public

module _ {𝓤 𝓦 : Universe} where

 REL : 𝓤 ̇ → 𝓦 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓦 ⊔ 𝓝 ⁺) ̇
 REL A B 𝓝 = A → B → 𝓝 ̇

 KER : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → 𝓤 ⊔ 𝓦 ̇
 KER {A} g = Σ x ꞉ A , Σ y ꞉ A , g x ≡ g y

 KER-pred : {A : 𝓤 ̇}{B : 𝓦 ̇} → (A → B) → Pred (A × A) 𝓦
 KER-pred g (x , y) = g x ≡ g y

Rel : {𝓤 : Universe} → 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
Rel A 𝓝 = REL A A 𝓝

KER-rel : {𝓤 𝓦 : Universe}{A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → Rel A 𝓦
KER-rel g x y = g x ≡ g y

-- Examples -----------------------------------------------------------
module _ {𝓤 : Universe} where
 ker : {A B : 𝓤 ̇ } → (A → B) → 𝓤 ̇
 ker = KER{𝓤}{𝓤}

 ker-rel : {A B : 𝓤 ̇ } → (A → B) → Rel A 𝓤
 ker-rel = KER-rel {𝓤} {𝓤}

 ker-pred : {A B : 𝓤 ̇ } → (A → B) → Pred (A × A) 𝓤
 ker-pred = KER-pred {𝓤} {𝓤}

module _ {𝓤 : Universe} where
 --The identity relation.
 𝟎 : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎 {A} = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

 --...on the domain of an algebra...
 𝟎-alg-rel : {𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝓤 𝑆} → 𝓤 ̇
 𝟎-alg-rel {𝑨 = 𝑨} = Σ a ꞉ ∣ 𝑨 ∣ , Σ b ꞉ ∣ 𝑨 ∣ , a ≡ b

 --...as a binary relation...
 𝟎-rel : {A : 𝓤 ̇ } → Rel A 𝓤
 𝟎-rel a b = a ≡ b

 --...as a binary predicate...
 𝟎-pred : {A : 𝓤 ̇ } → Pred (A × A) 𝓤
 𝟎-pred (a , a') = a ≡ a'

 𝟎-pred' : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎-pred' {A} = Σ p ꞉ (A × A) , ∣ p ∣ ≡ ∥ p ∥

 𝟏 : {A : 𝓤 ̇ } → Rel A 𝓤₀
 𝟏 a b = 𝟙
------------------------------------------------------------------------

-- Properties of binary relations --------------------------------------

module _ {𝓤 𝓡 : Universe} where
 reflexive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 reflexive _≈_ = ∀ x → x ≈ x

 symmetric : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

 transitive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

 is-subsingleton-valued : {A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-subsingleton-valued  _≈_ = ∀ x y → is-prop (x ≈ y)



-- Equivalence Relations -----------------------------------------------
module _ {𝓤 𝓡 : Universe} where

 record IsEquivalence {A : 𝓤 ̇ } (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
   field
     rfl  : reflexive _≈_
     sym   : symmetric _≈_
     trans : transitive _≈_

 is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-equivalence-relation _≈_ =
  is-subsingleton-valued _≈_
   × reflexive _≈_ × symmetric _≈_ × transitive _≈_

𝟎-IsEquivalence : ∀{𝓤}{A : 𝓤 ̇ } → IsEquivalence{𝓤 = 𝓤}{A = A} 𝟎-rel
𝟎-IsEquivalence = record { rfl = λ x → 𝓇ℯ𝒻𝓁
                         ; sym = λ x y x≡y → x≡y ⁻¹
                         ; trans = λ x y z x≡y y≡z → x≡y ∙ y≡z }




module relation-classes {𝓤 𝓡 : Universe} where

 -- relation class
 [_]ᵣ_ :  {A : 𝓤 ̇ } → A → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 [ a ]ᵣ R = Σ x ꞉ _ , R a x

 -- relation quotient
 _/ᵣ_ : (A : 𝓤 ̇ ) → Rel A 𝓡 → (𝓤 ⊔ 𝓡) ⁺ ̇
 A /ᵣ ≈ = Σ C ꞉ _ ,  Σ a ꞉ A ,  C ≡ ( [ a ]ᵣ ≈ )

 -- get relation class representative
 ⌜_⌝ᵣ : {A : 𝓤 ̇}{≈ : Rel A 𝓡} → A /ᵣ ≈  → A
 ⌜ 𝒂 ⌝ᵣ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

 -- intro rule for relation class with designated representative
 ⟦_⟧ᵣ : {A : 𝓤 ̇} → A → {≈ : Rel A 𝓡} → A /ᵣ ≈
 ⟦ a ⟧ᵣ {≈} = ([ a ]ᵣ ≈) , a , 𝓇ℯ𝒻𝓁

 -- elimination rule for relation class representative
 /ᵣ-Refl : {A : 𝓤 ̇}{a a' : A}{_≈_ : Rel A 𝓡}
  →   reflexive _≈_ → ⟦ a ⟧ᵣ{_≈_} ≡ ⟦ a' ⟧ᵣ → a ≈ a'
 /ᵣ-Refl rfl (refl _)  = rfl _


module relation-predicate-classes {𝓤 𝓡 : Universe} where

 -- relation class
 [_] : {A : 𝓤 ̇ } → A → Rel A 𝓡 → Pred A 𝓡
 [ a ] R = λ x → R a x

 --So, x ∈ [ a ]ₚ R iff R a x, and the following elimination rule is a tautology.
 []-elim : {A : 𝓤 ̇ }{a x : A}{R : Rel A 𝓡}
  →         R a x ⇔ (x ∈ [ a ] R)
 []-elim = id , id

 -- relation quotient (predicate version)
 _/ₚ_ : (A : 𝓤 ̇ ) → Rel A 𝓡 → 𝓤 ⊔ (𝓡 ⁺) ̇
 A /ₚ ≈ = Σ C ꞉ Pred A 𝓡 ,  Σ a ꞉ A ,  C ≡ ( [ a ] ≈ )

 -- For a reflexive relation, we have the following elimination rule.
 /ₚ-refl : {A : 𝓤 ̇}{a a' : A}{_≈_ : Rel A 𝓡}
  →   reflexive _≈_ → [ a ] _≈_ ≡ [ a' ] _≈_ → a ≈ a'
 /ₚ-refl{A = A}{a}{a'}{_≈_} rfl x  = γ
  where
   a'in : a' ∈ [ a' ] _≈_
   a'in = rfl a'
   γ : a' ∈ [ a ] _≈_
   γ = cong-app-pred a' a'in (x ⁻¹)

 ⌜_⌝ : {A : 𝓤 ̇}{≈ : Rel A 𝓡} → A /ₚ ≈  → A
 ⌜ 𝒂 ⌝ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

 -- introduction rule for relation class with designated representative
 ⟦_⟧ : {A : 𝓤 ̇} → A → {≈ : Rel A 𝓡} → A /ₚ ≈
 ⟦ a ⟧ {≈} = ([ a ] ≈) , a , 𝓇ℯ𝒻𝓁

 --So, x ∈ [ a ]ₚ R iff R a x, and the following elimination rule is a tautology.
 ⟦⟧-elim : {A : 𝓤 ̇ }{a x : A}{R : Rel A 𝓡}
  →         R a x ⇔ (x ∈ [ a ] R)
 ⟦⟧-elim = id , id

 -- []-⟦⟧-agreement : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
 --  →                (⟦ a ⟧ {R} ≡ ⟦ a' ⟧ {R})  ⇔  ([ a ] R ≡ [ a' ] R)
 -- []-⟦⟧-agreement = {!!}



 open IsEquivalence
 -- elimination rule for relation class representative
 /ₚ-Refl : {A : 𝓤 ̇}{a a' : A}{_≈_ : Rel A 𝓡}
  →   reflexive _≈_ → ⟦ a ⟧{_≈_} ≡ ⟦ a' ⟧ → a ≈ a'
 /ₚ-Refl rfl (refl _)  = rfl _

 -- []-refl : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
 --  →        IsEquivalence R
 --  →        R a a' ⇔  ([ a ] R ≡ [ a' ] R)
 -- []-refl {A = A}{a}{a'}{R} eqR = lr , rl
 --  where
 --   lr : R a a' → [ a ] R ≡ [ a' ] R
 --   lr = λ x → gfe λ y →
 --         [ a ] R y ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
 --         R a y ≡⟨ {!(sym eqR) a y !} ⟩
 --         R y a  ≡⟨ {!!} ⟩
 --         R y a' ≡⟨ {!!} ⟩
 --         R a' y ≡⟨ {!!} ⟩
 --         [ a' ] R y ∎


 --   rl : [ a ] R ≡ [ a' ] R → R a a'
 --   rl = {!!}


module relation-powerset-classes {𝓤 : Universe} where
 -- Properties of binary relations as powersets --------------------------------------

 record SetRel (A : 𝓤 ̇) : 𝓤 ⁺ ̇ where
   field
     ⟨_⟩ : 𝓟(A × A)
     isset : is-set A

 open SetRel


 module _ {A : 𝓤 ̇} where

  refl𝓟 : SetRel A → 𝓤 ̇
  refl𝓟 θ = ∀ x → (x , x) ∈₀ ⟨ θ ⟩

  symm𝓟 : SetRel A → 𝓤 ̇
  symm𝓟 θ = ∀ x y → (x , y) ∈₀ ⟨ θ ⟩  → (y , x) ∈₀ ⟨ θ ⟩

  trans𝓟 : SetRel A → 𝓤 ̇
  trans𝓟 θ = ∀ x y z → (x , y) ∈₀ ⟨ θ ⟩ → (y , z) ∈₀ ⟨ θ ⟩ → (x , z) ∈₀ ⟨ θ ⟩

  is-subsingleton-valued-𝓟 : SetRel A → 𝓤 ̇
  is-subsingleton-valued-𝓟 θ = ∀ x y → is-prop ((x , y) ∈₀ ⟨ θ ⟩)


  -- relation class
  _/_ : A → (θ : SetRel A) → 𝓟 A
  a / θ  = λ x → ((a , x) ∈₀ ⟨ θ ⟩) , (∈₀-is-subsingleton ⟨ θ ⟩ (a , x))

  --So, x ∈ [ a ]ₚ iff R a x, and the following elimination rule is a tautology.
  /-elim : {a x : A}{θ : SetRel A}
   →       (a , x) ∈₀ ⟨ θ ⟩ ⇔ (x ∈₀ (a / θ))
  /-elim = id , id

  -- For a reflexive relation, we have the following elimination rule.
  /-refl : {a a' : A}{θ : SetRel A}
   →       refl𝓟 θ → (a / θ) ≡ (a' / θ) → (a , a') ∈₀ ⟨ θ ⟩
  /-refl {a}{a'}{θ} rfl x  = γ
   where
    a'in : a' ∈₀ (a' / θ)
    a'in = rfl a'
    γ : a' ∈₀ (a / θ)
    γ = cong-app-𝓟 a' a'in (x ⁻¹)

 -- relation quotient (predicate version)
 _//_ : (A : 𝓤 ̇) → SetRel A → 𝓤 ⁺ ̇
 A // θ = Σ C ꞉ (𝓟 A) , Σ a ꞉ A , C ≡ (a / θ)

 ⌜_⌝ₚ : {A : 𝓤 ̇}{θ : SetRel A} → A // θ  → A
 ⌜ 𝒂 ⌝ₚ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

 -- introduction rule for relation class with designated representative
 ⟦_⟧ : {A : 𝓤 ̇} → A → (θ : SetRel A) → A // θ
 ⟦ a ⟧ θ = (a / θ) , a , 𝓇ℯ𝒻𝓁

 --So, x ∈ [ a ]ₚ R iff R a x, and the following elimination rule is a tautology.
 ⟦⟧-elim : {A : 𝓤 ̇ }{θ : SetRel A}{a x : A}
  →         (a , x) ∈₀ ⟨ θ ⟩  ⇔  x ∈₀ (a / θ)
 ⟦⟧-elim = id , id

 ⟦⟧→[]-agreement : {A : 𝓤 ̇}{θ : SetRel A}{x y : A}
  →                (⟦ x ⟧ θ ≡ ⟦ y ⟧ θ)  →  ((x / θ) ≡ (y / θ))
 ⟦⟧→[]-agreement equ = ap fst equ



_on_ : {𝓤 𝓥 𝓦 : Universe}
       {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
 →     (B → B → C) → (A → B) → (A → A → C)

_*_ on g = λ x y → g x * g y


_⇒_ : {𝓤 𝓥 𝓦 𝓧 : Universe}
      {A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →    REL A B 𝓦 → REL A B 𝓧
 →    𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧 ̇

P ⇒ Q = ∀ {i j} → P i j → Q i j
infixr 4 _⇒_


_=[_]⇒_ : {𝓤 𝓥 𝓡 𝓢 : Universe}
          {A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →        Rel A 𝓡 → (A → B) → Rel B 𝓢
 →        𝓤  ⊔ 𝓡 ⊔ 𝓢 ̇

P =[ g ]⇒ Q = P ⇒ (Q on g)
infixr 4 _=[_]⇒_


module _ {𝓤 𝓥 𝓦 : Universe} {γ : 𝓥 ̇ } {Z : 𝓤 ̇ } where

 lift-rel : Rel Z 𝓦 → (γ → Z) → (γ → Z) → 𝓥 ⊔ 𝓦 ̇
 lift-rel R f g = ∀ x → R (f x) (g x)

 compatible-fun : (f : (γ → Z) → Z)(R : Rel Z 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun f R  = (lift-rel R) =[ f ]⇒ R

module _ {𝑆 : Signature 𝓞 𝓥}  where

  -- relation compatible with an operation
  compatible-op : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} → ∣ 𝑆 ∣ → Rel ∣ 𝑨 ∣ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  compatible-op {𝑨 = 𝑨} f R = ∀{𝒂}{𝒃} → (lift-rel R) 𝒂 𝒃  → R ((f ̂ 𝑨) 𝒂) ((f ̂ 𝑨) 𝒃)
  -- alternative notation: (lift-rel R) =[ f ̂ 𝑨 ]⇒ R

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

module congruence-relations {𝑆 : Signature 𝓞 𝓥}  where

  open relation-classes

  Con : (A : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
  Con {𝓤} A =
   Σ θ ꞉ ( Rel ∣ A ∣ 𝓤 ) , IsEquivalence θ × compatible A θ

  con : (A : Algebra 𝓤 𝑆)  →  Pred (Rel ∣ A ∣ 𝓤) (𝓞 ⊔ 𝓥 ⊔ 𝓤)
  con A = λ θ → IsEquivalence θ × compatible A θ

  record Congruence {𝓠 𝓤 : Universe} (A : Algebra 𝓠 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ⁺ ̇  where
    constructor mkcon
    field
      ⟨_⟩ : Rel ∣ A ∣ 𝓤
      Compatible : compatible A ⟨_⟩
      IsEquiv : IsEquivalence ⟨_⟩
  open Congruence

  Δ : funext 𝓥 𝓤 → (A : Algebra 𝓤 𝑆) → Congruence A
  Δ fe A = mkcon 𝟎-rel
                ( 𝟎-compatible fe )
                ( 𝟎-IsEquivalence )

  _/̇_ : {𝓤 𝓧 : Universe}(A : Algebra 𝓤 𝑆) → Congruence{𝓤}{𝓧} A  -- type /̇ with `/\^.`
        ---------------------------------
   →     Algebra (𝓤 ⁺ ⊔ 𝓧 ⁺) 𝑆
  A /̇ θ = (( ∣ A ∣ /ᵣ ⟨ θ ⟩ ) , -- carrier (i.e. domain or universe))
            (λ f args         -- operations
             → ([ (f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) ]ᵣ ⟨ θ ⟩) ,
               ((f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
            )
          )

  Zero/̇ : {𝓤 𝓧 : Universe}{A : Algebra 𝓤 𝑆} → (θ : Congruence{𝓤}{𝓧} A) → Rel (∣ A ∣ /ᵣ ⟨ θ ⟩) (𝓤 ⁺ ⊔ 𝓧 ⁺)
  Zero/̇ θ = λ x x₁ → x ≡ x₁

  /̇-refl : {𝓤 𝓧 : Universe}(A : Algebra 𝓤 𝑆){θ : Congruence{𝓤}{𝓧} A}{a a' : ∣ A ∣}
   →   ⟦ a ⟧ᵣ{⟨ θ ⟩} ≡ ⟦ a' ⟧ᵣ → ⟨ θ ⟩ a a'
  /̇-refl A {θ} (refl _)  = IsEquivalence.rfl (IsEquiv θ) _


module congruence-relations-predicates {𝑆 : Signature 𝓞 𝓥}  where

  open relation-predicate-classes

  Con : (A : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
  Con {𝓤} A =
   Σ θ ꞉ ( Rel ∣ A ∣ 𝓤 ) , IsEquivalence θ × compatible A θ

  con : (A : Algebra 𝓤 𝑆)  →  Pred (Rel ∣ A ∣ 𝓤) (𝓞 ⊔ 𝓥 ⊔ 𝓤)
  con A = λ θ → IsEquivalence θ × compatible A θ

  record Congruence {𝓠 𝓤 : Universe} (A : Algebra 𝓠 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ⁺ ̇  where
    constructor mkcon
    field
      ⟨_⟩ : Rel ∣ A ∣ 𝓤
      Compatible : compatible A ⟨_⟩
      IsEquiv : IsEquivalence ⟨_⟩
  open Congruence

  Δ : funext 𝓥 𝓤 → (A : Algebra 𝓤 𝑆) → Congruence A
  Δ fe A = mkcon 𝟎-rel
                ( 𝟎-compatible fe )
                ( 𝟎-IsEquivalence )

  _╱_ : {𝓤 𝓧 : Universe}(A : Algebra 𝓤 𝑆) → Congruence{𝓤}{𝓧} A  -- type ╱ with `\---` and then
        ---------------------------------                          -- `C-f` a number of times
   →     Algebra (𝓤 ⊔ 𝓧 ⁺) 𝑆
  A ╱ θ = (( ∣ A ∣ /ₚ ⟨ θ ⟩ ) , -- carrier (i.e. domain or universe))
            (λ f args         -- operations
             → ([ (f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩) ,
               ((f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
            )
          )

  Zero╱ : {𝓤 𝓧 : Universe}{A : Algebra 𝓤 𝑆} → (θ : Congruence{𝓤}{𝓧} A) → Rel (∣ A ∣ /ₚ ⟨ θ ⟩) (𝓤 ⊔ 𝓧 ⁺)
  Zero╱ θ = λ x x₁ → x ≡ x₁

  ╱-refl : {𝓤 𝓧 : Universe}(A : Algebra 𝓤 𝑆){θ : Congruence{𝓤}{𝓧} A}{a a' : ∣ A ∣}
   →   ⟦ a ⟧{⟨ θ ⟩} ≡ ⟦ a' ⟧ → ⟨ θ ⟩ a a'
  ╱-refl A {θ} (refl _)  = IsEquivalence.rfl (IsEquiv θ) _


\end{code}


