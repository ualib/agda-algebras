\begin{code}
--FILE: terms.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--UPDATE: 4 Aug 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext)

module terms
 {𝑆 : Signature 𝓞 𝓥}
 {𝓤 : Universe}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext} where

open import homomorphisms {𝑆 = 𝑆}

open import prelude using (pr₂; Inv; InvIsInv; eq) public

data Term {𝓤 : Universe}{X : 𝓤 ̇} : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
  generator : X → Term{𝓤}{X}
  node : (f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓤}{X}) → Term

open Term

--The term algebra 𝑻(X).
𝑻 : {𝓤 : Universe}(X : 𝓤 ̇) → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) 𝑆
𝑻 {𝓤} X = Term{𝓤}{X} , node

term-op : {𝓤 : Universe}{X : 𝓤 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓤}{X} ) → Term
term-op f args = node f args

--1.a. Every map (X → 𝑨) lifts.
free-lift : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}{𝑨 : Algebra 𝓦 𝑆} (h : X → ∣ 𝑨 ∣)
 →          ∣ 𝑻 X ∣ → ∣ 𝑨 ∣

free-lift h (generator x) = h x
free-lift {𝑨 = 𝑨} h (node f args) = (f ̂ 𝑨) λ i → free-lift{𝑨 = 𝑨} h (args i)

--1.b. The lift is (extensionally) a hom
lift-hom : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}{𝑨 : Algebra 𝓦 𝑆}(h : X → ∣ 𝑨 ∣)
 →         hom (𝑻 X) 𝑨

lift-hom {𝑨 = 𝑨} h = free-lift{𝑨 = 𝑨} h , λ f a → ap (_ ̂ 𝑨) 𝓇ℯ𝒻𝓁

--2. The lift to (free → 𝑨) is (extensionally) unique.
free-unique : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → funext 𝓥 𝓦
 →            {𝑨 : Algebra 𝓦 𝑆}(g h : hom (𝑻 X) 𝑨)
 →            (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
 →            (t : Term{𝓤}{X})
             ---------------------------
 →            ∣ g ∣ t ≡ ∣ h ∣ t

free-unique fe g h p (generator x) = p x
free-unique {𝓤}{𝓦} {X} fe {𝑨 = 𝑨} g h p (node f args) =
   ∣ g ∣ (node f args)            ≡⟨ ∥ g ∥ f args ⟩
   (f ̂ 𝑨)(λ i → ∣ g ∣ (args i))  ≡⟨ ap (_ ̂ 𝑨) γ ⟩
   (f ̂ 𝑨)(λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ f args)⁻¹ ⟩
   ∣ h ∣ (node f args)             ∎
   where γ = fe λ i → free-unique {𝓤}{𝓦} fe {𝑨} g h p (args i)

--lift agrees on X
lift-agrees-on-X : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓤 𝑆}(h₀ : X → ∣ 𝑨 ∣)(x : X)
        ----------------------------------------
 →       h₀ x ≡ ∣ lift-hom{𝑨 = 𝑨} h₀ ∣ (generator x)

lift-agrees-on-X h₀ x = 𝓇ℯ𝒻𝓁

--Of course, the lift of a surjective map is surjective.
lift-of-epic-is-epic : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓤 𝑆}(h₀ : X → ∣ 𝑨 ∣)
 →                     Epic h₀
                      ----------------------
 →                     Epic ∣ lift-hom{𝑨 = 𝑨} h₀ ∣

lift-of-epic-is-epic{X = X}{𝑨 = 𝑨} h₀ hE y = γ
 where
  h₀pre : Image h₀ ∋ y
  h₀pre = hE y

  h₀⁻¹y : X
  h₀⁻¹y = Inv h₀ y (hE y)

  η : y ≡ ∣ lift-hom{𝑨 = 𝑨} h₀ ∣ (generator h₀⁻¹y)
  η =
   y                               ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
   h₀ h₀⁻¹y                        ≡⟨ lift-agrees-on-X{X = X}{𝑨 = 𝑨} h₀ h₀⁻¹y ⟩
   ∣ lift-hom{𝑨 = 𝑨} h₀ ∣ (generator h₀⁻¹y) ∎

  γ : Image ∣ lift-hom h₀ ∣ ∋ y
  γ = eq y (generator h₀⁻¹y) η

𝑻hom-gen : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} (𝑪 : Algebra 𝓤 𝑆)
 →         Σ h ꞉ (hom (𝑻 X) 𝑪), Epic ∣ h ∣
𝑻hom-gen {X = X}𝑪 = h , lift-of-epic-is-epic h₀ hE
 where
  h₀ : X → ∣ 𝑪 ∣
  h₀ = fst (𝕏 𝑪)

  hE : Epic h₀
  hE = snd (𝕏 𝑪)

  h : hom (𝑻 X) 𝑪
  h = lift-hom{𝑨 = 𝑪} h₀


_̇_ : {𝓤 𝓦 : Universe}{X : 𝓤 ̇ } → Term{𝓤}{X}
 →   (𝑨 : Algebra 𝓦 𝑆) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣

((generator x) ̇ 𝑨) 𝒂 = 𝒂 x

((node f args) ̇ 𝑨) 𝒂 = (f ̂ 𝑨) λ i → (args i ̇ 𝑨) 𝒂


-- Want (𝒕 : X → ∣ 𝑻(X) ∣) → ((p ̇ 𝑻(X)) 𝒕) ≡ p 𝒕... but what is (𝑝 ̇ 𝑻(X)) 𝒕 ?
-- By definition, it depends on the form of 𝑝 as follows:
-- * if 𝑝 = (generator x), then
--      (𝑝 ̇ 𝑻(X)) 𝒕 = ((generator x) ̇ 𝑻(X)) 𝒕 = 𝒕 x
-- * if 𝑝 = (node f args), then
--      (𝑝 ̇ 𝑻(X)) 𝒕 = ((node f args) ̇ 𝑻(X)) 𝒕 = (f ̂ 𝑻(X)) λ i → (args i ̇ 𝑻(X)) 𝒕
-- Let h : hom 𝑻 𝑨. Then by comm-hom-term,
-- ∣ h ∣ (p ̇ 𝑻(X)) 𝒕 = (p ̇ 𝑨) ∣ h ∣ ∘ 𝒕
-- * if p = (generator x), then
--    ∣ h ∣ p ≡ ∣ h ∣ (generator x)
--           ≡ λ 𝒕 → 𝒕 x) (where 𝒕 : X → ∣ 𝑻(X) ∣ )
--           ≡ (λ 𝒕 → (∣ h ∣ ∘ 𝒕) x)
--    ∣ h ∣ p ≡ ∣ h ∣ (λ 𝒕 → 𝒕 x) (where 𝒕 : X → ∣ 𝑻(X) ∣ )
--           ≡ (λ 𝒕 → (∣ h ∣ ∘ 𝒕) x)
-- * if p = (node f args), then
--    ∣ h ∣ p ≡ ∣ h ∣  (p ̇ 𝑻(X)) 𝒕 = ((node f args) ̇ 𝑻(X)) 𝒕 = (f ̂ 𝑻(X)) λ i → (args i ̇ 𝑻(X)) 𝒕

-- We claim that if p : ∣ 𝑻(X) ∣ then there exists 𝓅 : ∣ 𝑻(X) ∣ and 𝒕 : X → ∣ 𝑻(X) ∣
-- such that p ≡ (𝓅 ̇ 𝑻(X)) 𝒕. We prove this fact in the following module:

term-op-interp1 : {𝓤 : Universe}{X : 𝓤 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓤}{X})
 →                node f args ≡ (f ̂ 𝑻 X) args

term-op-interp1 = λ f args → 𝓇ℯ𝒻𝓁

term-op-interp2 : {𝓤 : Universe}{X : 𝓤 ̇}(f : ∣ 𝑆 ∣){a1 a2 : ∥ 𝑆 ∥ f → Term{𝓤}{X}}
 →                a1 ≡ a2  →  node f a1 ≡ node f a2

term-op-interp2 f a1≡a2 = ap (node f) a1≡a2

term-op-interp3 : {𝓤 : Universe}{X : 𝓤 ̇}(f : ∣ 𝑆 ∣){a1 a2 : ∥ 𝑆 ∥ f → Term{𝓤}{X}}
 →                a1 ≡ a2  →  node f a1 ≡ (f ̂ 𝑻 X) a2

term-op-interp3 f {a1}{a2} a1a2 = (term-op-interp2 f a1a2) ∙ (term-op-interp1 f a2)

term-gen : {𝓤 : Universe}{X : 𝓤 ̇}(p : ∣ 𝑻 X ∣)
 →         Σ 𝓅 ꞉ ∣ 𝑻 X ∣ , p ≡ (𝓅 ̇ 𝑻 X) generator

term-gen (generator x) = (generator x) , 𝓇ℯ𝒻𝓁
term-gen (node f args) = node f (λ i → ∣ term-gen (args i) ∣) ,
                                term-op-interp3 f (gfe λ i → ∥ term-gen (args i) ∥)

tg : {𝓤 : Universe}{X : 𝓤 ̇}(p : ∣ 𝑻 X ∣) → Σ 𝓅 ꞉ ∣ 𝑻 X ∣ , p ≡ (𝓅 ̇ 𝑻 X) generator
tg p = term-gen p

term-gen-agree : {𝓤 : Universe}{X : 𝓤 ̇}(p : ∣ 𝑻 X ∣)
 →               (p ̇ 𝑻 X) generator ≡ (∣ term-gen p ∣ ̇ 𝑻 X) generator
term-gen-agree (generator x) = 𝓇ℯ𝒻𝓁
term-gen-agree {X = X}(node f args) = ap (f ̂ 𝑻 X) (gfe λ x → term-gen-agree (args x))

term-agree : {𝓤 : Universe}{X : 𝓤 ̇}(p : ∣ 𝑻 X ∣)
 →            p ≡ (p ̇ 𝑻 X) generator
term-agree p = snd (term-gen p) ∙ (term-gen-agree p)⁻¹


interp-prod : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → funext 𝓥 𝓦
 →            {I : 𝓦 ̇}(p : Term{𝓤}{X})
              (𝒜 : I → Algebra 𝓦 𝑆)
              (x : X → ∀ i → ∣ (𝒜 i) ∣)
 →            (p ̇ (⨅ 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

interp-prod fe (generator x₁) 𝒜 x = 𝓇ℯ𝒻𝓁

interp-prod fe (node f t) 𝒜 x =
 let IH = λ x₁ → interp-prod fe (t x₁) 𝒜 x in
  (f ̂ ⨅ 𝒜) (λ x₁ → (t x₁ ̇ ⨅ 𝒜) x)
      ≡⟨ ap (f ̂ ⨅ 𝒜)(fe IH) ⟩
  (f ̂ ⨅ 𝒜) (λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
      ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
  (λ i₁ → (f ̂ 𝒜 i₁) (λ x₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
      ∎

interp-prod2 : global-dfunext → {𝓤 : Universe}{X : 𝓤 ̇}{I : 𝓤 ̇ }
 →             (p : Term) (𝒜 : I → Algebra 𝓤 𝑆)
     ----------------------------------------------------------------------
 →   (p ̇ ⨅ 𝒜)  ≡  λ(args : X → ∣ ⨅ 𝒜 ∣) → (λ i → (p ̇ 𝒜 i)(λ x → args x i))

interp-prod2 fe (generator x₁) 𝒜 = 𝓇ℯ𝒻𝓁

interp-prod2 fe {𝓤}{X} (node f t) 𝒜 = fe λ (tup : X → ∣ ⨅ 𝒜 ∣) →
  let IH = λ x → interp-prod fe (t x) 𝒜  in
  let tA = λ z → t z ̇ ⨅ 𝒜 in
   (f ̂ ⨅ 𝒜)(λ s → tA s tup)                          ≡⟨ ap (f ̂ ⨅ 𝒜)(fe  λ x → IH x tup) ⟩
   (f ̂ ⨅ 𝒜)(λ s → λ j → (t s ̇ 𝒜 j)(λ ℓ → tup ℓ j))  ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
   (λ i → (f ̂ 𝒜 i)(λ s → (t s ̇ 𝒜 i)(λ ℓ → tup ℓ i))) ∎

-- Homomorphisms commute (extensionally) with terms.
comm-hom-term : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇} → funext 𝓥 𝓦
 →       (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
 →       (h : hom 𝑨 𝑩) (t : Term{𝓧}{X}) (a : X → ∣ 𝑨 ∣)
         --------------------------------------------
 →         ∣ h ∣ ((t ̇ 𝑨) a) ≡ (t ̇ 𝑩) (∣ h ∣ ∘ a)

comm-hom-term  fe 𝑨 𝑩 h (generator x) a = 𝓇ℯ𝒻𝓁

comm-hom-term fe 𝑨 𝑩 h (node f args) a =
 ∣ h ∣((f ̂ 𝑨) λ i₁ → (args i₁ ̇ 𝑨) a)    ≡⟨ ∥ h ∥ f ( λ r → (args r ̇ 𝑨) a ) ⟩
 (f ̂ 𝑩)(λ i₁ →  ∣ h ∣((args i₁ ̇ 𝑨) a))  ≡⟨ ap (_ ̂ 𝑩)(fe (λ i₁ → comm-hom-term fe 𝑨 𝑩 h (args i₁) a))⟩
 (f ̂ 𝑩)(λ r → (args r ̇ 𝑩)(∣ h ∣ ∘ a))    ∎

-- Homomorphisms commute (intensionally) with terms.
comm-hom-term-intensional : global-dfunext → {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
 →       (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
 →       (h : hom 𝑨 𝑩) (t : Term{𝓧}{X})
         --------------------------------------------
 →         ∣ h ∣ ∘ (t ̇ 𝑨) ≡ (t ̇ 𝑩) ∘ (λ a → ∣ h ∣ ∘ a)

comm-hom-term-intensional gfe 𝑨 𝑩 h (generator x) = 𝓇ℯ𝒻𝓁

comm-hom-term-intensional gfe {X = X} 𝑨 𝑩 h (node f args) = γ
 where
  γ : ∣ h ∣ ∘ (λ a → (f ̂ 𝑨) (λ i → (args i ̇ 𝑨) a))
      ≡ (λ a → (f ̂ 𝑩)(λ i → (args i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣
  γ = (λ a → ∣ h ∣ ((f ̂ 𝑨)(λ i → (args i ̇ 𝑨) a)))  ≡⟨ gfe (λ a → ∥ h ∥ f ( λ r → (args r ̇ 𝑨) a )) ⟩
      (λ a → (f ̂ 𝑩)(λ i → ∣ h ∣ ((args i ̇ 𝑨) a)))  ≡⟨ ap (λ - → (λ a → (f ̂ 𝑩)(- a))) ih ⟩
      (λ a → (f ̂ 𝑩)(λ i → (args i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣  ∎
    where
     IH : (a : X → ∣ 𝑨 ∣)(i : ∥ 𝑆 ∥ f)
      →   (∣ h ∣ ∘ (args i ̇ 𝑨)) a ≡ ((args i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a
     IH a i = intensionality (comm-hom-term-intensional gfe 𝑨 𝑩 h (args i)) a

     ih : (λ a → (λ i → ∣ h ∣ ((args i ̇ 𝑨) a)))
           ≡ (λ a → (λ i → ((args i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a))
     ih = gfe λ a → gfe λ i → IH a i


-- Proof of 2. (If t : Term, θ : Con 𝑨, then a θ b → t(a) θ t(b))
compatible-term : {𝓤 : Universe}{X : 𝓤 ̇}
                  (𝑨 : Algebra 𝓤 𝑆)(t : Term{𝓤}{X})(θ : Con 𝑨)
                 ------------------------------------------------
 →                compatible-fun (t ̇ 𝑨) ∣ θ ∣

compatible-term 𝑨 (generator x) θ p = p x

compatible-term 𝑨 (node f args) θ p = pr₂ ∥ θ ∥ f λ x → (compatible-term 𝑨 (args x) θ) p

compatible-term' : {𝓤 : Universe} {X : 𝓤 ̇}
                   (𝑨 : Algebra 𝓤 𝑆)
                   (t : Term{𝓤}{X}) (θ : Con 𝑨)
                 ---------------------------------
 →                 compatible-fun (t ̇ 𝑨) ∣ θ ∣

compatible-term' 𝑨 (generator x) θ p = p x
compatible-term' 𝑨 (node f args) θ p = pr₂ ∥ θ ∥ f λ x → (compatible-term' 𝑨 (args x) θ) p

