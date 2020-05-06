--File: UF-Free.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 23 Feb 2020
--Notes: Based on the file `free.agda` (25 Dec 2019).

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude using (Universe; 𝓜; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; _≡_; refl; _∼_; _≡⟨_⟩_; _∎; ap; _⁻¹; _∘_)
open import UF-Basic using (Signature; Algebra; Π')
open import UF-Hom using (Hom)
open import UF-Con using (Con; compatible-fun)
open import UF-Extensionality using (propext; dfunext; funext; _∈_; global-funext)
open import Relation.Unary using (Pred)

module UF-Free {S : Signature 𝓞 𝓥}  where

----------------------------
-- TERMS in the signature S
----------------------------
-- open signature
module _ {X : 𝓤 ̇} where
  data Term  : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇  where
    generator : X → Term
    node : ( 𝓸 : ∣ S ∣ )  →  ( 𝒕 : ∥ S ∥ 𝓸 → Term )  →  Term

  open Term

  map-Term : (Term -> Term) -> Term -> Term
  map-Term f (generator x) = f (generator x)
  map-Term f (node 𝓸 𝒕) = node 𝓸 (λ i -> map-Term f (𝒕 i))

  ----------------------------------
  -- TERM ALGEBRA (for signature S)
  ----------------------------------

  𝔉 : Algebra _ S
  𝔉 = Term , node

-------------------------------------
-- The UNIVERSAL PROPERTY of free

module _ {X : 𝓤 ̇} {𝑨 : Algebra 𝓤 S} where

  -- We first prove this for algebras whose carriers are mere sets.

  -- 1. every h : X -> ⟦ A ⟧ᵤ  lifts to a hom from free to A.
  -- 2. the induced hom is unique.

  -- PROOF.
  -- 1.a. Every map  (X → A)  "lifts".
  free-lift : (h : X → ∣ 𝑨 ∣)  →   ∣ 𝔉 ∣ → ∣ 𝑨 ∣
  free-lift h (generator x) = h x
  free-lift h (node 𝓸 args) = (∥ 𝑨 ∥ 𝓸) λ{i -> free-lift  h (args i)}

  -- 1.b. The lift is a hom.
  lift-hom : (h : X → ∣ 𝑨 ∣) →  Hom 𝔉 𝑨
  lift-hom  h = free-lift h , λ 𝓸 𝒂 → ap (∥ 𝑨 ∥ _) (refl _) --cong (⟦ 𝑨 ⟧ _) refl
  --record { ⟦_⟧ₕ = free-lift {A} h; homo = λ args → refl }

  -- 2. The lift to  (free -> A)  is unique.
  --    (We need EXTENSIONALITY for this (imported from util.agda))
  free-unique : funext 𝓥 𝓤 → ( f g : Hom 𝔉 𝑨 )
   →             ( ∀ x  ->  ∣ f ∣ (generator x) ≡ ∣ g ∣ (generator x) )
   →             (t : Term {X = X})
                  ---------------------------
   →              ∣ f ∣ t ≡ ∣ g ∣ t

  free-unique fe f g p (generator x) = p x
  free-unique fe f g p (node 𝓸 args) =
      ( ∣ f ∣ )(node 𝓸 args)             ≡⟨ ∥ f ∥ 𝓸 args ⟩
      (∥ 𝑨 ∥ 𝓸) (λ i -> ∣ f ∣ (args i))   ≡⟨ ap (∥ 𝑨 ∥ _) (fe (λ i → free-unique fe f g p (args i)) ) ⟩
      (∥ 𝑨 ∥ 𝓸) (λ i -> ∣ g ∣ (args i))   ≡⟨ (∥ g ∥ 𝓸 args)⁻¹ ⟩
      ∣ g ∣ (node 𝓸 args)                 ∎

--SUGAR:  𝓸 ̂ 𝑨  ≡  ⟦ 𝑨 ⟧ 𝓸   -------------------------------------
--Before proceding, we define some syntactic sugar that allows us
--to replace ⟦ 𝑨 ⟧ 𝓸 with (the more standard-looking) 𝓸 ̂ 𝑨.
_̂_ :  (𝓸 : ∣ S ∣ ) → (𝑨 : Algebra 𝓤 S)
 →       ( ∥ S ∥ 𝓸  →  ∣ 𝑨 ∣ ) → ∣ 𝑨 ∣
𝓸 ̂ 𝑨 = λ x → (∥ 𝑨 ∥ 𝓸) x
--We can now write 𝓸 ̂ 𝑨 for the interpretation of the basic
--operation 𝓸 in the algebra 𝑨.  N.B. below, we will write
--   𝒕 ̇ 𝑨    for the interpretation of a TERM 𝒕 in 𝑨.

----------------------------------------------------------------------
--INTERPRETATION OF TERMS
--------------------------
--(cf Def 4.31 of Bergman)
--Let 𝒕 : Term be a term, 𝑨 an algebra, in the signature S. We define an
--n-ary operation, denoted (𝒕 ̇ 𝑨), on 𝑨 by recursion on the struct of 𝒕.
-- 1. if 𝒕 is the var x ∈ X, 𝒂 : X -> ∣ 𝑨 ∣ a tuple from A, then (t ̇ 𝑨) 𝒂 = 𝒂 x.
-- 2. if 𝒕 = 𝓸 args, 𝓸 ∈ ∣ S ∣ an op symbol, args : ⟦ S ⟧ 𝓸 -> Term a
--    (⟦ S ⟧ 𝓸)-tuple of terms, 𝒂 : X -> ∣ A ∣ a tuple from A, then
--    (𝒕 ̇ 𝑨) 𝒂 = ((𝓸 args) ̇ 𝑨) 𝒂 = (𝓸 ̂ 𝑨) λ{ i -> ((args i) ̇ 𝑨) 𝒂 }
-- Here is how we implement this definition in Agda.

--Interpretation of a term.
_̇_ : {X : 𝓤 ̇ } → Term → (𝑨 : Algebra 𝓤 S) →  ( X → ∣ 𝑨 ∣ ) → ∣ 𝑨 ∣
((generator x)̇ 𝑨) 𝒂 = 𝒂 x
((node 𝓸 args)̇ 𝑨) 𝒂 = (𝓸 ̂ 𝑨) λ{x → (args x ̇ 𝑨) 𝒂 }

interp-prod : funext 𝓥 𝓤 → {X I : 𝓤 ̇} (p : Term)  (𝓐 : I → Algebra 𝓤 S) ( x : X → ∀ i → ∣ (𝓐 i) ∣ )
 →              (p ̇ (Π' 𝓐)) x  ≡   (λ i → (p ̇ 𝓐 i) (λ j -> x j i))
interp-prod fe (generator x₁) 𝓐 x = refl _
interp-prod fe (node 𝓸 𝒕) 𝓐 x =
  let IH = λ x₁ → interp-prod fe (𝒕 x₁) 𝓐 x in
      ∥ Π' 𝓐 ∥ 𝓸 (λ x₁ → (𝒕 x₁ ̇ Π' 𝓐) x)                                ≡⟨ ap (∥ Π' 𝓐 ∥ 𝓸 ) (fe IH) ⟩
      ∥ Π' 𝓐 ∥ 𝓸 (λ x₁ → (λ i₁ → (𝒕 x₁ ̇ 𝓐 i₁) (λ j₁ → x j₁ i₁))) ≡⟨ refl _ ⟩   -- refl ⟩
      (λ i₁ → ∥ 𝓐 i₁ ∥ 𝓸 (λ x₁ → (𝒕 x₁ ̇ 𝓐 i₁) (λ j₁ → x j₁ i₁)))  ∎

interp-prod2 : global-funext → {X I : 𝓤 ̇} (p : Term) ( A : I → Algebra 𝓤 S )
 →              (p ̇ Π' A)  ≡  λ (args : X → ∣ Π' A ∣ ) → ( λ ᵢ → (p ̇ A ᵢ ) ( λ x → args x ᵢ ) )
interp-prod2 fe (generator x₁) A = refl _
interp-prod2 fe {X = X} (node 𝓸 𝒕) A = fe λ ( tup : X → ∣ Π' A ∣ ) →
  let IH = λ x → interp-prod fe (𝒕 x) A  in
  let tᴬ = λ z → 𝒕 z ̇ Π' A in
    ( 𝓸 ̂ Π' A )  ( λ s → tᴬ s tup )                                    ≡⟨ refl _ ⟩
    ∥ Π' A ∥ 𝓸 ( λ s →  tᴬ s tup )                                     ≡⟨ ap ( ∥ Π' A ∥ 𝓸 ) (fe  λ x → IH x tup) ⟩
    ∥ Π' A ∥ 𝓸 (λ s → (λ ⱼ → (𝒕 s ̇ A ⱼ ) ( λ ℓ → tup ℓ ⱼ ) ) )  ≡⟨ refl _ ⟩
    ( λ ᵢ → (𝓸 ̂ A ᵢ ) (λ s → (𝒕 s ̇ A ᵢ ) (λ ℓ → tup ℓ ᵢ ) ) )     ∎


-- Recall (cf. UAFST Thm 4.32)
-- Theorem 1. If A and B are algebras of type S, then the following hold:
--   1. For every n-ary term t and homomorphism g: A → B,  g ( tᴬ ( a₁, ..., aₙ ) ) = tᴮ ( g (a₁), ..., g (aₙ) ).
--
--  2. For every term t ∈ T(X) and every θ ∈ Con(A),  a θ b → t(a) θ t(b).
--
--  3. For every subset Y of A,  Sg ( Y ) = { t (a₁, ..., aₙ ) : t ∈ T(Xₙ), n < ω, aᵢ ∈ Y, i ≤ n}.
--
-- Proof of 1. (homomorphisms commute with terms).
comm-hom-term : funext 𝓥 𝓤 → {X : 𝓤 ̇} (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓤 S)
 →                   (g : Hom 𝑨 𝑩)   →  (𝒕 : Term)  →   (𝒂 : X → ∣ 𝑨 ∣)
                      --------------------------------------------
 →                           ∣ g ∣ ((𝒕 ̇ 𝑨) 𝒂) ≡ (𝒕 ̇ 𝑩) (∣ g ∣ ∘ 𝒂)

comm-hom-term fe 𝑨 𝑩 g (generator x) 𝒂 = refl _
comm-hom-term  fe 𝑨 𝑩 g (node 𝓸 args) 𝒂 =
    ∣ g ∣ ((𝓸 ̂ 𝑨)  (λ i₁ → (args i₁ ̇ 𝑨) 𝒂))     ≡⟨ ∥ g ∥ 𝓸 ( λ r → (args r ̇ 𝑨) 𝒂 ) ⟩
    (𝓸 ̂ 𝑩) ( λ i₁ →  ∣ g ∣ ((args i₁ ̇ 𝑨) 𝒂) )    ≡⟨ ap (_ ̂ 𝑩) ( fe (λ i₁ → comm-hom-term fe 𝑨 𝑩 g (args i₁) 𝒂) ) ⟩
    (𝓸 ̂ 𝑩) ( λ r -> (args r ̇ 𝑩) (∣ g ∣ ∘ 𝒂) )        ∎

-- Proof of 2.  (If t : Term, θ : Con A, then a θ b  →  t(a) θ t(b). )
compatible-term :    {X : 𝓤 ̇} (𝑨 : Algebra 𝓤 S) ( 𝒕 : Term {X = X} ) (θ : Con 𝑨)
                         ------------------------------------------------------
 →                              compatible-fun (𝒕 ̇ 𝑨) ∣ θ ∣

compatible-term 𝑨 (generator x) θ p = p x
compatible-term 𝑨 (node 𝓸 args) θ p = ∥ ∥ θ ∥ ∥ 𝓸 λ{ x -> (compatible-term 𝑨 (args x) θ) p }

-- For proof of 3, see `TermImageSub` in Subuniverse.agda.

------------------------------------------------------------------
_⊢_≈_ : {X : 𝓤 ̇} → Algebra 𝓤 S → Term {X = X} → Term → 𝓤 ̇
𝑨 ⊢ p ≈ q = p ̇ 𝑨 ≡ q ̇ 𝑨

_⊢_≋_ : {𝓤 : Universe} {X : 𝓤 ̇} → Pred (Algebra 𝓤 S) 𝓦 → Term {X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇
_⊢_≋_ 𝓚 p q = {A : Algebra _ S} → 𝓚 A → A ⊢ p ≈ q



---------------------------------------------------------


-- ARITY OF A TERM
-- argsum : ℕ -> (ℕ -> ℕ) -> ℕ
-- argsum nzero f = 0
-- argsum (succ n) f = f n + argsum n f
-- ⟨_⟩ₜ : Term -> ℕ
-- ⟨ generator x ⟩ₜ = 1
-- ⟨ node 𝓸 args ⟩ₜ = (S ρ) 𝓸 + argsum ((S ρ) 𝓸) (λ i -> ⟨ args i ⟩ₜ)


-- Goal: B ⊢ p ≈ q
-- ————————————————————————————————————————————————————————————
-- B≤A     : B is-subalgebra-of A
-- A∈SClo𝓚 : A ∈ SClo 𝓚
-- A       : Algebra 𝓤 S
-- B       : Algebra 𝓤 S
-- 𝓚⊢p≋q   : 𝓚 ⊢' p ≋ q
-- q       : Term
-- p       : Term
-- X       : 𝓤 ̇


--------------------------------------------------------------------
-- vclo-id1 {p} {q} α ( vsub A∈VClo𝓚 B≤A ) = {!!}
--  vsub : ∀ {𝑨 : Algebra _ S} {𝑩 : Algebra _ S} → 𝑨 ∈ VClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ VClo 𝓚

-- Goal: B ⊢ p ≈ q
-- ————————————————————————————————————————————————————————————
-- B≤A     : B is-subalgebra-of A
-- A∈VClo𝓚 : A ∈ VClo 𝓚
-- A       : Algebra 𝓤 S
-- B       : Algebra 𝓤 S
-- α       : 𝓚 ⊢' p ≋ q
-- q       : Term
-- p       : Term
-- X       : 𝓤 ̇


--   vhom : {𝑨 𝑩 : Algebra 𝓤 S} {f : Hom 𝑨 𝑩} → 𝑨 ∈ VClo 𝓚 →  hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ VClo 𝓚
-- Goal: hom-image-alg f ⊢ p ≈ q
-- ————————————————————————————————————————————————————————————
-- 𝑨∈VClo𝓚 : A ∈ VClo 𝓚
-- f       : Hom A B
-- B       : Algebra 𝓤 S
-- A       : Algebra 𝓤 S
-- α       : 𝓚 ⊢' p ≋ q
-- q       : Term
-- p       : Term
-- X       : 𝓤 ̇
