--File: Free.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 23 Feb 2020
--Notes: Based on the file `free.agda` (25 Dec 2019).
--       Used for 2nd half of talk at JMM Special Session (Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic 
open import Hom
open import Con

module Free {i j k : Level} {S : Signature i j} {X : Set k}  where

----------------------------
-- TERMS in the signature S
----------------------------
-- open signature

-- data Term : Set (i ⊔ j ⊔ k) where
--   generator : X -> Term
--   node : (𝓸 : ∣ S ∣) -> (𝒕 : ⟦ S ⟧ 𝓸 -> Term) -> Term
data Term : Set (i ⊔ j ⊔ k) where
  generator : X -> Term
  node : (𝓸 : ∣ S ∣) -> (𝒕 : ⟦ S ⟧ 𝓸 -> Term) -> Term

open Term

map-Term : (Term -> Term) -> Term -> Term
map-Term f (generator x) = f (generator x)
map-Term f (node 𝓸 𝒕) = node 𝓸 (λ i -> map-Term f (𝒕 i))

----------------------------------
-- TERM ALGEBRA (for signature S)
----------------------------------

-- open Algebra
-- open Term

𝔉 : Algebra _ S
𝔉 = Term , node
--record { ⟦_⟧ᵤ = Term ; _⟦_⟧ = node }
-------------------------------------
-- The UNIVERSAL PROPERTY of free

-- We first prove this for algebras whose carriers are mere sets.

-- 1. every h : X -> ⟦ A ⟧ᵤ  lifts to a hom from free to A.
-- 2. the induced hom is unique.

-- PROOF.
-- 1.a. Every map  (X -> A)  "lifts".
--∀{ℓ : Level} 
--free-lift : {𝑨 : Algebra  (i ⊔ j ⊔ k) S}
free-lift : ∀ {l} {𝑨 : Algebra l S}
  ->        (h : X -> ∣ 𝑨 ∣)
          -----------------------------------
  ->        ∣ 𝔉 ∣ -> ∣ 𝑨 ∣
free-lift h (generator x) = h x
free-lift {𝑨 = 𝑨} h (node 𝓸 args) =
  (⟦ 𝑨 ⟧ 𝓸) λ{i -> free-lift {𝑨 = 𝑨} h (args i)}

-- 1.b. The lift is a hom.
--lift-hom : {𝑨 : Algebra (i ⊔ j ⊔ k) S}
lift-hom : ∀ {l} {𝑨 : Algebra l S}
  ->       (h : X -> ∣ 𝑨 ∣)
          ------------------------------------
  ->       Hom 𝔉 𝑨
lift-hom {𝑨 = 𝑨} h = free-lift {𝑨 = 𝑨} h , λ 𝓸 𝒂 → cong (⟦ 𝑨 ⟧ _) refl
--record { ⟦_⟧ₕ = free-lift {A} h; homo = λ args → refl }

-- 2. The lift to  (free -> A)  is unique.
--    (We need EXTENSIONALITY for this (imported from util.agda))
free-unique : ∀ {l} {𝑨 : Algebra l S}
  ->    ( f g : Hom 𝔉 𝑨 )
  ->    ( ∀ x  ->  ∣ f ∣ (generator x) ≡ ∣ g ∣ (generator x) )
  ->    (t : Term)
       ---------------------------
  ->    ∣ f ∣ t ≡ ∣ g ∣ t

free-unique f g p (generator x) = p x
free-unique {l} {𝑨} f g p (node 𝓸 args) =
   begin
     ( ∣ f ∣ )(node 𝓸 args)
   ≡⟨ ⟦ f ⟧ 𝓸 args ⟩
     (⟦ 𝑨 ⟧ 𝓸) (λ i -> ∣ f ∣ (args i))
   ≡⟨ cong (⟦ 𝑨 ⟧ _)
        (∀-extensionality-ℓ₁-ℓ₂ {j} {l}
          ( λ i -> free-unique {𝑨 = 𝑨} f g p (args i))
        )
    ⟩
     (⟦ 𝑨 ⟧ 𝓸) (λ i -> ∣ g ∣ (args i))
   ≡⟨ sym (⟦ g ⟧ 𝓸 args) ⟩
     ∣ g ∣ (node 𝓸 args)
   ∎

--SUGAR:  𝓸 ̂ 𝑨  ≡  ⟦ 𝑨 ⟧ 𝓸   -------------------------------------
--Before proceding, we define some syntactic sugar that allows us
--to replace ⟦ 𝑨 ⟧ 𝓸 with (the more standard-looking) 𝓸 ̂ 𝑨.
_̂_ : ∀{ℓ₁ : Level}
  ->  (𝓸 : ∣ S ∣) ->  (𝑨 : Algebra ℓ₁ S)
  ->  (⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣) -> ∣ 𝑨 ∣
𝓸 ̂ 𝑨 = λ x → (⟦ 𝑨 ⟧ 𝓸) x
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
_̇_ : {ℓ₁ : Level} -> Term -> (𝑨 : Algebra ℓ₁ S) -> (X -> ∣ 𝑨 ∣) -> ∣ 𝑨 ∣
((generator x)̇ 𝑨) 𝒂 = 𝒂 x
((node 𝓸 args)̇ 𝑨) 𝒂 = (𝓸 ̂ 𝑨) λ{x -> (args x ̇ 𝑨) 𝒂 }

-- Recall (cf. UAFST Thm 4.32)
-- Theorem 1.
-- Let A and B be algebras of type S. Then the following hold:
-- 1. For every n-ary term t and homomorphism g: A —> B, 
--    g(tᴬ(a₁,...,aₙ)) = tᴮ(g(a₁),...,g(aₙ)).
-- 2. For every term t ∈ T(X) and every θ ∈ Con(A), 
--    a θ b => t(a) θ t(b).
-- 3. For every subset Y of A,
--    Sg(Y) = {t(a₁,...,aₙ) : t ∈ T(Xₙ), n < ω, aᵢ ∈ Y, i ≤ n}.
-- PROOF.
-- 1. (homomorphisms commute with terms).
comm-hom-term : ∀ {l m} → (𝑨 : Algebra l S) (𝑩 : Algebra m S)
  ->            (g : Hom 𝑨 𝑩) -> (𝒕 : Term)
  ->            (𝒂 : X -> ∣ 𝑨 ∣)
              ----------------------------------------
  ->            ∣ g ∣ ((𝒕 ̇ 𝑨) 𝒂) ≡ (𝒕 ̇ 𝑩) (∣ g ∣ ∘ 𝒂)

comm-hom-term 𝑨 𝑩 g (generator x) 𝒂 = refl
comm-hom-term {m = m} 𝑨 𝑩 g (node 𝓸 args) 𝒂 =
  begin
    ∣ g ∣ ((𝓸 ̂ 𝑨)  (λ i₁ → (args i₁ ̇ 𝑨) 𝒂))
  ≡⟨ ⟦ g ⟧ 𝓸 ( λ r → (args r ̇ 𝑨) 𝒂 ) ⟩
    (𝓸 ̂ 𝑩) ( λ i₁ →  ∣ g ∣ ((args i₁ ̇ 𝑨) 𝒂) )
    ≡⟨ cong (_ ̂ 𝑩) (( ∀-extensionality-ℓ₁-ℓ₂ {j} {m}
                         (λ i₁ -> comm-hom-term 𝑨 𝑩 g (args i₁) 𝒂  )
                      ))
     ⟩
    (𝓸 ̂ 𝑩) ( λ r -> (args r ̇ 𝑩) (∣ g ∣ ∘ 𝒂) )
  ∎

--For 2 of Thm 1, we need congruences (see Congruence.agda).
-- 2. If t : Term, θ : Con A, then a θ b => t(a) θ t(b).
compatible-term : (𝑨 : Algebra k S)
  ->              (𝒕 : Term)
  ->              (θ : Con 𝑨)
                 ------------------------------------
  ->              compatible-fun {i} {j} {k} {S} (𝒕 ̇ 𝑨) ∣ θ ∣
  -- wjd: I don't know why this ^^^^^^^^^^^^^^^^^ combination
  --      of implicit vars works... very weird.
compatible-term 𝑨 (generator x) θ p = p x
compatible-term 𝑨 (node 𝓸 args) θ p =
  ⟦ ⟦ θ ⟧ ⟧ 𝓸 λ{ x -> (compatible-term 𝑨 (args x) θ) p }

-- For proof of item (3), see `TermImageSub` in Subuniverse.agda.

------------------------------------------------------------------
_⊢_≈_ : ∀ {l} → Algebra l S → Term → Term → Set _
𝑨 ⊢ p ≈ q = p ̇ 𝑨 ≡ q ̇ 𝑨

_⊢_≋_ : ∀ {l m} → Pred (Algebra l S) m → Term → Term → Set _
_⊢_≋_ {l} K p q = {𝑨 : Algebra l S} → 𝑨 ∈ K → 𝑨 ⊢ p ≈ q

---------------------------------------------------------


  -- const : ∣ 𝑨 ∣ -> X -> ∣ 𝑨 ∣
  -- const a = λ x -> a
-- module _  {S : Signature i j} {𝑨 𝑩 : Algebra k S}(X : Set k) where

--   _ForkTerm_ : {𝓸 : ∣ S ∣ }-> (⟦ S ⟧ 𝓸 -> Term) -> (⟦ S ⟧ 𝓸 -> X -> ∣ 𝑨 ∣ )
--     ->          ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣
--   𝒕 ForkTerm args = (λ i -> ((𝒕 i) ̇ 𝑨) (args i))
  











-- ARITY OF A TERM
-- argsum : ℕ -> (ℕ -> ℕ) -> ℕ
-- argsum nzero f = 0
-- argsum (succ n) f = f n + argsum n f
-- ⟨_⟩ₜ : Term -> ℕ
-- ⟨ generator x ⟩ₜ = 1
-- ⟨ node 𝓸 args ⟩ₜ = (S ρ) 𝓸 + argsum ((S ρ) 𝓸) (λ i -> ⟨ args i ⟩ₜ)

