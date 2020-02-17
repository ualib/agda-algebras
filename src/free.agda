--File: free.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 25 Dec 2019
--Updated: 17 Feb 2020

{-# OPTIONS --without-K --exact-split #-}

open import preliminaries
-- open import preliminaries  using (_⊎_ ; ∀-extensionality; ∑; List)
open import basic 

module free  {S : signature} {X : Set} where

open import Level
open import Agda.Builtin.Nat public
  renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
open import Relation.Unary hiding (_⊆_;_⇒_)
-- open import Relation.Binary.Core using (IsEquivalence)
--open import Relation.Binary using (IsEquivalence)
import Relation.Binary.PropositionalEquality as Eq
  hiding (setoid; Reveal_·_is_;[_];∀-extensionality)
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning
open import Function using (_∘_)
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (cong)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
--  using    ( _+_; _*_ )

-- open import Data.Fin public
--   -- (See "NOTE on Fin" section below)
--   hiding ( _+_; _<_ )
--   renaming ( suc to fsucc; zero to fzero )
--------------------------------------------------------------


----------------------------
-- TERMS in the signature S
----------------------------
open signature


data Term : Set where
  generator : X -> Term
  node : ∀ (𝓸 : S 𝓕) -> (ℕ -> Term) -> Term

open Term

-- map-Term : (Term -> Term) -> Term -> Term
-- map-Term f (generator x) = f (generator x)
-- map-Term f (node 𝓸 t) = node 𝓸 (λ i -> map-Term f (t i))

----------------------------------
-- TERM ALGEBRA (for signature S)
----------------------------------

open algebra
open Term

free : algebra S
free = record { ⟦_⟧ᵤ = Term ; _⟦_⟧ = node }

--------------------------------------------------------------
-- analogue for setoid-based algebras
open Setoid
open Algebra

Free : Algebra S
Free = record
       { ⟦_⟧ᵣ = record
               { Carrier = Term
               ; _≈_ = _≡_
               ; isEquiv = isequiv
               }
       ; _⟦_⟧ = node
       }
       where
         isequiv = record
                   { refl = λ {x} → refl
                   ; sym = sym
                   ; trans = λ {i} {j} {k} p q
                              ->  begin
                                    i
                                  ≡⟨ p ⟩
                                    j
                                  ≡⟨ q ⟩
                                    k
                                  ∎
                   }


-------------------------------------
-- The UNIVERSAL PROPERTY of free

-- We first prove this for algebras whose carriers are mere sets.

-- 1. every h : X -> ⟦ A ⟧ᵤ  lifts to a hom from free to A.
-- 2. the induced hom is unique.

-- PROOF.
-- 1.a. Every map  (X -> A)  "lifts".
free-lift : {A : algebra  S}(h : X -> ⟦ A ⟧ᵤ) -> ⟦ free ⟧ᵤ -> ⟦ A ⟧ᵤ
free-lift h (generator x) = h x
free-lift {A} h (node 𝓸 args) = (A ⟦ 𝓸 ⟧) λ{i -> free-lift {A} h (args i)}

-- 1.b. The lift is a hom.
open hom
lift-hom : {A : algebra S} (h : X -> ⟦ A ⟧ᵤ) -> hom free A
lift-hom {A} h = record { ⟦_⟧ₕ = free-lift {A} h; homo = λ args → refl }

-- 2. The lift to  (free -> A)  is unique.
--    (We need EXTENSIONALITY for this (imported from util.agda))
free-unique : {A : algebra S}
  ->    ( f g : hom free A )
  ->    ( ∀ x  ->  ⟦ f ⟧ₕ (generator x) ≡ ⟦ g ⟧ₕ (generator x) )
  ->    (t : Term)
       ---------------------------
  ->    ⟦ f ⟧ₕ t ≡ ⟦ g ⟧ₕ t

free-unique {A} f g p (generator x) = p x
free-unique {A} f g p (node 𝓸 args) =
   begin
     ⟦ f ⟧ₕ (node 𝓸 args)
   ≡⟨ homo f args  ⟩
     (A ⟦ 𝓸 ⟧) (λ i -> ⟦ f ⟧ₕ (args i))
   ≡⟨ cong ((A ⟦_⟧)_)
      ( ∀-extensionality λ i -> free-unique f g p (args i) ) ⟩
     (A ⟦ 𝓸 ⟧) (λ i -> ⟦ g ⟧ₕ (args i))
   ≡⟨ sym (homo g args) ⟩
     ⟦ g ⟧ₕ (node 𝓸 args)
   ∎



---------------------------------------------------------------
-- SETOID-based analogue
--
-- Next we prove the universal property of Free for algebras
-- whose carriers are setoids.

open Setoid 
Free-Lift : {A : Algebra  S}(h : X -> ∥ ⟦ A ⟧ᵣ ∥) -> ∥ ⟦ Free ⟧ᵣ ∥ -> ∥ ⟦ A ⟧ᵣ ∥
Free-Lift h (generator x) = h x
Free-Lift {A} h (node 𝓸 args) = (A ⟦ 𝓸 ⟧) λ i -> Free-Lift {A} h (args i)

----------------------------------------
-- 1.b. The lift is a hom.
open Hom
Lift-Hom : {A : Algebra S} (h : X -> ∥ ⟦ A ⟧ᵣ ∥) -> Hom Free A
Lift-Hom {A} h = record { ⟦_⟧ₕ = Free-Lift {A} h; Homo = λ args → {!!}}
-- Lift-Hom {A} h = record { ⟦_⟧ₕ = Free-Lift {A} h; Homo = λ args → refl ⟦ A ⟧ᵣ }

-- 2. The lift to  (free -> A)  is unique.
--    (We need EXTENSIONALITY for this (imported from util.agda))
Free-Unique : {A : Algebra S}
  ->    ( f g : Hom Free A )
  ->    ( ∀ x  ->   (⟦ A ⟧ᵣ ≈ ⟦ f ⟧ₕ (generator x)) (⟦ g ⟧ₕ (generator x)) )
  ->    (t : Term)
       ---------------------------
  ->    ( ⟦ A ⟧ᵣ ≈  ⟦ f ⟧ₕ t ) (⟦ g ⟧ₕ t)
   --   ⟦ f ⟧ₕ (node 𝓸 args)
Free-Unique = {!!}
--    ( ∀-extensionality λ i -> free-unique f g p (args i) ) ⟩

--      ( ∀-extensionality  ) ⟩
   -- begin
   --   ⟦ f ⟧ₕ (node 𝓸 args)
   -- ≡⟨ Homo f args  ⟩
   --   (A ⟦ 𝓸 ⟧) (λ i -> ⟦ f ⟧ₕ (args i))
   -- ≡⟨ cong ((A ⟦_⟧)_)
   --    ( ∀-extensionality λ i -> free-unique f g p (args i) ) ⟩
   --   (A ⟦ 𝓸 ⟧) (λ i -> ⟦ g ⟧ₕ (args i))
   -- ≡⟨ Eq.sym (Homo g args) ⟩
   --   ⟦ g ⟧ₕ (node 𝓸 args)
   -- ∎

--------------------------
--INTERPRETATION OF TERMS
--------------------------

--(cf Def 4.31 of Bergman)

--Let t ∈ Term be a term, A an algebra, in the signature S.
--We define an n-ary operation, denoted (t ̂ A), on A by recursion on
--the structure of t, as follows:

-- (1) if t is the variable x ∈ X and tup : X -> ⟦ A ⟧ᵤ is a tuple of elements of A,
--     then we define (t ̂ A) tup = tup x.

-- (2) if t = 𝓸 args, where 𝓸 ∈ ⟨ S ⟩ₒ is an operation symbol (of arity ⟨ S ⟩ₐ 𝓸),
--        args : ⟨ S ⟩ₐ 𝓸 -> Term is an (⟨ S ⟩ₐ 𝓸)-tuple of terms, and
--        tup : X -> ⟦ A ⟧ᵤ is a tuple of elements of A, then we define

--     (t ̂ A) tup = ((𝓸 args) ̂ A) tup
--                  = (A ⟦ 𝓸 ⟧) λ{ i -> ((args i) ̂ A) tup }

-- Here's the Agda implementation of the foregoing definition.

_̇_ : Term -> (A : algebra S) -> (X -> ⟦ A ⟧ᵤ) -> ⟦ A ⟧ᵤ
((generator x) ̇ A) tup = tup x
((node 𝓸 args) ̇ A) tup = (A ⟦ 𝓸 ⟧) λ{i -> (args i ̇ A) tup }

-- Recall (cf. Theorem 4.32 of Bergman)
--
-- Theorem 1.
-- Let A and B be algebras of type S. Then the following hold:
--
--   (1) For every n-ary term t and homomorphism g: A —> B, 
--       g(tᴬ(a₁,...,aₙ)) = tᴮ(g(a₁),...,g(aₙ)).
--   (2) For every term t ∈ T(X) and every θ ∈ Con(A), 
--       a θ b => t(a) θ t(b).
--   (3) For every subset Y of A,
--       Sg(Y) = { t(a₁,...,aₙ) : t ∈ T(Xₙ), n < ω, and aᵢ ∈ Y, for i ≤ n}.
--
-- PROOF.
--
-- (1) (homomorphisms commute with terms).
comm-hom-term : {A B : algebra S}
  ->    (g : hom A B) -> (t : Term)
  ->    (tup : X -> ⟦ A ⟧ᵤ)
       ------------------------------
  ->     ⟦ g ⟧ₕ ((t ̇ A) tup) ≡ (t ̇ B) (⟦ g ⟧ₕ ∘ tup)
--
comm-hom-term g (generator x) tup = Eq.refl
comm-hom-term {A} {B} g (node 𝓸 args) tup =  
-- Goal: ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̇ A) tup })) ≡
--       (B ⟦ 𝓸 ⟧) (λ { i → (args i ̇ B) ((λ {.x} → ⟦ g ⟧ₕ) ∘ tup) })
  begin
    ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̇ A) tup }))
  ≡⟨ homo g ( λ i → (args i ̇ A) tup )⟩
    (B ⟦ 𝓸 ⟧) ( λ i → ⟦ g ⟧ₕ ((args i ̇ A) tup) )
  ≡⟨ cong ((B ⟦_⟧)_)
     ( ∀-extensionality  λ i -> comm-hom-term g (args i) tup  ) ⟩
    (B ⟦ 𝓸 ⟧) ( λ i → (args i ̇ B) (⟦ g ⟧ₕ ∘ tup) )
  ∎

-- (2) For every term t ∈ T(X) and every θ ∈ Con(A), 
--     a θ b => t(a) θ t(b).
open con

compatible-term : (A : algebra S)
 ->               (t : Term)
 ->               (θ : con A)
                 -------------------
 ->               compatible-fun (t ̇ A) ⟦ θ ⟧ᵣ

compatible-term A (generator x) θ p = p x
compatible-term A (node 𝓸 args) θ p =
  --Goal:
  -- ( ⟦ θ ⟧ᵣ Function.on
  --   ( λ tup -> (A ⟦ 𝓸 ⟧) (λ i -> (args i ̇ A) tup) )
  -- ) .i .j
  compat θ 𝓸 λ{ i -> (compatible-term A (args i) θ) p }

--------------------------------------------------------------
-- analogues for setoid-based algebras

open Setoid

_̂_ : Term -> (A : Algebra S) -> (X -> ∥ ⟦ A ⟧ᵣ ∥) -> ∥ ⟦ A ⟧ᵣ ∥
((generator x) ̂ A) tup = tup x
((node 𝓸 args) ̂ A) tup = (A ⟦ 𝓸 ⟧) λ{i -> (args i ̂ A) tup }

open Con

Compatible-Term :
    (A : Algebra S) -> (t : Term) -> (θ : Con A)
    ----------------------------------------------
  ->   compatible-fun (t ̂ A) ⟦ θ ⟧ᵣ

Compatible-Term A (generator x) θ p = p x
Compatible-Term A (node 𝓸 args) θ p =
  compat θ  λ{ k -> (Compatible-Term A (args k) θ) p }

--Function.on is the operation,
--  _on_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
--           → (B → B → C) → (A → B) → (A → A → C)
--  _*_ on f = λ x y → f x * f y
--
--So 
--  (⟦ θ ⟧ᵣ Function.on (λ tup → (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup }))) .i .j``
--means
--  ((λ tup → (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup })) .i)
--  ⟦ θ ⟧ᵣ
--  ((λ tup → (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup })) .j)
--Equivalently,
--   ⟦ θ ⟧ᵣ
--    (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) .i })
--    (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) .j })                   (1)
--We have,  ``p : lift-rel ⟦ θ ⟧ᵣ .i .j`` and the induction hypothesis,
--    ∀ i -> ⟦ θ ⟧ᵣ ((args i ̂ A) .i) ((args i ̂ A) .j)         (IH)
--which is equivalent to
--    lift-rel ⟦ θ ⟧ᵣ (λ { i → (args i ̂ A) .i }) (λ { i → (args i ̂ A) .j })
--Then we use
--    lift-rel ⟦ θ ⟧ᵣ =[ (A ⟦ 𝓸 ⟧) ]⇒ ⟦ θ ⟧ᵣ                    (2)
--to get (1).
--We get (2) from: compatible-alg A ⟦ θ ⟧ᵣ {𝓸}, which we get from ``compat θ {𝓸}``
--We get (IH) from: 
--
--  induct : (A : algebra S)
--    ->     (θ : con A)
--    ->     (args : ℕ → Term)
--    ->     (i : Fin (⟨ S ⟩ₐ 𝓸))
--          -------------------
--    ->     compatible-fun (args i ̂ A) ⟦ θ ⟧ᵣ
--  induct A θ args i = compatible-term A (args i) θ 

---------------------------------------------------------

-- ARITY OF A TERM
argsum : ℕ -> (ℕ -> ℕ) -> ℕ
argsum nzero f = 0
argsum (succ n) f = f n + argsum n f

⟨_⟩ₜ : Term -> ℕ
⟨ generator x ⟩ₜ = 1
⟨ node 𝓸 args ⟩ₜ = (S ρ) 𝓸 + argsum ((S ρ) 𝓸) (λ i -> ⟨ args i ⟩ₜ)


-------------------------------------------------------------


--Alternative approach to interpretation.

-- Essential arity
------------------

-- The definition of "arity" of a term is a bit nuanced as the following example shows:

-- Example. Suppose 𝑓 is a binary term, and 𝑝 and 𝑞 are ternary terms.

-- How should we define the "arity" of the following term?

--   𝑓(𝑝(𝑥, 𝑦, 𝑧), f(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))

-- On the face of it, it seems safe to say t has arity 6 since we express it as a function
-- of 6 variables as follows:

--   t(𝑢, 𝑣, 𝑤, 𝑥, 𝑦, 𝑧) = 𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))

-- But what if 𝑝(𝑥,𝑦,𝑧) = 𝑧?  Then we would say that the "essential arity" of g is 1 since
-- we can express g and t equivalently as 𝑝'(𝑧) = 𝑝(𝑥,𝑦,𝑧) and 

--   t'(𝑢, 𝑣, 𝑤, 𝑥, 𝑧) = 𝑓(𝑝'(𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤)),

-- resp., in which case it seems the "arity" of t is really 5 (or maybe, to be safe, *at most* 5).

-- By now it should be clear that we can't know the *essential* arity of t (that is, the minimum
-- number of variables required to express t) until we know the essential arities of 𝑓, 𝑝, and 𝑞.

-- If, for example, 𝑞(𝑢, 𝑣, 𝑤) = 𝑓(𝑣, 𝑤), then t is expressible as

--  t''(𝑣, 𝑤, 𝑥, 𝑧) = 𝑓(𝑝'(𝑧), 𝑓(𝑤, 𝑥), 𝑓(𝑣, 𝑤))

-- If moreover we know that 𝑓 has essential arity 2, then this is as far as we can reduce the
-- argument list of t so we can conclude that t has essential arity 4.


--Interpretation of Terms
--========================

-- Now, if X = {x₀, x₁, x₂,...}, then we can re-write the term in the following equivalent way:

--   t(x₀, x₁, x₂, x₃, x₄, x₅) = f(g(x₃, x₄, x₅), f(x₂, x₃), h(x₀, x₁, x₂)).

-- If 𝒙 : ω -> X, where 𝒙 𝑖 = xᵢ, then t can be expressed as

--   t 𝒙 = f(g(π₃𝒙, π₄𝒙, π₅𝒙), f(π₂𝒙, π₃𝒙), h(π₀𝒙, π₁𝒙, π₂𝒙)),

-- where πᵢ is the project onto the (zero offset) 𝑖-th coordinate.

-- (N.B. "zero offset" means that the smallest index (subscript) is 0; to avoid confusion, we refer to this as the index not of the "1st coordinate" but of the "0th coordinate.")
--Given a set ``X`` and an algebra ``𝐀 = ⟨A,...⟩``, we call a function ``ctx : X → A`` a **context**.

--**Definition**. (cf Def 4.31 of Bergman)
--
--Let :math:`t` be a term of arity :math:`ρ t`, and 𝐀 an algebra, in the signature :math:`S`.
--
--The **interpretation** of :math:`t` in 𝐀---often denoted in the literature by :math:`t^𝚨`---is the :math:`(ρ t)`-ary operation on :math:`A` defined by recursion on the structure of :math:`t`, as follows:

--1. if :math:`t` is the variable :math:`x ∈ X`, then in the context ``ctx`` we take :math:`t^𝚨` to be the projection onto the coordinate containing ``ctx x``.

--2. if :math:`t = 𝓸 𝐟`, where 𝓸 is a basic operation symbol with interpretation :math:`𝓸^𝚨` in 𝚨 and :math:`𝐟 : (ρ 𝓸) →` Term is a (ρ 𝓸)-tuple of terms, each with interpretation :math:`(𝐟 i)^𝚨`, then we take :math:`t^𝐀(𝐟)` to be :math:`𝓸^𝐀 \bigl( λ \{ (i : ρ 𝓸) . (𝐟 i)^𝐀\}\bigr)`.

-- Let's translate this definition using the Agda syntax we developed above.

-- Let ``t`` be a term, 𝐀 an algebra,  of signature ``S``.

-- The **interpretation** of :math:`t` in 𝐀---often denoted in the literature by :math:`t^𝚨`---is an operation of :math:`A` defined by recursion on the structure of :math:`t`.

-- 1. If ``t`` is a variable, say, ``x : X``, then we define ``(t ̂ A) : ⟦ A ⟧ᵤ -> ⟦ A ⟧ᵤ`` for each ``a : ⟦ A ⟧ᵤ`` by ``(t ̂ A) a = a``.
-- 2. If ``t = 𝓸 𝐟``, where ``𝓸 : ⟨ S ⟩ₒ`` is a basic operation symbol with interpretation ``A ⟦ 𝓸 ⟧`` in 𝚨, and if ``𝐟 : ⟨ S ⟩ₐ 𝓸 -> Term`` is a ``(⟨ S ⟩ₐ 𝓸)``-tuple of terms with interpretations ``(𝐟 i) ̂ A`` for each ``i : ⟨ S ⟩ₐ 𝓸``, then we define
--    ``(t ̂ A) = (𝓸 𝐟) ̂ A = (A ⟦ 𝓸 ⟧) λ{i -> (𝐟 i) ̂ A}``

-- Here's how we would implement this in Agda.
-- .. code-block:: agda
--    _̂_ : {ℓ₁ : Level} -> Term -> (A : algebra {ℓ₁} S) -> (X -> ⟦ A ⟧ᵤ) -> ⟦ A ⟧ᵤ
--    ((generator x) ̂ A) tup = tup x
--    ((node 𝓸 args) ̂ A) tup = (A ⟦ 𝓸 ⟧) λ{i -> (args i ̂ A) tup }


