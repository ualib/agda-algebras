--File: Free.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 21 Feb 2020
--Notes: Based on the file `free.agda` (25 Dec 2019).
--       Used for 2nd half of talk at JMM Special Session (Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic 
open import Hom

module Free {i j k ℓ : Level} {S : Signature i j} {X : Set k}  where

----------------------------
-- TERMS in the signature S
----------------------------
-- open signature


-- data Term : Set (i ⊔ j ⊔ k ⊔ ℓ) where
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

𝔉 : Algebra (i ⊔ j ⊔ k) S
𝔉 = Term , node
--record { ⟦_⟧ᵤ = Term ; _⟦_⟧ = node }
-------------------------------------
-- The UNIVERSAL PROPERTY of free

-- We first prove this for algebras whose carriers are mere sets.

-- 1. every h : X -> ⟦ A ⟧ᵤ  lifts to a hom from free to A.
-- 2. the induced hom is unique.

-- PROOF.
-- 1.a. Every map  (X -> A)  "lifts".
free-lift : ∀{ℓ} {𝑨 : Algebra ℓ S}(h : X -> ∣ 𝑨 ∣) -> ∣ 𝔉 ∣ -> ∣ 𝑨 ∣
free-lift h (generator x) = h x
free-lift {ℓ} {𝑨 = (A , 𝐹ᴬ)} h (node 𝓸 args) = (𝐹ᴬ 𝓸) λ{i -> free-lift {ℓ} {(A , 𝐹ᴬ)} h (args i)}

-- 1.b. The lift is a hom.
lift-hom : {𝑨 : Algebra (i ⊔ j ⊔ k) S} (h : X -> ∣ 𝑨 ∣) -> Hom 𝔉 𝑨
lift-hom {𝑨} h = free-lift {i ⊔ j ⊔ k}{𝑨} h , λ 𝓸 𝒂 → cong (⟦ 𝑨 ⟧ _) refl
--record { ⟦_⟧ₕ = free-lift {A} h; homo = λ args → refl }

-- 2. The lift to  (free -> A)  is unique.
--    (We need EXTENSIONALITY for this (imported from util.agda))
free-unique : {𝑨 : Algebra (i ⊔ j ⊔ k) S}
  ->    ( f g : Hom 𝔉 𝑨 )
  ->    ( ∀ x  ->  ∣ f ∣ (generator x) ≡ ∣ g ∣ (generator x) )
  ->    (t : Term)
       ---------------------------
  ->    ∣ f ∣ t ≡ ∣ g ∣ t

free-unique {𝑨} f g p (generator x) = p x
--free-unique {(A , 𝐹ᴬ)} f g p (node 𝓸 args) =
free-unique {𝑨} f g p (node 𝓸 args) =
   begin
     ( ∣ f ∣ )(node 𝓸 args)
   ≡⟨ ⟦ f ⟧ 𝓸 args ⟩
     (⟦ 𝑨 ⟧ 𝓸) (λ i -> ∣ f ∣ (args i))
   ≡⟨ cong (⟦ 𝑨 ⟧ _)
        (∀-extensionality-ℓ {j} {i} {k}
          ( λ i -> free-unique {𝑨} f g p (args i))
        )
    ⟩
     (⟦ 𝑨 ⟧ 𝓸) (λ i -> ∣ g ∣ (args i))
   ≡⟨ sym (⟦ g ⟧ 𝓸 args) ⟩
     ∣ g ∣ (node 𝓸 args)
   ∎


--------------------------
--INTERPRETATION OF TERMS
--------------------------

--(cf Def 4.31 of Bergman)

--Let 𝒕 : Term be a term, 𝑨 an algebra, in the signature S.
--We define an n-ary operation, denoted (𝒕 ̂ 𝑨), on 𝑨 by recursion on
--the structure of 𝒕, as follows:

-- (1) if 𝒕 is the variable x ∈ X and 𝒂 : X -> ∣ 𝑨 ∣ is a tuple of elements of A,
--     then we define (t ̂ 𝑨) 𝒂 = 𝒂 x.

-- (2) if 𝒕 = 𝓸 args, where 𝓸 ∈ ∣ S ∣ is an operation symbol (of arity ⟦ S ⟧ 𝓸),
--        args : ⟦ S ⟧ 𝓸 -> Term is an (⟦ S ⟧ 𝓸)-tuple of terms, and
--        𝒂 : X -> ∣ A ∣ is a tuple of elements of A, then we define

--     (t ̂ 𝑨) 𝒂 = ((𝓸 args) ̂ 𝑨) 𝒂
--                  = (⟦ 𝑨 ⟧ 𝓸) λ{ i -> ((args i) ̂ 𝑨) 𝒂 }

-- Here's the Agda implementation of the foregoing definition.

_̇_ : Term -> (𝑨 : Algebra k S) -> (X -> ∣ 𝑨 ∣) -> ∣ 𝑨 ∣
((generator x) ̇ 𝑨) 𝒂 = 𝒂 x
((node 𝓸 args) ̇ 𝑨) 𝒂 = (⟦ 𝑨 ⟧ 𝓸) λ{i -> (args i ̇ 𝑨) 𝒂 }

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
comm-hom-term : {𝑨 𝑩 : Algebra k S}
  ->    (g : Hom 𝑨 𝑩) -> (𝒕 : Term)
  ->    (𝒂 : X -> ∣ 𝑨 ∣)
       ------------------------------
  ->     ∣ g ∣ ((𝒕 ̇ 𝑨) 𝒂) ≡ (𝒕 ̇ 𝑩) (∣ g ∣ ∘ 𝒂)
--
comm-hom-term g (generator x) 𝒂 = refl
comm-hom-term {𝑨 = (A , 𝐹ᴬ)} {𝑩 = (B , 𝐹ᴮ)}
  g (node 𝓸 args) 𝒂 = {!!}
  -- begin
  --   ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̇ A) tup }))
  -- ≡⟨ homo g ( λ i → (args i ̇ A) tup )⟩
  --   (B ⟦ 𝓸 ⟧) ( λ i → ⟦ g ⟧ₕ ((args i ̇ A) tup) )
  -- ≡⟨ cong ((B ⟦_⟧)_)
  --    ( ∀-extensionality  λ i -> comm-hom-term g (args i) tup  ) ⟩
  --   (B ⟦ 𝓸 ⟧) ( λ i → (args i ̇ B) (⟦ g ⟧ₕ ∘ tup) )
  -- ∎

-- (2) For every term t ∈ T(X) and every θ ∈ Con(A), 
--     a θ b => t(a) θ t(b).

-- compatible-term : (A : Algebra k S)
--  ->               (t : Term)
--  ->               (θ : con A)
--                  -------------------
--  ->               compatible-fun (t ̇ A) ⟦ θ ⟧ᵣ

-- compatible-term A (generator x) θ p = p x
-- compatible-term A (node 𝓸 args) θ p =
--   --Goal:
--   -- ( ⟦ θ ⟧ᵣ Function.on
--   --   ( λ tup -> (A ⟦ 𝓸 ⟧) (λ i -> (args i ̇ A) tup) )
--   -- ) .i .j
--   compat θ 𝓸 λ{ i -> (compatible-term A (args i) θ) p }

-- Compatible-Term A (generator x) θ p = p x
-- Compatible-Term A (node 𝓸 args) θ p =
--   compat θ  λ{ k -> (Compatible-Term A (args k) θ) p }

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
-- argsum : ℕ -> (ℕ -> ℕ) -> ℕ
-- argsum nzero f = 0
-- argsum (succ n) f = f n + argsum n f

-- ⟨_⟩ₜ : Term -> ℕ
-- ⟨ generator x ⟩ₜ = 1
-- ⟨ node 𝓸 args ⟩ₜ = (S ρ) 𝓸 + argsum ((S ρ) 𝓸) (λ i -> ⟨ args i ⟩ₜ)


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


-- open import Level
-- open import Agda.Builtin.Nat public
--   renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )
-- open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
-- open import Relation.Unary hiding (_⊆_;_⇒_)
-- -- open import Relation.Binary.Core using (IsEquivalence)
-- --open import Relation.Binary using (IsEquivalence)
-- import Relation.Binary.PropositionalEquality as Eq
--   hiding (setoid; Reveal_·_is_;[_];∀-extensionality)
-- open Eq using (_≡_; refl; cong; sym)
-- open Eq.≡-Reasoning
-- open import Function using (_∘_)
-- open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (cong)

-- open import Relation.Nullary using (¬_)
-- open import Relation.Nullary.Negation using ()
--   renaming (contradiction to ¬¬-intro)
--  using    ( _+_; _*_ )

-- open import Data.Fin public
--   -- (See "NOTE on Fin" section below)
--   hiding ( _+_; _<_ )
--   renaming ( suc to fsucc; zero to fzero )
--------------------------------------------------------------
-- open import preliminaries  using (_⊎_ ; ∀-extensionality; ∑; List)
