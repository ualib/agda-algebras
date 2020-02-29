--File: Preliminaries.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020 
--Updated: 21 Feb 2020
--Notes: Based on the file `preliminaries.agda` (27 Dec 2019).

{-# OPTIONS --without-K --exact-split #-}

--`without-K` disables Streicher's K axiom; see "Note on axiom K" 
  --            of the ualib documentation (ualib.org).
  --
  --`exact-split` makes Agda to only accept definitions with the
  --              equality sign "=" that behave like so-called
  --              judgmental or definitional equalities.

module Preliminaries where

-- Export common imports
open import Level public renaming (suc to lsuc ; zero to lzero)
open import Data.Empty using (⊥) public
open import Data.Bool using (Bool) public
--open import Data.Product using (∃; _,_; _×_; proj₁; proj₂) public
open import Data.Product using (∃; _,_; _×_) public
  renaming (proj₁ to ∣_∣; proj₂ to ⟦_⟧)

open import Relation.Unary using (Pred; _∈_; _⊆_; ⋂) public
open import Relation.Binary public
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; cong-app; sym; subst) public
open Eq.≡-Reasoning public
open import Function using (_∘_) public
open import Agda.Builtin.Nat public
  renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )

-- ∣_∣ = proj₁
-- ⟦_⟧ = proj₂

_∈∈_ : {i j k : Level} {A : Set i} {B : Set j}
  ->   (A -> B)
  ->   Pred B k
      ---------------
  ->   Set (i ⊔ k)
_∈∈_ {A = A} f S = (x : A) -> f x ∈ S

Im_⊆_ : {i j k : Level} {A : Set i} {B : Set j}
  ->    (A -> B)
  ->    Pred B k
      -------------------
  ->    Set (i ⊔ k)
Im_⊆_ {A = A} f S = (x : A) -> f x ∈ S

----------------------------
--EXTENSIONALITY Postulate
----------------------------
--The only way to distinguish functions is by applying them; if two functions
--applied to the same argument always yield the same result, then they are
--the same function. It is the converse of cong-app.
--
--Agda DOES NOT PRESUME EXTENSIONALITY, but we can POSTULATE that it holds.
--This postulate is okay since it's CONSISTENT with the theory underlying Agda.

--------------------------------------
--Ordinary function extensionality
postulate
  extensionality : ∀ {A B : Set} {f g : A -> B}
    ->             (∀ (x : A) -> f x ≡ g x)
                  --------------------------
    ->             f ≡ g
                   
--------------------------------------
--Dependent function extensionality
postulate
  ∀-extensionality :
    ∀ {A : Set} {B : A -> Set} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

postulate
  ∀-extensionality-ℓ :
    ∀ {ℓ : Level} {A : Set ℓ} {B : A -> Set ℓ} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

postulate
  ∀-extensionality-ℓ₁-ℓ₂ :
    ∀ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A -> Set ℓ₂} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

-- (more extensionality postulates we haven't used appear at bottom of this file for now)

data Image_∋_ {ℓ₁ ℓ₂ : Level}{A : Set ℓ₁}{B : Set ℓ₂}
              (f : A -> B) : B -> Set (ℓ₁ ⊔ ℓ₂)
  where
  im : (x : A) -> Image f ∋ f x
  eq : (b : B) -> (a : A) -> b ≡ f a -> Image f ∋ b

image_ : {i j : Level} {A : Set i} {B : Set j}
  ->  (A -> B) ->  Pred B (i ⊔ j)
image f = λ b -> ∃ λ a -> b ≡ f a

-- ImageIsImage : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
--   ->           (f : A -> B)
--   ->           (b : B) -> (a : A)
--   ->           b ≡ f a
--              --------------------
--   ->           Image f ∋ b
-- ImageIsImage {A = A} {B = B} = λ f b a b≡fa → eq b a b≡fa


--N.B. the assertion Image f ∋ y must come with a proof, which is of the
--form ∃a f a = y, so we have a witness, so the inverse can be "computed"
--in the following way:
Inv : {ℓ₁ ℓ₂ : Level}{A : Set ℓ₁} {B : Set ℓ₂}
  ->  (f : A -> B) ->  (b : B) -> Image f ∋ b -> A
Inv f .(f a) (im a) = a  -- Cool!!!
Inv f b (eq b a b≡fa) = a

-- special case for Set
inv : {A B : Set}(f : A -> B)(b : B) -> Image f ∋ b -> A
inv{A}{B} = Inv {lzero}{lzero}{A}{B}

InvIsInv : {ℓ₁ ℓ₂ : Level}{A : Set ℓ₁} {B : Set ℓ₂}
  ->       (f : A -> B)
  ->       (b : B) -> (b∈Imgf : Image f ∋ b)
         --------------------------------------
  ->      f (Inv f b b∈Imgf) ≡ b
InvIsInv f .(f a) (im a) = refl
InvIsInv f b (eq b a b≡fa) = sym b≡fa

-------------------------------------------------------------------------------
identity : {ℓ : Level} (A : Set ℓ) -> A -> A
identity{ℓ} A x = x
--(see also `id` in Hom.agda)

-- Epic (surjective) function from Set ℓ₁ to Set ℓ₂
Epic : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (g : A -> B) -> Set _
Epic g = ∀ y -> Image g ∋ y

-- special case: epic function on Set
epic : {A B : Set} (g : A -> B) -> Set _
epic {A}{B} g = Epic {lzero}{lzero}{A}{B} g

-- The (pseudo-)inverse of an epic function
EpicInv : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
  ->      (f : A -> B)
  ->      Epic f
         -----------------
  ->       B -> A
EpicInv f fEpic b = Inv f b (fEpic b)

-- The (psudo-)inverse of an epic is the right inverse.
EInvIsRInv : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
  ->         (f : A -> B)
  ->         (fEpic : Epic f)
    ----------------------------------------
  -> f ∘ (EpicInv f fEpic) ≡ identity {ℓ₂} B
EInvIsRInv f fEpic = (∀-extensionality-ℓ₁-ℓ₂)
                     (λ x → InvIsInv f x (fEpic x))

-- (this belongs elsewhere)
-- The (pseudo-)inverse of an epimorphism is total.
-- EInvTotal : {𝑨 𝑪 : Algebra k S} 
--   ->        (g : Hom{i}{j}{k} 𝑨 𝑪)
--   ->        Epic ∣ g ∣
--            -----------------------
--   ->        ∣ 𝑪 ∣ -> ∣ 𝑨 ∣
-- EInvTotal{𝑨}{𝑪} g gEpic = (λ c → EpicInv ∣ g ∣ gEpic c)

---------------------------------------------------------
--Monics (injectivity)
--monic function from Set ℓ₁ to Set ℓ₂
Monic : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (g : A -> B) -> Set _
Monic g = ∀ a₁ a₂ -> g a₁ ≡ g a₂ -> a₁ ≡ a₂

-- special case: monic function on Set
monic : {A B : Set} (g : A -> B) -> Set _
monic {A}{B} g = Monic {lzero} {lzero} {A}{B} g

--The (pseudo-)inverse of a monic function
MonicInv : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
  ->       (f : A -> B)
  ->       Monic f
         -----------------
  ->       (b : B) -> Image f ∋ b -> A
MonicInv f fMonic  = λ b Imf∋b → Inv f b Imf∋b

-- The (psudo-)inverse of a monic is the left inverse.
-- MInvIsLInv : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
--   ->         (f : A -> B)
--   ->         (fMonic : Monic f)
--            ----------------------------------------
--   ->        (MonicInv f fMonic) ∘ f ≡ identity A
-- MInvIsLInv f fMonic =  ?

--bijectivity
bijective : {A B : Set} (g : A -> B) -> Set _
bijective g = epic g × monic g

Bijective : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (g : A -> B) -> Set _
Bijective g = Epic g × Monic g


------------------
--SET ISOMORPHISM
-------------------
infix 0 _≃₀_
record _≃₀_ (A B : Set) : Set where
  field
    to : A -> B
    from : B -> A

    --from is left-inv for to
    from∘to : ∀ (x : A) -> from (to x) ≡ x

    --from is right-inv for to
    to∘from : ∀ (y : B) -> to (from y) ≡ y  

-- open _≃₀_

--More general

infix 0 _≃_
record _≃_ {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  field
    to : A -> B
    from : B -> A

    --from is left-inv for to
    from∘to : ∀ (x : A) -> from (to x) ≡ x

    --from is right-inv for to
    to∘from : ∀ (y : B) -> to (from y) ≡ y  

open _≃_

-------------------------------------------------------------------

-------------------------------
--ISOMORPHISM IS AN EQUIVALENCE
-------------------------------
--Isomorphism is an equivalence (reflexive, symmetric, transitive).
--To show reflexivity, take both to and from to be the identity function.
≃-refl : ∀ {ℓ : Level} {A : Set ℓ}
         ----------
  ->      A ≃ A

≃-refl =
  record
    {
      to      = λ{x -> x};
      from    = λ{y -> y};
      from∘to = λ{x -> refl};
      to∘from = λ{y -> refl}
    }  

≃-sym : ∀ {ℓ : Level} {A B : Set ℓ}
  ->    A ≃ B
        ------
  ->    B ≃ A
≃-sym A≃B =
  record
    {
    to = from A≃B;
    from = to A≃B;
    from∘to = to∘from A≃B;
    to∘from = from∘to A≃B
    }

≃-trans : ∀ {ℓ : Level} {A B C : Set ℓ}
  ->      A ≃ B  ->  B ≃ C
          ----------------
  ->      A ≃ C
≃-trans A≃B B≃C =
  record
    {
    to      = to B≃C ∘ to A≃B ;
    from    = from A≃B ∘ from B≃C ;
    from∘to = λ {x ->
      begin -- Goal: (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x) ≡ x
        from A≃B ((from B≃C ∘ to B≃C) ((to A≃B) x))
      ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
        from A≃B (to A≃B x)
      ≡⟨ from∘to A≃B x ⟩
        x
      ∎} ;
    to∘from = λ {y ->
      begin -- Goal: (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y) ≡ y
        to B≃C (to A≃B (from A≃B (from B≃C y)))
      ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
        to B≃C (from B≃C y)
      ≡⟨ to∘from B≃C y ⟩
        y
      ∎}
    }

-----------------------------------------------------------------------

--------------------------------------
--Reasoning for Isomorphism
--------------------------------------
--Here's a variant of equational reasoning for isomorphism.
--The form that corresponds to _≡⟨⟩_ is omitted, since trivial
--isomorphisms arise far less often than trivial equalities.

--Chains of Set isomorphisms
module ≃-Reasoning {ℓ : Level} where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set ℓ}
    ->     A ≃ B
           -----
    ->     A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (x : Set ℓ) {y z : Set ℓ}
    ->    x ≃ y  ->  y ≃ z
          ----------------
    ->     x ≃ z
  x ≃⟨ x≃y ⟩ y≃z = ≃-trans x≃y y≃z

  _≃-∎ : ∀ (x : Set ℓ)
         ---------
    ->   x ≃ x
  x ≃-∎ = ≃-refl

open ≃-Reasoning
----------------------------------------------------------------------
--SUBSETS (embeddings)
-----------------------

--Embedding shows that the first type is included in the second.
infix 0 _≲_

-- record _≲_ {ℓ : Level} (A : Set ℓ) (B : Set ℓ) : Set ℓ where
--   field
--     to   : A -> B
--     from : B -> A
--     from∘to : ∀ (x : A) -> from (to x) ≡ x

record _≲_ (A : Set) (B : Set) : Set where
  field
    to   : A -> B
    from : B -> A
    from∘to : ∀ (x : A) -> from (to x) ≡ x

open _≲_

--Embedding is a preorder (reflexive and transitive)
≲-refl : ∀ {A : Set}
        ------------
  ->      A ≲ A

≲-refl =
  record {
    to = λ x -> x ;
    from = λ x -> x ;
    from∘to = λ x -> Eq.refl
  }

≲-trans : ∀ {A B C : Set}
  ->      A ≲ B  ->  B ≲ C
         ------------------
  ->          A ≲ C

≲-trans A≲B B≲C =
  record {
    to   = to B≲C ∘ to A≲B ;
    from = from A≲B ∘ from B≲C ;
    from∘to = λ x ->
      begin -- Goal: (from A≲B ∘ from B≲C) ((to B≲C ∘ to A≲B) x) ≡ x
        from A≲B (from B≲C (to B≲C (to A≲B x)))
      ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x))  ⟩
        from A≲B (to A≲B x)
      ≡⟨ from∘to A≲B x ⟩
        x
      ∎
  }

--------------------------------
--REASONING with the ≲ relation
--------------------------------

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    ->     A ≲ B
           -----
    ->     A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (x : Set) {y z : Set}
    ->    x ≲ y  ->  y ≲ z
          ----------------
    ->     x ≲ z
  x ≲⟨ x≲y ⟩ y≲z = ≲-trans x≲y y≲z


  _≲-∎ : ∀ (x : Set)
         ---------
    ->   x ≲ x
  x ≲-∎ = ≲-refl

open ≲-Reasoning



-- Special dependent functions (fork and join/eval)

---------------------------------------------------
--Forks
------

-- binary fork
fork₂ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}
  ->   (A -> B) -> (A -> C) -> A -> (B × C)
fork₂ f g a = f a , g a

dep-fork₂ : ∀ {a b c : Level} {A : Set a}{B : A -> Set b}{C : A -> Set c}
  ->        (f : (a : A) -> B a) -> (g : (a : A) -> C a) -> ∀ (a : A) -> (B a × C a)
dep-fork₂ f g a = (f a , g a)

_Fork_ : ∀ {i j a : Level}{I : Set i}{J : I -> Set j}{A : Set a}
  ->      ((i : I) -> (J i -> A) -> A)
  ->      ((i : I) -> (J i -> A))
        ---------------------------
  ->        I -> A
f Fork 𝒂𝒂 = λ i -> (f i)(𝒂𝒂 i)
-- e.g., (f₁,…,fₙ)((a11,…,a1n), …, (an1,…,ann)) = (f₁(a11,…,a1n), …,fₙ(an1,…,ann))
-- 𝒂𝒂 : (i : I) -> (J i -> A)
-- f : (i : I) -> (J i -> A) -> A
-- forkA f 𝒂𝒂 : I -> A 

------------------------------------------------------------------------------
--EVAL. Function application on types A and B.
eval : ∀ {a b : Level} {A : Set a}{B : Set b} -> ((A -> B) × A) -> B
eval (f , a) = f a

_Eval_ : ∀ {i a : Level} {I : Set i}{A : Set a}
  ->      ((I -> A) -> A)
  ->      (I -> A)
        --------------------
  ->      A
f Eval a = f a

--GENERAL COMPOSITION.
_Comp_ : ∀ {i j a : Level}{I : Set i}{J : I -> Set j}{A : Set a}
  ->     ((I -> A) -> A)
  ->     ((i : I) -> (J i -> A) -> A)
       ---------------------------------------
  ->     ((i : I) -> (J i -> A)) -> A
f Comp g = λ 𝒂𝒂 → f Eval (g Fork 𝒂𝒂)

--------------------------------------------------------

--=============================================================================
-- MISC NOTES
--============
--
-- When importing `Data.Product` we rename `proj₁` to `∣_∣` and `proj₂` to `⟦_⟧`.
-- If, e.g., `S : Signature i j`, then
--   ∣ S ∣ = the set of operation symbols (which we used to call 𝓕).
--   ⟦ S ⟧ = the arity function (which we used to call ρ).

-------------------------------------------------------------------------------
-- How to write definitions interactively in Agda
-- ----------------------------------------------
--
-- Add a question mark and then type C-c C-l to create a new "hole."
--
-- Type C-c C-f to move into the next unfilled hole.
--
-- Type C-c C-c (from inside the hole) to be prompted for what type should
-- fill the given hole.
--
-- Type m to split on the variable in the hole.
--
-- Type C-c C-f to move into the next hole.
--
-- Type C-c C-, to get the type required in the current hole.
--
-- Enter an appropriate object in the hole; type C-c C-space to remove the hole.
--
-- SUMMARY
--    ? then C-c C-l creates hole
--    C-c C-f moves to next hole
--    C-c C-c prompts for what goes in hole
--    m splits on variable in hole
--    C-c C-, in hole gets type required
--    C-c C-space removes hole
--
------------------------------------
-- Induction
-- ---------
-- For a proof by structural induction over a recursively defined data type,
-- make a hole, enter the hole, type C-c C-c, and when prompted enter the
-- symbol over which you wish to induct.




















-- postulate
--   ∀-extensionality-ℓ₁-ℓ₁⊔ℓ₂ :
--     ∀ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A -> Set (ℓ₁ ⊔ ℓ₂)} {f g : ∀(x : A) -> B x}
--     ->    (∀ (x : A) -> f x ≡ g x)
--          -------------------------
--     ->    f ≡ g

-- postulate
--   ∀-extensionality-ℓ₁-ℓ₂⊔ℓ₃ :
--     ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : A -> Set (ℓ₂ ⊔ ℓ₃)} {f g : ∀(x : A) -> B x}
--     ->    (∀ (x : A) -> f x ≡ g x)
--          -------------------------
--     ->    f ≡ g

-- postulate
--   ∀-extensionality-ℓ₁-ℓ₁⊔ℓ₂⊔ℓ₃ :
--     ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : A -> Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)} {f g : ∀(x : A) -> B x}
--     ->    (∀ (x : A) -> f x ≡ g x)
--          -------------------------
--     ->    f ≡ g

--   -------------------------------------------------------------
--   --Dependent function extensionality (with product codomain)
-- postulate
--   extensionality-dep-× :
--     ∀ {A : Set} {B C : A -> Set} {f g : (x : A) -> B x × C x}
--       ->   (∀ (x : A) -> ∣ f x ∣ ≡ ∣ g x ∣ -> ⟦ f x ⟧ ≡ ⟦ g x ⟧)
--           --------------------------------------------------
--       ->   f ≡ g

