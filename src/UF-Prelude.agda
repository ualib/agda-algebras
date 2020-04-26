--FILE: UF-Prelude.agda
--BLAME: williamdemeo@gmail.com
--DATE: 21 Apr 2020
--UPDATED: 21 Apr 2020
--REF:  Some of what appears in this file is based on Martin Escardo's HoTT/UF notes.
--     cf. https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ 
--     In particular, comments appearing in quotes below, along with the code to which those comments refer, are due to Martin Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Unary using (Pred; _∈_; _⊆_)
open import Data.Product  renaming (_,_ to _؛_) using (∃) -- ; _,_; _×_;Σ-syntax) public renaming (proj₁ to ∣_∣; proj₂ to ⟦_⟧)

module UF-Prelude where

--------------------------------------------------------------------------------------------
--TYPE UNIVERSES.
-- (cf https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#universes )

open import Agda.Primitive public
 renaming (
            Level to Universe -- We speak of universes rather than of levels.
           ; lzero to 𝓤₀       -- Our first universe is called 𝓤₀
           ; lsuc to _⁺           -- The universe after 𝓤 is 𝓤 ⁺
           ; Setω to 𝓤ω      -- There is a universe 𝓤ω strictly above 𝓤₀, 𝓤₁, ⋯ , 𝓤ₙ, ⋯
           )
 using    (_⊔_)               -- Least upper bound of two universes, e.g. 𝓤₀ ⊔ 𝓤₁ is 𝓤₁

Type = λ ℓ → Set ℓ

_̇   : (𝓤 : Universe) → Type (𝓤 ⁺)
𝓤 ̇  = Type 𝓤

infix  1 _̇
--The ̇ operator maps a universe 𝓤 (i.e., a level) to Set 𝓤, and the latter has type Set (lsuc 𝓤), a.k.a. Type (𝓤 ⁺).
--That is,    𝓤 ̇   is simply an alias for  Set 𝓤, and we have Set 𝓤 : Set (lsuc 𝓤).
--The level lzero is renamed  𝓤₀, so 𝓤₀ ̇ is an alias for Set lzero.  (This corresponds to `Sort 0` in Lean.)
--Thus,   Set (lsuc lzero)  is denoted by  Set 𝓤₀ ⁺  which is denoted by  𝓤₀ ⁺ ̇
--
-- +--------------------|-------------------------------|------------------------------+
-- |       Agda                 |          MHE Notation                  |        Lean analog                      |
-- +--------------------|-------------------------------|------------------------------+
-- |  ``Level``              |   ``Universe``                         |  ``universe``                         |
-- |   ``lzero``             |   ``𝓤₀``                               |  ``0 : universe``                     |
-- |  ``Set lzero``        |   ``𝓤₀ ̇`` ( = ``Type 𝓤₀``)  |  ``Sort 0``                            |
-- |   ``lsuc lzero``       |   ``𝓤₀ ⁺``                            |  ``1 : universe``                     |
-- |  ``Set (lsuc lzero)`` |   ``𝓤₀ ⁺ ̇``                           |  ``Sort 1 = Type = Type 0``   |
-- +--------------------|-------------------------------|------------------------------+
--  (Table: translation from standard Agda syntax into MHE notation and Lean syntax)

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺
𝓤₃ = 𝓤₂ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : {𝓤 : Universe} (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤

--"We will refer to universes by letters 𝓤,𝓥,𝓦,𝓣 (type these with, resp, ``\MCU``, ``\MCV``, etc)"
variable
  𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓞 𝓟 𝓠 𝓡 𝓢 𝓣 𝓤 𝓥 𝓦 : Universe

------------------------------------------------------------------------
-- Unary relations (aka predicates).  (cf. Relation/Unary.agda from the Agda std lib)
-- `Pred A 𝓤` can be viewed as some property that elements of type A might satisfy.
-- Consequently `P : Pred A 𝓤` can also be seen as a subset of A containing all the elements of A that satisfy property P.
-- Pred : ∀ {𝓤} → 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
-- Pred A 𝓥 = A → 𝓥 ̇

-- The one-element type (type `\b1` to get 𝟙; and type `\*` to get ⋆)
--"We place it in the first universe, `𝓤₀ ̇` [= `Set (lsuc lzero)`] and we name its unique element `⋆`.
-- We use the data declaration in Agda to introduce it:
data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

{-"It is important that `⋆` lives in the type `𝟙` and in no other type.

       Moto: 'There's no dual citizenship in our type theory.'

  "When we create a type, we also create new elements for it, in this case `⋆`.  Here's a mechanism to prove that all points of
   the type `𝟙` satisfy a given property `A`.  The property is a function `A : 𝟙 → 𝓤` for some universe `𝓤`. The type `A(x)`,
   which we write simply `A x`, doesn't need to be a truth value; it can be any type. In MLTT, mathematical statements are types,
   such as `Π (A : 𝟙 → 𝓤), A ⋆ → Π (x : 𝟙), A x`. We read this in natural language as follows: "For property `A` of elements of
   type `𝟙`, if `A ⋆`, then `∀ x : 𝟙 → A x`.

  "In Agda, the above type is written `(A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x`. This is the type of functions with three arguments:
   `A : 𝟙 → 𝓤 ̇` and `a : A ⋆` and `x : 𝟙`, with values in the type `A x`. -}

--"A proof of a mathematical statement (i.e., a type) is a construction of an element of that type.
-- In our example, we have to construct a function, which we will name `𝟙-induction`.
𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A A⋆ ⋆ = A⋆

-- IMPORTANT: Instead of supplying an arbitrary `x : 𝟙`, we give `⋆` and Agda accepts this because,
-- from the definition of `𝟙`, `⋆` is the only element of the type `𝟙`. This is *pattern matching*.
𝟙-recursion : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆

-----------------------------------------------------------------------------
--"The empty type `𝟘`. It is defined like `𝟙`, except that no elements are listed for it.
data 𝟘 : 𝓤₀ ̇ where

--"That's the complete definition. This has a dual interpretation:
--   * mathematically, as the empty set (we can actually prove that this type is a set,  once we know the definition of set), and
--   * logically, as the truth value *false*.
-- To prove that a property of elements of the empty type holds for all elements of the empty type, we have to do nothing.
𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
𝟘-induction A ()

--"The expression `()` corresponds to the mathematical phrase 'vacuously true.'
-- The *unique* function from `𝟘` to any type is a particular case of `𝟘-induction`.
𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

--"We will use the following categorical notation for `𝟘-recursion`:
!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 = 𝟘-recursion

--"We give the two names `is-empty` and `¬` to the same function.
is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

--"This says that a type is empty precisely when we have a function to the empty type. Assuming univalence, once we have defined
-- the identity type former `_≡_`, we will be able to prove that `(is-empty X) ≡ (X ≃ 𝟘)`, where `X ≃ 𝟘` is the type of bijections,
-- or equivalences, from `X` to `𝟘`.

--"We will also be able to prove things like `(2 + 2 ≡ 5) ≡ 𝟘` and `(2 + 2 ≡ 4) ≡ 𝟙`.
-- This is for *numbers*. If we define *types* `𝟚 = 𝟙 + 𝟙` and `𝟜 = 𝟚 + 𝟚` with two and four elements,
-- respectively, where we are anticipating the definition of `_+_` for types, then we will instead have
-- `𝟚 + 𝟚 ≡ 𝟜` is a type with `4!` elements, which is the number of permutations of a set with four
-- elements, rather than a truth value `𝟘` or `𝟙`, as a consequence of the univalence axiom.

--"That is, we will have `(𝟚 + 𝟚 ≡ 𝟜) ≃ (𝟜 + 𝟜 + 𝟜 + 𝟜 + 𝟜 + 𝟜)`, so that the type identity `𝟚 + 𝟚 ≡ 𝟜`
-- holds in [many more ways](https://arxiv.org/abs/math/9802029) (see Categorification paper) than the
-- numerical equation `2 + 2 ≡ 4`.

--"The above is possible only because universes are genuine types and hence their elements (that is,
-- types) have identity types themselves, so that writing `X ≡ Y` for types `X` and `Y` (inhabiting the same
-- universe) is allowed.

--"When we view `𝟘` as *false*, we can read the definition of the *negation* `¬ X` as saying that "`X`
-- implies *false*". With univalence we will be able to show that "(*false* → *true*) `≡` *true*", which
-- amounts to `(𝟘 → 𝟙) ≡ 𝟙`, which in turn says that there is precisely one function `𝟘 → 𝟙`, namely
-- the (vacuous) function."

------------------------------------------------------------------------
--"The type `ℕ` of natural numbers"
-- ------------------------------

--"The def is similar but not quite the same as the one via Peano Axioms."
data ℕ : 𝓤₀ ̇ where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

--"In the following, the type family `A` can be seen as playing the role of a property of elements of `ℕ`,
-- except that it doesn't need to be necessarily subsingleton valued. When it is, the *type* of the function
-- gives the familiar principle of mathematical induction for natural numbers, whereas, in general, its
-- definition says how to compute with induction.
ℕ-induction : (A : ℕ → 𝓤 ̇)
 →            A 0 --                             base step      : "A 0 holds"
 →            ((n : ℕ) → A n → A (succ n)) -- induction step : "∀n, if A n, then A (succ n) holds"
              -------------------------------- -- ----------------------------------------------------
 →            (n : ℕ) → A n --                 conclusion     : "∀n, A n holds"

ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h zero = a₀
  h (succ n) = f n (h n)

--"Notice also that `ℕ-induction` is the dependently typed version of primitive recursion, where the
-- non-dependently typed version is
ℕ-recursion : (X : 𝓤 ̇)  →  X  →  (ℕ → X → X)
              --------------------------------------
 →                     ℕ → X
ℕ-recursion X = ℕ-induction λ _ → X

--"The following special case occurs often (and is related to the fact that `ℕ` is the initial algebra
-- of the functor `𝟙 + (-)`)
ℕ-iteration : (X : 𝓤 ̇)
 →            X    →   (X → X)
             --------------------
 →              ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x) -- !!WARNING!! Agda is capable of automatically
                                                                       --                 filling in the wrong proof term here.
--"We now define addition and multiplication for the sake of illustration.
-- We first do it in Peano style. We will create a local `module` so definitions are not globally visible;
-- things in the module are indented and are visible outside the module only if we `open` the module or
-- if we write them as e.g. `Arithmetic._+_` in the following example.
module Arithmetic where
 _+_ _×_ : ℕ → ℕ → ℕ
 x + 0 = x
 x + succ y = succ (x + y)
 x × 0 = 0
 x × succ y = x + x × y
 infixl 20 _+_
 infixl 21 _×_

--"Equivalent definitions use `ℕ-induction` on the second argument `y`, via `ℕ-iteration`
module Arithmetic' where

 _+_ _×_ : ℕ → ℕ → ℕ
 
 x + y = h y
  where
   h : ℕ → ℕ
   h = ℕ-iteration ℕ x succ

  --What this does:
  -- h y = (ℕ-iteration ℕ x succ) y
  --     = (ℕ-recursion ℕ x (λ _ x → succ x)) y
  --     = (ℕ-induction (λ _ → ℕ) x (λ _ x → succ x)) y = (ℕ-induction (λ _ → ℕ) A0 f) y = h y
  --       where
  --         h : (y : ℕ) → ℕ
  --         h (y = 0) = x
  --         h (y = succ n) = f n (h n) = (λ _ x → succ x) n (h n) = succ (h n)

 x × y = h y
  where
   h : ℕ → ℕ
   h = ℕ-iteration ℕ 0 (x +_)

 infixl 20 _+_
 infixl 21 _×_

--"As another example, we define the less-than-or-equal relation by nested induction, on the first argument
--and then the second, but we use pattern matching for the sake of readability."
module ℕ-order where
 _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
 0 ≤ y = 𝟙
 succ x ≤ 0 = 𝟘
 succ x ≤ succ y = x ≤ y
 x ≥ y = y ≤ x
 infix 10 _≤_
 infix 10 _≥_

--"Exercise. Write it using `ℕ-induction`, recursion or iteration, as appropriate."
--SOLUTION. come back later (and/or see HoTT-UF-Agda.html#someexercisessol)
--"Exercise. After learning about the types `Σ` and `_≡_` explained below, prove 
-- > `x ≤ y` if and only if `Σ \(z : ℕ) → x + z ≡ y`."
--SOLUTION. come back to this later (and/or see HoTT-UF-Agda.html#basicarithmetic)
--"After learning univalence prove that in this case this implies `(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`."
--SOLUTION. come back later (see: HoTT-UF-Agda.html#additionalexercisessol and HoTT-UF-Agda.html#univalence).
--"That bi-implication can be turned into equality only holds for types that are subsingletons and this is
--called propositional extensionality." (HoTT-UF-Agda.html#univalence-gives-propext, HoTT-UF-Agda.html#propext)."

--"The identity function (in two versions with different implicit arguments)
id : {X : 𝓤 ̇} → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇) → X → X
𝑖𝑑 X = id



-------------------------------------------------------------------------------------------------------------
-- The identity type former `Id`, also written `_≡_`
-- see: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#identitytype

--"We now introduce the central type constructor of MLTT from the point of view of univalent mathematics.

--"In Agda we can define Martin-Löf's identity type as follows:
infix 0 Id
data Id {𝓤} (X : 𝓤 ̇) : X → X → 𝓤 ̇ where
 refl : (x : X) → Id X x x

{-"Intuitively, the above definition says the only element of the type `Id X x x` is something called `refl x` (for reflexivity).
    But, as we shall see in a moment, this intuition turns out to be incorrect.

   Here we have a TYPE FAMILY indexed by the ELEMENTS of a given type. As Escardo puts it,

  "Given a type `X` in a universe `𝓤`, we define a FUNCTION `Id X : X → X → 𝓤` by some mysterious sort of induction. It is this that
   prevents us from being able to prove that the only element of the type `Id X x x` is `refl x`, or that the type `Id X x y` has at most one
   element no matter what `y : X` is. There is however, one interesting, and crucial, thing we CAN prove---namely that for a fixed `x : X`, the
   type
               `Σ y ꞉ Y , Id X x y` is a singleton    (or, in the old notation, `Σ λ (y ꞉ Y) → Id X x y`is a singleton)

   [...but we cannot prove that there is only one proof of this?]  <== Question. -}

--"We will use the following alternative notation for the identity type former `Id`, where the symbol `_` in the right-hand side of the
-- definition indicates that we ask Agda to infer which type we are talking about (which is `X`, but this name is not available in the scope
-- of the DEFINING EQUATION of the type former `_≡_`):
infix   0 _≡_
_≡_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≡ y = Id _ x y

≡-sym : {X : 𝓤 ̇ }{x y : X} → x ≡ y → y ≡ x
≡-sym (refl _) = refl _

--"Another intuition for the type family `_≡_ : X → X → 𝓤` is that it gives the least reflexive relation on the type `X`, as suggested by
-- Martin-Löf's induction principle J (discussed below)."

{-"Whereas we can make the intuition that `x ≡ x` has precisely one element good by POSTULATING a certain `K` axiom due to
   Thomas Streicher (which comes with Agda by default but we have disabled above) we cannot PROVE that `refl x` is the only element of
   `x ≡ x` for an arbitrary type `X`. This non-provability result was established by Hofmann and Streicher by giving a model of type theory
   in which types are interpreted as `1`-groupoids. However, for the elements of SOME types, such as the type `ℕ` of natural numbers,
   it IS possible to prove that an identity type `x ≡ y` has at most one element. Such types are called SETS in univalent mathematics.

  "If instead of the axiom `K` we adopt Voevodsky's UNIVALENCE axiom, we get specific examples of objects `x` and `y` such that the
   type `x ≡ y` has multiple elements, WITHIN the type theory.  It follows that the identity type `x ≡ y` is fairly under-specified in
   general, in that we can't prove or disprove that it has at most one element.

  "There are two opposing ways to resolve the ambiguity or under-specification of the identity types:
     (1) We can consider the `K` axiom, which postulates that all types are sets, or
     (2) we can consider the UNIVALENCE AXIOM, arriving at univalent mathematics, which gives rise to
         types that are more general than sets, the `n`-groupoids and `∞`-groupoids.
   In fact, the univalence axiom will say, in particular, that for some types `X` and elements `x y : X`, the identity type `x ≡ y`
   does have more than one element.

  "A possible way to understand the element `refl x` of the type `x ≡ x` is as the "generic identification" between the point `x` and
   itself, but which is by no means necessarily the ONLY identitification in univalent foundations. It is generic in the sense that to explain
   what happens with all identifications `p : x ≡ y` between any two points `x` and `y` of a type `X`, it suffices to explain what happens
   with the identification `refl x : x ≡ x` for all points `x : X`. This is what the induction principle for identity given by Martin-Löf says,
   which he called J (we could have called it `≡-induction`, but we prefer to honour MLTT tradition)." -}

𝕁 : (X : 𝓤 ̇)  →  ( A : (x y : X) → x ≡ y → 𝓥 ̇ )
 →     ( (x : X) → A x x (refl x) )    →    (x y : X) (p : x ≡ y)
        ------------------------------------------------
 →                       A x y p
𝕁 X A Ax x x (refl x) = Ax x

≡-induction : (X : 𝓤 ̇) → (A : (x y : X) → x ≡ y → 𝓥 ̇) → ((x : X) → A x x (refl x)) → (x y : X) (p : x ≡ y) → A x y p
≡-induction = 𝕁 -- alias

{-"This is related to the YONEDA LEMMA (see: https://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html)
   in category theory...which says that certain natural transformations are UNIQUELY DETERMINED by their ACTION ON THE IDENTITY
   ARROWS, even if they are DEFINED FOR ALL ARROWS. Similarly here, `𝕁` is uniquely determined by its ACTION ON REFLEXIVE
   IDENTIFICATIONS, but is DEFINED FOR ALL IDENTIFICATIONS between two points, not just reflexivities.

  "In summary, Martin-Löf's identity type is given by the data
    * `Id`,
    * `refl`,
    * `𝕁`,
    * the above equation for `𝕁`.

  "However, we will not always use this induction principle, because we can instead work with the instances we need by pattern
   matching on `refl` (which is just what we did to define the principle itself) and there is a theorem by Jesper Cockx that says that
   with the Agda option `without-K`, pattern matching on `refl` can define/prove precisely what `𝕁` can.
   (see: https://dl.acm.org/citation.cfm?id=2628139 )." -}

--*Exercise*. Define
ℍ : {X : 𝓤 ̇ }(x : X)(B : (y : X) → x ≡ y → 𝓥 ̇ )
 →       B x (refl x)  → (y : X)  → (p : x ≡ y)
         ---------------------------------
 →                             B y p
ℍ x B b x (refl x) = b

--Then we can define `𝕁` from `ℍ` as follows:
𝕁' : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
 →   ( (x : X) → A x x (refl x) )   →   (x y : X) (p : x ≡ y)
      --------------------------------------------
 →                       A x y p

𝕁' X A f x = ℍ x (A x) (f x)

𝕁-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
                 ( f : (x : X) → A x x (refl x) )  (x y : X) (p : x ≡ y)
             ---------------------------------------------
 →               𝕁 X A f x y p ≡ 𝕁' X A f x y p
𝕁-agreement X A f x x (refl x) = refl (f x)


--"Similarly define `ℍ'` from `𝕁` without using pattern matching on `refl` and show that it
-- coincides with `ℍ` (possibly using pattern matching on `refl`). This is harder
-- ( see http://www.cse.chalmers.se/~coquand/singl.pdf )"

-- SOLUTION. (attempt)
ℍ' : (X : 𝓤 ̇) (x : X) ( B : (y : X) → x ≡ y → 𝓥 ̇ )
 →          B x (refl x)    →   (y : X) (p : x ≡ y)
     ---------------------------------------------
 →                      B y p -- B y p : 𝓥 ̇  -- 𝕁 will prove A x y p, which we must tranfer into B y p
ℍ' X x B Bxr x (refl x) =  𝕁 (B x (refl x)) (λ x₁ y₁ x₁≡y₁ → B x (refl x)) (λ _ → Bxr) Bxr Bxr (refl Bxr)

----- !!! I don't yet fully understand how ℍ' and 𝕁 work... come back to this!!! --------

{-NOTATION.
  "The symbols "`=`" and "`≡`" are swapped with respect to the HoTT book convention for definitional/judgemental equality and
   type valued equality, and there is nothing we can do about that because "`=`" is a reserved Agda symbol for definitional equality.
   Irrespective of this, it does make sense to use "`≡`" with a triple bar, if we understand this as indicating that there are multiple
   ways of identifying two things in general.

  "With this, we have concluded the rendering of our spartan MLTT in Agda notation." -}


-------------------------------------------------------------------------------------------------------
-- SUMS AND PRODUCTS.
--The binary sum type constructor `_+_`.  The "disjoint sum" (or "direct sum") of the types `X` and `Y`. Elements of the type
--`X + Y` have the forms `inl x` and `inr y`, with `x : X` and `y : Y`. If `X : 𝓤` and `Y : 𝓥`, then `X + Y : 𝓤 ⊔ 𝓥`, where
--`𝓤 ⊔ 𝓥` is the lub of the universes `𝓤` and `𝓥`. In Agda we define this as follows.
infixr 20 _+_
data _+_ {𝓤 𝓥} (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 inl : X → X + Y
 inr : Y → X + Y

--"To prove that a property `A` of the sum holds for all `z : X + Y`, it is enough to prove that `A (inl x)` holds for all `x : X`
-- and that `A (inr y)` holds for all `y : Y`. This amounts to definition by cases:
+-induction : {X : 𝓤 ̇}{Y : 𝓥 ̇} (A : X + Y → 𝓦 ̇)
 →           ( (x : X) → A (inl x) )  →  ( (y : Y) → A (inr y) )
             ---------------------------------------------
 →                       (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-intro : {X : 𝓤 ̇}{Y : 𝓥 ̇} (A : X + Y → 𝓦 ̇) → ( (x : X) → A (inl x) )  →  ( (y : Y) → A (inr y) ) → (z : X + Y) → A z
+-intro = +-induction -- alias

+-recursion : {X : 𝓤 ̇}{Y : 𝓥 ̇} {A : 𝓦 ̇}
 →        (X → A)  →  (Y → A)
         --------------------------
 →             X + Y → A
+-recursion{A = A} = +-induction λ _ → A

--"When `A` and `B` are viewed as props, `A + B` is understood as "`A` or `B`", the proof of which requires
-- to prove one of `A` and `B`. When `A` and `B` are simultaneously possible, we have two proofs, but sometimes
-- we want to deliberately ignore which one we get, when we want to get a truth value rather than a possibly
-- more general type, and in this case we use the **truncation** `∥ A + B ∥`."

--"But also `_+_` is used to construct mathematical objects. For example, we can define a two-point type:"

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙
  
--"We can name the left and right points as follows, using patterns, so that they can be used in pattern matching:
pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

--"We can define induction on 𝟚 directly by pattern matching:
𝟚-induction : (A : 𝟚 → 𝓤 ̇) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

--"Or we can prove it by induction on `_+_` and `𝟙`:
𝟚-induction' : (A : 𝟚 → 𝓤 ̇) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A (𝟙-induction (λ z → A (inl z)) a₀) (𝟙-induction (λ z → A (inr z)) a₁)

--------------------------------------------------------

-- -----------
-- `Σ` types
-- -----------
--"Given universes `𝓤` and `𝓥`, a type `X : 𝓤` and a type family `Y : X → 𝓥`, we want to construct its sum,
-- which is a type whose elements are of the form `(x , y)`, with `x : X` and `y : Y x`. This sum type will live
-- in the lub `𝓤 ⊔ 𝓥` of the universes `𝓤` and `𝓥`. We will write `Σ Y` for this sum, with `X`, as well as
-- the universes, implicit.

--"Often Agda, and people, can figure out what the unwritten type `X` is, from the definition of `Y`. But sometimes
-- there may be either lack of enough information, or of enough concentration power by people, or of sufficiently
-- powerful inference algorithms in the implementation of Agda. In such cases we can write `Σ λ(x : X) → Y x`,
-- because `Y = λ (x : X) → Y x` by a so-called η-rule.

--"However, we will often use the synonym `\` of `λ` for `Σ`, as if considering it as part of the `Σ` syntax:
-- `Σ \(x : X) → Y x`.

--"In MLTT we would write this as `Σ (x : X), Y x`, for example with the indexing `x : X` written as a subscript of
-- `Σ` or under it.

--"Or it may be that the name `Y` is not defined, and we work with a nameless family defined on the fly, as in the
-- exercise proposed above: `Σ \(z : ℕ) → x + z ≡ y`, where `Y z = (x + z ≡ y)` in this case, and where we haven't
-- defined the identity type former `_≡_` yet.

--"We can construct the `Σ` type former as follows in Agda:
infixr 50 _,_
record Σ {𝓤 𝓥} {X : 𝓤 ̇}(Y : X → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 constructor
  _,_
 field
  x : X
  y : Y x

--"This says we are defining a binary operator `_,_` to construct the elements of this type as `x , y`.
-- The definition says that an element of `Σ Y` has two `fields`, giving the types for them."

--"*Remark*. Normally people call the two fields `x` and `y` something like `pr₁` and `pr₂`, or `fst` and `snd`, and
-- then do `open Σ public` and have the projections available as functions automatically. But we will deliberately not
-- do that, and instead define the projections ourselves, because this is confusing for beginners; in particular because
-- it will not be immediately clear that the projections have the following types.
pr₁ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → Σ Y → X
pr₁ (x , y) = x

∣_∣ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → Σ Y → X
∣ x , y ∣ = x

pr₂ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

∥_∥ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → (z : Σ Y) → Y (pr₁ z)
∥ x , y ∥ = y
--"We now introduce syntax to be able to write `Σ x ꞉ X , y` instead of `Σ λ(x ꞉ X) → y`. For this purpose, we first
-- define a version of Σ that makes the index type explicit."
infixr -1 -Σ
-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
syntax -Σ X (λ x → y) = Σ x ꞉ X , y -- type `꞉` as `\:4`

--"For some reason, Agda has this kind of definition backwards: the definiendum and the definiens are swapped with respect
-- to the normal convention of writing what is defined on the left-hand side of the equality sign.
-- Notice also that "꞉" in the above syntax definition is not the same as “:”, even though they may look the same.
-- For the above notation Σ x ꞉ A , b, the symbol “꞉” has to be typed “\:4” in the emacs Agda mode.

--"To prove that `A z` holds for all `z : Σ Y`, for a given property `A`, we just prove that we have `A (x , y)` for all
-- `x : X` and `y : Y x`.  This is called `Σ` induction or `Σ` elimination, or `uncurry`, after Haskell Curry.
Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
 →           ( (x : X)  (y : Y x)   →   A (x , y) )   →   ( (x , y) : Σ Y )
             --------------------------------------------------
 →                                 A (x , y)
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇}{Y : X → 𝓥 ̇}{A : Σ Y → 𝓦 ̇} → ( ( (x , y) : Σ Y ) → A (x , y) ) → ( (x : X) (y : Y x) → A (x , y) )
curry f x y = f (x , y)

Σ-inv = curry

--"An important particular case of the sum type is the binary cartesian product, when the type family
-- doesn't depend on the indexing type:
infixr 30 _×_
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

--alternatively,
_×'_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ×' Y = Σ λ(x : X) → Y

--"We have seen by way of examples that the function type symbol `→` represents logical implication, and that a
-- dependent function type (x : X) → A x` represents a universal quantification.

--"We have the following uses of `Σ`.
--
--×The binary cartesian product represents conjunction "and". If the types `A` and `B` stand for mathematical statements,
-- then the mathematical statement "`A` and `B`" is codified as `A × B`, because to establish "`A` and `B`", we have to
-- provide a pair `(a , b)` of proofs `a : A` and `b : B`. So notice that in type theory proofs are mathematical objects,
-- rather than meta-mathematical entities like in set theory. They are just elements of types.
--
--×The more general type `Σ (x : X), A x`---with `X` a collections of objects and `A` a prop---represents *designated*
-- existence there is a designated `x : X` with `A x`. To establish this, we have to
-- provide a specific element `x : X` and a proof `a : A x`, together in a pair `(x , a)`.
--
--×Later we will discuss *unspecified* existence `∃ (x : X), A x`, which will be obtained by a sort of quotient of
-- `Σ (x : X), A x`, written `∥ Σ (x : X), A x ∥`, that identifies all the elements of the type `Σ (x : X), A x` in
-- a single equivalence class, called its subsingleton (or truth value or propositional) truncation.
--
--×Another reading of `Σ (x : X), A x` is as the type of `x : X` with `A x`, similar to set-theoretical notation
-- `{ x ∈ X | A x }`. But we have to be careful because if there is more than one element in the type `A x`, then `x`
-- will occur more than once in this type. More precisely, for `a₀ a₁ : A x` we have inhabitants `(x , a₀)` and `(x , a₁)`
-- of the type `Σ (x : X), A x`. In such situations, if we don't want that, we have to either ensure that the type `A x`
-- has at most one element for every `x : X`, or instead consider the truncated type `∥ A x ∥` and write `Σ (x : X), ∥ A x ∥`.
--
-- An example is the image of a function `f : X → Y`, which will be defined to be `Σ (y : Y), ∥ Σ (x : X), f x ≡ y ∥`.
--
-- This is the type of `y : Y` for which there is an unspecified `x : X` with `f x ≡ y`.
--
-- (For constructively minded readers, we emphasize that this *doesn't erase* the witness `x:X`.)

-------------------------------------

-- `Π` types
------------------

--"`Π` types are builtin with a different notation in Agda, as discussed above, but we can introduce the notation `Π`
-- for them, similar to that for `Σ`:
Π : {X : 𝓤 ̇} (A : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y
infixr -1 -Π
syntax -Π A (λ x → b) = Π x ꞉ A , b

--"We take the opportunity to define the identity function (in two versions with different implicit arguments)
-- and function composition:"
-- (moved to Basic.agda)
-- id : {X : 𝓤 ̇} → X → X
-- id x = x

-- 𝑖𝑑 : (X : 𝓤 ̇) → X → X
-- 𝑖𝑑 X = id

--"Usually the type of function composition `_∘_` is given as simply `(Y → Z) → (X → Y) → (X → Z)`.
-- With dependent functions, we can give it a more general type:
infixl 70 _∘_ -- NOTATION. type ∘ as `\circ`
_∘_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇}
 →   ( (y : Y) → Z y )  →  (f : X → Y)  →  (x : X) → Z (f x)
g ∘ f = λ x → g (f x) 

--"Notice that this type for the composition function can be read as a mathematical statement: If `Z y` holds for all `y : Y`,
-- then for any given `f : X → Y` we have that `Z (f x)` holds for all `x : X`. And the non-dependent one is just the transitivity
-- of implication. The following functions are sometimes useful when we are using implicit arguments, in order to recover them
-- explicitly without having to list them as given arguments:
domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} _ = X

codomain : {X : 𝓤 ̇}{Y : 𝓥 ̇} → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} _ = Y

type-of : {X : 𝓤 ̇} → X → 𝓤 ̇
type-of {𝓤} {X} x = X




-----------------------------------------------------------------------------------------------
-- TRANSPORT.


{-"Before embarking on the development of univalent mathematics within our spartan MLTT, we pause to discuss some basic
   examples of mathematics in Martin-Löf type theory." -}

------------------------------------------------------------
-- Transport along an identification

transport : {X : 𝓤 ̇} (F : X → 𝓥 ̇) {s t : X}  →  s ≡ t  →  F s → F t
transport F (refl s) = 𝑖𝑑 (F s)

--               F
--         s ------> Fs
--         ||              ||
-- refl s ||              ||   transport
--         V              V
--         t ------> Ft
--                F

--"We can equivalently define transport using `𝕁` as follows:"

transport𝕁 : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x y : X} → x ≡ y  →  A x → A y
transport𝕁{𝓤}{𝓥}{X} A {x} {y} = 𝕁 X (λ x₁ y₁ _ → A x₁ → A y₁) (λ x₁ → 𝑖𝑑 (A x₁)) x y

--"In the same way `ℕ`-recursion can be seen as the non-dependent special case of `ℕ`-induction,
-- the following transport function can be seen as the non-dependent special case of the `≡`-induction
-- principle `ℍ` with some of the arguments permuted and made implicit:
nondep-ℍ : {X : 𝓤 ̇} (x : X) (A : X → 𝓥 ̇) → A x → (y : X) → x ≡ y → A y
nondep-ℍ x A = ℍ x (λ y _ → A y)

transportℍ : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x y : X} → x ≡ y  →  A x  →  A y
transportℍ A {x} {y} x≡y v = nondep-ℍ x A v y x≡y

--"All the above transports coincide:
transport-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇) {x y : X} (p : x ≡ y)
 → (transportℍ A p ≡ transport A p) × (transport𝕁 A p ≡ transport A p)
transport-agreement  A (refl x) = refl (transport A (refl x)) , refl (transport A (refl x))

--"The following is for use when we want to recover implicit arguments without mentioning them.
lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤}{X}{x}{y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤}{X}{x}{y} p = y

-- ---------------------------------------------------------------------------
-- Composition of identifications

--"Given two identifications `p : x ≡ y` and `q : y ≡ z`, we can compose them to get an identification `p ∙ q : x ≡ z`. This can also
-- be seen as transitivity of equality. Because the type of composition doesn't mention `p` and `q`, we can use the
-- non-dependent version of `≡`-induction.
infixl 30 _∙_ -- NOTATION: type ∙ using `\.`
_∙_ : {X : 𝓤 ̇}{s t u : X} → s ≡ t → t ≡ u → s ≡ u
p ∙ q = transport ( lhs p ≡_ ) q p

--"Here we are considering the family `F a = (s ≡ a)`, and using the identification `q : t ≡ u` to transport
-- `F t` to `F u`, that is `s ≡ t` to `s ≡ u`.

-- *Exercise*. Can you define an alternative version that uses `p` to transport. Do the two versions give equal results?
-- SOLUTION. Use the family F a = (a ≡ u) and use the identification p : s ≡ t to transport F t to F s.
_⋆'_ : {X : 𝓤 ̇}{s t u : X} → s ≡ t → t ≡ u → s ≡ u
p ⋆' q = transport (_≡ rhs q) (≡-sym p) q

--"When writing `p ∙ q`, we lose information on the lhs and the rhs of the identifications `p : s ≡ t` and `q : t ≡ u`,
-- which makes some definitions hard to read. We now introduce notation to be able to write e.g. s ≡⟨ p ⟩ t ≡⟨ q ⟩ u ∎
-- as a synonym of the expression `p ∙ q` with some of the implicit arguments of `_∙_` made explicit."
--"We have one ternary mixfix operator `_≡⟨_⟩_` and one unary `postfix` operator `_∎`.
infixr  0 _≡⟨_⟩_
_≡⟨_⟩_ : {X : 𝓤 ̇} (s : X) {t u : X} → s ≡ t → t ≡ u → s ≡ u
s ≡⟨ p ⟩ q = p ∙ q

infix   1 _∎
_∎ : {X : 𝓤 ̇} (s : X) → s ≡ s
s ∎ = refl s

--Inversion of identifications
--"Given an identification, we get an identification in the opposite direction:
infix  40 _⁻¹
_⁻¹ : {X : 𝓤 ̇} → {s t : X} → s ≡ t → t ≡ s
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))  -- Let F a = a ≡ s, and use  ≡ y to transport
                                                       -- F s (i.e., s ≡ s) to F t (i.e., t ≡ s)

--"We can define an alternative of identification composition with this:
_∙'_ : {X : 𝓤 ̇} {s t u : X} → s ≡ t → t ≡ u → s ≡ u
p ∙' q = transport ( _≡ rhs q ) ( p ⁻¹ ) q

--"This agrees with the previous one:"
∙agreement : {X : 𝓤 ̇}{s t u : X} (p : s ≡ t) (q : t ≡ u)
  →     p ∙' q ≡ p ∙ q
∙agreement (refl s) (refl s) = refl (refl s)

--"But `refl t` is a definitional neutral element for one of them on the right and for the other one on the left,
--  * `p ∙ refl t = p`,
--  * `refl t ∙' q = q`,
-- which can be checked as follows"
rdnel : {X : 𝓤 ̇}{s t : X} (p : s ≡ t)  → p ∙ refl t ≡ p
rdnel p = refl p

∙-right-id : {X : 𝓤 ̇}{s t : X} (p : s ≡ t)  → p ∙ refl t ≡ p
∙-right-id = rdnel -- alias.

rdner : {X : 𝓤 ̇}{t u : X} (q : t ≡ u)  →  refl t ∙' q ≡ q
rdner q = refl q

∙'-left-id : {X : 𝓤 ̇}{t u : X} (q : t ≡ u)  →  refl t ∙' q ≡ q
∙'-left-id = rdner -- alias.

--*Exercise*. The identification `refl y` is neutral on both sides of each of the two operations `_∙_` and
-- `_∙'_`, although not definitionally. This has to be proved by induction on identifications, as in `∙-agreement`.
--SOLUTION.
∙-left-id : {X : 𝓤 ̇}{t u : X} (q : t ≡ u) → refl t ∙ q ≡ q
∙-left-id (refl s) = refl (refl s)

-- ----------------------------------------------------------------------------------
-- Application of a function to an identification
-- Given an identification `p : x ≡ x'` we get an identification `ap f p : f x ≡ f x'` for any `f : X → Y`:
ap : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y){x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} p = transport (λ - → f x ≡ f -) p (refl (f x))
--NOTATION (cf. `cong` in `Relation/Binary/PropositionalEquality/Core.agda` )

--"Here the symbol "`-`", which is not to be confused with the symbol "`_`", is a variable. We will adopt the
-- convention in these notes of using this variable name "`-`" to make clear which part of an expression we
-- are replacing with `transport`.

--"Notice that we have so far used the recursion principle `transport` only. To reason about `transport`,
-- `_∙_`, `_⁻¹` and `ap`, we will need to use the full induction principle `𝕁` (or equivalently pattern
-- matching on `refl`)."

-- ------------------------------------------------------------------------------
-- Pointwise (extensional) equality of functions

--"We will work with pointwise equality of functions, defined as follows, which, using univalence,
-- will be equivalent to equality of functions. (see: HoTT-UF-Agda.html#hfunext)."

infix 0 _∼_
_∼_ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x

--"The symbol `∀` is a built-in notation for `Π` . We could equivalently write the *definiens* as
-- `(x : _) → f x ≡ g x`, or, with our `Π` notation, `Π \x → f x ≡ g x`, or, with our `domain` notation
-- `(x : domain f) → f x ≡ g x`.

   -- infix   0 _∼_
   -- infixr 50 _,_
   -- infixr 30 _×_
   -- infixr 20 _+_
   -- infixl 70 _∘_
   -- infix   0 _≡_
   -- infix  10 _⇔_
   -- infixl 30 _∙_
   -- infixr  0 _≡⟨_⟩_
   -- infix   1 _∎
   -- infix  40 _⁻¹
   -- infix  10 _◁_
   -- infixr  0 _◁⟨_⟩_
   -- infix   1 _◀
   -- infix  10 _≃_
   -- infixl 30 _●_
   -- infixr  0 _≃⟨_⟩_
   -- infix   1 _■
   -- infix  40 _∈_
   -- infix  30 _[_,_]

--more equations for transport, including a dependent version
transport-× : {X : 𝓤 ̇ }(A : X → 𝓥 ̇ )(B : X → 𝓦 ̇ ){x y : X}
              (p : x ≡ y)    {c : A x × B x}
             -------------------------------------------------
 → transport (λ x → A x × B x) p c ≡ (transport A p (pr₁ c) ,
                                        transport B p (pr₂ c))
transport-× A B (refl x) {c} = refl c

transportd : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : (x : X) → A x → 𝓦 ̇ )
             {x : X} (a : A x) ((a' , b) : Σ a ꞉ A x , B x a)  {y : X}
             (p : x ≡ y)  →   B x a'
             ---------------------------------------------------------
 →          B y (transport A p a')
transportd A B a σ (refl y) = id

transport-Σ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )(B : (x : X) → A x → 𝓦 ̇ )
             {x : X}(y : X)
             (p : x ≡ y)  (a : A x)   {(a' , b) : Σ a ꞉ A x , B x a}
       ----------------------------------------------------------------------
 → transport (λ x → Σ y ꞉ A x , B x y) p (a' , b) ≡ transport A p a' ,
                                                      transportd A B a (a' , b) p b
transport-Σ A B {x} x (refl x) a {σ} = refl σ


-- Added later. see: https://www.cs.bham.ac.uk/~mhe/agda-new/Id.html#1449


back-transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} → x ≡ y → A y → A x
back-transport B p = transport B (p ⁻¹)

------------------------------------------------------------------------------------
-- NEGATION.
---------------------------------------------------------
--"Reasoning with negation
--"We first introduce notation for double and triple negation to avoid the use of brackets.
¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬ A = ¬(¬ A)

¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬¬ A = ¬(¬¬ A)

--"To prove that `A → ¬¬ A`, that is, `A → ( (A → 𝟘) → 𝟘 )`, we start with a hypothetical element `a : A` and a
-- hypothetical function `u : A → 𝟘` and the goal is to get an element of `𝟘`. All we need to do is to apply the
-- function `u` to `a`. This gives double-negation introduction:
dni : (A : 𝓤 ̇) → A → ¬¬ A
dni A a A→𝟘 = A→𝟘 a

¬¬-intro = dni -- alias

{-"We don't assume a "double-negation-elimination" rule, like `¬¬-elim : ¬¬ A → A`, and we cannot prove such a rule unless
   we assume something else (e.g., em, which is equivalent to ¬¬-elim).

  "Mathematically, this says that if we have a point of `A` (we say that `A` is pointed) then `A` is nonempty. There is no
   general procedure to implement the converse, that is, from a function `(A → 𝟘) → 𝟘` to get a point of `A`. For truth
   values `A`, we can assume this as an axiom if we wish, because it is equivalent to the law of excluded middle. For arbitrary
   types `A`, this would be a form of global choice for type theory.  However, global choice is inconsistent with univalence
   (see HoTT book, Theorem 3.2.2), because there is no way to choose an element of every non-empty type in a way that is
   invariant under automorphisms. However, the axiom of choice IS consistent with univalent type theory, as stated above." -}

--"In the proof of the following, we are given...functions `f : A → B` and `v : B → 𝟘`, and an...element `a : A`, and our goal
-- is to get an element of `𝟘`. But this is easy, because `f a : B` and hence `v (f a) : 𝟘`.
contrapositive : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → (¬ B → ¬ A)
contrapositive A→B B→𝟘 = λ a → B→𝟘 (A→B a)

--"We have given a logical name to this function. Mathematically, this says that if we have a function `A → B` and `B` is empty,
-- then `A` must be empty, too. And from this we get that three negations imply one:
tno : (A : 𝓤 ̇) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

¬¬¬-elim = tno -- alias

--"Hence, using `dni` once again, we get that `¬¬¬ A` if and only if `¬ A`. It is entertaining to see how Brouwer formulated
-- and proved this fact in his Cambridge Lectures on Intuitionism.
-- (see: https://books.google.co.uk/books/about/Brouwer_s_Cambridge_Lectures_on_Intuitio.html?id=B88L2k5KnkkC&redir_esc=y )

--"If we define *logical equivalence* by
_⇔_  : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)
infix 10 _⇔_

_iff_  : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
_iff_ = _⇔_ -- alias
infix 10 _iff_

lr-implication : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X iff Y) → (X → Y)
lr-implication = pr₁

iff-elim-left : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X iff Y) → (X → Y)
iff-elim-left = lr-implication -- alias

rl-implication : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X iff Y) → (Y → X)
rl-implication = pr₂

iff-elim-right : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X iff Y) → (Y → X)
iff-elim-right = rl-implication -- alias

--"then we can render Brouwer’s argument in Agda as follows, where the “established fact” is dni:
absurdity³-is-absurdity : {A : 𝓤 ̇} → ¬¬¬ A iff ¬ A
absurdity³-is-absurdity {𝓤} {A} = firstly , secondly
 where
  firstly : ¬¬¬ A → ¬ A
  firstly = contrapositive (¬¬-intro A)

  secondly : ¬ A → ¬¬¬ A
  secondly = ¬¬-intro (¬ A)

--"We now define a symbol for the negation of equality.
_≢_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x₁ ≢ x₂ = ¬ (x₁ ≡ x₂)

--"In the following proof, we have `u : x ≡ y → 𝟘` and need to define a function `y ≡ x → 𝟘`. So all we
-- need to do is to compose the function that inverts identifications with `u`:
≢-sym : {X : 𝓤 ̇} {u v : X} → u ≢ v → v ≢ u
≢-sym {𝓤} {X} {u}{v} u≡v→𝟘 = λ v≡u → u≡v→𝟘 (v≡u ⁻¹)

--"To show that the type `𝟙` is not equal to the type `𝟘`, we use that `transport id` gives `𝟙 ≡ 𝟘 → id 𝟙 → id 𝟘`
-- where `id` is the identity function of the universe `𝓤₀`. More generally, we have the following conversion of type
-- identifications into functions:
Id→Fun : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇))

--"Here the identity function is that of the universe `𝓤` where the types `X` and `Y` live. An equivalent
-- definition is the following, where this time the identity function is that of the type `X`:
Id→Fun' : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Id→Fun' (refl X) = 𝑖𝑑 X

Id→Funs-agree : {X Y : 𝓤 ̇} (p : X ≡ Y)
 →              Id→Fun p ≡ Id→Fun' p
Id→Funs-agree (refl X) = refl (𝑖𝑑 X)

--"So if we have a hypothetical identification `p : 𝟙 ≡ 𝟘`, then we get a function `𝟙 → 𝟘`. We apply this
-- function to `⋆ : 𝟙` to conclude the proof.
𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 𝟙≡𝟘 = Id→Fun 𝟙≡𝟘 ⋆

--"To show that the elements `₁` and `₀` of the two-point type `𝟚` are not equal, we reduce to the above case.
--(where, recall, 𝟚 = 𝟙 + 𝟙 is the disjoint sum of singleton type 𝟙 with itself and 
-- we named the left and right points of 𝟚 using patterns `₀ = inl ⋆` and `₁ = inr ⋆`)
₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ ₁≡₀ = 𝟙-is-not-𝟘 𝟙≡𝟘
 where
  f : 𝟚 → 𝓤₀ ̇  -- 𝟚→𝓤₀̇
  f ₀ = 𝟘
  f ₁ = 𝟙

  𝟙≡𝟘 : 𝟙 ≡ 𝟘
  𝟙≡𝟘 = ap f ₁≡₀
  
--"*Remark*. Agda allows us to use a pattern `()` to get the following quick proof.  However, this method of
-- proof doesn't belong to the realm of MLTT. Hence we will use the pattern `()` only in the above
-- definition of `𝟘-induction` and nowhere else in these notes.
₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ≡ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()

--"Perhaps the following is sufficiently self-explanatory given the above:
decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

has-decidable-equality : (X : 𝓤 ̇) → 𝓤 ̇
has-decidable-equality X = (x₁ x₂ : X) → decidable (x₁ ≡ x₂)

𝟚-has-decidable-equality : has-decidable-equality 𝟚
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

{-"So we consider four cases. In the first and the last, we have equal things and so we give an answer in the left-hand side
   of the sum. In the middle two, we give an answer in the right-hand side, where we need functions
   `₀ ≡ ₁ → 𝟘` and `₁ ≡ ₀ → 𝟘`... `≢-sym₁-is-not-₀` and `₁-is-not-₀` respectively.

  "The following is more interesting. We consider the two possible cases for `n`. The first one assumes a hypothetical function
   `f : ₀ ≡ ₀ → 𝟘`, from which we get `f (refl ₀) : 𝟘`, and then, using `!𝟘`, we get an element of any type we like, which we
   choose to be `₀ ≡ ₁`, and we are done. The other case `n = ₁` doesn't need to use the hypothesis `f : ₁ ≡ ₀ → 𝟘`,
   because the desired conclusion holds right away, as it is `₁ ≡ ₁`, which is proved by `refl ₁`. But notice that there is
   nothing wrong with the hypothesis `f : ₁ ≡ ₀ → 𝟘`. For example, we can use `not-zero-is-one` taking `n` to be `₀`
   and `f`to be `₁-is-not-₀`, so that the hypotheses can be fulfilled in the second equation. -}
not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ n≢₀ = !𝟘 (₀ ≡ ₁) (n≢₀ (refl ₀))
not-zero-is-one ₁ _ = refl ₁

--"The following generalizes `₁-is-not-₀`, both in its statement and its proof (so we could have formulated
-- it first and then used it to deduce `₁-is-not-₀`):
inl-inr-disjoint-images : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤}{𝓥}{X}{Y} inlx≡inry = 𝟙-is-not-𝟘 𝟙≡𝟘
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘

  𝟙≡𝟘 : 𝟙 ≡ 𝟘
  𝟙≡𝟘 = ap f inlx≡inry

--"If `P or Q` holds and `P` fails, then `Q` holds:
right-fails-gives-left-holds : {P : 𝓤 ̇} {Q : 𝓥 ̇} → P + Q → ¬ Q → P
right-fails-gives-left-holds (inl p) _ = p
right-fails-gives-left-holds (inr q) ¬Q = !𝟘 _ (¬Q q)

disjunctive-syllogism = right-fails-gives-left-holds

-- -----------------------------------------------------------------------------
--"Example: formulation of the twin-prime conjecture
--"We illustrate the above constructs of MLTT to formulate [the Twin Prime] conjecture.
module twin-primes where
 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n) × is-prime p × is-prime (p ∔ 2)

--"Thus, not only can we write down definitions, constructions, theorems and proofs, but also conjectures.
-- They are just definitions of types. Likewise, the univalence axiom (to be formulated in due course) is a type."



-------------------------------------------------------------------------------------------------
-- PEANO  (remaining Peano axioms and basic arithmetic).
-- see:  https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#basicarithmetic

--"We first prove the remaining Peano axioms:
s≢0 : (x : ℕ) -> succ x ≢ 0
s≢0 x s≡0 = 𝟙-is-not-𝟘 (g s≡0)
 where
  f : ℕ -> 𝓤₀ ̇
  f 0 = 𝟘
  f (succ x) = 𝟙

  g : succ x ≡ 0 -> 𝟙 ≡ 𝟘
  g = ap f

positive-not-zero = s≢0 -- alias

--"To show that the successor function is left cancellable, we can use the following predecessor function."
pred : ℕ -> ℕ
pred 0 = 0
pred (succ n) = n

succ-elim : {x y : ℕ} -> succ x ≡ succ y -> x ≡ y
succ-elim = ap pred

succ-lc = succ-elim -- alias
--"With this we have proved all the Peano axioms."

--"Without assuming the principle of excluded middle, we can prove that `ℕ` has decidable equality:"
ℕ-decidable : has-decidable-equality ℕ 
ℕ-decidable 0 0 = inl (refl 0)
ℕ-decidable 0 (succ y) = inr (≢-sym (s≢0 y))
ℕ-decidable (succ x) 0 = inr (s≢0 x)
ℕ-decidable (succ x) (succ y) = f (ℕ-decidable x y)
 where
  f : decidable (x ≡ y) -> decidable (succ x ≡ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) -> k (succ-elim s))
  
ℕ-has-decidable-equality = ℕ-decidable

--"*Exercise*. Students should do this kind of thing at least once in their academic life: rewrite the
-- above proof of the decidability of equality of `ℕ` to use the `ℕ-induction` principle instead of
-- pattern matching and recursion, to understand by themselves that this can be done."

--"We now move to basic arithmetic, and we use a module for that."
module basic-arithmetic-and-order where

  open ℕ-order public
  open Arithmetic renaming (_+_ to _∔_) hiding (_×_)

  --"We can show that addition is associative as follows, by induction on `z`, where `IH` stands for
  -- "induction hypothesis":
  +-assoc : (x y z : ℕ) -> (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
  +-assoc x y 0 = (x ∔ y) ∔ 0 ≡⟨ refl _ ⟩ x ∔ (y ∔ 0) ∎
  +-assoc x y (succ z) = (x ∔ y) ∔ succ z   ≡⟨ refl _     ⟩
                         succ ((x ∔ y) ∔ z) ≡⟨ ap succ IH ⟩
                         succ (x ∔ (y ∔ z)) ≡⟨ refl _     ⟩
                         x ∔ (y ∔ succ z)   ∎
   where
    IH : (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
    IH = +-assoc x y z

  --"Notice that the proofs `refl _` should be read as 'by definition' or 'by construction'. They are not necessary, because Agda
  -- knows the definitions and silently expands them when necessary, but we are writing them here for the sake of clarity. Elsewhere
  -- in these notes, we do occasionally rely on silent expansions of definitions. Here is the version with the silent expansion of definitions,
  -- for the sake of illustration (the author of these notes can write, but not read it the absence of the above verbose version):
  +-assoc' : (x y z : ℕ) -> (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
  +-assoc' x y zero = refl (x ∔ y)
  +-assoc' x y (succ z) = ap succ (+-assoc' x y z)

  --"We defined addition by induction on the second argument. Next we show that the base case and induction step of a definition by
  -- induction on the first argument hold (but of course not definitionally). We do this by induction on the second argument."
  +-base-on-first : (x : ℕ) -> 0 ∔ x ≡ x
  +-base-on-first 0        = refl 0
  +-base-on-first (succ x) = ap succ (+-base-on-first x) 

  +-step-on-first : (x y : ℕ) -> succ x ∔ y ≡ succ (x ∔ y)
  +-step-on-first x zero     = refl (succ x)
  +-step-on-first x (succ y) = ap succ (+-step-on-first x y)

  --"Using this, the commutativity of addition can be proved by induction on the first argument."
  +-comm : (x y : ℕ) -> x ∔ y ≡ y ∔ x
  +-comm 0 y        = +-base-on-first y
  +-comm (succ x) y = -- Goal: succ x ∔ y ≡ succ (y ∔ x)
    succ x ∔ y  ≡⟨ +-step-on-first x y ⟩
    succ(x ∔ y) ≡⟨ ap succ (+-comm x y) ⟩
    succ(y ∔ x) ∎

  --"We now show that addition is cancellable in its left argument, by induction on the left argument:"
  +-lc :  (x y z : ℕ) -> x ∔ y ≡ x ∔ z -> y ≡ z
  +-lc 0 y z p =   -- Goal: y ≡ z
    y     ≡⟨  (+-base-on-first y)⁻¹ ⟩
    0 ∔ y ≡⟨ p ⟩
    0 ∔ z ≡⟨ +-base-on-first z ⟩
    z     ∎
  +-lc (succ x) y z p = IH
   where
    q = succ (x ∔ y) ≡⟨ (+-step-on-first x y)⁻¹ ⟩
        succ x ∔ y   ≡⟨ p ⟩
        succ x ∔ z   ≡⟨ +-step-on-first x z ⟩
        succ (x ∔ z) ∎

    IH : y ≡ z
    IH = +-lc x y z (succ-elim q)

-- COME BACK TO THIS SECTION LATER --
--"Now we solve part of an exercise given above, namely that `(x ≤ y) ⇔ Σ \(z : ℕ) → x + z ≡ y`."
--"First we name the alternative definition of `≤`:"
--\begin{code}\end{code}
--"Next we show that the two relations `≤` and `≼` imply each other."
--"In both cases, we proceed by induction on both arguments."
--\begin{code}\end{code}
--"[Later](HoTT-UF-Agda.html#additionalexercisesswol) we will show that `(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`, using univalence."
--"We now develop some generally useful material regarding the order `≤` on natural numbers. First, it is reflexive, transitive and antisymmetric:""
--\begin{code}\end{code}
--"The type of roots of a function:"
--\begin{code}\end{code}
--"The type of minimal roots of a function:"
--\begin{code}\end{code}
--"Given any root, we can find a minimal root."
--\begin{code}\end{code}

  _≼_ : ℕ → ℕ → 𝓤₀ ̇
  x ≼ y = Σ \(z : ℕ) → x ∔ z ≡ y

  ≤-gives-≼ : (x y : ℕ) → x ≤ y → x ≼ y
  ≤-gives-≼ 0 0               l = 0 , refl 0
  ≤-gives-≼ 0 (succ y)        l = succ y , +-base-on-first (succ y)
  ≤-gives-≼ (succ x) 0        l = !𝟘 (succ x ≼ zero) l
  ≤-gives-≼ (succ x) (succ y) l = γ
   where
    IH : x ≼ y
    IH = ≤-gives-≼ x y l

    z : ℕ
    z = pr₁ IH

    p : x ∔ z ≡ y
    p = pr₂ IH

    γ : succ x ≼ succ y
    γ = z , (succ x ∔ z   ≡⟨ +-step-on-first x z ⟩
             succ (x ∔ z) ≡⟨ ap succ p           ⟩
             succ y       ∎)

  ≼-gives-≤ : (x y : ℕ) → x ≼ y → x ≤ y

  ≼-gives-≤ 0 0               (z , p) = ⋆

  ≼-gives-≤ 0 (succ y)        (z , p) = ⋆

  ≼-gives-≤ (succ x) 0        (z , p) = positive-not-zero (x ∔ z) q
   where
    q = succ (x ∔ z) ≡⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ≡⟨ p                       ⟩
        zero         ∎

  ≼-gives-≤ (succ x) (succ y) (z , p) = IH
   where
    q = succ (x ∔ z) ≡⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ≡⟨ p                       ⟩
        succ y       ∎

    IH : x ≤ y
    IH = ≼-gives-≤ x y (z , succ-lc q)

  ≤-refl : (n : ℕ) → n ≤ n
  ≤-refl zero     = ⋆
  ≤-refl (succ n) = ≤-refl n

  ≤-trans : (l m n : ℕ) → l ≤ m → m ≤ n → l ≤ n
  ≤-trans zero m n p q = ⋆
  ≤-trans (succ l) zero n p q = !𝟘 (succ l ≤ n) p
  ≤-trans (succ l) (succ m) zero p q = q
  ≤-trans (succ l) (succ m) (succ n) p q = ≤-trans l m n p q

  ≤-anti : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
  ≤-anti zero zero p q = refl zero
  ≤-anti zero (succ n) p q = !𝟘 (zero ≡ succ n) q
  ≤-anti (succ m) zero p q = !𝟘 (succ m ≡ zero) p
  ≤-anti (succ m) (succ n) p q = ap succ (≤-anti m n p q)

  ≤-succ : (n : ℕ) → n ≤ succ n
  ≤-succ zero     = ⋆
  ≤-succ (succ n) = ≤-succ n

  zero-minimal : (n : ℕ) → zero ≤ n
  zero-minimal n = ⋆

  unique-minimal : (n : ℕ) → n ≤ zero → n ≡ zero
  unique-minimal zero p = refl zero
  unique-minimal (succ n) p = !𝟘 (succ n ≡ zero) p

  ≤-split : (m n : ℕ) → m ≤ succ n → (m ≤ n) + (m ≡ succ n)
  ≤-split zero n l = inl l
  ≤-split (succ m) zero l = inr (ap succ (unique-minimal m l))
  ≤-split (succ m) (succ n) l = +-recursion inl (inr ∘ ap succ) (≤-split m n l)

  _<_ : ℕ → ℕ → 𝓤₀ ̇
  x < y = succ x ≤ y

  infix 10 _<_

  not-<-gives-≥ : (m n : ℕ) → ¬(n < m) → m ≤ n
  not-<-gives-≥ zero n u = zero-minimal n
  not-<-gives-≥ (succ m) zero = dni (zero < succ m) (zero-minimal m)
  not-<-gives-≥ (succ m) (succ n) = not-<-gives-≥ m n

  bounded-∀-next : (A : ℕ → 𝓤 ̇ ) (k : ℕ)
                 → A k
                 → ((n : ℕ) → n < k → A n)
                 → (n : ℕ) → n < succ k → A n
  bounded-∀-next A k a φ n l = +-recursion f g s
   where
    s : (n < k) + (succ n ≡ succ k)
    s = ≤-split (succ n) k l

    f : n < k → A n
    f = φ n

    g : succ n ≡ succ k → A n
    g p = transport A ((succ-lc p)⁻¹) a

  root : (ℕ → ℕ) → 𝓤₀ ̇
  root f = Σ \(n : ℕ) → f n ≡ 0

  _has-no-root<_ : (ℕ → ℕ) → ℕ → 𝓤₀ ̇
  f has-no-root< k = (n : ℕ) → n < k → f n ≢ 0

  is-minimal-root : (ℕ → ℕ) → ℕ → 𝓤₀ ̇
  is-minimal-root f m = (f m ≡ 0) × (f has-no-root< m)

  at-most-one-minimal-root : (f : ℕ → ℕ) (m n : ℕ)
                           → is-minimal-root f m → is-minimal-root f n → m ≡ n

  at-most-one-minimal-root f m n (p , φ) (q , ψ) = c m n a b
   where
    a : ¬(m < n)
    a u = ψ m u p

    b : ¬(n < m)
    b v = φ n v q

    c : (m n : ℕ) → ¬(m < n) → ¬(n < m) → m ≡ n
    c m n u v = ≤-anti m n (not-<-gives-≥ m n v) (not-<-gives-≥ n m u)

  minimal-root : (ℕ → ℕ) → 𝓤₀ ̇
  minimal-root f = Σ \(m : ℕ) → is-minimal-root f m

  minimal-root-is-root : ∀ f → minimal-root f → root f
  minimal-root-is-root f (m , p , _) = m , p

  bounded-ℕ-search : ∀ k f → (minimal-root f) + (f has-no-root< k)
  bounded-ℕ-search zero f = inr (λ n → !𝟘 (f n ≢ 0))
  bounded-ℕ-search (succ k) f = +-recursion φ γ (bounded-ℕ-search k f)
   where
    A : ℕ → (ℕ → ℕ) → 𝓤₀ ̇
    A k f = (minimal-root f) + (f has-no-root< k)

    φ : minimal-root f → A (succ k) f
    φ = inl

    γ : f has-no-root< k → A (succ k) f
    γ u = +-recursion γ₀ γ₁ (ℕ-has-decidable-equality (f k) 0)
     where
      γ₀ : f k ≡ 0 → A (succ k) f
      γ₀ p = inl (k , p , u)

      γ₁ : f k ≢ 0 → A (succ k) f
      γ₁ v = inr (bounded-∀-next (λ n → f n ≢ 0) k v u)

  root-gives-minimal-root : ∀ f → root f → minimal-root f
  root-gives-minimal-root f (n , p) = γ
   where
    g : ¬(f has-no-root< (succ n))
    g φ = φ n (≤-refl n) p

    γ : minimal-root f
    γ = right-fails-gives-left-holds (bounded-ℕ-search (succ n) f) g




-- =====================================================================
-- Stuff from our old Preliminaries.agda file, moderately notationally tweaked.


--_∈∈_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} →  (A  →  B) →  𝓟 B → 𝓤 ⊔ 𝓥 ̇
_∈∈_ :  {A : 𝓤 ̇} {B : 𝓦 ̇} →  (A  →  B) →  Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
_∈∈_  f S = (x : _) → f x ∈ S

--Im_⊆_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } →  (A → B)  → 𝓟 B → 𝓤 ⊔ 𝓥 ̇
Im_⊆_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } →  (A → B)  → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
Im_⊆_ {A = A} f S = (x : A) → f x ∈ S

img :  {X : 𝓤 ̇ } {Y : 𝓤 ̇} (f : X → Y) (P : Pred Y 𝓤) → Im f ⊆ P →  X → ∃ P
img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ ؛ Imf⊆P x₁

≡-elim-left :  {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇ } → (A₁ , B₁) ≡ (A₂ , B₂)   →   A₁ ≡ A₂
≡-elim-left e = ap pr₁ e

≡-elim-right : { A₁ A₂ : 𝓤 ̇ } { B₁ B₂ : 𝓦 ̇ } → (A₁ , B₁) ≡ (A₂ , B₂) → B₁ ≡ B₂
≡-elim-right e = ap pr₂ e

-------------------------------------------------------------------------------------------------------------
-- Images and surjections.
-- image : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
-- image f = Σ y ꞉ (codomain f) , ∃! x ꞉ (domain f) , f x ≡ y

-- restriction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → image f → Y
-- restriction f (y , _) = y

--NOTATION (cf. Relation/Binary/PropositionalEquality/Core.agda)
cong : {X : 𝓤 ̇} {Y : 𝓦 ̇} (f : X → Y){x y : X} → x ≡ y → f x ≡ f y
cong  = ap

-- cf. Relation/Binary/Core.agda
cong-app : ∀ {A : 𝓤 ̇} {B : A → 𝓦 ̇} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
cong-app {f = f} (refl _) a = refl (f a)

cong-app-pred : ∀ { A : 𝓤 ̇ } { B₁ B₂ : Pred A 𝓤} (x : A)
 →          x ∈ B₁   →   B₁ ≡ B₂
            -------------------------
 →                    x ∈ B₂
cong-app-pred x x∈B₁ (refl _) = x∈B₁

cong-pred : {A : 𝓤 ̇ } {B : Pred A 𝓤} (x y : A)
 →            x ∈ B   →   x ≡ y
               -------------------------
 →                   y ∈ B
cong-pred x .x x∈B (refl .x) = x∈B


data Image_∋_ {A : 𝓤 ̇} {B : 𝓦 ̇ } (f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
  where
  im : (x : A) → Image f ∋ f x
  eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

-- image_ : {A : 𝓤 ̇} {B : 𝓦 ̇} → (A → B) → Pred B (𝓤 ⊔ 𝓦)
-- image f = λ b → ∃ λ a → b ≡ f a

ImageIsImage :  {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) (b : B) (a : A)
 →                  b ≡ f a    →     Image f ∋ b
ImageIsImage {A = A} {B = B} f b a b≡fa = eq b a b≡fa

--N.B. the assertion Image f ∋ y must come with a proof, which is of the form ∃a f a = y, so we have a witness.
--Thus, the inverse can be "computed" in the following way:
Inv : {A : 𝓤 ̇}  {B : 𝓦 ̇} (f : A → B) (b : B) → Image f ∋ b  →  A
Inv f .(f a) (im a) = a  -- Cool!!!
Inv f b (eq b a b≡fa) = a

-- special case for Set
inv : {A B : 𝓤₀ ̇}(f : A → B)(b : B) → Image f ∋ b → A
inv {A} {B} = Inv {𝓤₀}{𝓤₀}{A}{B}

InvIsInv : {A : 𝓤 ̇} {B : 𝓦 ̇} (f : A → B) (b : B) (b∈Imgf : Image f ∋ b)
             --------------------------------------
 →          f (Inv f b b∈Imgf) ≡ b
InvIsInv f .(f a) (im a) = refl _
InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹















