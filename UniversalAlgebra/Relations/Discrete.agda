{-
layout: default
title : Relations.Discrete module (The Agda Universal Algebra Library)
date : 2021-02-28
author: [agda-algebras development team][]
-}

-- Discrete Relations
-- ==================
--
-- This is the [Relations.Discrete][] module of the [Agda Universal Algebra Library][].

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Discrete where

open import stdlib-imports

private variable 𝓤 𝓥 𝓦 𝓧 𝓨 𝓩 : Level

-- We define convenient notation for asserting that the image of a function (the first argument) is contained
-- in a predicate (the second argument).

Im_⊆_ : {A : Type 𝓤}{B : Type 𝓦} → (A → B) → Pred B 𝓩 → Type (𝓤 ⊔ 𝓩)
Im f ⊆ S = ∀ x → f x ∈ S


-- Kernels
-- -------

-- The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be
-- represented in type theory and Agda in a number of ways, each of which may be useful in a particular
-- context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, or a
-- (unary) predicate type.


module _ {A : Type 𝓤}{B : Type 𝓦} where

 ker : (A → B) → Rel A 𝓦
 ker g x y = g x ≡ g y

 kernel : (A → B) → Pred (A × A) 𝓦
 kernel g (x , y) = g x ≡ g y


-- Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be
-- represented as follows.


module _ {A : Type 𝓤 } where

 𝟎 : Rel A 𝓤
 𝟎 x y = x ≡ y


-- Operation type and compatibility
-- --------------------------------
-- **Notation**. For consistency and readability, throughout the [UniversalAlgebra][] library we reserve two
-- universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that
-- represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types
-- representing *arities* of relations or operations. 
--
-- In the next subsection, we will define types that are useful for asserting and proving facts about
-- *compatibility* of *operations* with relations, but first we need a general type with which to represent
-- operations.  Here is the definition, which we justify below. 

Op : Type 𝓥 → Type 𝓤 → Type(𝓤 ⊔ 𝓥)  --The type of operations
Op I A = (I → A) → A

-- The type `Op` encodes the arity of an operation as an arbitrary type `I : Type 𝓥`, which gives us a very
-- general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and
-- codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the
-- type `Op I A` as follows.

π : {I : Type 𝓥 } {A : Type 𝓤 } → I → Op I A
π i x = x i

-- Now suppose `A` and `I` are types and let `𝑓 : Op I` and `R : Rel A 𝓦` be an `I`-ary operation and a binary
-- relation on `A`, respectively. We say `𝑓` and `R` are *compatible* and we write `𝑓 |: R` just in case `∀ u
-- v : I → A`,
--
-- `Π i ꞉ I , R (u i) (v i) → R (f u) (f v).
--
-- Here is how we implement this in the [UniversalAlgebra][] library.

eval-rel : {A : Type 𝓤}{I : Type 𝓥} → Rel A 𝓦 → Rel (I → A)(𝓥 ⊔ 𝓦)
eval-rel R u v = ∀ i → R (u i) (v i)

_|:_ : {A : Type 𝓤}{I : Type 𝓥} → Op I A → Rel A 𝓦 → Type(𝓤 ⊔ 𝓥 ⊔ 𝓦)
f |: R  = (eval-rel R) =[ f ]⇒ R

-- The function `eval-rel` "lifts" a binary relation to the corresponding `I`-ary relation.
--
-- In case it helps the reader, we note that instead of using the slick implication notation, we could have
--defined the `|:` relation more explicitly, like so.

compatible-op : {A : Type 𝓤}{I : Type 𝓥} → (f : Op I A)(R : Rel A 𝓦) → Type(𝓤 ⊔ 𝓥 ⊔ 𝓦)
compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

-- However, this is a rare case in which the more elegant syntax used to define `|:` sometimes results in
-- simpler proofs when applying the definition. (See, for example, `compatible-term` in the
-- [Terms.Operations][] module.)


--------------------------------------

-- [agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
