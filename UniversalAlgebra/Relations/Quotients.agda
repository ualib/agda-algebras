{-
layout: default
title : Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: [agda-algebras development team][]
-}

-- Equivalence Relations and Quotients
-- ===================================
--
-- This section presents the [Relations.Quotients][] module of the [Agda Universal Algebra Library][].

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Quotients where

open import stdlib-imports
open import Relations.Discrete using (ker)

private variable 𝓤 𝓥 𝓦 : Level


-- Equivalence relations
-- ---------------------
-- A binary relation is called a *preorder* if it is reflexive and transitive. An *equivalence relation* is a
-- symmetric preorder. The property of being an equivalence relation is represented in the [Agda Standard
-- Library][] by a record type called `IsEquivalence`.

-- Thus, if we have `(R ,  p) : Equivalence A`, then `R` denotes a binary relation over `A` and `p` is of
-- record type `IsEquivalence R` with fields containing the three proofs showing that `R` is an equivalence
-- relation.

-- A prominent example of an equivalence relation is the kernel of any function.

ker-IsEquivalence : {A : Type 𝓤}{B : Type 𝓦}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record { refl = refl ; sym = λ x → sym x ; trans = λ x y → trans x y }


-- Equivalence classes (blocks)
-- ----------------------------
-- If `R` is an equivalence relation on `A`, then for each `u : A` there is an *equivalence class* (or
-- *equivalence block*, or `R`-*block*) containing `u`, which we denote and define by
-- `[ u ] := {v : A | R u v}`.

[_] : {A : Type 𝓤} → A → {R : Rel A 𝓦} → Pred A 𝓦
[ u ]{R} = R u

infix 60 [_]

-- Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]` as the `R`-*block
-- containing* `u`.
--
-- A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.  We represent this
-- characterization of an `R`-block as follows.

record IsBlock {A : Type 𝓤}(C : Pred A 𝓦){R : Rel A 𝓦} : Type(𝓤 ⊔ lsuc 𝓦) where
  constructor R-block
  field
    block-u : A
    C≡[u] : C ≡ [ block-u ]{R}


-- Quotients
-- ---------
-- If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is denoted by `A / R` and
-- is defined to be the collection `{[ u ] ∣  y : A}` of all `R`-blocks.

module _ {𝓤 𝓦 : Level} where

 _/_ : (A : Type 𝓤 ) → Rel A 𝓦 → Type(𝓤 ⊔ lsuc 𝓦)
 A / R = Σ[ C ∈ Pred A 𝓦 ] IsBlock C {R}

 infix -1 _/_

-- We use the following type to represent an R-block with a designated representative.

⟪_⟫ : {A : Type 𝓤} → A → {R : Rel A 𝓦} → A / R
⟪ a ⟫{R} = [ a ]{R} , R-block a refl

-- Dually, the next type provides an *elimination rule*.<sup>[2](Relations.Quotients.html#fn2)</sup>

⌞_⌟ : {A : Type 𝓤}{R : Rel A 𝓦} → A / R  → A
⌞ _ , R-block a _ ⌟ = a

-- Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.
--
-- It will be convenient to have the following subset inclusion lemmas on hand when working with quotient
-- types.

private variable A : Type 𝓤 ; x y : A ; R : Rel A 𝓦
open IsEquivalence

/-subset : IsEquivalence R → R x y →  [ x ]{R} ⊆  [ y ]{R}
/-subset Req Rxy {z} Rxz = IsEquivalence.trans Req (IsEquivalence.sym Req Rxy) Rxz

/-supset : IsEquivalence R → R x y →  [ y ]{R} ⊆ [ x ]{R}
/-supset Req Rxy {z} Ryz = IsEquivalence.trans Req Rxy Ryz

-- An example application of these is the `block-ext` type in the [Relations.Extensionality] module.

----------------------------

-- [agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
