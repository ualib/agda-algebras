{-
layout: default
title : Overture.Preliminaries module
date : 2021-01-13
author: the agda-algebras development team
-}

-- Preliminaries
-- =============
--
-- This is the [Overture.Preliminaries][] module of the [agda-algebras][].
--
-- Logical foundations
-- -------------------
-- The [Agda Universal Algebra Library](https://github.com/ualib/agda-algebras) (or
-- [agda-algebras](https://github.com/ualib/agda-algebras) for short) is based on a version of
-- [Martin-Löf type theory (MLTT)](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory). We don't
-- discuss [MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) in great detail here because
-- there are already good and freely available resources covering the theory. (See, for example, the section of
-- [Escardó's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes) on
-- [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda),
-- or the
-- [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory),
-- or the [HoTT book](https://homotopytypetheory.org/book/).)

-- The objects and assumptions that form the foundation of
-- [MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) are few. There are the *primitive types*
-- (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`,
-- `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type). Each of these type formers is defined
-- by a *type forming rule* which specifies how that type is constructed. Lastly, we have an infinite collection of
-- *type universes* (types of types) and *universe variables* to denote them. Following Escardó, [agda-algebras][]
-- denotes universe levels by upper-case calligraphic letters from the second half of the English alphabet; to be
-- precise, these are `𝓞`, `𝓠`, `𝓡`, …, `𝓧`, `𝓨`, `𝓩`.<sup>[1](Overture.Preliminaries.html#fn1)</sup>

-- That's all. There are no further axioms or logical deduction (proof derivation) rules needed for the foundations of
-- [MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) that we take as the starting point of
-- [agda-algebras][].  The logical semantics come from the
-- [propositions-as-types correspondence](https://ncatlab.org/nlab/show/propositions+as+types): propositions and
-- predicates are represented by types and the inhabitants of these types are the proofs of the propositions and
-- predicates.  As such, proofs are constructed using the type forming rules. In other words, the type forming rules
-- *are* the proof derivation rules.

-- To this foundation, we add certain *extensionality principles* when and were we need them.  These will be developed
-- as we progress.  However, classical axioms such as the
-- [*Axiom of Choice*](https://ncatlab.org/nlab/show/axiom+of+choice) or the
-- [*Law of the Excluded Middle*](https://ncatlab.org/nlab/show/excluded+middle) are not needed and are not assumed
-- anywhere in the library. In this sense, all theorems and proofs in [agda-algebras][] are
-- [*constructive*](https://ncatlab.org/nlab/show/constructive+mathematics) (according to
-- [nlab's definition](https://ncatlab.org/nlab/show/constructive+mathematics)).

-- A few specific instances (e.g., the proof of the Noether isomorphism theorems and Birkhoff's HSP theorem) require
-- certain *truncation* assumptions. In such cases, the theory is not
-- [predicative](https://ncatlab.org/nlab/show/predicative+mathematics) (according to
-- [nlab's definition](https://ncatlab.org/nlab/show/predicative+mathematics)). These instances are always clearly
-- identified.


-- Specifying logical foundations in Agda
-- --------------------------------------
-- An Agda program typically begins by setting some options and by importing types from existing Agda libraries. Options
-- are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical
-- axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda
-- program in [agda-algebras][] begins with the following line.

{-# OPTIONS --without-K --exact-split --safe #-}

-- These options control certain foundational assumptions that Agda makes when type-checking the program to verify its
-- correctness.

-- * `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also
--   the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the
--   [Agda Language Reference][] manual.
--
-- * `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.
--   [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;"
--   see also the [Pattern matching and equality
--   section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of
--   the [Agda Tools][] documentation. 
--
-- * `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g.,
--   an argument to a function or module); see also
--   [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the
--   [Agda Tools][] documentation and the
--   [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the
--   [Agda Language Reference][]. 

-- Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we
-- must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions
-- of) the [agda-algebras][] library. 


-- Agda Modules
-- ------------
-- The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][]
-- module begins with the following line, and then a line that imports lots of stuff from the Agda Standard Library.

module Overture.Preliminaries where

open import stdlib-imports


-- Agda Universes
-- --------------
-- Here we import the basic primitive operations we need for working with Agda's type universes. For the very small
-- amount of background about *type universes* we require, we refer the reader to the brief [section on
-- universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the Agda documentation.
--
-- We prefer to use `Type` in place of Agda's `Set` since for us *set* will mean a very special kind of (truncated)
-- type. (See [Relations.Truncation][]). 

-- Type : (𝓤 : Level) → Set (lsuc 𝓤)
-- Type 𝓤 = Set 𝓤

-- We often adopt Escardó's convention of denoting universe levels by capital calligraphic letters.

private
  variable
    𝓘 𝓞 𝓠 𝓡 𝓢 𝓣 𝓤 𝓥 𝓦 𝓧 𝓨 𝓩 : Level


-- Projection notation
-- -------------------
-- The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂` representing the first and second
-- projections out of the product.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥` respectively.
-- However, for emphasis or readability we alternate between these and the following standard notations: `proj₁` and
-- `fst` for the first projection, `proj₂` and `snd` for the second.  We define these alternative notations for
-- projections out of pairs as follows. 

module _ {A : Type 𝓤 }{B : A → Type 𝓥} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd

 infix  40 ∣_∣

-- Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an
-- underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the
-- "parameters" of the module (e.g., `A : Type 𝓤`)---out of the way so they don't obfuscate the definitions inside the
-- module. 
--
-- Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.
--
-- We prove that `≡` obeys the substitution rule (subst) in the next subsection (see the definition of `ap` below), but
-- first we define some syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in
-- proofs.<sup>[2](Overture.Equality.html#fn3)</sup> 

_⁻¹ : {A : Type 𝓤} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p

infix  40 _⁻¹

-- If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `sym p` we can use the more intuitive
-- `p ⁻¹`. Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

_∙_ : {A : Type 𝓤}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

𝑖𝑑 : (A : Type 𝓤 ) → A → A
𝑖𝑑 A = λ x → x

infixl 30 _∙_


-- Agda's universe hierarchy
-- -------------------------
-- The hierarchy of universes in Agda is structured as follows:<sup>[1](Overture.Lifts.html#fn1)</sup>
--
-- Type 𝓤 : Type (lsuc 𝓤),   Type(lsuc 𝓤) : Type (lsuc (lsuc 𝓤)),  etc.
--
-- This means that the universe `Type 𝓤` has type `Type(lsuc 𝓤)`, and  `Type(lsuc 𝓤)` has type `Type(lsuc (lsuc 𝓤))`,
-- and so on.  It is important to note, however, this does *not* imply that  `Type 𝓤 : Type(lsuc(lsuc 𝓤))`. In other
-- words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to treat universe levels more precisely,
-- which is nice. On the other hand, a non-cumulative hierarchy can sometimes make for a non-fun proof assistant.
-- Specifically, in certain situations, the non-cumulativity makes it unduly difficult to convince Agda that a program
-- or proof is correct.

-- We now describe a general `Lift` type that help us overcome the technical issue described above. Later we will define
-- a couple domain-specific lifting types which have certain properties that make them useful for resolving universe
-- level problems when working with algebra types.
--
-- Let us be more concrete about what is at issue here by considering a typical example. Agda will often complain with
-- errors like the following:
--
-- Birkhoff.lagda:498,20-23
-- 𝓤 != 𝓞 ⊔ 𝓥 ⊔ (lsuc 𝓤) when checking that the expression... has type...
--
-- This error message means that Agda encountered the universe level `lsuc 𝓤`, on line 498 (columns 20--23) of the file
-- `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⊔ 𝓥 ⊔ lsuc 𝓤` instead.
--
-- The general `Lift` record type that we now describe makes these situations easier to deal with. It takes a type
-- inhabiting some universe and embeds it into a higher universe and, apart from syntax and notation, it is equivalent
-- to the `Lift` type one finds in the `Level` module of the [Agda Standard Library][].
--
-- record Lift {𝓦 𝓤 : Level} (A : Type 𝓤) : Type (𝓤 ⊔ 𝓦) where
--  constructor lift
--   field lower : A
--
-- The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if
-- we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application
-- of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation.
-- Similarly, `lift` followed by `lower` is the identity.

lift∼lower : ∀ {𝓤 𝓦}{A : Type 𝓤} → lift ∘ lower ≡ 𝑖𝑑 (Lift 𝓦 A)
lift∼lower = refl

lower∼lift : {𝓤 𝓦 : Level}{A : Type 𝓤} → lower {𝓤}{𝓦}(lift {𝓤}{𝓦}(λ x → x)) ≡ 𝑖𝑑 A
lower∼lift = refl

-- The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


-- Pointwise equality of dependent functions
-- -----------------------------------------
-- We conclude this module with a definition that conveniently represents te assertion that two functions are
-- (extensionally) the same in the sense that they produce the same output when given the same input.  (We will have
-- more to say about this notion of equality in the [Relations.Extensionality][] module.) 

_∼_ : {X : Type 𝓤 } {A : X → Type 𝓥 } → (f g : (x : X) → A x) → Type (𝓤 ⊔ 𝓥)
f ∼ g = ∀ x → f x ≡ g x

infix 8 _∼_





{- OLD/UNUSED STUFF

<sup>1</sup><span class="footnote" id="fn0"> We avoid using `𝓟` as a universe
variable because in some libraries `𝓟` denotes a powerset type.</span>

<sup>2</sup> <span class="footnote" id="fn2"> Most of these types are already defined by in the [Type Topology][] library or the [Agda Standard Library][], so we often imports the definitions; occasionally, however, we repeat the definitions here for pedagogical reasons and to keep the presentation somewhat self-contained.


<sup>4</sup> <span class="footnote" id="fn4"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).)</span>

<sup>5</sup><span class="footnote" id="fn5">Recall, from the [Overture.Preliminaries][] module, the special notation we use to denote Agda's *levels* and *universes*.</span>


OLD LIST OF IMPORTS (replaced with import of stdlib-imports.agda
-- open import Agda.Builtin.Equality using (_≡_; refl)
-- open import Data.Product using (_,_; Σ; Σ-syntax; _×_; proj₁; proj₂)
-- open import Function.Base using (_∘_; id)
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Relation.Binary.PropositionalEquality.Core using (sym; trans)



-}
