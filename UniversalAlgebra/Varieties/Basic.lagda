---
layout: default
title : Varieties.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the ualib/agda-algebras development team][]
---

### Varieties, Model Theory, and Equational Logic

This section presents the [Varieties.Basic][] module of the [Agda Universal Algebra Library][] where the binary "models" relation ⊧, relating algebras (or classes of algebras) to the identities that they satisfy, is defined.

Agda supports the definition of infix operations and relations, and we use this to define ⊧ so that we may write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊫ p ≈ q`.



**Notation**. In the [Agda UniversalAlgebra][] library, because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊫ p ≈ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊧ 𝑝 ≋ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

**Unicode Hints**. To produce the symbols ≈, ⊧, and ≋ in [agda2-mode][], type `\~~`, `\models`, and `\~~~`, respectively.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


-- Imports from Agda (builtin/primitive) and the Agda Standard Library

open import Level using ( Level )
open import Algebras.Basic

module Varieties.Basic {𝑆 : Signature 𝓞 𝓥} where


-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Builtin.Equality   using    ( _≡_ ;  refl )
open import Agda.Primitive          using    ( _⊔_ ;  lsuc )
                                   renaming ( Set to Type
                                            ; lzero to  ℓ₀       )
open import Axiom.Extensionality.Propositional
                                    renaming ( Extensionality to funext )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Function.Base           using    ( _∘_ )
open import Relation.Binary.PropositionalEquality
                                    using    ( cong ; cong-app
                                             ; module ≡-Reasoning)
open import Relation.Unary          using    ( Pred ; _∈_ ; _⊆_ ; ⋂ )



-- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ ; ∥_∥ ; 𝑖𝑑 ; _⁻¹ ; _≈_ ; Π ; Π-syntax)
open import Overture.Inverses            using ( IsInjective ; ∘-injective )
open import Relations.Extensionality using (DFunExt; SwellDef; swelldef)

open import Algebras.Products          {𝑆 = 𝑆} using ( ov ; ⨅ )
open import Homomorphisms.Basic        {𝑆 = 𝑆} using ( hom; 𝒾𝒹 ; ∘-hom ; is-homomorphism )
open import Homomorphisms.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅-sym ; ≅-trans ; Lift-≅ )
open import Terms.Basic                {𝑆 = 𝑆} using ( Term ; 𝑻 ; lift-hom )
open import Terms.Operations           {𝑆 = 𝑆} using ( _⟦_⟧ ; comm-hom-term
                                               ; interp-prod ; term-agreement )
open import Subalgebras.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; SubalgebraOfClass ; iso→injective )
open Term

\end{code}


#### <a id="the-models-relation">The models relation</a>

We define the binary "models" relation ⊧ using infix syntax so that we may write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊫ p ≈ q`, relating algebras (or classes of algebras) to the identities that they satisfy. We also prove a coupld of useful facts about ⊧.  More will be proved about ⊧ in the next module, [Varieties.EquationalLogic](Varieties.EquationalLogic.html).

\begin{code}


-- curried versions
-- (unicode: use \models and \~~ to get ⊧ and ≈)
_⊧_≈_ : {χ : Level}{X : Type χ} → {α : Level} → Algebra α 𝑆 → Term X → Term X → Type _
𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

-- (unicode: use \||= and \~~ to get ⊫ and ≈)
_⊫_≈_ : {χ : Level}{X : Type χ} → {α ρ : Level} → Pred(Algebra α 𝑆) ρ → Term X → Term X → Type _
𝒦 ⊫ p ≈ q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q


\end{code}

##### <a id="semantics-of-⊧">Syntax and semantics of ⊧</a>
The expression `𝑨 ⊧ p ≈ q` represents the assertion that the identity `p ≈ q` holds when interpreted in the algebra `𝑨`; syntactically, `𝑨 ⟦ p ⟧ ≡ 𝑨 ⟦ q ⟧`.  It should be emphasized that the expression  `𝑨 ⟦ p ⟧ ≡ 𝑨 ⟦ q ⟧` interpreted computationally as an *extensional equality*, by which we mean that for each *assignment function*  `𝒂 :  X → ∣ 𝑨 ∣`, assigning values in the domain of `𝑨` to the variable symbols in `X`, we have `⟦ p ⟧ 𝑨 𝒂 ≡ ⟦ q ⟧  𝑨 𝒂`.



#### <a id="equational-theories-and-classes">Equational theories and models</a>

Here we define a type `Th` so that, if 𝒦 denotes a class of algebras, then `Th 𝒦` represents the set of identities modeled by all members of 𝒦.

\begin{code}

module _ {χ : Level}{X : Type χ} where

 Th : {α : Level} → Pred (Algebra α 𝑆) (ov α) → Pred(Term X × Term X) (χ ⊔ ov α)
 Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

\end{code}

If `ℰ` denotes a set of identities, then the class of algebras satisfying all identities in ℰ is represented by `Mod ℰ`, which we define in the following natural way.

\begin{code}

 Mod : {α : Level} → Pred(Term X × Term X) (ov α) → Pred(Algebra α 𝑆) (ov (χ ⊔ α))
 Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

 -- tupled version
 Modᵗ : {ι : Level}{I : Type ι} → (I → Term X × Term X) → {α : Level} → Pred(Algebra α 𝑆)(χ ⊔ ι ⊔ α)
 Modᵗ ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ (fst (ℰ i)) ≈ (snd (ℰ i))

\end{code}







-------------------------------------

[↑ Varieties](Varieties.html)
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}


--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team














<!--

  -- open import Relation.Binary.Core using (_⇔_)

  -- ⊧-H : DFunExt → {p q : Term X} → 𝒦 ⊫ p ≈ q ⇔ (∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∣ φ ∣ ∘ (𝑻 X ⟦ p ⟧) ≡ ∣ φ ∣ ∘(𝑻 X ⟦ q ⟧))
  -- ⊧-H fe {p}{q} = ⊧-H-class-invar fe {p}{q} , ⊧-H-class-coinvar fe {p}{q}


-->
Soundness of the inference rules. We assume a model 𝑨 that validates all equations in ℰ.


\begin{code}

-- module Soundness {ι : Level}{I : Type ι}
--                  {χ : Level}(ℰ : {X : Type χ} → I → Term X × Term X)
--                  {α : Level}(𝑨 : Algebra α 𝑆)
--                  (Amod : 𝑨 ∈ Modtup ℰ) where

--  -- In any 𝑨 ∈ Mod ℰ, derived equality is actual equality.

--  sound : {X : Type χ}{p q : Term X} → ℰ ⊢ X ▹ p ≈ q → 𝑨 ⊧ p ≈ q
--  sound x = {!!}

\end{code}
 -- (hyp i)                        =  V i
 --    sound (app {op = op} es) ρ           =  den .cong (refl , λ i → sound (es i) ρ)
 --    sound (sub {t = t} {t' = t'} e σ) ρ  =  begin
 --      ⦅ t [ σ ]   ⦆ .apply ρ   ≈⟨ substitution {M = M} t σ ρ ⟩
 --      ⦅ t         ⦆ .apply ρ'  ≈⟨ sound e ρ' ⟩
 --      ⦅ t'        ⦆ .apply ρ'  ≈˘⟨ substitution {M = M} t' σ ρ ⟩
 --      ⦅ t' [ σ ]  ⦆ .apply ρ   ∎
 --      where
 --      open SetoidReasoning Den
 --      ρ' = ⦅ σ ⦆s ρ

 --    sound (base x {f} {f'})              =  isEquiv {M = M} .IsEquivalence.refl {var' x λ()}

 --    sound (refl t)                       =  isEquiv {M = M} .IsEquivalence.refl {t}
 --    sound (sym {t = t} {t' = t'} e)      =  isEquiv {M = M} .IsEquivalence.sym
 --                                            {x = t} {y = t'} (sound e)
 --    sound (trans  {t₁ = t₁} {t₂ = t₂}
 --                  {t₃ = t₃} e e')        =  isEquiv {M = M} .IsEquivalence.trans
 --                                            {i = t₁} {j = t₂} {k = t₃} (sound e) (sound e')



