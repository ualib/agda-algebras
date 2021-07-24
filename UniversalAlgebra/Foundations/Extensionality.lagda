---
layout: default
title : Foundations.Extensionality module (The Agda Universal Algebra Library)
date : 2021-02-23
author: [the ualib/agda-algebras development team][]
---

### Extensionality

This is the [Foundations.Extensionality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Foundations.Extensionality where

-- imports from Agda and the Agda Standard Library ------------------------------------
open import Agda.Builtin.Equality  using (_≡_ ; refl )
open import Agda.Primitive         using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type ; Setω to Typeω )
open import Data.Product           using ( _,_ ;  _×_ )
open import Function.Base          using ( _∘_ ; id )
open import Relation.Binary        using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Unary         using ( Pred ; _⊆_ )
open import Axiom.Extensionality.Propositional using () renaming ( Extensionality to funext )
import Relation.Binary.PropositionalEquality as PE


-- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries using ( _≈_; _⁻¹ ; _∙_ ; transport )
open import Overture.Inverses      using ( IsSurjective ; SurjInv ; InvIsInv ; Image_∋_ ; eq )
open import Relations.Discrete     using ( Op )
open import Relations.Quotients    using ( [_] ; []-⊆ ; []-⊇ ; IsBlock ; ⟪_⟫ )
open import Foundations.Truncation   using ( blk-uip ; to-Σ-≡ )


private variable α β γ ρ 𝓥 : Level

\end{code}

#### Function Extensionality


Previous versions of [UniversalAlgebra][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.
However, we decided to remove all instances of global function extensionality from the latest version of the library and limit ourselves to local applications of the principle. This has the advantage of making transparent precisely how and where the library depends on function extensionality. The price we pay for this precision is a library that is littered with extensionality postulates. Eventually we will probably remove these postulates in favor of an alternative approach to extensionality, or even remove the need for it altogether.

The following definition is useful for postulating function extensionality when and where needed.

\begin{code}

DFunExt : Typeω
DFunExt = (𝓤 𝓥 : Level) → funext 𝓤 𝓥


module _ {A : Type α}{B : Type β} where

 SurjInvIsRightInv : (f : A → B)(fE : IsSurjective f) → ∀ b → f ((SurjInv f fE) b) ≡ b
 SurjInvIsRightInv f fE b = InvIsInv f (fE b)

 open PE.≡-Reasoning

 -- composition law for epics
 epic-factor : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
  →            f ≈ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor f g h compId fe y = Goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : y ≡ f (finv y)
   ζ = (SurjInvIsRightInv f fe y)⁻¹

   η : y ≡ (h ∘ g) (finv y)
   η = ζ ∙ compId (finv y)

   Goal : Image h ∋ y
   Goal = eq (g (finv y)) η

 epic-factor-intensional : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
  →                        f ≡ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor-intensional f g h compId fe y = Goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : f (finv y) ≡ y
   ζ = SurjInvIsRightInv f fe y

   η : (h ∘ g) (finv y) ≡ y
   η = (PE.cong-app (compId ⁻¹)(finv y)) ∙ ζ

   Goal : Image h ∋ y
   Goal = eq (g (finv y)) (η ⁻¹)

\end{code}


#### An alternative way to express function extensionality

A useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `happly` function is actually an *equivalence*.


The principle of *proposition extensionality* asserts that logically equivalent propositions are equivalent.  That is, if `P` and `Q` are propositions and if `P ⊆ Q` and `Q ⊆ P`, then `P ≡ Q`. For our purposes, it will suffice to formalize this notion for general predicates, rather than for propositions (i.e., truncated predicates).

\begin{code}

_≐_ : {α β : Level}{A : Type α}(P Q : Pred A β ) → Type _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

pred-ext : (α β : Level) → Type (lsuc (α ⊔ β))
pred-ext α β = ∀ {A : Type α}{P Q : Pred A β } → P ⊆ Q → Q ⊆ P → P ≡ Q

\end{code}

Note that `pred-ext` merely defines an extensionality principle. It does not postulate that the principle holds.  If we wish to postulate `pred-ext`, then we do so by assuming that type is inhabited (see `block-ext` below, for example).


#### Quotient extensionality

We need an identity type for congruence classes (blocks) over sets so that two different presentations of the same block (e.g., using different representatives) may be identified.  This requires two postulates: (1) *predicate extensionality*, manifested by the `pred-ext` type; (2) *equivalence class truncation* or "uniqueness of block identity proofs", manifested by the `blk-uip` type defined in the [Relations.Truncation][] module. We now use `pred-ext` and `blk-uip` to define a type called `block-ext|uip` which we require for the proof of the First Homomorphism Theorem presented in [Homomorphisms.Noether][].

\begin{code}

module _ {A : Type α}{R : BinRel A ρ} where

 block-ext : pred-ext α ρ → IsEquivalence{a = α}{ℓ = ρ} R
  →          {u v : A} → R u v → [ u ] R ≡ [ v ] R

 block-ext pe Req {u}{v} Ruv = pe ([]-⊆ {R = (R , Req)} u v Ruv)
                                  ([]-⊇ {R = (R , Req)} u v Ruv)


 private
   to-subtype|uip : blk-uip A R
    →               {C D : Pred A ρ}{c : IsBlock C {R}}{d : IsBlock D {R}}
    →               C ≡ D → (C , c) ≡ (D , d)

   to-subtype|uip buip {C}{D}{c}{d} CD =
    to-Σ-≡ (CD , buip D (transport (λ B → IsBlock B) CD c) d)

 block-ext|uip : pred-ext α ρ → blk-uip A R
  →              IsEquivalence R → ∀{u}{v} → R u v → ⟪ u ⟫ ≡ ⟪ v ⟫

 block-ext|uip pe buip Req Ruv = to-subtype|uip buip (block-ext pe Req Ruv)

\end{code}





---------------------------------------

{% include UALib.Links.md %}


[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team

