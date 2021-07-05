---
layout: default
title : Relations.Extensionality module (The Agda Universal Algebra Library)
date : 2021-02-23
author: [the ualib/agda-algebras development team][]
---

### <a id="relation-extensionality">Relation Extensionality</a>

This section presents the [Relations.Extensionality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Extensionality where

open import Axiom.Extensionality.Propositional    using    ()
                                                  renaming (Extensionality to funext)

open import Agda.Builtin.Equality                 using    (_≡_    ;  refl    )
open import Agda.Primitive                        using    ( _⊔_              )
                                                  renaming ( Set   to Type    )
open import Data.Product                          using    ( _,_   ; Σ-syntax
                                                           ; _×_   ; Σ        )
                                                  renaming ( proj₁ to fst
                                                           ; proj₂ to snd     )
open import Function.Base                         using    ( _∘_   ;  id      )
open import Level                                 renaming ( suc   to lsuc    )
open import Relation.Binary                       using    ( IsEquivalence    )
                                                  renaming ( Rel   to BinRel  )
open import Relation.Binary.PropositionalEquality using    ( sym   ;  cong-app
                                                           ; trans            )
open import Relation.Unary                        using    ( Pred  ; _⊆_      )
import Relation.Binary.PropositionalEquality as PE



open import Overture.Preliminaries using ( 𝑖𝑑 ; _⁻¹ ; _∙_ ; transport ; _≈_)
open import Overture.Inverses      using ( IsSurjective ; SurjInv
                                         ; InvIsInv ; Image_∋_ ; eq  )
open import Relations.Discrete     using ( Op                        )
open import Relations.Quotients    using ( [_] ; []-⊆ ; []-⊇ -- /-subset ; /-supset
                                         ; IsBlock ; ⟪_⟫  )
open import Relations.Truncation   using ( blk-uip ; to-Σ-≡          )


private variable α β γ ρ 𝓥 : Level
\end{code}

#### <a id="extensionality">Function Extensionality</a>


Previous versions of [UniversalAlgebra][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.
However, we decided to remove all instances of global function extensionality from the latest version of the library and limit ourselves to local applications of the principle. This has the advantage of making transparent precisely how and where the library depends on function extensionality. The price we pay for this precision is a library that is littered with extensionality postulates. Eventually we will probably remove these postulates in favor of an alternative approach to extensionality, or even remove the need for it altogether.

The following definition is useful for postulating function extensionality when and where needed.

\begin{code}

DFunExt : Setω
DFunExt = (𝓤 𝓥 : Level) → funext 𝓤 𝓥


module _ {A : Type α}{B : Type β} where

 SurjInvIsRightInv : (f : A → B)(fE : IsSurjective f) → ∀ b → f ((SurjInv f fE) b) ≡ b
 SurjInvIsRightInv f fE b = InvIsInv f (fE b)

\end{code}

We can also prove the following composition law for epics.

\begin{code}

 open PE.≡-Reasoning
 epic-factor : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
  →            f ≈ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor f g h compId fe y = Goal -- Goal
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
   η = (cong-app (compId ⁻¹)(finv y)) ∙ ζ

   Goal : Image h ∋ y
   Goal = eq (g (finv y)) (η ⁻¹)

\end{code}


#### <a id="alternative-extensionality-type">An alternative way to express function extensionality</a>

A useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `happly` function is actually an *equivalence*.


The principle of *proposition extensionality* asserts that logically equivalent propositions are equivalent.  That is, if `P` and `Q` are propositions and if `P ⊆ Q` and `Q ⊆ P`, then `P ≡ Q`. For our purposes, it will suffice to formalize this notion for general predicates, rather than for propositions (i.e., truncated predicates).

\begin{code}

_≐_ : {α β : Level}{A : Type α}(P Q : Pred A β ) → Type _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

pred-ext : (α β : Level) → Type (lsuc (α ⊔ β))
pred-ext α β = ∀ {A : Type α}{P Q : Pred A β } → P ⊆ Q → Q ⊆ P → P ≡ Q

\end{code}

Note that `pred-ext` merely defines an extensionality principle. It does not postulate that the principle holds.  If we wish to postulate `pred-ext`, then we do so by assuming that type is inhabited (see `block-ext` below, for example).



#### <a id="quotient-extensionality">Quotient extensionality</a>

We need an identity type for congruence classes (blocks) over sets so that two different presentations of the same block (e.g., using different representatives) may be identified.  This requires two postulates: (1) *predicate extensionality*, manifested by the `pred-ext` type; (2) *equivalence class truncation* or "uniqueness of block identity proofs", manifested by the `blk-uip` type defined in the [Relations.Truncation][] module. We now use `pred-ext` and `blk-uip` to define a type called `block-ext|uip` which we require for the proof of the First Homomorphism Theorem presented in [Homomorphisms.Noether][].

\begin{code}

module _ {A : Type α}{R : BinRel A ρ} where

 block-ext : pred-ext α ρ → IsEquivalence{a = α}{ℓ = ρ} R → {u v : A} → R u v → [ u ] R ≡ [ v ] R
 -- block-ext pe Req {u}{v} Ruv = pe (/-subset Req Ruv) (/-supset Req Ruv)
 block-ext pe Req {u}{v} Ruv = pe ([]-⊆ {R = (R , Req)} u v Ruv) ([]-⊇ {R = (R , Req)} u v Ruv)


 private
   to-subtype|uip : blk-uip A R → {C D : Pred A ρ}{c : IsBlock C {R}}{d : IsBlock D {R}}
    →               C ≡ D → (C , c) ≡ (D , d)

   to-subtype|uip buip {C}{D}{c}{d}CD = to-Σ-≡(CD , buip D(transport(λ B → IsBlock B)CD c)d)

 block-ext|uip : pred-ext α ρ → blk-uip A R → IsEquivalence R → ∀{u}{v} → R u v → ⟪ u ⟫ ≡ ⟪ v ⟫
 block-ext|uip pe buip Req Ruv = to-subtype|uip buip (block-ext pe Req Ruv)

\end{code}

#### <a id="strongly-well-defined-operations">Strongly well-defined operations</a>

We now describe an extensionality principle that seems weaker than function extensionality, but still (probably) not provable in [MLTT][]. (We address this and other questions  below.)  We call this the principle *strong well-definedness of operations*. We will encounter situations in which this weaker extensionality principle suffices as a substitute for function extensionality.

Suppose we have a function whose domain is a function type, say, `I → A`.  For example, inhabitants of the type `Op` defined above are such functions.  (Recall, the domain of inhabitants of type `Op I A := (I → A) → A` is `I → A`.)

Of course, operations of type `Op I A` are well-defined in the sense that equal inputs result in equal outputs.

\begin{code}

welldef : {A : Type α}{I : Type 𝓥}(f : Op A I) → ∀ u v → u ≡ v → f u ≡ f v
welldef f u v refl = refl

\end{code}

A stronger form of well-definedness of operations is to suppose that point-wise equal inputs lead to the same output.  In other terms, we could suppose that  for all `f : Op I A`, we have `f u ≡ f v` whenever `∀ i → u i ≡ v i` holds.  We call this formalize this notation in the following type.

\begin{code}

swelldef : (𝓥 α : Level) → Type (lsuc (α ⊔ 𝓥))
swelldef 𝓥 α = ∀ {A : Type α}{I : Type 𝓥}(f : Op A I)(u v : I → A) → (∀ i → u i ≡ v i) → f u ≡ f v

private
  funext→swelldef : {α 𝓥 : Level} → funext 𝓥 α → swelldef 𝓥 α
  funext→swelldef fe f u v ptweq = Goal
   where
   uv : u ≡ v
   uv = fe ptweq
   Goal : f u ≡ f v
   Goal = welldef f u v uv


SwellDef : Setω
SwellDef = (𝓤 𝓥 : Level) → swelldef 𝓤 𝓥


\end{code}




---------------------------------------

[← Relations.Truncation](Relations.Truncation.html)
<span style="float:right;">[Algebras →](Algebras.html)</span>


{% include UALib.Links.md %}


-----------------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team

