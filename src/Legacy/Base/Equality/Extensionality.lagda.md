---
layout: default
title : "Base.Equality.Extensionality module (The Agda Universal Algebra Library)"
date : "2021-02-23"
author: "agda-algebras development team"
---

### <a id="extensionality">Extensionality</a>

This is the [Base.Equality.Extensionality][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Legacy.Base.Equality.Extensionality where

-- imports from Agda and the Agda Standard Library ------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type ; Setω to Typeω )
open import Data.Product     using ( _,_ )   renaming ( _×_ to _∧_ )
open import Level            using ( _⊔_ ; Level )
open import Relation.Binary  using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Unary   using ( Pred ; _⊆_ )

open  import Axiom.Extensionality.Propositional    using () renaming ( Extensionality to funext )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

-- imports from agda-algebras --------------------------------------------------------------
open import Overture        using ( transport )
open import Legacy.Base.Relations  using ( [_] ; []-⊆ ; []-⊇ ; IsBlock ; ⟪_⟫ )
open import Legacy.Base.Equality.Truncation using ( blk-uip ; to-Σ-≡ )

private variable α β γ ρ 𝓥 : Level
```


#### <a id="function-extensionality">Function Extensionality</a>


Previous versions of the [agda-algebras][] library made heavy use of a *global function extensionality
principle* asserting that function extensionality holds at all universe levels.
However, we have removed all instances of global function extensionality from the current version of the library and we now limit ourselves to local applications of the principle. This has the advantage of making transparent precisely how and where the library depends on function extensionality. Eventually we hope to be able to remove these postulates altogether in favor of an alternative approach to extensionality (e.g., by working with setoids or by reimplementing the entire library in Cubical Agda).

The following definition is useful for postulating function extensionality when and where needed.


```agda


DFunExt : Typeω
DFunExt = (𝓤 𝓥 : Level) → funext 𝓤 𝓥
```



#### <a id="an-alternative-way-to-express-function-extensionality">An alternative way to express function extensionality</a>

A useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `happly` function is actually an *equivalence*.

The principle of *proposition extensionality* asserts that logically equivalent propositions are equivalent.  That is, if `P` and `Q` are propositions and if `P ⊆ Q` and `Q ⊆ P`, then `P ≡ Q`. For our purposes, it will suffice to formalize this notion for general predicates, rather than for propositions (i.e., truncated predicates).


```agda


_≐_ : {α β : Level}{A : Type α}(P Q : Pred A β ) → Type _
P ≐ Q = (P ⊆ Q) ∧ (Q ⊆ P)

pred-ext : (α β : Level) → Type _
pred-ext α β = ∀ {A : Type α}{P Q : Pred A β } → P ⊆ Q → Q ⊆ P → P ≡ Q
```


Note that `pred-ext` merely defines an extensionality principle. It does not postulate that the principle holds.  If we wish to postulate `pred-ext`, then we do so by assuming that type is inhabited (see `block-ext` below, for example).


#### Quotient extensionality

We need an identity type for congruence classes (blocks) over sets so that two different presentations of the same block (e.g., using different representatives) may be identified.  This requires two postulates: (1) *predicate extensionality*, manifested by the `pred-ext` type; (2) *equivalence class truncation* or "uniqueness of block identity proofs", manifested by the `blk-uip` type defined in the [Base.Relations.Truncation][] module. We now use `pred-ext` and `blk-uip` to define a type called `block-ext|uip` which we require for the proof of the First Homomorphism Theorem presented in [Base.Homomorphisms.Noether][].


```agda


module _ {A : Type α}{R : BinRel A ρ} where

 block-ext :  pred-ext α ρ → IsEquivalence{a = α}{ℓ = ρ} R
  →           {u v : A} → R u v → [ u ] R ≡ [ v ] R

 block-ext pe Req {u}{v} Ruv = pe  ([]-⊆ {R = (R , Req)} u v Ruv)
                                   ([]-⊇ {R = (R , Req)} u v Ruv)

 private
   to-subtype|uip :  blk-uip A R
    →                {C D : Pred A ρ}{c : IsBlock C {R}}{d : IsBlock D {R}}
    →                C ≡ D → (C , c) ≡ (D , d)

   to-subtype|uip buip {C}{D}{c}{d} CD =
    to-Σ-≡ (CD , buip D (transport (λ B → IsBlock B) CD c) d)

 block-ext|uip :  pred-ext α ρ → blk-uip A R
  →               IsEquivalence R → ∀{u}{v} → R u v → ⟪ u ⟫ ≡ ⟪ v ⟫

 block-ext|uip pe buip Req Ruv = to-subtype|uip buip (block-ext pe Req Ruv)
```


---------------------------------------

<span style="float:left;">[← Base.Equality.Truncation](Base.Equality.Truncation.html)</span>
<span style="float:right;">[Adjunction →](Adjunction.html)</span>

{% include UALib.Links.md %}
