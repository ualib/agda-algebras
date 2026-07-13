---
layout: default
file: "src/Setoid/Varieties/FreeSubstitution.lagda.md"
title: "Setoid.Varieties.FreeSubstitution module"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### A substitution kit for derivable equality

This is the [Setoid.Varieties.FreeSubstitution][] module of the [Agda Universal Algebra Library][].

Substitution `_[_]` ([Setoid.Terms.Basic][]) pushes into a node *pointwise*,

    (node f ts) [ σ ] = node f (λ i → ts i [ σ ]).

When `ts` is a finite tuple written as a pattern-matching lambda, say,
`λ { 0F → s ; 1F → t }`, the natural way to write a binary term is, e.g.,
`s · t = node ∙-Op (λ { 0F → s ; 1F → t })`.

Unfortunately, the result `node f (λ i → ts i [ σ ])` is not definitionally equal to
a freshly *rebuilt* term

    s [ σ ] · t [ σ ] = node ∙-Op (λ { 0F → s [ σ ] ; 1F → t [ σ ] }),

since a pattern-matching lambda does not reduce under a variable index `i`, and
bridging the two position functions needs function extensionality, which is
unavailable under `--safe` / `--cubical-compatible`.[^1]

The practical bite is that the obvious way to instantiate an equation at *compound*
terms fails: `sub (hyp i) σ` produces a goal in `_[ σ ]`-form that will not match a
readable, rebuilt term, so a multi-step rewrite like a four-fold reassociation cannot
be written directly.

The fix is small, because the bookkeeping half of the kit is already proved: the
`_≐_`-level laws `[]-unitˡ` (left unit, the issue's `[]-ℊ`), `[]-unitʳ`, `[]-assoc`,
and `[]-cong` live in [Setoid.Terms.Monad][].  What is added here is the bridge
between the two equalities on
terms — the inductive equality `_≐_` of [Setoid.Terms.Basic][] and the *derivable*
equality `_⊢_▹_≈_` of [Setoid.Varieties.SoundAndComplete][]:

+  `≐→⊢`{.AgdaFunction} — every `_≐_`-equality is derivable.  Two terms that are
   `_≐_` (same shape, equal variables at the leaves) are equal in *every* equational
   theory, by `refl` at the leaves and the congruence rule `app` at the nodes.  This
   is exactly the tool for rewriting a `_[ σ ]`-form into the rebuilt term it agrees
   with pointwise: the rebuild is a `_≐_`-fact (a finite, mechanical `gnl` /
   `≐-isRefl` match), and `≐→⊢` turns it into a derivation step.
+  `sub▹`{.AgdaFunction} — instantiate a derivation at a substitution and land on
   *readable* end terms.  It packages `sub` between two `≐→⊢` bridges, so a consumer
   writes `sub▹ d σ l≐pσ qσ≐r` and gets `E ⊢ Γ ▹ l ≈ r` directly.

The worked four-fold reassociation that motivated the substitution kit is in
[Examples.Setoid.FreeSemigroup][], built from one application of `sub▹` (a generic
`assoc▹` that instantiates associativity at arbitrary subterms) plus the congruence rule.

The kit also has a *semantic* face, used by the converse Maltsev conditions:

+  `subhom`{.AgdaFunction} / `renhom`{.AgdaFunction} — a substitution acts on the
   relatively free algebra `𝔽[_]`{.AgdaFunction}
   ([Setoid.Varieties.SoundAndComplete][]) as a homomorphism, whose congruence is
   precisely the `sub`{.AgdaInductiveConstructor} rule;
+  `cg-pair→⊢`{.AgdaFunction} / `cg-pairs→⊢`{.AgdaFunction} — the free-algebra
   congruence/derivability bridge: a membership in a principal congruence
   `Cg ❴ a , b ❵` of `𝔽[ Δ ]` — or in the join of two principal congruences — becomes
   a derivable equation after any substitution that collapses the generating pair(s).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.FreeSubstitution {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; proj₁ )
open import Data.Sum.Base    using ( inj₁ ; inj₂ )
open import Function         using ( Func )
open import Level            using ( Level )
open import Relation.Binary  using () renaming ( _⇒_ to _⊆_ )

import Relation.Binary.PropositionalEquality as ≡

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Terms          {𝑆 = 𝑆}  using  ( Term ; ℊ )
open import Setoid.Algebras.Basic   {𝑆 = 𝑆}  using  ( 𝔻[_] )
open import Setoid.Congruences.Generation    using  ( Gen ; Cg ; base ; symmetric
                                                    ; _∨_ ; _∪ᵣ_ ; module principal )
open import Setoid.Homomorphisms.Basic       using ( hom ; mkIsHom )
open import Setoid.Homomorphisms.Kernels     using ( kercon )
open import Setoid.Homomorphisms.Properties  using ( Cg⊆ker )
open import Setoid.Terms.Basic      {𝑆 = 𝑆}  using ( _≐_ ; Sub ; _[_] )
open import Setoid.Varieties.SoundAndComplete {𝑆 = 𝑆}
  using ( Eq ; _⊢_▹_≈_ ; module FreeAlgebra )

open _≐_         using ( rfl ; gnl )
open _⊢_▹_≈_     using ( app ; sub ; refl ; trans )

private variable
  χ ι : Level
  Γ Δ : Type χ
  I   : Type ι
```
-->

#### Derivable equality refines term equality

Every `_≐_`-equality is derivable in any theory `E`.  The leaf case is the reflexivity
rule (the variables are equal, so the terms are literally equal); the node case is the
congruence rule `app` applied to the inductive hypotheses at the positions.  No clause
inspects the equation set `E`, so this holds uniformly.

```agda
≐→⊢ : {E : I → Eq} {s t : Term Γ} → s ≐ t → E ⊢ Γ ▹ s ≈ t
≐→⊢ (rfl ≡.refl)  = refl
≐→⊢ (gnl ps)      = app (λ i → ≐→⊢ (ps i))
```

#### Instantiating a derivation at compound terms

`sub▹ d σ` substitutes `σ` into a derivation `d : E ⊢ Δ ▹ p ≈ q` and rewrites both ends
to readable terms supplied by the caller: given `l ≐ p [ σ ]` and `q [ σ ] ≐ r`, it
returns `E ⊢ Γ ▹ l ≈ r`.  This is the clean way to use an equation at compound terms —
the `_≐_` arguments are the mechanical "rebuild" bridges, and `sub▹` hides the
`_[ σ ]`-form behind them.

```agda
sub▹ : {E : I → Eq} {p q : Term Δ} (d : E ⊢ Δ ▹ p ≈ q) (σ : Sub Γ Δ)
       {l r : Term Γ} → l ≐ p [ σ ] → q [ σ ] ≐ r → E ⊢ Γ ▹ l ≈ r
sub▹ d σ l≐pσ qσ≐r = trans (≐→⊢ l≐pσ) (trans (sub d σ) (≐→⊢ qσ≐r))
```

#### The substitution-induced homomorphism

Fix a theory `E : I → Eq`.  A substitution `σ : Sub Γ Δ` (each `Δ`-variable to a
`Γ`-term) induces the homomorphism `subhom σ : 𝔽[ Δ ] → 𝔽[ Γ ]`{.AgdaFunction} on the
relatively free algebra whose underlying map is `_[ σ ]`{.AgdaFunction}.  It respects
derivable equality by the `sub`{.AgdaInductiveConstructor} rule, and the homomorphism
square holds by `refl`{.AgdaInductiveConstructor} because `(node f ts) [ σ ]` is
`node f (λ i → ts i [ σ ])` on the nose.

```agda
module _ {Γ Δ : Type χ} {I : Type ι} (E : I → Eq) where
  open FreeAlgebra E using ( 𝔽[_] )

  subhom : (σ : Sub Γ Δ) → hom 𝔽[ Δ ] 𝔽[ Γ ]
  subhom σ = subfunc , mkIsHom (λ {f}{a} → refl)
    where
    subfunc : Func 𝔻[ 𝔽[ Δ ] ] 𝔻[ 𝔽[ Γ ] ]
    subfunc = record { to = _[ σ ] ; cong = λ pq → sub pq σ }
```

The special case of a plain variable renaming `r : Δ → Γ` is `subhom (ℊ ∘ r)`.

```agda
  renhom : (r : Δ → Γ) → hom 𝔽[ Δ ] 𝔽[ Γ ]
  renhom r = subhom (λ v → ℊ (r v))
```

#### The principal-pair bridge

Combining the substitution homomorphism with `Cg⊆ker`{.AgdaFunction}
([Setoid.Homomorphisms.Properties][]) yields the **free-algebra
congruence/derivability bridge**: given a substitution `σ` that collapses the pair
`(a , b)` — i.e. `E ⊢ Γ ▹ a [ σ ] ≈ b [ σ ]` is derivable — every pair `(s , t)` in
the principal congruence `Cg ❴ a , b ❵` of `𝔽[ Δ ]` becomes derivably equal after `σ`.
This is how the converse Maltsev conditions read term identities off congruences of
the free algebra ([Setoid.Varieties.Maltsev.Permutability][],
[Setoid.Varieties.Maltsev.Distributivity][]).

```agda
  open principal 𝔽[ Δ ]

  cg-pair→⊢ : (σ : Sub Γ Δ)(a b : Term Δ)
    → E ⊢ Γ ▹ a [ σ ] ≈ b [ σ ]
    → {s t : Term Δ} → Gen ❴ a , b ❵ s t → E ⊢ Γ ▹ s [ σ ] ≈ t [ σ ]
  cg-pair→⊢ σ a b coll = Cg⊆ker (subhom σ) incl
    where
    incl : ❴ a , b ❵ ⊆ proj₁ (kercon (subhom σ))
    incl pᵣ = coll
```

The converse of Day's theorem ([Setoid.Varieties.Maltsev.Modularity][]) needs the same
bridge for the **join of two principal congruences**: two of the congruences in Day's
construction collapse *two* generator pairs at once, so their collapsing substitutions
must kill both.  Given a substitution `σ` that collapses the pair `(a , b)` *and* the
pair `(c , d)`, every pair in `Cg ❴ a , b ❵ ∨ Cg ❴ c , d ❵` becomes derivably equal
after `σ`.  The proof is the same `Cg⊆ker`{.AgdaFunction} instance: the union of the
two generating congruences is included in the kernel componentwise, each component by
`cg-pair→⊢`{.AgdaFunction}.

```agda
  cg-pairs→⊢ : (σ : Sub Γ Δ)(a b c d : Term Δ)
    → E ⊢ Γ ▹ a [ σ ] ≈ b [ σ ]
    → E ⊢ Γ ▹ c [ σ ] ≈ d [ σ ]
    → {s t : Term Δ} → proj₁ (Cg ❴ a , b ❵ ∨ Cg ❴ c , d ❵) s t
    → E ⊢ Γ ▹ s [ σ ] ≈ t [ σ ]
  cg-pairs→⊢ σ a b c d coll-ab coll-cd = Cg⊆ker (subhom σ) incl
    where
    incl : (Cg ❴ a , b ❵ ∪ᵣ Cg ❴ c , d ❵) ⊆ proj₁ (kercon (subhom σ))
    incl (inj₁ p) = cg-pair→⊢ σ a b coll-ab p
    incl (inj₂ q) = cg-pair→⊢ σ c d coll-cd q
```

#### Smoke test: recovering a derivable identity from a principal congruence

A small end-to-end consumer.  Fix two variables `u`, `v`, a substitution `σ` that
*merges* them (`σ u`, `σ v` are derivably equal), and the principal congruence
`Cg ❴ ℊ u , ℊ v ❵`.  Then every pair in that congruence is recovered as a derivable
equation after `σ`; in particular the generators themselves, and (by symmetry) the
swapped pair.

```agda
module _
  {Γ : Type χ}
  {I : Type ι}
  (E : I → Eq)
  (σ : Sub Γ Γ)  (u v : Γ)
  (merge : E ⊢ Γ ▹ σ u ≈ σ v)
  where
  open FreeAlgebra E using ( 𝔽[_] )
  open principal 𝔽[ Γ ]

  recover : {s t : Term Γ} → Gen ❴ ℊ u , ℊ v ❵ s t → E ⊢ Γ ▹ s [ σ ] ≈ t [ σ ]
  recover = cg-pair→⊢ E σ (ℊ u) (ℊ v) merge

  recover-gen : E ⊢ Γ ▹ σ u ≈ σ v
  recover-gen = recover (base pᵣ)

  recover-swap : E ⊢ Γ ▹ σ v ≈ σ u
  recover-swap = recover (symmetric (base pᵣ))
```

--------------------------------------

[^1]: This is the same `Fin n` η-gap that the M4-5 development meets repeatedly; see [ADR-002][] §6.


[M4-10]: https://github.com/ualib/agda-algebras/issues/362
