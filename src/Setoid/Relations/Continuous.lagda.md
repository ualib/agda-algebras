---
layout: default
title : "Setoid.Relations.Continuous module (The Agda Universal Algebra Library)"
date : "2026-05-10"
author: "the agda-algebras development team"
---

### Continuous Relations on Setoids

This is the [Setoid.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

A *continuous relation* of arity `I` over a type `A` is a predicate on `I`-tuples drawn from `A`.  The arity `I : Type ι` is an arbitrary type — not a fixed natural number — so the API generalises uniformly over finite, countable, and uncountable arities.  This module is the canonical setoid-flavoured home for the continuous-relation API, ported from `Legacy.Base.Relations.Continuous` under [#308][].  Three deliberate design choices distinguish it from the legacy:

+  **Π-setoid as the canonical `I`-tuple object.**  The natural `I`-tuple type whose pointwise equivalence a relation may be required to respect is the carrier of the Π-setoid `⨅ˢ 𝒜`, defined below.  Its level signature `(α ⊔ ι, ρᵃ ⊔ ι)` matches that of [`Setoid.Algebras.Products.⨅`][] exactly; in fact the inlined `Domain` of `⨅` *is* `⨅ˢ` applied to the algebras' domain setoids, so `⨅ˢ` and `⨅` compose by definitional unfolding.  Lifting this construction to a named referent here means every downstream relational development can speak about "I-tuples up to pointwise equivalence" without re-rolling the Π-setoid inline.

+  **Bare carrier types in `Rel`/`REL`, with setoid-respect as an external overlay.**  The relation types `Rel A I` and `REL I 𝒜` themselves take *bare* carrier types, exactly matching the legacy carrier shape.  Setoid structure is introduced through `⨅ˢ` and through the `Π-Respects-*` predicates, which name the property "respects pointwise equivalence" as a separate assertion.  This factorisation has three concrete payoffs.  (i) The consumer-side migration of existing call sites is purely an import-path change.  (ii) It mirrors how `Setoid.Relations.Quotients` uses bare `Pred` types throughout.  (iii) Agda's level inference works out cleanly: a setoid-parameterised `Rel` would force the user to disambiguate the unconstrained equivalence-level `ρᵃ` of every implicit setoid argument at every call site, since the projection `Carrier : Setoid α ρᵃ → Type α` is not injective in `ρᵃ`.

+  **Cubical-friendly by construction.**  `⨅ˢ` is defined against `Setoid`'s public interface (`Carrier`, `_≈_`, `isEquivalence`); a Cubical port replaces these with path equality, and the construction goes through with the equivalence-witness layer collapsing to triviality.  The bare-types `Rel`/`REL` are independent of the equivalence story and port with no change at all.

A note on `compatible-REL`. The legacy `Legacy.Base.Relations.Continuous.compatible-REL` reads `compatible-REL 𝑓 R = Π[ t ∈ … ] eval-REL R t`, which is unconditional in `t` and never references `𝑓` — a bug, since it makes the predicate independent of the operations.  The intended definition, mirroring the structure of the (correct) single-sorted `compatible-Rel`, is `∀ t → eval-REL R t → R (λ i → 𝑓 i (t i))`.  The canonical port below uses the corrected definition.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Relations.Continuous where

-- Imports from Agda primitives and the standard library.
open import Agda.Primitive    using () renaming ( Set to Type )
open import Level             using ( Level ; _⊔_ ; suc )
open import Relation.Binary   using ( Setoid ; IsEquivalence )

open Setoid         using ( Carrier ; _≈_ ) renaming ( isEquivalence to isEqv )
open IsEquivalence  using () renaming ( refl to reflᴱ ; sym to symᴱ ; trans to transᴱ )

-- Imports from agda-algebras.
open import Overture          using ( Op ; arity[_] )

private variable α ρᵃ ρ ι : Level
```

#### <a id="pi-setoid">The Π-setoid construction</a>

Given an indexing type `I : Type ι` and a family `𝒜 : I → Setoid α ρᵃ`, the indexed-product setoid `⨅ˢ 𝒜` has carrier the dependent function type `(i : I) → Carrier (𝒜 i)` and equivalence the pointwise equivalence `λ a b → ∀ i → _≈_ (𝒜 i) (a i) (b i)`, an equivalence relation by appeal to each `isEquivalence (𝒜 i)`.  The level signature matches `Setoid.Algebras.Products.⨅` exactly; lifting the construction to a named referent means downstream consumers can reference a single canonical Π-setoid rather than rolling it inline at each use site.

```agda
⨅ˢ : {I : Type ι} → (𝒜 : I → Setoid α ρᵃ) → Setoid (α ⊔ ι) (ρᵃ ⊔ ι)
⨅ˢ {I = I} 𝒜 = record
  { Carrier        = (i : I) → Carrier (𝒜 i)
  ; _≈_            = λ a b → (i : I) → _≈_ (𝒜 i) (a i) (b i)
  ; isEquivalence  = record
      { refl   = λ i      → reflᴱ   (isEqv (𝒜 i))
      ; sym    = λ p i    → symᴱ    (isEqv (𝒜 i)) (p i)
      ; trans  = λ p q i  → transᴱ  (isEqv (𝒜 i)) (p i) (q i)
      }
  }
```

#### Continuous and dependent relations

The single-sorted continuous relation type `Rel A I` represents predicates of arity `I` over a single carrier `A`.

```agda
Rel : (A : Type α) (I : Type ι) → {ρ : Level} → Type (α ⊔ ι ⊔ suc ρ)
Rel A I {ρ} = (I → A) → Type ρ

-- single-sorted: ρ explicit, syntax binds it
Rel-syntax : (A : Type α) (I : Type ι) (ρ : Level) → Type (α ⊔ ι ⊔ suc ρ)
Rel-syntax A I ρ = Rel A I {ρ}

syntax Rel-syntax A I ρ = Rel[ A ^ I ] ρ
infix 6 Rel-syntax
```

The multi-sorted (or *dependent*) continuous relation type `REL I 𝒜` represents predicates over an indexed family `𝒜 : I → Type α` of carriers.  Inhabitants are predicates on dependent `I`-tuples — i.e. on `(i : I) → 𝒜 i`.  When `𝒜 i = Carrier (𝒮 i)` for an indexed family `𝒮 : I → Setoid α ρᵃ`, this is definitionally the same as a predicate on `Carrier (⨅ˢ 𝒮)`, which is the bridge to the Π-setoid story.

```agda
REL : (I : Type ι) → (I → Type α) → {ρ : Level} → Type (α ⊔ ι ⊔ suc ρ)
REL I 𝒜 {ρ} = ((i : I) → 𝒜 i) → Type ρ

-- multi-sorted: ρ implicit, syntax does NOT bind it
REL-syntax : (I : Type ι) → (I → Type α) → {ρ : Level} → Type (α ⊔ ι ⊔ suc ρ)
REL-syntax I 𝒜 {ρ} = REL I 𝒜 {ρ}

syntax REL-syntax I (λ i → 𝒜) = REL[ i ∈ I ] 𝒜
infix 6 REL-syntax
```

#### Respecting pointwise equivalence

A continuous relation `R` on the carrier of a setoid `𝐴` *respects pointwise equivalence on tuples* if `R f` and `f ≈ g` (the pointwise lift of `_≈_ 𝐴` to tuples) imply `R g`.  Equivalently, `R Respects (_≈_ (⨅ˢ {I = I} (λ _ → 𝐴)))` against stdlib's `Relation.Unary._Respects_`.

The predicates `Π-Respects-Rel` and `Π-Respects-REL` below name this property as an explicit assertion rather than bundling it into the relation type itself, leaving consumers free to demand it where it matters and ignore it elsewhere — for the polymorphism-clone machinery in #274, the infinitary-CSP work in #281, and the Scott-continuous-DCPO work in #282 it is load-bearing; for transient working relations it is overhead.  The setoid argument is *explicit* in both predicates: the projection `Carrier : Setoid α ρᵃ → Type α` is not injective in `ρᵃ`, so an implicit setoid argument would be undetermined at every call site.

```agda
Π-Respects-Rel :  (𝐴 : Setoid α ρᵃ){I : Type ι}{ρ : Level}
  →                Rel (Carrier 𝐴) I {ρ} → Type (ι ⊔ α ⊔ ρᵃ ⊔ ρ)
Π-Respects-Rel 𝐴 {I = I} R =
  ∀ {f g} → ((i : I) → _≈_ 𝐴 (f i) (g i)) → R f → R g

Π-Respects-REL :  {I : Type ι}(𝒜 : I → Setoid α ρᵃ){ρ : Level}
  →                REL I (λ i → Carrier (𝒜 i)) {ρ} → Type (ι ⊔ α ⊔ ρᵃ ⊔ ρ)
Π-Respects-REL {I = I} 𝒜 R =
  ∀ {f g} → ((i : I) → _≈_ (𝒜 i) (f i) (g i)) → R f → R g
```

#### <a id="compatibility-with-general-relations">Compatibility of operations with continuous relations</a>

The operation `eval-Rel` lifts an `I`-ary relation to an `(I → J)`-ary relation: the lifted relation relates an `I`-tuple of `J`-tuples just in case each `J`-indexed *row* of the tuple-of-tuples (viewed as a `J`-indexed family of `I`-tuples) belongs to the original relation.

```agda
eval-Rel :  {A : Type α}{I : Type ι}
  →          Rel A I {ρ} → (J : Type ι) → (I → J → A) → Type (ι ⊔ ρ)
eval-Rel R J t = (j : J) → R (λ i → t i j)
```

A relation `R` is *compatible* with an operation `f : Op A J` if, for every `I`-tuple-of-`J`-tuples whose `J`-indexed rows lie in `R`, applying `f` columnwise yields a tuple in `R`.

```agda
compatible-Rel :  {A : Type α}{I J : Type ι}
  →                Op A J → Rel A I {ρ} → Type (ι ⊔ α ⊔ ρ)
compatible-Rel f R = ∀ t → eval-Rel R arity[ f ] t → R (λ i → f (t i))
```

#### <a id="compatibility-of-operations-with-dependent-relations">Compatibility of operations with dependent relations</a>

The multi-sorted analogues `eval-REL` and `compatible-REL` mirror the single-sorted versions exactly, with `Rel A I` replaced by `REL I 𝒜` and tuple types replaced by their dependent counterparts.  The definition of `compatible-REL` corrects the buggy form in the legacy module; see the module header.

```agda
eval-REL :  {I : Type ι}{𝒜 : I → Type α}{J : Type ι}
  →          REL I 𝒜 {ρ}
  →          ((i : I) → J → 𝒜 i)
  →          Type (ι ⊔ ρ)
eval-REL {J = J} R t = (j : J) → R (λ i → t i j)

compatible-REL :  {I J : Type ι}{𝒜 : I → Type α}
  →                (∀ i → Op (𝒜 i) J)
  →                REL I 𝒜 {ρ}
  →                Type (ι ⊔ α ⊔ ρ)
compatible-REL 𝑓 R = ∀ t → eval-REL R t → R (λ i → 𝑓 i (t i))
```

--------------------------------------

<span style="float:left;">[← Setoid.Relations.Quotients](Setoid.Relations.Quotients.html)</span>
<span style="float:right;">[Setoid.Relations.Properties →](Setoid.Relations.Properties.html)</span>

{% include UALib.Links.md %}
