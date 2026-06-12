---
layout: default
file: "src/Setoid/Terms/Monad.lagda.md"
title: "Setoid.Terms.Monad module"
date: "2026-06-12"
author: "the agda-algebras development team"
---

#### The term monad

This is the [Setoid.Terms.Monad][] module of the [Agda Universal Algebra Library][].

This module establishes that `Term`{.AgdaDatatype} — terms over a type of variables,
in the ambient signature `𝑆` — carries the structure of a *monad*: variables embed
into terms (`ℊ`{.AgdaInductiveConstructor}, the unit), terms whose "variables" are
themselves terms flatten into terms (substitution, the multiplication), and the three
monad laws hold.  This is the precise content of the slogan "the term algebra is the
free algebra": freeness *is* a monad, and the monad laws are the familiar bookkeeping
facts about substitution that universal-algebra proofs use tacitly all the time.

##### Which form do the laws take?  The Kleisli presentation

A monad can be presented two equivalent ways:

+  the **categorical (μ) form** — an endofunctor `T` with natural transformations
   `η : Id ⟹ T` and `μ : T ∘ T ⟹ T` and three commuting diagrams — packaged
   abstractly by the [`Monad`][Setoid.Categories.Monad] record; or
+  the **Kleisli (extension) form** — `η` together with an *extension* operation
   turning each `σ : X → T Y` into `σ✶ : T X → T Y`, satisfying three equations.
   For terms, the extension of `σ` is exactly *substitution* `_[ σ ]`, already
   defined in [Setoid.Terms.Basic][] (following Abel), and the three equations are
   the left unit, right unit, and associativity laws proved below.

We state the laws in Kleisli form, and the choice is forced, not stylistic: in a
predicative universe hierarchy `Term` **raises universe levels**.  For variables
`X : Type χ` the terms live one universe up, `Term X : Type (ov χ)` where
`ov χ = 𝓞 ⊔ 𝓥 ⊔ suc χ` — the `suc` is unavoidable because a term mixes leaves from
`X` with operation symbols from `Type 𝓞`.  Consequently `Term` is not an endofunctor
of any single category `Setoid α ρ`, there is no level at which `η : Id ⟹ Term` even
type-checks, and the `Monad` record cannot be instantiated.  What `Term` is, exactly,
is a *relative monad* in the sense of Altenkirch–Chapman–Uustalu, relative to the
universe-lifting inclusion `Type χ → Type (ov χ)`; and the Kleisli form is precisely
the presentation of a relative monad that never mentions `T ∘ T`, so it states and
proves at heterogeneous levels what the μ form cannot.  (See
`docs/notes/m4-5e-term-monad.md`; this level obstruction is a fact about
predicativity that a cubical port will *not* dissolve, unlike the η-gap obstructions
recorded elsewhere.)

The equality in the laws is `_≐_`{.AgdaDatatype}, the equality-of-terms relation of
[Setoid.Terms.Basic][] — two terms are `≐`-related when they have the same shape with
equal variables at the leaves.  Only the left unit law holds by `refl`; the other two
genuinely recurse over the term, because two functions on positions (`λ i → …`) are
involved and `--safe` provides no function extensionality.  Per the library's
strict-first convention, the left unit law is stated in its strongest, function-level
`≡` form first, with the pointwise corollary derived.

##### The payoff: substitution becomes a category

The monad laws are not merely recorded — they are *packaged*.  Substitutions compose
(`_⊙ˢ_`{.AgdaFunction}), the generator map `ℊ` is a unit for that composition, and
composition is associative; so variable types and substitutions form a category, the
**Kleisli category** of the term monad, assembled below as a bona fide instance
`TermKleisli`{.AgdaFunction} of the [`Category`][Setoid.Categories.Category] record.
The three category laws *are* the three monad laws — no residue is lost in the
packaging, and the level arithmetic works out (`Obj = Type χ` lives at `suc χ`,
hom-sets at `ov χ`), which is how the term monad gets a fully categorical, checked
statement despite not being an endofunctor.

A concrete reading, for the signature of monoids: an object is a supply of variable
names; an arrow `X ⟶ Y` assigns to each name in `X` a monoid term over the names in
`Y` — for instance `x ↦ (y₁ ∙ y₂) ∙ ε` — that is, an arrow is a *simultaneous change
of variables*; composing arrows substitutes the second assignment into the terms of
the first; and the identity arrow renames nothing (`x ↦ x`).  Equational reasoning
about composite substitutions — the daily bread of free-algebra arguments — is then
just diagram chasing in `TermKleisli`.

The interpretation (fold) side of the story — every algebra `𝑨` evaluates terms, and
evaluation interacts with this monad structure — is distributed as follows:
`substitution` in [Setoid.Terms.Basic][] says evaluation takes `_[ σ ]` to
composition of environments (`𝑨` is an Eilenberg–Moore-style algebra for the monad);
`free-lift-natural` and `comm-hom-term` in [Setoid.Terms.Properties][] and
[Setoid.Terms.Operations][] say the fold is natural in the algebra; and
[Classical.Varieties.Invariance][] adds naturality in the *signature*.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Terms.Monad {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level ; suc )

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong-app )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Terms          {𝑆 = 𝑆} using ( Term ; ℊ ; node ; ov )
open import Setoid.Terms.Basic      {𝑆 = 𝑆} using ( Sub ; _[_] ; _≐_
                                                  ; ≐-isRefl ; ≐-isSym ; ≐-isTrans )
open import Setoid.Categories.Category      using ( Category )

open _≐_

private variable
  χ : Level
  W X Y : Type χ
```

##### Composition of substitutions

`σ ⊙ˢ τ` performs `σ` and then `τ`: each variable is sent by `σ` to a term, into
which `τ` then substitutes.  (Diagrammatic order, like `⊙-hom`; the Kleisli category
below flips it into the applicative order of the `Category` record's `_∘_`, exactly
as the algebra category does with `⊙-hom`.)

```agda
_⊙ˢ_ : Sub X Y → Sub W X → Sub W Y
(σ ⊙ˢ τ) y = (σ y) [ τ ]
```

##### The monad laws

**Left unit.**  Substituting into a bare variable just looks the variable up:
`(ℊ y) [ σ ]` *is* `σ y`, by the first defining clause of `_[_]`.  Stated
strict-first: as functions of the variable, `(λ y → (ℊ y) [ σ ])` and `σ` are
definitionally equal (function η), so the law is `refl`, with the pointwise corollary
one `cong-app` away.

```agda
module _ {X Y : Type χ} {σ : Sub X Y} where

  []-unitˡ : (λ y → (ℊ y) [ σ ]) ≡ σ
  []-unitˡ = refl

  []-unitˡ-ptw : (y : Y) → (ℊ y) [ σ ] ≡ σ y
  []-unitˡ-ptw = cong-app []-unitˡ
```

**Right unit.**  Substituting the generator term `ℊ y` for each variable `y` rebuilds
the term unchanged.  This is the identity substitution, and the proof is the
structural recursion the statement suggests; the result is `_≐_`, not `_≡_`, because
at each node the two argument tuples agree only pointwise.

```agda
[]-unitʳ : (t : Term X) → (t [ ℊ ]) ≐ t
[]-unitʳ (ℊ x)       = ≐-isRefl
[]-unitʳ (node f ts) = gnl (λ i → []-unitʳ (ts i))
```

**Associativity.**  Substituting in two stages is one substitution by the composite.
This is the law a syntactician would call the *substitution lemma for substitutions*;
it is what makes towers of changes-of-variables collapse.

```agda
[]-assoc : (t : Term Y) (σ : Sub X Y) (τ : Sub W X)
  → ((t [ σ ]) [ τ ]) ≐ (t [ σ ⊙ˢ τ ])
[]-assoc (ℊ y)       σ τ = ≐-isRefl
[]-assoc (node f ts) σ τ = gnl (λ i → []-assoc (ts i) σ τ)
```

**Congruence.**  Substitution respects `_≐_` in both arguments — replacing the term
by an equal term and the substitution by a pointwise-equal substitution gives equal
results.  This is what makes `_[_]` a legitimate operation on the term *setoid* (and
it is the `∘-resp-≈` law of the Kleisli category).

```agda
[]-cong : {s t : Term Y} {σ τ : Sub X Y}
  → s ≐ t → ((y : Y) → σ y ≐ τ y) → (s [ σ ]) ≐ (t [ τ ])
[]-cong (rfl refl) σ≐τ = σ≐τ _
[]-cong (gnl ps)   σ≐τ = gnl (λ i → []-cong (ps i) σ≐τ)
```

##### The Kleisli category

Objects: variable types at level `χ`.  An arrow `X ⟶ Y` is a substitution
`Sub Y X` — a term over `Y` for each variable in `X` (the arrow points from
variables to the terms that replace them).  Identity is `ℊ`; composition is `_⊙ˢ_`
read in the applicative order; hom-equality is pointwise `_≐_`.  Note how each
category law is discharged by exactly one monad law — that correspondence is the
theorem "`(Term , ℊ , _[_])` is a (relative) monad," stated as the well-formedness
of a category.

```agda
TermKleisli : (χ : Level) → Category (suc χ) (ov χ) (ov χ)
TermKleisli χ = record
  { Obj        = Type χ
  ; Hom        = λ X Y → Sub Y X
  ; _≈_        = λ σ τ → ∀ x → σ x ≐ τ x
  ; id         = ℊ
  ; _∘_        = λ τ σ → σ ⊙ˢ τ
  ; ≈-equiv    = record  { refl   = λ _ → ≐-isRefl
                         ; sym    = λ p x → ≐-isSym (p x)
                         ; trans  = λ p q x → ≐-isTrans (p x) (q x)
                         }
  ; assoc      = λ {A} {B} {C} {D} {f} {g} {h} a → ≐-isSym ([]-assoc (f a) g h)
  ; identityˡ  = λ {A} {B} {f} a → []-unitʳ (f a)
  ; identityʳ  = λ _ → ≐-isRefl
  ; ∘-resp-≈   = λ f≈g h≈i a → []-cong (h≈i a) f≈g
  }
```

##### The multiplication, for the record

For completeness — and because the μ form is the one the `Monad` record speaks — here
is the multiplication itself: a term whose leaves are terms flattens by grafting each
leaf-term in place of its leaf.  Its characterizing equations are the defining
clauses; its laws are the `[]-`laws above, specialized.  (It cannot be *defined* as
`_[ id ]` here, because `Sub` fixes both variable types at one level, while `join`'s
domain `Term (Term X)` is inherently heterogeneous — `Term X` lives at `ov χ`, not
`χ`.  The direct recursion sidesteps that cleanly.)

```agda
join : Term (Term X) → Term X
join (ℊ t)       = t
join (node f ts) = node f (λ i → join (ts i))

-- The μ-form unit law that is definitional: flattening a trivial
-- expression-of-expressions yields the expression.
join-ℊ : (t : Term X) → join (ℊ t) ≡ t
join-ℊ _ = refl
```

--------------------------------------

{% include UALib.Links.md %}
