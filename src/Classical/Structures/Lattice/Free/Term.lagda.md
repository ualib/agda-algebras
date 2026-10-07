---
layout: default
file: "src/Classical/Structures/Lattice/Free/Term.lagda.md"
title: "Classical.Structures.Lattice.Free.Term module"
date: "2026-10-07"
author: "the agda-algebras development team"
---

### Lattice terms

This is the [Classical.Structures.Lattice.Free.Term][] module of the [Agda Universal Algebra Library][].

A *lattice term* over a set `X` of generators is a generator, a formal meet of two
lattice terms, or a formal join of two lattice terms.  The free lattice `FL(X)` is
the set of lattice terms modulo the equations that hold in every lattice, and
Whitman's solution to the word problem ([Freese, Ježek, and Nation (1995)][], Theorem
1.11) decides those equations by a structural recursion on pairs of terms.  This
module supplies the terms that recursion runs on.

The library already has terms over any signature: `Term X`{.AgdaDatatype} of
[Overture.Terms.Basic][], whose internal nodes carry an operation symbol and a
*function* from the symbol's arity to the children.  Over
`Sig-Lattice`{.AgdaFunction} a meet is `node ∧-Op (pair s t)`, and two such terms
with pointwise-equal children are equal only up to `_≐_`{.AgdaDatatype}, since
identifying the two child functions would take function extensionality.  That is
the right representation for equational logic, and the wrong one for a recursion
that compares terms by shape.  So the free-lattice development works over a
dedicated inductive type, `LatTerm X`{.AgdaDatatype}, whose binary constructors
take their children directly, and translates to and from `Term X`{.AgdaDatatype}
at the one place the two meet: the bridge to derivability of
[Classical.Structures.Lattice.Free.Derivability][].

The module provides the type, its rank, its evaluation in any
`Lattice`{.AgdaFunction}, and the two translations with their round trips.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Term where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Nat.Base                          using ( ℕ ; suc ; _+_ )
open import Data.Product                           using ( proj₁ )
open import Function                               using ( Func )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong₂ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Operations                 using ( pair )
open import Classical.Signatures.Lattice         using ( Sig-Lattice ; ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret       using ( interp-cong )
open import Classical.Structures.Lattice.Basic   using ( Lattice ; module Lattice-Op )
open import Overture.Terms {𝑆 = Sig-Lattice}     using ( Term ; ℊ ; node )
open import Setoid.Algebras.Basic                using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms.Basic                   using ( _≐_ ; module Environment )

open Func renaming ( to to _⟨$⟩_ )
open _≐_

private variable
  α ρ χ : Level
  X : Type χ
```
-->

#### The type of lattice terms

`LatTerm X`{.AgdaDatatype} has three constructors: `ℊ`{.AgdaInductiveConstructor}
embeds a generator (the same symbol `Term`{.AgdaDatatype} uses for its leaves),
and `_∧̇_`{.AgdaInductiveConstructor} and `_∨̇_`{.AgdaInductiveConstructor} form
the meet and the join of two terms.  The dot over the symbol marks the *formal*
operation, as the dot in `_≈̇_`{.AgdaInductiveConstructor} of
[Setoid.Varieties.SoundAndComplete][] marks a formal equation; the undotted `_∧_`
and `_∨_` remain the operations of a lattice.  The two formal operations share
the precedence of the lattice operations of `Lattice-Op`{.AgdaModule}.

```agda
data LatTerm (X : Type χ) : Type χ where
  ℊ    : X → LatTerm X
  _∧̇_  : LatTerm X → LatTerm X → LatTerm X
  _∨̇_  : LatTerm X → LatTerm X → LatTerm X

infixl 7 _∧̇_ _∨̇_
```

#### Rank

[Freese, Ježek, and Nation (1995)][], Section I.2, measure a term by its *rank*: a
generator has rank 1, and a meet or join of `k` terms has rank one more than the
sum of their ranks, so the rank counts the occurrences of generators plus the
pairs of parentheses.  `rank`{.AgdaFunction} is that measure on binary terms.  The
book's terms are `n`-ary and prefer `x ∨ y ∨ z` (rank 4) to `x ∨ (y ∨ z)` (rank 5);
a binary term always carries the second form, so its rank is that of the fully
parenthesized reading.  The canonical forms of Section I.3, which flatten
iterated joins and meets, live on a type of their own.

```agda
rank : LatTerm X → ℕ
rank (ℊ x)    = 1
rank (s ∧̇ t)  = suc (rank s + rank t)
rank (s ∨̇ t)  = suc (rank s + rank t)
```

#### Evaluation in a lattice

Given a lattice `𝑳`{.AgdaBound} and an assignment `η`{.AgdaBound} of elements of
`𝑳`{.AgdaBound} to the generators, `⟦ t ⟧ η`{.AgdaFunction} is the value of `t`
in `𝑳`{.AgdaBound}: generators go to their values under `η`{.AgdaBound}, and the
formal operations to the curried operations of `Lattice-Op`{.AgdaModule}.
Evaluation is collected in the module `Evaluation`{.AgdaModule}, parameterized by
the lattice, in the way `Environment`{.AgdaModule} of [Setoid.Terms.Basic][]
collects the evaluation of `Term`{.AgdaDatatype}; a consumer opens it at the
lattice it works in.  `⟦⟧-cong`{.AgdaFunction} says that evaluation respects
pointwise equality of assignments.

```agda
module Evaluation (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳                 using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong )
  open Setoid 𝔻[ proj₁ 𝑳 ]          using ( _≈_ )

  ⟦_⟧ : LatTerm X → (X → 𝕌[ proj₁ 𝑳 ]) → 𝕌[ proj₁ 𝑳 ]
  ⟦ ℊ x ⟧    η = η x
  ⟦ s ∧̇ t ⟧  η = ⟦ s ⟧ η ∧ ⟦ t ⟧ η
  ⟦ s ∨̇ t ⟧  η = ⟦ s ⟧ η ∨ ⟦ t ⟧ η

  ⟦⟧-cong : (t : LatTerm X) {η η' : X → 𝕌[ proj₁ 𝑳 ]}
    → (∀ x → η x ≈ η' x) → ⟦ t ⟧ η ≈ ⟦ t ⟧ η'
  ⟦⟧-cong (ℊ x)    η≈η' = η≈η' x
  ⟦⟧-cong (s ∧̇ t)  η≈η' = ∧-cong (⟦⟧-cong s η≈η') (⟦⟧-cong t η≈η')
  ⟦⟧-cong (s ∨̇ t)  η≈η' = ∨-cong (⟦⟧-cong s η≈η') (⟦⟧-cong t η≈η')
```

#### Translation to and from `Term`

`toTerm`{.AgdaFunction} sends a lattice term to the `Term`{.AgdaDatatype} over
`Sig-Lattice`{.AgdaFunction} with the same shape, packing the two children of each
node with `pair`{.AgdaFunction}; `fromTerm`{.AgdaFunction} reads the children of a
`node`{.AgdaInductiveConstructor} back at the two positions `0F` and `1F` of its
arity `Fin 2`.

```agda
toTerm : LatTerm X → Term X
toTerm (ℊ x)    = ℊ x
toTerm (s ∧̇ t)  = node ∧-Op (pair (toTerm s) (toTerm t))
toTerm (s ∨̇ t)  = node ∨-Op (pair (toTerm s) (toTerm t))

fromTerm : Term X → LatTerm X
fromTerm (ℊ x)           = ℊ x
fromTerm (node ∧-Op ts)  = fromTerm (ts 0F) ∧̇ fromTerm (ts 1F)
fromTerm (node ∨-Op ts)  = fromTerm (ts 0F) ∨̇ fromTerm (ts 1F)
```

The round trips differ in strength, and the difference is the reason
`LatTerm`{.AgdaDatatype} exists.  Reading a translated lattice term back gives the
term itself, up to `_≡_`{.AgdaDatatype}, by induction (`fromTerm-toTerm`{.AgdaFunction}).
Translating a read-back `Term`{.AgdaDatatype} gives a term whose child functions
are `pair`{.AgdaFunction}`(ts 0F) (ts 1F)` rather than `ts`{.AgdaBound}; these
agree at every position without being equal functions, so the round trip holds up
to the inductive term equality `_≐_`{.AgdaDatatype} of [Setoid.Terms.Basic][]
(`toTerm-fromTerm`{.AgdaFunction}).

```agda
fromTerm-toTerm : (t : LatTerm X) → fromTerm (toTerm t) ≡ t
fromTerm-toTerm (ℊ x)    = refl
fromTerm-toTerm (s ∧̇ t)  = cong₂ _∧̇_ (fromTerm-toTerm s) (fromTerm-toTerm t)
fromTerm-toTerm (s ∨̇ t)  = cong₂ _∨̇_ (fromTerm-toTerm s) (fromTerm-toTerm t)

toTerm-fromTerm : (p : Term X) → toTerm (fromTerm p) ≐ p
toTerm-fromTerm (ℊ x)           = rfl refl
toTerm-fromTerm (node ∧-Op ts)  =
  gnl λ { 0F → toTerm-fromTerm (ts 0F) ; 1F → toTerm-fromTerm (ts 1F) }
toTerm-fromTerm (node ∨-Op ts)  =
  gnl λ { 0F → toTerm-fromTerm (ts 0F) ; 1F → toTerm-fromTerm (ts 1F) }
```

#### The translations preserve values

In every lattice the two translations preserve the value of a term under every
assignment, where a `Term`{.AgdaDatatype} is evaluated by the generic
`Environment`{.AgdaModule} of [Setoid.Terms.Basic][] (here renamed `⟦_⟧ᵀ` to keep
it apart from the evaluation of lattice terms).  Each proof is an induction that,
at a node, feeds the two inductive hypotheses at positions `0F` and `1F` to
`interp-cong`{.AgdaFunction}.  These two lemmas are what let a theorem about
`LatTerm`{.AgdaDatatype} speak about `Term`{.AgdaDatatype}, and conversely.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Environment (proj₁ 𝑳)  using () renaming ( ⟦_⟧ to ⟦_⟧ᵀ )
  open Evaluation 𝑳           using ( ⟦_⟧ )
  open Setoid 𝔻[ proj₁ 𝑳 ]    using ( _≈_ ) renaming ( refl to ≈refl )

  ⟦toTerm⟧ : (t : LatTerm X) (η : X → 𝕌[ proj₁ 𝑳 ]) → ⟦ toTerm t ⟧ᵀ ⟨$⟩ η ≈ ⟦ t ⟧ η
  ⟦toTerm⟧ (ℊ x)    η = ≈refl
  ⟦toTerm⟧ (s ∧̇ t)  η =
    interp-cong (proj₁ 𝑳) ∧-Op λ { 0F → ⟦toTerm⟧ s η ; 1F → ⟦toTerm⟧ t η }
  ⟦toTerm⟧ (s ∨̇ t)  η =
    interp-cong (proj₁ 𝑳) ∨-Op λ { 0F → ⟦toTerm⟧ s η ; 1F → ⟦toTerm⟧ t η }

  ⟦fromTerm⟧ : (p : Term X) (η : X → 𝕌[ proj₁ 𝑳 ]) → ⟦ p ⟧ᵀ ⟨$⟩ η ≈ ⟦ fromTerm p ⟧ η
  ⟦fromTerm⟧ (ℊ x)           η = ≈refl
  ⟦fromTerm⟧ (node ∧-Op ts)  η =
    interp-cong (proj₁ 𝑳) ∧-Op λ { 0F → ⟦fromTerm⟧ (ts 0F) η ; 1F → ⟦fromTerm⟧ (ts 1F) η }
  ⟦fromTerm⟧ (node ∨-Op ts)  η =
    interp-cong (proj₁ 𝑳) ∨-Op λ { 0F → ⟦fromTerm⟧ (ts 0F) η ; 1F → ⟦fromTerm⟧ (ts 1F) η }
```
