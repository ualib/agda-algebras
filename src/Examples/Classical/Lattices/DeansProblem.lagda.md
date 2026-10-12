---
layout: default
file: "src/Examples/Classical/Lattices/DeansProblem.lagda.md"
title: "Examples.Classical.Lattices.DeansProblem module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Worked example: Freese's step toward Dean's problem

This is the [Examples.Classical.Lattices.DeansProblem][] module of the [Agda Universal Algebra Library][].

Dean asked whether a free lattice can have an infinite ascending chain of
sublattices, each isomorphic to `FL(3)`.  A descending chain is easy, since
`FL(3)` has proper sublattices isomorphic to itself, and one might hope to rule
out an ascending chain by showing that whenever `{a, b, c}` and `{a', b', c'}`
freely generate copies of `FL(3)` with `⟨a, b, c⟩ ⊆ ⟨a', b', c'⟩`, the primed
generators occur as subterms of `a`, `b`, and `c`.  Freese ("Notes on Dean's
problem", 1997) gives an example showing that this is not so, and this module
checks it by evaluation.

The example lives in the free lattice on nine generators
`a₁, a₂₁, a₂₂, b₁, b₂₁, b₂₂, c₁, c₂₁, c₂₂`.  Freese's program finds elements
`ā₁, ā₂₁, ā₂₂` (and `b̄₁, …, c̄₂₂` by the cyclic permutation `a ↦ b ↦ c ↦ a` of
the letters) satisfying twelve relations, among them `ā₂₁ ≥ c̄₁` and
`ā₂₁ ≥ b̄₂₁ ∧ b̄₂₂`.  He sets `a = ā₁ ∨ (ā₂₁ ∧ ā₂₂)` and `a' = a ∧ b̄₂₁ ∧ c̄₂₂`,
with `b`, `c`, `b'`, `c'` again by the permutation, and claims the following:

+  `{a, b, c}` and `{a', b', c'}` each freely generate a sublattice isomorphic to
   `FL(3)`;
+  `⟨a, b, c⟩` is properly contained in `⟨a', b', c'⟩`; indeed
   `a = a' ∨ (b' ∧ c')`, the term his Figure 1 suggests, and symmetrically.

Each claim is checked below by decisions of Whitman's procedure and of the free
generation test of [Classical.Structures.Lattice.Free.Generation][], evaluated
while the module is checked and turned into theorems by `from-yes` or `from-no`.
The proper containment then follows from Corollary 1.6 of [Freese, Ježek, and
Nation (1995)][]: `a'` lies in `⟨a, b, c⟩` only if the generator `x` of `FL(3)` is
one of the three terms `x ∨ (y ∧ z)`, `y ∨ (z ∧ x)`, `z ∨ (x ∧ y)` that express
`a`, `b`, `c` in `a'`, `b'`, `c'`, and it is none of them.

**One misprint**.  The notes also display the canonical form of `a`.  Its third
joinand, as printed, has the meetands `b₁ ∨ a₂₂ ∨ b₂₁` and
`a₁ ∨ c₁ ∨ a₂₁ ∨ b₂₂ ∨ c₂₂`, where the canonical form computed from the printed
`ā₁`, `ā₂₁`, `ā₂₂` has `a₂₂ ∨ b₁ ∨ c₂₁` and `a₁ ∨ a₂₁ ∨ b₂₁ ∨ c₁ ∨ c₂₂`, which
are meetands of the printed `ā₂₂` and `ā₂₁`.  The displayed expression is not
equal to `a`; `a` does not even lie below it (`misprint`{.AgdaFunction}).  The printed `ā`'s satisfy all twelve
relations, so the misprint is in the display of the canonical form, and Freese's
claims, which are about `a` as defined, stand.

**Cost**.  Whitman's procedure is exponential in the worst case, and on terms of
this size each decision takes up to a few seconds and a few gigabytes; run on the
defining terms, the checks of this module exhaust the 6 GB heap the build allows.
So the decisions run on smaller terms equal to the defined ones: the canonical form
of `a`, and the notes' own simplification `a' = a ∧ (a₁ ∨ b₂₁ ∨ c₂₂)`.  Each
replacement is checked equal to the original, and free generation and containment
carry over along equality.  The cases of `b` and `c` follow from the case of `a`
by applying the permutation, an automorphism of `FL(9)`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Examples.Classical.Lattices.DeansProblem where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F
                                                         ; 7F ; 8F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( allFin )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin )
open import Data.Product                           using ( _,_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong₂ ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Free.Canonical.Basic
                                                   using ( ≈ʷ-sym ; ≈ʷ-trans )
open import Classical.Structures.Lattice.Free.Generation
                                                   using ( FreelyGenerates ; freelyGenerates-resp
                                                         ; freelyGenerates→injective
                                                         ; free-generator-in-image ; module Decide )
open import Classical.Structures.Lattice.Free.Substitution
                                                   using ( Sub ; _[_] ; _⨟_ ; []-mono ; []-cong
                                                         ; []-congʳ )
open import Classical.Structures.Lattice.Free.Term using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Classical.Structures.Lattice.Free.Whitman
                                                   using ( _≤ʷ_ ; _≈ʷ_ ; module Decision )
```
-->

#### The nine generators and the permutation

The generators are `ℊ 0F` through `ℊ 8F`, in the order Freese lists them.  The
cyclic permutation `a ↦ b ↦ c ↦ a` of the letters is a substitution,
`π`{.AgdaFunction}; applying it to a term over the `a`-generators gives the
corresponding term over the `b`-generators, and applying it twice gives the
`c`-generators.  Applied three times it is the identity (`π³`{.AgdaFunction}), so
it is an automorphism of `FL(9)`, and by `[]-mono`{.AgdaFunction} and
`[]-cong`{.AgdaFunction} of [Classical.Structures.Lattice.Free.Substitution][] it
carries every inequality and equation to its image.

```agda
a₁ a₂₁ a₂₂ b₁ b₂₁ b₂₂ c₁ c₂₁ c₂₂ : LatTerm (Fin 9)
a₁   = ℊ 0F
a₂₁  = ℊ 1F
a₂₂  = ℊ 2F
b₁   = ℊ 3F
b₂₁  = ℊ 4F
b₂₂  = ℊ 5F
c₁   = ℊ 6F
c₂₁  = ℊ 7F
c₂₂  = ℊ 8F

π : Sub (Fin 9) (Fin 9)
π 0F = b₁
π 1F = b₂₁
π 2F = b₂₂
π 3F = c₁
π 4F = c₂₁
π 5F = c₂₂
π 6F = a₁
π 7F = a₂₁
π 8F = a₂₂

π³-ℊ : (x : Fin 9) → π x [ π ] [ π ] ≡ ℊ x
π³-ℊ 0F = refl
π³-ℊ 1F = refl
π³-ℊ 2F = refl
π³-ℊ 3F = refl
π³-ℊ 4F = refl
π³-ℊ 5F = refl
π³-ℊ 6F = refl
π³-ℊ 7F = refl
π³-ℊ 8F = refl

π³ : (t : LatTerm (Fin 9)) → t [ π ] [ π ] [ π ] ≡ t
π³ (ℊ x)    = π³-ℊ x
π³ (s ∧̇ t)  = cong₂ _∧̇_ (π³ s) (π³ t)
π³ (s ∨̇ t)  = cong₂ _∨̇_ (π³ s) (π³ t)
```

#### Freese's solution

These are the elements `ā₁`, `ā₂₁`, and `ā₂₂` exactly as the notes print them,
with each join and meet of several terms nested to the left, and the images under
`π`{.AgdaFunction} and its square that the relations mention.

```agda
ā₁ ā₂₁ ā₂₂ : LatTerm (Fin 9)
ā₁ = a₁ ∨̇ ((a₁ ∨̇ b₂₁ ∨̇ c₂₂) ∧̇ (c₁ ∨̇ a₂₁ ∨̇ b₂₂)
           ∧̇ (a₁ ∨̇ b₁ ∨̇ a₂₂ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₁)
           ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₂))
        ∨̇ ((a₁ ∨̇ b₂₁ ∨̇ c₂₂) ∧̇ (b₁ ∨̇ a₂₂ ∨̇ c₂₁)
           ∧̇ (a₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₂ ∨̇ c₂₂) ∧̇ (b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₂ ∨̇ c₂₁)
           ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₂))
ā₂₁ = a₂₁ ∨̇ ((a₂₁ ∨̇ b₂₂ ∨̇ c₁) ∧̇ (a₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₁ ∨̇ c₂₂)
            ∧̇ (a₂₂ ∨̇ b₁ ∨̇ b₂₂ ∨̇ c₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ a₂₁ ∨̇ b₁ ∨̇ b₂₁ ∨̇ c₁ ∨̇ c₂₁)
            ∧̇ (a₁ ∨̇ a₂₂ ∨̇ b₁ ∨̇ b₂₁ ∨̇ c₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ a₂₂ ∨̇ b₁ ∨̇ b₂₁ ∨̇ c₁ ∨̇ c₂₂)
            ∧̇ (a₁ ∨̇ a₂₂ ∨̇ b₁ ∨̇ b₂₂ ∨̇ c₁ ∨̇ c₂₂))
ā₂₂ = a₂₂ ∨̇ ((a₂₂ ∨̇ b₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ a₂₂ ∨̇ b₁ ∨̇ b₂₁ ∨̇ c₂₂)
            ∧̇ (a₂₁ ∨̇ b₁ ∨̇ b₂₂ ∨̇ c₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ a₂₁ ∨̇ b₁ ∨̇ b₂₁ ∨̇ c₁ ∨̇ c₂₁)
            ∧̇ (a₁ ∨̇ a₂₁ ∨̇ b₁ ∨̇ b₂₁ ∨̇ c₁ ∨̇ c₂₂) ∧̇ (a₁ ∨̇ a₂₁ ∨̇ b₁ ∨̇ b₂₂ ∨̇ c₁ ∨̇ c₂₂)
            ∧̇ (a₁ ∨̇ a₂₂ ∨̇ b₁ ∨̇ b₂₂ ∨̇ c₁ ∨̇ c₂₂))

b̄₁ b̄₂₁ b̄₂₂ c̄₁ c̄₂₁ c̄₂₂ : LatTerm (Fin 9)
b̄₁   = ā₁ [ π ]
b̄₂₁  = ā₂₁ [ π ]
b̄₂₂  = ā₂₂ [ π ]
c̄₁   = ā₁ [ π ] [ π ]
c̄₂₁  = ā₂₁ [ π ] [ π ]
c̄₂₂  = ā₂₂ [ π ] [ π ]
```

#### The twelve relations

Freese's relations (1) to (4) for the `a` column are decided directly
(`relation-1`{.AgdaFunction} to `relation-4`{.AgdaFunction}): `ā₂₁ ≥ c̄₁`,
`ā₂₂ ≥ b̄₁`, `ā₂₁ ≥ b̄₂₁ ∧ b̄₂₂`, and `ā₂₂ ≥ c̄₂₁ ∧ c̄₂₂`.  The `b` and `c` columns
are their images under `π`{.AgdaFunction}, by `[]-mono`{.AgdaFunction} and
`π³`{.AgdaFunction} (`relation-1ᵇ`{.AgdaFunction} to
`relation-4ᶜ`{.AgdaFunction}).  Since the relations are what Freese's program
solved for, they are a check on the transcription of the `ā`'s.

```agda
open Decision (_≟_ {9}) using ( _≤ʷ?_ ; _≈ʷ?_ )

relation-1 : c̄₁ ≤ʷ ā₂₁
relation-1 = from-yes (c̄₁ ≤ʷ? ā₂₁)

relation-2 : b̄₁ ≤ʷ ā₂₂
relation-2 = from-yes (b̄₁ ≤ʷ? ā₂₂)

relation-3 : b̄₂₁ ∧̇ b̄₂₂ ≤ʷ ā₂₁
relation-3 = from-yes (b̄₂₁ ∧̇ b̄₂₂ ≤ʷ? ā₂₁)

relation-4 : c̄₂₁ ∧̇ c̄₂₂ ≤ʷ ā₂₂
relation-4 = from-yes (c̄₂₁ ∧̇ c̄₂₂ ≤ʷ? ā₂₂)

relation-1ᵇ : ā₁ ≤ʷ b̄₂₁
relation-1ᵇ = subst (_≤ʷ b̄₂₁) (π³ ā₁) ([]-mono π relation-1)

relation-2ᵇ : c̄₁ ≤ʷ b̄₂₂
relation-2ᵇ = []-mono π relation-2

relation-3ᵇ : c̄₂₁ ∧̇ c̄₂₂ ≤ʷ b̄₂₁
relation-3ᵇ = []-mono π relation-3

relation-4ᵇ : ā₂₁ ∧̇ ā₂₂ ≤ʷ b̄₂₂
relation-4ᵇ = subst₂ (λ s t → s ∧̇ t ≤ʷ b̄₂₂) (π³ ā₂₁) (π³ ā₂₂) ([]-mono π relation-4)

relation-1ᶜ : b̄₁ ≤ʷ c̄₂₁
relation-1ᶜ = []-mono π relation-1ᵇ

relation-2ᶜ : ā₁ ≤ʷ c̄₂₂
relation-2ᶜ = subst (_≤ʷ c̄₂₂) (π³ ā₁) ([]-mono π relation-2ᵇ)

relation-3ᶜ : ā₂₁ ∧̇ ā₂₂ ≤ʷ c̄₂₁
relation-3ᶜ = subst₂ (λ s t → s ∧̇ t ≤ʷ c̄₂₁) (π³ ā₂₁) (π³ ā₂₂) ([]-mono π relation-3ᵇ)

relation-4ᶜ : b̄₂₁ ∧̇ b̄₂₂ ≤ʷ c̄₂₂
relation-4ᶜ = []-mono π relation-4ᵇ
```

#### The two triples, as defined

`a`, `b`, `c` and `a'`, `b'`, `c'` are defined as in the notes, and each triple is
a substitution from the three generators of `FL(3)`.

```agda
a b c a' b' c' : LatTerm (Fin 9)
a   = ā₁ ∨̇ (ā₂₁ ∧̇ ā₂₂)
b   = a [ π ]
c   = a [ π ] [ π ]
a'  = a ∧̇ b̄₂₁ ∧̇ c̄₂₂
b'  = a' [ π ]
c'  = a' [ π ] [ π ]

abc abc' : Sub (Fin 3) (Fin 9)
abc 0F   = a
abc 1F   = b
abc 2F   = c
abc' 0F  = a'
abc' 1F  = b'
abc' 2F  = c'
```

#### Equal and smaller terms

`â`{.AgdaFunction} is the canonical form of `a`, as `canonical`{.AgdaFunction} of
[Classical.Structures.Lattice.Free.Canonical.Algorithm][] computes it (that
computation is too slow to repeat at every build, so here `â`{.AgdaFunction} is
written out and only checked equal to `a`: `a≈â`{.AgdaFunction}).  The display in
the notes, `a-as-printed`{.AgdaFunction}, differs in two meetands, and `a` does
not lie below it (`misprint`{.AgdaFunction}).  `a″`{.AgdaFunction} is the notes'
simplification of `a'`, with `â`{.AgdaFunction} for `a`, and is checked equal to
`a'` (`a'≈a″`{.AgdaFunction}).

```agda
â a-as-printed a″ : LatTerm (Fin 9)
â = a₁ ∨̇ ((a₁ ∨̇ b₂₁ ∨̇ c₂₂) ∧̇ (c₁ ∨̇ a₂₁ ∨̇ b₂₂)
           ∧̇ (a₁ ∨̇ b₁ ∨̇ a₂₂ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₁)
           ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₂))
       ∨̇ ((a₁ ∨̇ b₂₁ ∨̇ c₂₂) ∧̇ (b₁ ∨̇ a₂₂ ∨̇ c₂₁)
           ∧̇ (a₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₂ ∨̇ c₂₂) ∧̇ (b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₂ ∨̇ c₂₁)
           ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₂))
       ∨̇ ((a₂₁ ∨̇ b₂₂ ∨̇ c₁) ∧̇ (a₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₁ ∨̇ c₂₂)
           ∧̇ (a₁ ∨̇ a₂₁ ∨̇ b₁ ∨̇ b₂₁ ∨̇ c₁ ∨̇ c₂₁) ∧̇ (a₂₂ ∨̇ b₁ ∨̇ c₂₁)
           ∧̇ (a₁ ∨̇ a₂₂ ∨̇ b₁ ∨̇ b₂₁ ∨̇ c₂₂) ∧̇ (a₁ ∨̇ a₂₂ ∨̇ b₁ ∨̇ b₂₂ ∨̇ c₁ ∨̇ c₂₂))
a-as-printed =
  a₁ ∨̇ ((a₁ ∨̇ b₂₁ ∨̇ c₂₂) ∧̇ (c₁ ∨̇ a₂₁ ∨̇ b₂₂)
        ∧̇ (a₁ ∨̇ b₁ ∨̇ a₂₂ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₁)
        ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₂))
     ∨̇ ((a₁ ∨̇ b₂₁ ∨̇ c₂₂) ∧̇ (b₁ ∨̇ a₂₂ ∨̇ c₂₁)
        ∧̇ (a₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₂ ∨̇ c₂₂) ∧̇ (b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₂ ∨̇ c₂₁)
        ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₂))
     ∨̇ ((c₁ ∨̇ a₂₁ ∨̇ b₂₂) ∧̇ (b₁ ∨̇ a₂₂ ∨̇ b₂₁)
        ∧̇ (a₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₂ ∨̇ c₂₂) ∧̇ (a₁ ∨̇ b₁ ∨̇ a₂₂ ∨̇ b₂₁ ∨̇ c₂₂)
        ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₁ ∨̇ b₂₁ ∨̇ c₂₁) ∧̇ (a₁ ∨̇ b₁ ∨̇ c₁ ∨̇ a₂₂ ∨̇ b₂₂ ∨̇ c₂₂))
a″ = â ∧̇ (a₁ ∨̇ b₂₁ ∨̇ c₂₂)

a≈â : a ≈ʷ â
a≈â = from-yes (a ≈ʷ? â)

misprint : ¬ (a ≤ʷ a-as-printed)
misprint = from-no (a ≤ʷ? a-as-printed)

a'≈a″ : a' ≈ʷ a″
a'≈a″ = from-yes (a' ≈ʷ? a″)
```

The working triples `abĉ`{.AgdaFunction} and `abc″`{.AgdaFunction} are the images
of `â`{.AgdaFunction} and `a″`{.AgdaFunction} under the permutation, and they agree
with the defined triples pointwise (`abc≈abĉ`{.AgdaFunction},
`abc'≈abc″`{.AgdaFunction}): the case of `a` is decided above, and the cases of
`b` and `c` are its images under `π`{.AgdaFunction}.

```agda
abĉ abc″ : Sub (Fin 3) (Fin 9)
abĉ 0F   = â
abĉ 1F   = â [ π ]
abĉ 2F   = â [ π ] [ π ]
abc″ 0F  = a″
abc″ 1F  = a″ [ π ]
abc″ 2F  = a″ [ π ] [ π ]

abc≈abĉ : ∀ i → abc i ≈ʷ abĉ i
abc≈abĉ 0F = a≈â
abc≈abĉ 1F = []-cong π a≈â
abc≈abĉ 2F = []-cong π ([]-cong π a≈â)

abc'≈abc″ : ∀ i → abc' i ≈ʷ abc″ i
abc'≈abc″ 0F = a'≈a″
abc'≈abc″ 1F = []-cong π a'≈a″
abc'≈abc″ 2F = []-cong π ([]-cong π a'≈a″)
```

#### Both triples freely generate

`freelyGenerates?`{.AgdaFunction} decides Corollary 1.13's condition by six
decisions of Whitman's procedure for each triple (each element against the join
and against the meet of the other two).  Both working triples pass, and by
`freelyGenerates-resp`{.AgdaFunction} so do the defined ones: each generates a
sublattice isomorphic to `FL(3)` (`abc-free`{.AgdaFunction},
`abc'-free`{.AgdaFunction}).

```agda
open Decide (_≟_ {3}) (allFin 3) ∈-allFin (_≟_ {9}) using ( freelyGenerates? )

abĉ-free : FreelyGenerates abĉ
abĉ-free = from-yes (freelyGenerates? abĉ)

abc″-free : FreelyGenerates abc″
abc″-free = from-yes (freelyGenerates? abc″)

abc-free : FreelyGenerates abc
abc-free = freelyGenerates-resp (λ i → ≈ʷ-sym (abc≈abĉ i)) abĉ-free

abc'-free : FreelyGenerates abc'
abc'-free = freelyGenerates-resp (λ i → ≈ʷ-sym (abc'≈abc″ i)) abc″-free
```

#### Containment

In `FL(3)`, with generators `x`, `y`, `z`, the substitution `ρ`{.AgdaFunction}
sends each generator to the term that expresses the corresponding unprimed element
in the primed ones.  The equation `â = a″ ∨ (b″ ∧ c″)` is decided
(`â≈`{.AgdaFunction}), and its images under `π`{.AgdaFunction} and its square are
the other two cases (`abĉ≈`{.AgdaFunction}); through the equalities above, `a`
equals `a' ∨ (b' ∧ c')`, and symmetrically (`abc≈`{.AgdaFunction}).  So every
element of `⟨a, b, c⟩` lies in `⟨a', b', c'⟩`: the value of a term `t` at
`a, b, c` is its value under the composite substitution `ρ ⨟ abc'`, which is the
value of `t [ ρ ]` at `a', b', c'` (`⟨abc⟩⊆⟨abc'⟩`{.AgdaFunction}).

```agda
x y z : LatTerm (Fin 3)
x = ℊ 0F
y = ℊ 1F
z = ℊ 2F

ρ : Sub (Fin 3) (Fin 3)
ρ 0F = x ∨̇ (y ∧̇ z)
ρ 1F = y ∨̇ (z ∧̇ x)
ρ 2F = z ∨̇ (x ∧̇ y)

â≈ : â ≈ʷ a″ ∨̇ (a″ [ π ] ∧̇ a″ [ π ] [ π ])
â≈ = from-yes (â ≈ʷ? a″ ∨̇ (a″ [ π ] ∧̇ a″ [ π ] [ π ]))

abĉ≈ : ∀ i → abĉ i ≈ʷ ρ i [ abc″ ]
abĉ≈ 0F = â≈
abĉ≈ 1F = subst (λ w → â [ π ] ≈ʷ a″ [ π ] ∨̇ (a″ [ π ] [ π ] ∧̇ w)) (π³ a″) ([]-cong π â≈)
abĉ≈ 2F = subst (λ w → â [ π ] [ π ] ≈ʷ a″ [ π ] [ π ] ∨̇ (w ∧̇ a″ [ π ])) (π³ a″)
                ([]-cong π (abĉ≈ 1F))

abc≈ : ∀ i → abc i ≈ʷ ρ i [ abc' ]
abc≈ i = ≈ʷ-trans (abc≈abĉ i) (≈ʷ-trans (abĉ≈ i) ([]-congʳ (ρ i) λ j → ≈ʷ-sym (abc'≈abc″ j)))

⟨abc⟩⊆⟨abc'⟩ : (t : LatTerm (Fin 3)) → t [ abc ] ≈ʷ t [ ρ ⨟ abc' ]
⟨abc⟩⊆⟨abc'⟩ t = []-congʳ t abc≈
```

#### Proper containment

The generator `x` of `FL(3)` is none of the three terms `ρ i`
(`x∉ρ`{.AgdaFunction}), each decided in `FL(3)`.  So by Corollary 1.6,
transported through the embedding `abc'`{.AgdaFunction}
(`free-generator-in-image`{.AgdaFunction}), `a'` is not the value under
`ρ ⨟ abc'` of any term; and since every element of `⟨a, b, c⟩` is such a value,
`a'` is not in `⟨a, b, c⟩` (`a'∉⟨abc⟩`{.AgdaFunction}).  The containment of the
two free sublattices is proper.

```agda
open Decision (_≟_ {3}) using () renaming ( _≈ʷ?_ to _≈ʷ?₃_ )

x∉ρ : ∀ i → ¬ (x ≈ʷ ρ i)
x∉ρ 0F = from-no (x ≈ʷ?₃ ρ 0F)
x∉ρ 1F = from-no (x ≈ʷ?₃ ρ 1F)
x∉ρ 2F = from-no (x ≈ʷ?₃ ρ 2F)

a'∉⟨abc⟩ : (t : LatTerm (Fin 3)) → ¬ (t [ abc ] ≈ʷ a')
a'∉⟨abc⟩ t e =
  let (i , x≈) = free-generator-in-image abc' (freelyGenerates→injective abc' abc'-free) ρ t {0F}
                   (≈ʷ-trans (≈ʷ-sym e) (⟨abc⟩⊆⟨abc'⟩ t))
  in x∉ρ i x≈
```
