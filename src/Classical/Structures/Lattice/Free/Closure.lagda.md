---
layout: default
file: "src/Classical/Structures/Lattice/Free/Closure.lagda.md"
title: "Classical.Structures.Lattice.Free.Closure module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Solutions of lattice equations and their closure

This is the [Classical.Structures.Lattice.Free.Closure][] module of the [Agda Universal Algebra Library][].

McNulty's free-lattice Nullstellensatz problem (McNulty, "A juggler's dozen of
easy problems", Algebra Universalis 74, 2015) is posed in these terms.  An
*equation* over generators `X` is a pair `(s , t)` of lattice terms.  A
*solution* of a set `Σ` of equations is an assignment of elements of `FL(X)` to
the generators, that is, a substitution `σ` from `X` to `X`, under which each
equation of `Σ` becomes an equality of `FL(X)`: `s [ σ ] = t [ σ ]`.  The
equations that hold under *every* solution of `Σ` form its *closure*, and
McNulty asks for a characterization of this closure operator on the congruences
of `FL(n)`, in the way Hilbert's Nullstellensatz characterizes the polynomials
that vanish on the common zeros of a set of polynomials.

This module supplies the vocabulary and the first facts.  The equations a
substitution solves are the pairs in the kernel of the homomorphism it induces,
a congruence of `FL(X)`; for a finite list of equations, whether a given
substitution solves them is decidable.  The closure of a list of equations
contains the congruence the list generates, since every kernel containing the
list contains that congruence.  An equation outside the closure has a
*refutation certificate*, a substitution that solves the list but not the
equation, and a certificate is checked by evaluation.  In the other direction,
an equation lies outside the generated congruence as soon as some homomorphism
into any lattice identifies the pairs of the list and separates the two sides
of the equation.

Following McNulty, the closure quantifies over endomorphisms of `FL(X)`, the
substitutions from `X` to `X`; solutions in a different free lattice are not
part of the definition.  In the text a list of equations is `Σ`; in the code it
is `E`, since `Σ` names the standard library's dependent pair type.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Closure where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Base                         using ( List )
open import Data.List.Membership.Propositional     using ( _∈_ ; find )
open import Data.List.Relation.Unary.All           using ( All ; all? ; lookup ; tabulate )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( refl )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; _×-dec_ ; ¬? )

import Data.List.Relation.Unary.Any as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic             using ( Lattice )
open import Classical.Structures.Lattice.Free.Canonical.Basic
                                                           using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import Classical.Structures.Lattice.Free.Substitution using ( Sub ; _[_] ; []-cong
                                                                 ; subst-hom )
open import Classical.Structures.Lattice.Free.Term         using ( LatTerm ; module Evaluation )
open import Classical.Structures.Lattice.Free.Universal    using ( FL ; FL-extend-hom ; ≈ʷ-sound )
open import Classical.Structures.Lattice.Free.Whitman      using ( _≈ʷ_ ; module Decision )
open import Setoid.Algebras.Basic                          using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic                       using ( Con )
open import Setoid.Congruences.Generation                  using ( Gen ; Cg-least )
open import Setoid.Congruences.Presented.Basic             using ( fromPairs )
open import Setoid.Homomorphisms.Kernels                   using ( kercon )

open Func using () renaming ( to to _⟨$⟩_ )

private variable
  α ρ χ υ : Level
  X : Type χ
  Y : Type υ
  s t : LatTerm X
```
-->

#### The kernel of a substitution

The kernel of the homomorphism `subst-hom σ`{.AgdaFunction} is a congruence of
`FL(X)` (`subst-kernel`{.AgdaFunction}), by the library's `kercon`{.AgdaFunction}
of [Setoid.Homomorphisms.Kernels][].  It relates `s` and `t` exactly when
`s [ σ ]` and `t [ σ ]` are equal in `FL(Y)`, and it does so by definition, since
the homomorphism's underlying map is substitution.

```agda
subst-kernel : {X : Type χ} {Y : Type υ} (σ : Sub X Y) → Con (proj₁ (FL X)) υ
subst-kernel σ = kercon (subst-hom σ)
```

#### Solutions of a list of equations

A substitution `σ` *solves* a list `E` of equations if it makes the two sides of
each equal (`Solves`{.AgdaFunction}).  With decidable equality of the generators
of the target, this is decided equation by equation, each by Whitman's procedure
(`solves?`{.AgdaFunction}).

```agda
Solves : {X : Type χ} {Y : Type υ} → Sub X Y → List (LatTerm X × LatTerm X) → Type (χ ⊔ υ)
Solves σ E = All (λ e → proj₁ e [ σ ] ≈ʷ proj₂ e [ σ ]) E

module _ {Y : Type υ} (_≟_ : DecidableEquality Y) where
  open Decision _≟_ using ( _≈ʷ?_ )

  solves? : (σ : Sub X Y) (E : List (LatTerm X × LatTerm X)) → Dec (Solves σ E)
  solves? σ E = all? (λ e → proj₁ e [ σ ] ≈ʷ? proj₂ e [ σ ]) E
```

#### The congruence generated by a list of equations

`InCg E (s , t)`{.AgdaFunction} says that `(s , t)` lies in the congruence of
`FL(X)` generated by the equations of `E`.  It is the relation
`Gen (fromPairs E)`{.AgdaDatatype} of the Congruence Generation Theorem of
[Setoid.Congruences.Generation][], at the algebra `FL(X)`, where
`fromPairs E`{.AgdaFunction} of [Setoid.Congruences.Presented.Basic][] relates
every pair of terms equal in `FL(X)` to the two sides of an equation of `E`.  The
algebra is given explicitly, since the carrier `LatTerm X`{.AgdaDatatype} does
not determine it.

```agda
InCg : {X : Type χ} → List (LatTerm X × LatTerm X) → LatTerm X × LatTerm X → Type χ
InCg {X = X} E (s , t) = Gen {𝑨 = proj₁ (FL X)} (fromPairs {𝑨 = proj₁ (FL X)} E) s t
```

To solve `E` is to have a kernel containing the relation `E` presents
(`Solves→⊆kernel`{.AgdaFunction}, `⊆kernel→Solves`{.AgdaFunction}).  The kernel
of a solution therefore contains the congruence generated by `E`
(`Solves→InCg⊆kernel`{.AgdaFunction}), the least congruence containing that
relation.

```agda
module _ {X : Type χ} {Y : Type υ} (σ : Sub X Y) {E : List (LatTerm X × LatTerm X)} where
  Solves→⊆kernel : Solves σ E → fromPairs {𝑨 = proj₁ (FL X)} E s t → s [ σ ] ≈ʷ t [ σ ]
  Solves→⊆kernel sol r =
    let (e , e∈ , s≈ , t≈) = find r
    in ≈ʷ-trans ([]-cong σ s≈) (≈ʷ-trans (lookup sol e∈) (≈ʷ-sym ([]-cong σ t≈)))

  ⊆kernel→Solves : (∀ {s t} → fromPairs {𝑨 = proj₁ (FL X)} E s t → s [ σ ] ≈ʷ t [ σ ])
                 → Solves σ E
  ⊆kernel→Solves h = tabulate λ e∈ → h (Any.map (λ { refl → ≈ʷ-refl , ≈ʷ-refl }) e∈)

  Solves→InCg⊆kernel : Solves σ E → InCg E (s , t) → s [ σ ] ≈ʷ t [ σ ]
  Solves→InCg⊆kernel sol = Cg-least (subst-kernel σ) (Solves→⊆kernel sol)
```

#### The closure

An equation `(s , t)` is in the *closure* of `E` (`InClosure`{.AgdaFunction}) if
every solution of `E` in `FL(X)` solves it.  This is McNulty's `Σ→←`, the
composite of the two polarities of the Galois connection between equations and
solutions.  It contains `E` (`∈→InClosure`{.AgdaFunction}) and, more strongly,
the congruence `E` generates (`InCg⊆InClosure`{.AgdaFunction}), by the kernel
argument above.  McNulty's problem asks how much larger than that congruence
the closure is.

```agda
InClosure : {X : Type χ} → List (LatTerm X × LatTerm X) → LatTerm X × LatTerm X → Type χ
InClosure {X = X} E (s , t) = (σ : Sub X X) → Solves σ E → s [ σ ] ≈ʷ t [ σ ]

module _ {E : List (LatTerm X × LatTerm X)} where
  ∈→InClosure : (s , t) ∈ E → InClosure E (s , t)
  ∈→InClosure e∈ σ sol = lookup sol e∈

  InCg⊆InClosure : InCg E (s , t) → InClosure E (s , t)
  InCg⊆InClosure g σ sol = Solves→InCg⊆kernel σ sol g
```

#### Refutation certificates

A substitution *refutes* the membership of `(s , t)` in the closure of `E` if it
solves `E` and does not solve `(s , t)` (`Refutes`{.AgdaFunction}).  Such a
certificate is checked by evaluation (`refutes?`{.AgdaFunction}), and a valid one
shows that `(s , t)` is not in the closure (`Refutes→∉InClosure`{.AgdaFunction}).
Since the closure quantifies over all substitutions, a certificate is the only
kind of negative evidence a finite check can give.

```agda
Refutes : {X : Type χ} → Sub X X → List (LatTerm X × LatTerm X) → LatTerm X × LatTerm X
        → Type χ
Refutes σ E (s , t) = Solves σ E × ¬ (s [ σ ] ≈ʷ t [ σ ])

module _ (_≟_ : DecidableEquality X) where
  open Decision _≟_ using ( _≈ʷ?_ )

  refutes? : (σ : Sub X X) (E : List (LatTerm X × LatTerm X)) (e : LatTerm X × LatTerm X)
           → Dec (Refutes σ E e)
  refutes? σ E (s , t) = solves? _≟_ σ E ×-dec ¬? (s [ σ ] ≈ʷ? t [ σ ])

Refutes→∉InClosure : {σ : Sub X X} {E : List (LatTerm X × LatTerm X)} {e : LatTerm X × LatTerm X}
                   → Refutes σ E e → ¬ InClosure E e
Refutes→∉InClosure {σ = σ} (sol , ne) cl = ne (cl σ sol)
```

#### Outside the generated congruence

To show that `(s , t)` is *not* in the congruence `E` generates, it suffices to
find a lattice `𝑳`{.AgdaBound} and an assignment `f`{.AgdaBound} of its elements
to the generators under which each equation of `E` holds and `s = t` fails
(`Cg-separated`{.AgdaFunction}).  The homomorphism `FL(X) → 𝑳`{.AgdaBound} that
`f`{.AgdaBound} induces has a kernel containing `E`, hence containing the
generated congruence, and not containing `(s , t)`.  Together with a proof that
`(s , t)` is in the closure, such a separation shows that the closure is strictly
larger than the generated congruence.

```agda
module _ {X : Type χ} (𝑳 : Lattice α ρ) (f : X → 𝕌[ proj₁ 𝑳 ])
         {E : List (LatTerm X × LatTerm X)} where
  open Evaluation 𝑳          using ( ⟦_⟧ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ) renaming ( sym to ≈sym ; trans to ≈trans )

  Cg-separated : All (λ e → ⟦ proj₁ e ⟧ f ≈ ⟦ proj₂ e ⟧ f) E → ¬ (⟦ s ⟧ f ≈ ⟦ t ⟧ f)
               → ¬ InCg E (s , t)
  Cg-separated sat ne g = ne (Cg-least (kercon (FL-extend-hom 𝑳 f)) base g)
    where
    base : ∀ {u v} → fromPairs {𝑨 = proj₁ (FL X)} E u v → ⟦ u ⟧ f ≈ ⟦ v ⟧ f
    base r = let (e , e∈ , u≈ , v≈) = find r
             in ≈trans (≈ʷ-sound 𝑳 u≈ f) (≈trans (lookup sat e∈) (≈sym (≈ʷ-sound 𝑳 v≈ f)))
```
