---
layout: default
file: "src/Classical/Structures/Lattice/Free/Derivability.lagda.md"
title: "Classical.Structures.Lattice.Free.Derivability module"
date: "2026-10-07"
author: "the agda-algebras development team"
---

### Derivable equality of lattice terms is decidable

This is the [Classical.Structures.Lattice.Free.Derivability][] module of the [Agda Universal Algebra Library][].

[Setoid.Varieties.SoundAndComplete][] builds, for any equational theory `E`, the
relatively free algebra `𝔽[ X ]`{.AgdaFunction}, whose carrier is the set of terms
over `X` and whose equality is *derivability*, `E ⊢ X ▹ p ≈ q`{.AgdaDatatype}: the
equation `p ≈ q` follows from `E` by the rules of equational logic.  For the theory
of lattices that is a relation with no procedure behind it.  This module connects
it to Whitman's order and so makes it decidable: for generators with decidable
equality, `E-Lattice ⊢ X ▹ p ≈ q` holds if and only if the lattice terms read off
`p` and `q` are equal in `FL X`{.AgdaFunction}, which `_≈ʷ?_`{.AgdaFunction}
decides.

The proof joins the two soundness theorems and the two completeness theorems in
play, Birkhoff's for equational logic and Whitman's for `_≤ʷ_`{.AgdaDatatype}.

+  **From derivations to Whitman's order**.  `FL X`{.AgdaFunction} is a lattice,
   hence a model of the theory, so by soundness of equational logic a derivable
   equation holds in it under every assignment, in particular under the
   assignment of each generator to itself, under which every term evaluates to
   itself.
+  **From Whitman's order to derivations**.  By soundness of Whitman's rules, an
   equation that holds in `FL X`{.AgdaFunction} holds in every lattice, that is,
   in every model of the theory; so by Birkhoff's completeness theorem it is
   derivable.

The completeness theorem of [Setoid.Varieties.SoundAndComplete][] takes the
variables of the equations and the generators of the free algebra in one
universe, and the equations of `Th-Lattice`{.AgdaFunction} are stated over
`Fin 3 : Type`, so the bridge is stated for generators in `Type`.  That is the
case of interest, `Fin n`; the free lattice itself is level polymorphic.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Derivability where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func ; _⇔_ ; mk⇔ )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.Definitions            using ( DecidableEquality ; Decidable )
open import Relation.Binary.PropositionalEquality  using ( subst₂ ; sym )
open import Relation.Nullary.Decidable.Core        using ( Dec ; map′ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Lattice            using ( Sig-Lattice )
open import Classical.Structures.Lattice.Free.Term  using ( LatTerm ; ℊ ; toTerm ; fromTerm
                                                          ; fromTerm-toTerm ; ⟦fromTerm⟧
                                                          ; module Evaluation )
open import Classical.Structures.Lattice.Free.Universal
                                                    using ( FL ; FL-setoid ; ⟦⟧-ℊ ; ≈ʷ-sound )
open import Classical.Structures.Lattice.Free.Whitman
                                                    using ( _≈ʷ_ ; module Decision )
open import Classical.Theories.Lattice              using ( Eq-Lattice ; Th-Lattice )
open import Overture.Terms {𝑆 = Sig-Lattice}        using ( Term )
open import Setoid.Algebras.Basic                   using ( 𝔻[_] )
open import Setoid.Terms.Basic                      using ( module Environment )
open import Setoid.Varieties.SoundAndComplete       using ( Eq ; toEq ; _⊢_▹_≈_ ; _≈̇_
                                                          ; ModTuple ; _⊫_ ; ⊫-intro
                                                          ; module Soundness
                                                          ; module FreeAlgebra )

open Func renaming ( to to _⟨$⟩_ )
```
-->

#### The theory of lattices as a family of equations

`Th-Lattice`{.AgdaFunction} of [Classical.Theories.Lattice][] lists the eight
lattice equations as pairs of terms; derivations and the free algebra consume a
theory as a family of equations.  `E-Lattice`{.AgdaFunction} is the same theory
in that shape, through the library's converter `toEq`{.AgdaFunction}.  A model of
`E-Lattice`{.AgdaFunction} is definitionally an algebra satisfying
`Th-Lattice`{.AgdaFunction}, so a model paired with the proof that it is one is
a `Lattice`{.AgdaFunction}, and every `Lattice`{.AgdaFunction} is a model.

```agda
E-Lattice : Eq-Lattice → Eq
E-Lattice = toEq Th-Lattice

open FreeAlgebra E-Lattice using ( 𝔽[_] ; completeness )
```

#### From derivations to the free lattice

A derivable equation holds in `FL X`{.AgdaFunction}, a model of
`E-Lattice`{.AgdaFunction}, under every assignment, by
`Soundness.sound`{.AgdaFunction}.  Under the assignment of each generator to the
term `ℊ x` the generic evaluation of a `Term`{.AgdaDatatype} agrees with the
evaluation of its translation (`⟦fromTerm⟧`{.AgdaFunction}), which returns the
translation itself (`⟦⟧-ℊ`{.AgdaFunction}).  So a derivable equation `p ≈ q`
gives `fromTerm p ≈ʷ fromTerm q` (`⊢→≈ʷ`{.AgdaFunction}).

```agda
module _ {X : Type} where
  open Environment (proj₁ (FL X))  using () renaming ( ⟦_⟧ to ⟦_⟧ᵀ )
  open Evaluation (FL X)           using ( ⟦_⟧ )
  open Soundness E-Lattice (proj₁ (FL X)) (proj₂ (FL X)) using ( sound )
  open SetoidReasoning (FL-setoid X)

  ⊢→≈ʷ : {p q : Term X} → E-Lattice ⊢ X ▹ p ≈ q → fromTerm p ≈ʷ fromTerm q
  ⊢→≈ʷ {p} {q} d = begin
    fromTerm p        ≡⟨ ⟦⟧-ℊ (fromTerm p) ⟨
    ⟦ fromTerm p ⟧ ℊ  ≈⟨ ⟦fromTerm⟧ (FL X) p ℊ ⟨
    ⟦ p ⟧ᵀ ⟨$⟩ ℊ      ≈⟨ sound d ℊ ⟩
    ⟦ q ⟧ᵀ ⟨$⟩ ℊ      ≈⟨ ⟦fromTerm⟧ (FL X) q ℊ ⟩
    ⟦ fromTerm q ⟧ ℊ  ≡⟨ ⟦⟧-ℊ (fromTerm q) ⟩
    fromTerm q        ∎
```

#### From the free lattice to derivations

Conversely, if `fromTerm p ≈ʷ fromTerm q`, then `p ≈ q` holds in every model of
`E-Lattice`{.AgdaFunction}, at every universe level (`≈ʷ→⊫`{.AgdaFunction}): a
model is a lattice, in which the translations of `p` and `q` have equal values
by Whitman soundness (`≈ʷ-sound`{.AgdaFunction}), and the generic evaluation of
each term agrees with the evaluation of its translation.  Birkhoff's completeness
theorem, `completeness`{.AgdaFunction}, needs this only at the levels of
`𝔽[ X ]`{.AgdaFunction}, and returns a derivation (`≈ʷ→⊢`{.AgdaFunction}).

```agda
module _ {X : Type} {p q : Term X} where

  ≈ʷ→⊫ : {α ρ : Level} → fromTerm p ≈ʷ fromTerm q
    → ModTuple {α = α} {ρᵃ = ρ} E-Lattice ⊫ (p ≈̇ q)
  ≈ʷ→⊫ e = ⊫-intro λ 𝑨 𝑨⊨E η →
    let 𝑳 = 𝑨 , 𝑨⊨E
        open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᵀ )
        open Evaluation 𝑳   using ( ⟦_⟧ )
        open SetoidReasoning 𝔻[ 𝑨 ]
    in begin
      ⟦ p ⟧ᵀ ⟨$⟩ η       ≈⟨ ⟦fromTerm⟧ 𝑳 p η ⟩
      ⟦ fromTerm p ⟧ η   ≈⟨ ≈ʷ-sound 𝑳 e η ⟩
      ⟦ fromTerm q ⟧ η   ≈⟨ ⟦fromTerm⟧ 𝑳 q η ⟨
      ⟦ q ⟧ᵀ ⟨$⟩ η       ∎

  ≈ʷ→⊢ : fromTerm p ≈ʷ fromTerm q → E-Lattice ⊢ X ▹ p ≈ q
  ≈ʷ→⊢ e = completeness p q (≈ʷ→⊫ e)
```

#### The bridge and the decision

Together the two directions say that derivability of `p ≈ q` from the lattice
axioms is equality of `fromTerm p` and `fromTerm q` in the free lattice
(`⊢⇔≈ʷ`{.AgdaFunction}), and, read through `fromTerm-toTerm`{.AgdaFunction}, that
equality in the free lattice is derivability of the translated equation
(`≈ʷ⇔⊢`{.AgdaFunction}).

```agda
module _ {X : Type} where

  ⊢⇔≈ʷ : {p q : Term X} → E-Lattice ⊢ X ▹ p ≈ q ⇔ fromTerm p ≈ʷ fromTerm q
  ⊢⇔≈ʷ = mk⇔ ⊢→≈ʷ ≈ʷ→⊢

  ≈ʷ⇔⊢ : {s t : LatTerm X} → s ≈ʷ t ⇔ E-Lattice ⊢ X ▹ toTerm s ≈ toTerm t
  ≈ʷ⇔⊢ {s} {t} = mk⇔
    (λ e → ≈ʷ→⊢ (subst₂ _≈ʷ_ (sym (fromTerm-toTerm s)) (sym (fromTerm-toTerm t)) e))
    (λ d → subst₂ _≈ʷ_ (fromTerm-toTerm s) (fromTerm-toTerm t) (⊢→≈ʷ d))
```

Given decidable equality of the generators, `⊢?`{.AgdaFunction} decides
derivability from the lattice axioms by deciding `_≈ʷ_`{.AgdaFunction} on the
translations and transporting the answer along the bridge.  Since the equality
of `𝔽[ X ]`{.AgdaFunction} *is* derivability, this decides equality in the
relatively free lattice (`𝔽-≈?`{.AgdaFunction}): the word problem for the free
lattice, solved for the library's own free algebra.

```agda
module _ {X : Type} (_≟_ : DecidableEquality X) where
  open Decision _≟_ using ( _≈ʷ?_ )

  ⊢? : (p q : Term X) → Dec (E-Lattice ⊢ X ▹ p ≈ q)
  ⊢? p q = map′ ≈ʷ→⊢ ⊢→≈ʷ (fromTerm p ≈ʷ? fromTerm q)

  𝔽-≈? : Decidable (Setoid._≈_ 𝔻[ 𝔽[ X ] ])
  𝔽-≈? = ⊢?
```
