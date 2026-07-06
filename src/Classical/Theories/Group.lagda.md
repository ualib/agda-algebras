---
layout: default
file: "src/Classical/Theories/Group.lagda.md"
title: "Classical.Theories.Group module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### The equational theory of groups

This is the [Classical.Theories.Group][] module of the [Agda Universal Algebra Library][].

`Th-Group` has five equations: the three monoid equations — associativity, left
identity, right identity — composed from the same builders `Th-Monoid` uses, plus the
two inverse laws `LeftInverse` and `RightInverse` from [`Classical.Equations`][]
applied to `Sig-Group`'s symbols.  The inverse laws are the first equations in the
[`Classical/`][Classical] tree to mention a *unary* operation symbol (`⁻¹-Op`); their
arity-conformance evidence is the triple `refl refl refl` for the binary `∙-Op`, the
unary `⁻¹-Op`, and the nullary `ε-Op` respectively.  The variable carrier is uniformly
`Fin 3` as for `Th-Monoid` (per [ADR-002 v2 §2](../../docs/adr/002-classical-layer-design.md));
the identity and inverse equations use `0F` and ignore `1F`, `2F`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.Group where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Group             using ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Equations                    using ( Associative ; LeftIdentity ; RightIdentity
                                                         ; LeftInverse ; RightInverse )
open import Overture.Terms {𝑆 = Sig-Group}         using ( Term )
```
-->

```agda
data Eq-Group : Type where
  assoc idˡ idʳ invˡ invʳ : Eq-Group

Th-Group : Eq-Group → Term (Fin 3) × Term (Fin 3)
Th-Group assoc = Associative   ∙-Op             refl           0F 1F 2F
Th-Group idˡ   = LeftIdentity  ∙-Op ε-Op        refl refl      0F
Th-Group idʳ   = RightIdentity ∙-Op ε-Op        refl refl      0F
Th-Group invˡ  = LeftInverse   ∙-Op ⁻¹-Op ε-Op  refl refl refl 0F
Th-Group invʳ  = RightInverse  ∙-Op ⁻¹-Op ε-Op  refl refl refl 0F
```
