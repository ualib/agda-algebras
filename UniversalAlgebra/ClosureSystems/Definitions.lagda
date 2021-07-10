---
layout: default
title : ClosureSystems.Definitions module (The Agda Universal Algebra Library)
date : 2021-07-10
author: [agda-algebras development team][]
---

### Definitions for Closure Systems and Operators

\begin{code}

{-# OPTIONS --without-K --safe #-}

module ClosureSystems.Definitions where

open import Agda.Primitive          using    ( Level )
                                    renaming ( Set to Type )
open import Relation.Binary.Core    using    ( Rel )


private variable
 a ℓ : Level
 A : Type a


Extensive : Rel A ℓ → (A → A) → Type _
Extensive _≤_ C = ∀{x} → x ≤ C x

OrderPreserving : Rel A ℓ → (A → A) → Type _
OrderPreserving _≤_ C = ∀ {x y} → x ≤ y → C x ≤ C y

Idempotent : Rel A ℓ → (A → A) → Type _
Idempotent _≈_ C = ∀ {x} → C (C x) ≈ C x

\end{code}

--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

