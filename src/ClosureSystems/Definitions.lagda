---
layout: default
title : ClosureSystems.Definitions module (The Agda Universal Algebra Library)
date : 2021-07-10
author: [agda-algebras development team][]
---

### <a id="definitions-for-closure-systems-and-operators">Definitions for Closure Systems and Operators</a>

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
-- Try to replace Extensive by proposing a new stdlib equivalent: Relation.Binary.Core.Extensive

-- (Deprecated) Replaced with stdlib equivalent: Relation.Binary.Core._Preserves_⟶_)
-- OrderPreserving : Rel A ℓ → (A → A) → Type _
-- OrderPreserving _≤_ C = ∀ {x y} → x ≤ y → C x ≤ C y

-- (Deprecated) Replaced with stdlib equivalent: Algebra.Definitions(_≈_).IdempotentFun
-- Idempotent : Rel A ℓ → (A → A) → Type _
-- Idempotent _≈_ C = ∀ {x} → C (C x) ≈ C x

\end{code}

--------------------------------------

<br>
<br>

[↑ ClosureSystems](ClosureSystems.html)
<span style="float:right;">[ClosureSystems.Basic →](ClosureSystems.Basic.html)</span>

{% include UALib.Links.md %}


[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

