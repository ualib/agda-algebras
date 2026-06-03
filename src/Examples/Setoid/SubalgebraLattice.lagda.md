---
layout: default
file: "src/Examples/Setoid/SubalgebraLattice.lagda.md"
title: "Examples.Setoid.SubalgebraLattice module"
date: "2026-06-02"
author: "the agda-algebras development team"
---

### Worked example: the subalgebra lattice of a two-element algebra {#examples-setoid-subalgebralattice}

This is the [Examples.Setoid.SubalgebraLattice][] module of the [Agda Universal Algebra Library][].

We exercise [Setoid.Subalgebras.CompleteLattice][] on the two-element algebra `𝟚` in
the *empty* signature (no operations), whose carrier is `Bool`.  Since there are no
operations, *every* subset of the carrier is closed under the operations (vacuously),
so the subuniverses of `𝟚` are exactly the four subsets of a two-element set:
`Sub 𝟚` is the Boolean lattice `2²` (the diamond), with bottom `∅`, top `{true,
false}`, and the two incomparable singletons in between.

We instantiate the `Lattice`, `BoundedLattice`, and `CompleteLattice` bundles for `𝟚`
and verify the lattice is nontrivial by proving `⊤ ⋬ ⊥` (the full subuniverse is not
contained in the empty one).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.SubalgebraLattice where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Bool.Base    using ( Bool ; true )
open import Data.Empty        using ( ⊥ )
open import Data.Product      using ( _,_ )
open import Data.Unit.Base    using ( tt )
open import Function          using ( Func )
open import Level             using ( 0ℓ ; Lift ; lift ; lower )
open import Relation.Binary   using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )
open import Relation.Nullary  using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture using ( 𝓞 ; 𝓥 ; Signature )

open Func renaming ( to to _⟨$⟩_ )
```

#### The empty signature and the two-element algebra `𝟚` {#the-algebra}

```agda
𝑆₀ : Signature 0ℓ 0ℓ
𝑆₀ = ⊥ , λ ()

open import Setoid.Algebras {𝑆 = 𝑆₀} using ( Algebra ; 𝕌[_] ; ⟨_⟩ )

-- The two-element algebra: carrier Bool with ≡, and no operations to interpret.
𝟚 : Algebra 0ℓ 0ℓ
𝟚 = record { Domain = ≡.setoid Bool ; Interp = interp }
 where
 interp : Func (⟨ 𝑆₀ ⟩ (≡.setoid Bool)) (≡.setoid Bool)
 interp ⟨$⟩ (() , _)
 cong interp {() , _}
```

#### Instantiating the bundles {#the-bundles}

With base level `ℓ₀ = 0ℓ` the absorbing level `L` is `0ℓ`, so the subalgebra lattice
of `𝟚` lives on `Subᴸ 𝟚 0ℓ`.  All three bundles type-check.

```agda
open import Setoid.Subalgebras.CompleteLattice {𝑆 = 𝑆₀}
  using ( Subᴸ ; _≤_ ; Sub-Lattice ; Sub-BoundedLattice ; Sub-CompleteLattice
        ; 1ˢ ; 0ˢ ; 0ˢ-minimum )

Sub𝟚-Lattice          = Sub-Lattice         𝟚 0ℓ
Sub𝟚-BoundedLattice   = Sub-BoundedLattice  𝟚 0ℓ
Sub𝟚-CompleteLattice  = Sub-CompleteLattice 𝟚 0ℓ
```

#### Nontriviality: `⊤ ⋬ ⊥` {#nontriviality}

The empty subuniverse `∅` is a genuine subuniverse of `𝟚` (vacuously, as `𝑆₀` has no
operations).  If we had `⊤ ≤ ⊥`, then since `⊥` is the *least* subuniverse it is below
`∅`, so `true ∈ ⊤` would force `true ∈ ∅` — impossible.

```agda
-- The empty subuniverse, as an element of Subᴸ 𝟚 0ℓ.
∅ˢ : Subᴸ 𝟚 0ℓ
∅ˢ = (λ _ → Lift 0ℓ ⊥) , λ ()

Sub𝟚-nontrivial : ¬ ( _≤_ 𝟚 0ℓ (1ˢ 𝟚 0ℓ) (0ˢ 𝟚 0ℓ) )
Sub𝟚-nontrivial 1≤0 = lower (0ˢ-minimum 𝟚 0ℓ ∅ˢ (1≤0 {true} (lift tt)))
```

--------------------------------------

<span style="float:left;">[← Setoid.Subalgebras.CompleteLattice](Setoid.Subalgebras.CompleteLattice.html)</span>
<span style="float:right;">[Setoid.Homomorphisms →](Setoid.Homomorphisms.html)</span>

{% include UALib.Links.md %}
