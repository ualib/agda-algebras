---
layout: default
file: "src/Examples/Setoid/CongruenceLattice.lagda.md"
title: "Examples.Setoid.CongruenceLattice module"
date: "2026-06-02"
author: "the agda-algebras development team"
---

### Worked example: the congruence lattice of a two-element algebra {#examples-setoid-congruencelattice}

This is the [Examples.Setoid.CongruenceLattice][] module of the [Agda Universal Algebra Library][].

We exercise [Setoid.Algebras.Congruences.CompleteLattice][] on the smallest
nontrivial example: the two-element algebra `𝟚` in the *empty* signature (no
operations), whose carrier is `Bool` under propositional equality.  Because there are
no operations, every equivalence relation on `Bool` is automatically a congruence, so
`Con 𝟚` is just the lattice of equivalence relations on a two-element set — the
two-element chain `⊥ < ⊤`, where `⊥` is the diagonal (`≡`) and `⊤` is the all-relation.

We instantiate the `Lattice`, `BoundedLattice`, and `CompleteLattice` bundles for
`𝟚`, and verify the lattice is genuinely nontrivial by proving `⊤ ⋬ ⊥`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.CongruenceLattice where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Bool.Base    using ( Bool ; true ; false )
open import Data.Empty        using ( ⊥ )
open import Data.Product      using ( _,_ ; proj₁ )
open import Function          using ( Func )
open import Level             using ( 0ℓ ; Lift ; lift )
open import Relation.Binary   using ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )
open import Relation.Nullary  using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture using ( 𝓞 ; 𝓥 ; Signature )

open Func renaming ( to to _⟨$⟩_ )
```

#### The empty signature and the two-element algebra `𝟚` {#the-algebra}

The empty signature has no operation symbols (`⊥`), hence no arities.

```agda
𝑆₀ : Signature 0ℓ 0ℓ
𝑆₀ = ⊥ , λ ()

open import Setoid.Algebras {𝑆 = 𝑆₀} using ( Algebra ; 𝕌[_] ; ⟨_⟩ )
open import Setoid.Algebras.Congruences {𝑆 = 𝑆₀} using ( Con ; mkcon )

-- The two-element algebra: carrier Bool with ≡, and no operations to interpret.
𝟚 : Algebra 0ℓ 0ℓ
𝟚 = record { Domain = ≡.setoid Bool ; Interp = interp }
  where
  interp : Func (⟨ 𝑆₀ ⟩ (≡.setoid Bool)) (≡.setoid Bool)
  interp ⟨$⟩ (() , _)
  cong interp {() , _}
```

#### The Diagonal Congruence

Propositional equality `_≡_` is a congruence of `𝟚`: it is reflexive over the
setoid equality (which *is* `_≡_` here), an equivalence relation, and — since `𝑆₀`
has no operations — compatibility is vacuous.

```agda
Δ : Con 𝟚 0ℓ
Δ = _≡_ , mkcon  (λ e → e)
                 (record { refl = ≡.refl ; sym = ≡.sym ; trans = ≡.trans })
                 (λ ())
```

#### Instantiating the bundles

With the base level `ℓ₀ = 0ℓ` the absorbing level `L` is `0ℓ`, so the congruence
lattice of `𝟚` is the chain on `Con 𝟚 {0ℓ}`.  All three bundles type-check.

```agda
open import Setoid.Algebras.Congruences.Lattice {𝑆 = 𝑆₀} using ( _≤_ )
open import Setoid.Algebras.Congruences.CompleteLattice {𝑆 = 𝑆₀}
  using ( Con-Lattice ; Con-BoundedLattice ; Con-CompleteLattice ; 1ᴬ ; 0ᴬ ; 0ᴬ-minimum )

Con𝟚-Lattice          = Con-Lattice         𝟚 0ℓ
Con𝟚-BoundedLattice   = Con-BoundedLattice  𝟚 0ℓ
Con𝟚-CompleteLattice  = Con-CompleteLattice 𝟚 0ℓ
```

#### Nontriviality: `⊤ ⋬ ⊥` {#nontriviality}

The top and bottom congruences are distinct.  If we had `⊤ ≤ ⊥`, then composing with
`0 ≤ Δ` (the bottom is the least congruence, so it is below `Δ`) would give `⊤ ≤ Δ`;
but `⊤` relates `true` and `false` while `Δ` (namely `_≡_`) does not, so `true ≡ false`
— a contradiction.

```agda
Con𝟚-nontrivial : ¬ ( (1ᴬ 𝟚 0ℓ) ≤ (0ᴬ 𝟚 0ℓ) )
Con𝟚-nontrivial ⊤≤⊥ with 0ᴬ-minimum 𝟚 0ℓ Δ (⊤≤⊥ {true} {false} (lift _))
... | ()
```

--------------------------------------

<span style="float:left;">[← Setoid.Algebras.Congruences.CompleteLattice](Setoid.Algebras.Congruences.CompleteLattice.html)</span>
<span style="float:right;">[Setoid.Homomorphisms →](Setoid.Homomorphisms.html)</span>

{% include UALib.Links.md %}
