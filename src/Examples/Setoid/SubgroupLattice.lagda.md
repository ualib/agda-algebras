---
layout: default
file: "src/Examples/Setoid/SubgroupLattice.lagda.md"
title: "Examples.Setoid.SubgroupLattice module"
date: "2026-06-02"
author: "the agda-algebras development team"
---

### Worked example: the subgroup lattice of the Klein four-group {#examples-setoid-subgrouplattice}

This is the [Examples.Setoid.SubgroupLattice][] module of the [Agda Universal Algebra Library][].

We formalize the **Klein four-group** `V₄ = ℤ/2ℤ × ℤ/2ℤ` as a setoid algebra over the
group signature [`Sig-Group`][Classical.Signatures.Group] and study its lattice of
subuniverses via [Setoid.Subalgebras.CompleteLattice][].

Two remarks make this a *group*-theoretic example rather than a bare subset example.
First, because `Sig-Group` carries the binary `∙`, the unary inverse `⁻¹`, and the
nullary identity `ε`, a subuniverse (i.e., a subset closed under all the operations)
is exactly a **subgroup**.  Second, the nullary `ε` forces every subuniverse to contain
the identity, so the *bottom* subuniverse `Sg ∅` is already the trivial subgroup
`{e}`; we get it for free as the lattice bottom `0ˢ`.

`V₄` has exactly five subgroups: the trivial group `{e}`, the whole group, and three
non-trivial, order-two subgroups in between, pairwise incomparable, any two of which
meet at `{e}` and join to the whole group.  That is the lattice **`M₃`** — the
five-element diamond, and the smallest *non-distributive* lattice.

This module exhibits the three middle subgroups as elements of `Sub V₄`, instantiates
the lattice bundles, and proves that the subgroup lattice is an `M₃` lattice: the
three atoms are pairwise incomparable and proper, any two meet at `{e}`, and any two
join to the whole group.  The one piece left for future work is to prove that these
five are the only subgroups.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.SubgroupLattice where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Bool.Base  using ( Bool ; true ; false ; _xor_ )
open import Data.Empty      using ( ⊥ )
open import Data.Fin.Patterns using ( 0F ; 1F )
open import Data.Product    using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base   using ( inj₁ ; inj₂ )
open import Data.Unit.Base  using ( tt )
open import Function        using ( Func )
open import Level           using ( 0ℓ ; lift )
open import Relation.Binary using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡
                            using ( _≡_ ; refl ; sym ; cong₂ )
open import Relation.Nullary  using ( ¬_ ; contradiction)
open import Relation.Unary    using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Group  using ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )
open import Setoid.Algebras {𝑆 = Sig-Group} using ( Algebra ; 𝕌[_] ; ⟨_⟩ )
open Func renaming ( to to _⟨$⟩_ )
```

#### The Klein four-group `V₄`

The carrier is `Bool × Bool`; the group operation is componentwise exclusive-or,
every element is its own inverse, and the identity is `(false , false)`.  We define
`_⊕_` through the projections (rather than by matching the pairs) so that it computes
on arbitrary (not just literal) arguments, which keeps the closure proofs below
definitional.

```agda
infixl 6 _⊕_
_⊕_ : Bool × Bool → Bool × Bool → Bool × Bool
x ⊕ y = proj₁ x xor proj₁ y , proj₂ x xor proj₂ y

V₄ : Algebra 0ℓ 0ℓ
V₄ = record { Domain = ≡.setoid (Bool × Bool) ; Interp = interp }
 where
 interp : Func (⟨ Sig-Group ⟩ (≡.setoid (Bool × Bool))) (≡.setoid (Bool × Bool))
 interp ⟨$⟩ (∙-Op , args) = args 0F ⊕ args 1F
 interp ⟨$⟩ (ε-Op , _)  = false , false
 interp ⟨$⟩ (⁻¹-Op , args) = args 0F
 cong interp {∙-Op , _} {.∙-Op , _} (refl , a≈) = cong₂ _⊕_ (a≈ 0F) (a≈ 1F)
 cong interp {ε-Op , _} {.ε-Op , _} (refl , _) = refl
 cong interp {⁻¹-Op , _} {.⁻¹-Op , _} (refl , a≈) = a≈ 0F
```

#### The three order-two subgroups {#the-subgroups}

Each order-two subgroup is cut out by one linear condition on the coordinates:
`H₁ = {(0,y)}` (first coordinate trivial), `H₂ = {(x,0)}` (second coordinate
trivial), and `H₌ = {(x,x)}` (the diagonal).  Each is closed under the operations,
hence a subuniverse: closure under `∙` is `xor` respecting the condition (via
`cong₂`), closure under `ε` is immediate, and closure under `⁻¹` is trivial since the
inverse is the identity map.

```agda
open import Setoid.Subalgebras.Subuniverses {𝑆 = Sig-Group}
  using ( Subuniverses ; Sg ; var ; app )

H₁ H₂ H₌ : Pred (Bool × Bool) 0ℓ
H₁ x = proj₁ x ≡ false
H₂ x = proj₂ x ≡ false
H₌ x = proj₁ x ≡ proj₂ x

H₁-isSub : H₁ ∈ Subuniverses V₄
H₁-isSub ∙-Op _ im = cong₂ _xor_ (im 0F) (im 1F)
H₁-isSub ε-Op _ _ = refl
H₁-isSub ⁻¹-Op _ im = im 0F

H₂-isSub : H₂ ∈ Subuniverses V₄
H₂-isSub ∙-Op _ im = cong₂ _xor_ (im 0F) (im 1F)
H₂-isSub ε-Op _ _ = refl
H₂-isSub ⁻¹-Op _ im = im 0F

H₌-isSub : H₌ ∈ Subuniverses V₄
H₌-isSub ∙-Op _ im = cong₂ _xor_ (im 0F) (im 1F)
H₌-isSub ε-Op _ _ = refl
H₌-isSub ⁻¹-Op _ im = im 0F
```

#### Instantiating the lattice bundles {#the-bundles}

With base level `ℓ₀ = 0ℓ` the absorbing level `L` is `0ℓ`.  We `open Sublattice V₄ 0ℓ`
to bring the order, operations, bounds, and bundles into scope specialized to `V₄` —
so we write `𝑯₁ ≤ 𝑯₂`, `𝑯₁ ∧ 𝑯₂`, `0ˢ`, etc. directly.  All three bundles type-check.

```agda
open import Setoid.Subalgebras.CompleteLattice {𝑆 = Sig-Group}
  using ( module Sublattice )
open Sublattice V₄ 0ℓ

-- The three middle subgroups as elements of Sub V₄.
𝑯₁ 𝑯₂ 𝑯₌ : Subᴸ
𝑯₁ = H₁ , H₁-isSub
𝑯₂ = H₂ , H₂-isSub
𝑯₌ = H₌ , H₌-isSub
```

#### The `M₃` shape {#the-m3-shape}

Each middle subgroup lies strictly between the bottom `{e}` and the top: it is above
`0ˢ` (every subgroup is, since `0ˢ` is least) and below `1ˢ` (likewise), and it is
*proper* — distinct from the top, because it omits some element of the group.

```agda
0≤𝑯₁ : 0ˢ ≤ 𝑯₁
0≤𝑯₁ = 0ˢ-minimum 𝑯₁

𝑯₁≤1 : 𝑯₁ ≤ 1ˢ
𝑯₁≤1 _ = lift tt

-- 𝑯₁ is a *proper* subgroup: the top is not contained in it (it omits (true , false)).
1⋬𝑯₁ : ¬ ( 1ˢ ≤ 𝑯₁ )
1⋬𝑯₁ le = ex falso
  where
  ex : (true , false) ∈ proj₁ 𝑯₁ → ⊥
  ex ()

  falso : (true , false) ∈ proj₁ 𝑯₁
  falso = le {true , false} (lift tt)

0≤𝑯₂ : 0ˢ ≤ 𝑯₂
0≤𝑯₂ = 0ˢ-minimum 𝑯₂

𝑯₂≤1 : 𝑯₂ ≤ 1ˢ
𝑯₂≤1 _ = lift tt

-- 𝑯₂ omits (false , true) (its second coordinate is not trivial).
1⋬𝑯₂ : ¬ ( 1ˢ ≤ 𝑯₂ )
1⋬𝑯₂ le = ex falso
  where
  ex : (false , true) ∈ proj₁ 𝑯₂ → ⊥
  ex ()
  falso : (false , true) ∈ proj₁ 𝑯₂
  falso = le {false , true} (lift tt)

0≤𝑯₌ : 0ˢ ≤ 𝑯₌
0≤𝑯₌ = 0ˢ-minimum 𝑯₌

𝑯₌≤1 : 𝑯₌ ≤ 1ˢ
𝑯₌≤1 _ = lift tt

-- 𝑯₌ omits (true , false) (its coordinates differ).
1⋬𝑯₌ : ¬ ( 1ˢ ≤ 𝑯₌ )
1⋬𝑯₌ le = ex (le (lift tt))
  where
  ex : (true , false) ∈ proj₁ 𝑯₌ → ⊥
  ex ()
```

The three middle subgroups are pairwise incomparable: each contains a non-identity
element the others lack — `(false , true) ∈ H₁`, `(true , false) ∈ H₂`,
`(true , true) ∈ H₌`.

```agda
𝑯₁⋬𝑯₂ : ¬ ( 𝑯₁ ≤ 𝑯₂ )
𝑯₁⋬𝑯₂ le = ex (le refl)
  where
  ex : (false , true) ∈ proj₁ 𝑯₂ → ⊥
  ex ()

𝑯₂⋬𝑯₁ : ¬ ( 𝑯₂ ≤ 𝑯₁ )
𝑯₂⋬𝑯₁ le = ex (le refl)
  where
  ex : (true , false) ∈ proj₁ 𝑯₁ → ⊥
  ex ()

𝑯₁⋬𝑯₌ : ¬ ( 𝑯₁ ≤ 𝑯₌ )
𝑯₁⋬𝑯₌ le = ex (le refl)
  where
  ex : (false , true) ∈ proj₁ 𝑯₌ → ⊥
  ex ()

𝑯₌⋬𝑯₁ : ¬ ( 𝑯₌ ≤ 𝑯₁ )
𝑯₌⋬𝑯₁ le = ex (le refl)
  where
  ex : (true , false) ∈ proj₁ 𝑯₁ → ⊥
  ex ()

𝑯₂⋬𝑯₌ : ¬ ( 𝑯₂ ≤ 𝑯₌ )
𝑯₂⋬𝑯₌ le = ex (le refl)
  where
  ex : (true , false) ∈ proj₁ 𝑯₌ → ⊥
  ex ()

𝑯₌⋬𝑯₂ : ¬ ( 𝑯₌ ≤ 𝑯₂ )
𝑯₌⋬𝑯₂ le = ex (le refl)
  where
  ex : (true , true) ∈ proj₁ 𝑯₂ → ⊥
  ex ()
```

Together these facts give the order skeleton of `M₃`: three pairwise-incomparable
proper subgroups, each strictly between `0ˢ = {e}` and `1ˢ`.

#### The meet/join table: `M₃` is non-distributive {#the-m3-table}

The lattice is `M₃`: any two atoms meet at `{e}` and join to the whole group.

For a meet, an element trivial in both relevant coordinates is the identity
`(false , false)`, which the nullary `ε` generates, so it lies in `0ˢ = Sg ∅`.

For a join, the union of two atoms generates all four elements — the fourth as the
`⊕` of the other two atom witnesses
(e.g., `(true , true) = (false , true) ⊕ (true , false)`).

```agda
𝑯₁∧𝑯₂≈⊥ : 𝑯₁ ∧ 𝑯₂ ≈ 0ˢ
𝑯₁∧𝑯₂≈⊥ = m , 0ˢ-minimum (𝑯₁ ∧ 𝑯₂)
  where m : 𝑯₁ ∧ 𝑯₂ ≤ 0ˢ
        m (refl , refl) = app ε-Op (λ ()) λ ()

𝑯₁∧𝑯₌≈⊥ : (𝑯₁ ∧ 𝑯₌) ≈ 0ˢ
𝑯₁∧𝑯₌≈⊥ = m , 0ˢ-minimum (𝑯₁ ∧ 𝑯₌)
  where m : (𝑯₁ ∧ 𝑯₌) ≤ 0ˢ
        m  (refl , refl) = app ε-Op (λ ()) (λ ())

𝑯₂∧𝑯₌≈⊥ : (𝑯₂ ∧ 𝑯₌) ≈ 0ˢ
𝑯₂∧𝑯₌≈⊥ = m , 0ˢ-minimum (𝑯₂ ∧ 𝑯₌)
  where m : (𝑯₂ ∧ 𝑯₌) ≤ 0ˢ
        m (refl , refl) = app ε-Op (λ ()) (λ ())

𝑯₁∨𝑯₂≈⊤ : (𝑯₁ ∨ 𝑯₂) ≈ 1ˢ
𝑯₁∨𝑯₂≈⊤ = (λ _ → lift tt) , j
  where
  j : 1ˢ ≤ (𝑯₁ ∨ 𝑯₂)
  j {false , false} _ = var (inj₁ refl)
  j {false , true} _ = var (inj₁ refl)
  j {true , false} _ = var (inj₂ refl)
  j {true , true} _ = app ∙-Op (λ { 0F → false , true ; 1F → true , false })
                               (λ { 0F → var (inj₁ refl) ; 1F → var (inj₂ refl) })

𝑯₁∨𝑯₌≈⊤ : (𝑯₁ ∨ 𝑯₌) ≈ 1ˢ
𝑯₁∨𝑯₌≈⊤ = (λ _ → lift tt) , j
  where
  j : 1ˢ ≤ (𝑯₁ ∨ 𝑯₌)
  j {false , false} _ = var (inj₁ refl)
  j {false , true} _ = var (inj₁ refl)
  j {true , true} _ = var (inj₂ refl)
  j {true , false} _ = app ∙-Op (λ { 0F → false , true ; 1F → true , true })
                                (λ { 0F → var (inj₁ refl) ; 1F → var (inj₂ refl) })

𝑯₂∨𝑯₌≈⊤ : (𝑯₂ ∨ 𝑯₌) ≈ 1ˢ
𝑯₂∨𝑯₌≈⊤ = (λ _ → lift tt) , j
  where
  j : 1ˢ ≤ (𝑯₂ ∨ 𝑯₌)
  j {false , false} _ = var (inj₁ refl)
  j {true , false} _ = var (inj₁ refl)
  j {true , true} _ = var (inj₂ refl)
  j {false , true} _ = app ∙-Op (λ { 0F → true , false ; 1F → true , true })
                                (λ { 0F → var (inj₁ refl) ; 1F → var (inj₂ refl) })
```

These equalities are exactly non-distributivity: with `x = 𝑯₁`, `y = 𝑯₂`, `z = 𝑯₌`,
the meet `x ∧ (y ∨ z) = x ∧ 1ˢ = x` (a proper, nonzero subgroup), whereas
`(x ∧ y) ∨ (x ∧ z) = 0ˢ ∨ 0ˢ = 0ˢ` — so `M₃` is not distributive.

#### Remaining work {#remaining}

What remains is **completeness**: that `0ˢ`, `1ˢ`, `𝑯₁`, `𝑯₂`, `𝑯₌` are *all* the
subgroups — a finite case analysis over the four group elements.

--------------------------------------

<span style="float:left;">[← Setoid.Subalgebras.CompleteLattice](Setoid.Subalgebras.CompleteLattice.html)</span>
<span style="float:right;">[Setoid.Homomorphisms →](Setoid.Homomorphisms.html)</span>

{% include UALib.Links.md %}
