---
layout: default
file: "src/Examples/Setoid/SubgroupLattice.lagda.md"
title: "Examples.Setoid.SubgroupLattice module"
date: "2026-06-02"
author: "the agda-algebras development team"
---

### Worked example: the subgroup lattice of the Klein four-group {#examples-setoid-subgrouplattice}

This is the [Examples.Setoid.SubgroupLattice][] module of the [Agda Universal Algebra Library][].

We realize the **Klein four-group** `V₄ = ℤ/2ℤ × ℤ/2ℤ` as a setoid algebra over the
group signature [`Sig-Group`][Classical.Signatures.Group] and study its lattice of
subuniverses via [Setoid.Subalgebras.CompleteLattice][].

Two remarks make this a *group*-theoretic example rather than a bare subset example.
First, because `Sig-Group` carries the binary `∙`, the unary inverse `⁻¹`, and the
nullary identity `ε`, a subuniverse (i.e., a subset closed under all the operations)
is exactly a **subgroup**.  Second, the nullary `ε` forces every subuniverse to contain
the identity, so the *bottom* subuniverse `Sg ∅` is already the trivial subgroup
`{e}`; we get it for free as the lattice bottom `0ˢ`.

`V₄` has exactly five subgroups: the trivial group `{e}`, the whole group, and three
order-two subgroups in between, pairwise incomparable, any two of which meet at `{e}`
and join to the whole group.  That is the lattice **`M₃`** — the five-element diamond,
and the smallest *non-distributive* lattice.  This module exhibits the three middle
subgroups as elements of `Sub V₄`, instantiates the lattice bundles, and proves the
*order skeleton* of `M₃`: the three atoms are pairwise incomparable and proper (each
strictly between `{e}` and the whole group).  The lattice-equation content that makes
`M₃` non-distributive — that any two atoms meet at `{e}` and join to the top — and the
completeness claim that these *are all* the subgroups, are left for future work (see
*Remaining work* below).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.SubgroupLattice where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Bool.Base  using ( Bool ; true ; false ; _xor_ )
open import Data.Fin.Patterns using ( 0F ; 1F )
open import Data.Product    using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Unit.Base  using ( tt )
open import Function        using ( Func )
open import Level           using ( 0ℓ ; lift )
open import Relation.Binary using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡
                            using ( _≡_ ; refl ; cong₂ )
open import Relation.Nullary  using ( ¬_ )
open import Relation.Unary    using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Group  using ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )

open Func renaming ( to to _⟨$⟩_ )
```

#### The Klein four-group `V₄` {#the-group}

The carrier is `Bool × Bool`; the group operation is componentwise exclusive-or,
every element is its own inverse, and the identity is `(false , false)`.  We define
`_⊕_` through the projections (rather than by matching the pairs) so that it computes
on arbitrary — not just literal — arguments, which keeps the closure proofs below
definitional.

```agda
infixl 6 _⊕_
_⊕_ : Bool × Bool → Bool × Bool → Bool × Bool
x ⊕ y = (proj₁ x xor proj₁ y) , (proj₂ x xor proj₂ y)

open import Setoid.Algebras {𝑆 = Sig-Group} using ( Algebra ; 𝕌[_] ; ⟨_⟩ )

V₄ : Algebra 0ℓ 0ℓ
V₄ = record { Domain = ≡.setoid (Bool × Bool) ; Interp = interp }
 where
 interp : Func (⟨ Sig-Group ⟩ (≡.setoid (Bool × Bool))) (≡.setoid (Bool × Bool))
 interp ⟨$⟩ (∙-Op  , args)  = args 0F ⊕ args 1F
 interp ⟨$⟩ (ε-Op  , _)     = false , false
 interp ⟨$⟩ (⁻¹-Op , args)  = args 0F
 cong interp {∙-Op  , _} {.∙-Op  , _} (refl , a≈)  = cong₂ _⊕_ (a≈ 0F) (a≈ 1F)
 cong interp {ε-Op  , _} {.ε-Op  , _} (refl , _)   = refl
 cong interp {⁻¹-Op , _} {.⁻¹-Op , _} (refl , a≈)  = a≈ 0F
```

#### The three order-two subgroups {#the-subgroups}

Each order-two subgroup is cut out by one linear condition on the coordinates:
`H₁ = {(0,y)}` (first coordinate trivial), `H₂ = {(x,0)}` (second coordinate
trivial), and `H₌ = {(x,x)}` (the diagonal).  Each is closed under the operations,
hence a subuniverse: closure under `∙` is `xor` respecting the condition (via
`cong₂`), closure under `ε` is immediate, and closure under `⁻¹` is trivial since the
inverse is the identity map.

```agda
open import Setoid.Subalgebras.Subuniverses {𝑆 = Sig-Group} using ( Subuniverses )

H₁ H₂ H₌ : Pred (Bool × Bool) 0ℓ
H₁ x = proj₁ x ≡ false
H₂ x = proj₂ x ≡ false
H₌ x = proj₁ x ≡ proj₂ x

H₁-isSub : H₁ ∈ Subuniverses V₄
H₁-isSub ∙-Op  a im = cong₂ _xor_ (im 0F) (im 1F)
H₁-isSub ε-Op  a im = refl
H₁-isSub ⁻¹-Op a im = im 0F

H₂-isSub : H₂ ∈ Subuniverses V₄
H₂-isSub ∙-Op  a im = cong₂ _xor_ (im 0F) (im 1F)
H₂-isSub ε-Op  a im = refl
H₂-isSub ⁻¹-Op a im = im 0F

H₌-isSub : H₌ ∈ Subuniverses V₄
H₌-isSub ∙-Op  a im = cong₂ _xor_ (im 0F) (im 1F)
H₌-isSub ε-Op  a im = refl
H₌-isSub ⁻¹-Op a im = im 0F
```

#### Instantiating the lattice bundles {#the-bundles}

With base level `ℓ₀ = 0ℓ` the absorbing level `L` is `0ℓ`, so the subgroups live in
`Sub V₄ {0ℓ}`.  All three bundles type-check.

```agda
open import Setoid.Subalgebras.CompleteLattice {𝑆 = Sig-Group}
  using ( Subᴸ ; _≤_ ; Sub-Lattice ; Sub-BoundedLattice
        ; Sub-CompleteLattice ; 0ˢ ; 1ˢ ; 0ˢ-minimum )

SubV₄-Lattice          = Sub-Lattice         V₄ 0ℓ
SubV₄-BoundedLattice   = Sub-BoundedLattice  V₄ 0ℓ
SubV₄-CompleteLattice  = Sub-CompleteLattice V₄ 0ℓ

-- The three middle subgroups as elements of Sub V₄.
𝑯₁ 𝑯₂ 𝑯₌ : Subᴸ V₄ 0ℓ
𝑯₁ = H₁ , H₁-isSub
𝑯₂ = H₂ , H₂-isSub
𝑯₌ = H₌ , H₌-isSub
```

#### The `M₃` shape {#the-m3-shape}

Each middle subgroup lies strictly between the bottom `{e}` and the top: it is above
`0ˢ` (every subgroup is, since `0ˢ` is least) and below `1ˢ` (likewise), and it is
*proper* — distinct from the top, because it omits some element of the group.

```agda
0≤𝑯₁ : _≤_ V₄ 0ℓ (0ˢ V₄ 0ℓ) 𝑯₁
0≤𝑯₁ = 0ˢ-minimum V₄ 0ℓ 𝑯₁

𝑯₁≤1 : _≤_ V₄ 0ℓ 𝑯₁ (1ˢ V₄ 0ℓ)
𝑯₁≤1 _ = lift tt

-- 𝑯₁ is a *proper* subgroup: the top is not contained in it (it omits (true , false)).
1⋬𝑯₁ : ¬ ( _≤_ V₄ 0ℓ (1ˢ V₄ 0ℓ) 𝑯₁ )
1⋬𝑯₁ le with le {true , false} (lift tt)
... | ()

0≤𝑯₂ : _≤_ V₄ 0ℓ (0ˢ V₄ 0ℓ) 𝑯₂
0≤𝑯₂ = 0ˢ-minimum V₄ 0ℓ 𝑯₂

𝑯₂≤1 : _≤_ V₄ 0ℓ 𝑯₂ (1ˢ V₄ 0ℓ)
𝑯₂≤1 _ = lift tt

-- 𝑯₂ omits (false , true) (its second coordinate is not trivial).
1⋬𝑯₂ : ¬ ( _≤_ V₄ 0ℓ (1ˢ V₄ 0ℓ) 𝑯₂ )
1⋬𝑯₂ le with le {false , true} (lift tt)
... | ()

0≤𝑯₌ : _≤_ V₄ 0ℓ (0ˢ V₄ 0ℓ) 𝑯₌
0≤𝑯₌ = 0ˢ-minimum V₄ 0ℓ 𝑯₌

𝑯₌≤1 : _≤_ V₄ 0ℓ 𝑯₌ (1ˢ V₄ 0ℓ)
𝑯₌≤1 _ = lift tt

-- 𝑯₌ omits (true , false) (its coordinates differ).
1⋬𝑯₌ : ¬ ( _≤_ V₄ 0ℓ (1ˢ V₄ 0ℓ) 𝑯₌ )
1⋬𝑯₌ le with le {true , false} (lift tt)
... | ()
```

The three middle subgroups are pairwise **incomparable**: each contains a non-identity
element the others lack — `(false , true) ∈ H₁`, `(true , false) ∈ H₂`,
`(true , true) ∈ H₌`.

```agda
𝑯₁⋬𝑯₂ : ¬ ( _≤_ V₄ 0ℓ 𝑯₁ 𝑯₂ )
𝑯₁⋬𝑯₂ le with le {false , true} refl
... | ()

𝑯₂⋬𝑯₁ : ¬ ( _≤_ V₄ 0ℓ 𝑯₂ 𝑯₁ )
𝑯₂⋬𝑯₁ le with le {true , false} refl
... | ()

𝑯₁⋬𝑯₌ : ¬ ( _≤_ V₄ 0ℓ 𝑯₁ 𝑯₌ )
𝑯₁⋬𝑯₌ le with le {false , true} refl
... | ()

𝑯₌⋬𝑯₁ : ¬ ( _≤_ V₄ 0ℓ 𝑯₌ 𝑯₁ )
𝑯₌⋬𝑯₁ le with le {true , true} refl
... | ()

𝑯₂⋬𝑯₌ : ¬ ( _≤_ V₄ 0ℓ 𝑯₂ 𝑯₌ )
𝑯₂⋬𝑯₌ le with le {true , false} refl
... | ()

𝑯₌⋬𝑯₂ : ¬ ( _≤_ V₄ 0ℓ 𝑯₌ 𝑯₂ )
𝑯₌⋬𝑯₂ le with le {true , true} refl
... | ()
```

Together these facts pin down the **`M₃`** shape: three pairwise-incomparable proper
subgroups, each strictly between the trivial subgroup `0ˢ = {e}` and the whole group
`1ˢ`.

#### Remaining work {#remaining}

Two pieces complete the picture and are left for follow-up:

+  **The meet/join table.**  Any two atoms *meet* in `{e}` (`𝑯ᵢ ∧ 𝑯ⱼ ≈ 0ˢ`) and
   *join* to the whole group (`𝑯ᵢ ∨ 𝑯ⱼ ≈ 1ˢ`) — the equalities that make `M₃`
   non-distributive.  The meet direction needs `(false , false) ∈ Sg ∅`, i.e. the
   identity is generated by the nullary `ε`; expressing that cleanly runs into the
   usual difficulty that a nullary application `(ε ̂ V₄) a` does not constrain its
   (empty) argument tuple `a`, so it wants a small dedicated lemma.
+  **Completeness.**  That `0ˢ`, `1ˢ`, `𝑯₁`, `𝑯₂`, `𝑯₌` are *all* the subgroups —
   a finite case analysis over the four group elements.

--------------------------------------

<span style="float:left;">[← Setoid.Subalgebras.CompleteLattice](Setoid.Subalgebras.CompleteLattice.html)</span>
<span style="float:right;">[Setoid.Homomorphisms →](Setoid.Homomorphisms.html)</span>

{% include UALib.Links.md %}
