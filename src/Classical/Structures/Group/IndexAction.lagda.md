---
layout: default
file: "src/Classical/Structures/Group/IndexAction.lagda.md"
title: "Classical.Structures.Group.IndexAction module"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### Right actions of a group on an index set

This is the [Classical.Structures.Group.IndexAction][] module of the [Agda Universal Algebra Library][].

A **right action** of a group `G` on a set `I` assigns to each group element a
map `I → I`, contravariantly: acting by `x ∙ y` is acting by `x`, then by `y`.

This is the gadget the wreath product construction consumes: the multiplication of
`S ≀ G` twists the base tuple of the right factor by the action of the left
factor's second component:

    (s , x) (t , y) =  (s₁ tₓ₁ , … , sₙ tₓₙ , x y).

Coordinate `i` of the product is `s i ∙ t (x i)`.[^1]
Associativity of the wreath product multiplication comes from the contravariant
law `(x ∙ y) i = y (x i)`.

**Three design points**.

+  **The index set is a bare type**, acted on up to propositional equality `≡`,
   not a setoid.  The intended instances are finite index sets `Fin n` (the cosets
   of a finite-index subgroup, enumerated), where `≡` is the right equality;
   keeping the index side propositional lets tuples `I → S` be permuted by plain
   precomposition, with no `Func` bookkeeping.  The group side *is* a setoid, so
   the action carries a congruence field.

+  **No bijectivity field**.  Invertibility of each `act x` is a consequence of
   the action laws (`act-invˡ`{.AgdaFunction}, `act-invʳ`{.AgdaFunction},
   `act-injective`{.AgdaFunction}), not an axiom; every group action is by
   bijections.

+  **Relation to [Classical.Structures.Group.GSet][]**.  The library encoding of
   G-sets presents the coset action as a unary algebra on the coset *setoid* (one
   operation per group element); that form feeds the congruence bridge of
   [FLRP.Bridge][].  The present module is the *enumerated* counterpart: an action
   on a bare index set, which is what underlies `Sᴵ` and the wreath product.
   The two meet in the coset-action specification below.

**Kernel–core correspondence.**  The module closes with the observation that, for
an action satisfying the (pointed) coset-action specification for a subgroup `H`,
the action is faithful precisely when `H` is core-free.[^2]  Both directions are
proved outright; nothing here is assumed.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.IndexAction where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                           using  ( Σ-syntax ; proj₁ ; proj₂ ; _,_ )
open import Level                                  using  ( Level ; _⊔_ )
open import Relation.Binary                        using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; sym ; trans ; cong )
open import Relation.Unary                         using  ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic        using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Conjugation  using  ( module Conjugate )
open import Classical.Structures.Group.NormalCore   using  ( module Core )
open import Classical.Structures.Group.Subgroups    using  ( IsSubgroup
                                                           ; trivialSubgroup )
open import Setoid.Algebras.Basic                   using  ( 𝕌[_] ; 𝔻[_] )

private variable ι β σ ℓ : Level
```
-->

#### The right-action record

`RightAction`{.AgdaRecord}` I 𝒢` packages an action of `𝒢` on the index type
`I`: the map `act`{.AgdaField}, its congruence in the group argument (the group
carrier is a setoid, and `≈`-equal elements must act identically), the identity
law, and the contravariant compatibility law.

```agda
record RightAction (I : Type ι) (𝒢 : Group β σ) : Type (ι ⊔ β ⊔ σ) where
  open Group-Op 𝒢 using ( _∙_ ; ε ; _⁻¹ ; invˡ-law ; invʳ-law )
  open Setoid 𝔻[ 𝒢 .proj₁ ] using ( _≈_ )

  field
    act       : 𝕌[ 𝒢 .proj₁ ] → I → I
    act-cong  : ∀ {x y} → x ≈ y → ∀ i → act x i ≡ act y i
    act-ε     : ∀ i → act ε i ≡ i
    act-∙     : ∀ x y i → act (x ∙ y) i ≡ act y (act x i)
```

Every group element acts invertibly: acting by `x ⁻¹` undoes acting by `x` on
either side, by one compatibility step, one congruence step along the inverse
law, and the identity law.  Injectivity of each `act x` follows.

```agda
  -- Acting by x, then by x ⁻¹, is the identity.
  act-invˡ : ∀ x i → act (x ⁻¹) (act x i) ≡ i
  act-invˡ x i =
    trans (sym (act-∙ x (x ⁻¹) i)) (trans (act-cong (invʳ-law x) i) (act-ε i))

  -- Acting by x ⁻¹, then by x, is the identity.
  act-invʳ : ∀ x i → act x (act (x ⁻¹) i) ≡ i
  act-invʳ x i =
    trans (sym (act-∙ (x ⁻¹) x i)) (trans (act-cong (invˡ-law x) i) (act-ε i))

  -- Each group element acts injectively on the index set.
  act-injective : ∀ x {i j} → act x i ≡ act x j → i ≡ j
  act-injective x {i} {j} e =
    trans (sym (act-invˡ x i)) (trans (cong (act (x ⁻¹)) e) (act-invˡ x j))
```

An action is **faithful** when only the identity class acts as the identity
map — the vanishing of the kernel of the induced permutation representation,
in pointwise form.

```agda
  -- Only elements ≈ ε act as the identity on every index.
  Faithful : Type (ι ⊔ β ⊔ σ)
  Faithful = ∀ {x} → (∀ i → act x i ≡ i) → x ≈ ε
```

#### The coset-action specification

The action Kurzweil's construction uses is the action of `G` on the (right)
cosets of a subgroup `H`, enumerated by an index set.

We specify it precisely as follows:

+  Some index plays the role of the coset `H` itself, its stabilizer is exactly
   `H`, in both directions.
+  Every index is reachable from it (transitivity).

This ties the abstract action to the pair `(G , H)` up to isomorphism of G-sets,
which is all any consumer needs, while staying indifferent to the way cosets are
enumerated.

```agda
record IsCosetAction {I : Type ι} {𝒢 : Group β σ}
  (A : RightAction I 𝒢) (H : Pred 𝕌[ 𝒢 .proj₁ ] ℓ) : Type (ι ⊔ β ⊔ σ ⊔ ℓ)
  where
  open RightAction A

  field
    basepoint  : I
    stab-in    : ∀ {g} → g ∈ H → act g basepoint ≡ basepoint
    stab-out   : ∀ {g} → act g basepoint ≡ basepoint → g ∈ H
    reach      : ∀ i → Σ[ g ∈ 𝕌[ 𝒢 .proj₁ ] ] (act g basepoint ≡ i)
```

#### The kernel–core correspondence

For a coset action of `H`, faithfulness is *equivalent* to core-freeness of
`H`; classically, the kernel of the action of `G` on the cosets of `H` is the
normal core `Core_G(H)`.

Both directions are proved outright below, against the library's constructive core
(the meet of all conjugates, [Classical.Structures.Group.NormalCore][]);
"core-free" is the containment of the core in the ≈-class of the identity, exactly
the form `CoreFree`{.AgdaFunction} of [FLRP.Enforceable][] unfolds to.

`ActionKernel`{.AgdaModule} fixes the data once for both directions.

```agda
module ActionKernel {I : Type ι} (𝒢@(𝑮 , eqns) : Group β σ)
  (H : Pred 𝕌[ 𝑮 ] ℓ) (H-sg : IsSubgroup 𝒢 H)
  (A : RightAction I 𝒢) (spec : IsCosetAction A H)
  where
  open Setoid 𝔻[ 𝑮 ]   using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢      using ( _∙_ ; ε ; _⁻¹ ; assoc-law ; idʳ-law ; invˡ-law ; ∙-cong )
  open Conjugate 𝒢     using ( conj-syntax )
  open Core 𝒢 H H-sg   using ( core ; core-mem-conj ; conj-mem-core )
  open RightAction A
  open IsCosetAction spec
```

One algebraic step is shared by the second direction: multiplying a conjugate
`g ∙ x ∙ g ⁻¹` by `g` on the right recovers `g ∙ x`.

```agda
  private
    -- (g ∙ x ∙ g ⁻¹) ∙ g ≈ g ∙ x, by reassociating and cancelling the inverse.
    conj-slide : ∀ g x → (x ^ g) ∙ g ≈ g ∙ x
    conj-slide g x = begin
      g ∙ x ∙ g ⁻¹ ∙ g    ≈⟨ assoc-law (g ∙ x) (g ⁻¹) g ⟩
      g ∙ x ∙ (g ⁻¹ ∙ g)  ≈⟨ ∙-cong ≈refl (invˡ-law g) ⟩
      g ∙ x ∙ ε           ≈⟨ idʳ-law (g ∙ x) ⟩
      g ∙ x               ∎
```

**Core-free implies faithful**.  If `x` acts as the identity on every index,
then every conjugate `g ∙ x ∙ g ⁻¹` stabilizes the basepoint — unfold the
conjugate along the action laws and let `x` disappear — so by the stabilizer
specification every conjugate of `x` lies in `H`; that puts `x` in the core,
which core-freeness collapses to the identity class.

```agda
  coreFree→faithful : core .proj₁ ⊆ trivialSubgroup 𝒢 .proj₁ → Faithful
  coreFree→faithful cf {x} fix = cf (conj-mem-core conj∈H)
    where
    -- Every conjugate of x stabilizes the basepoint, hence lies in H.
    conj∈H : ∀ g → x ^ g ∈ H
    conj∈H g = stab-out (trans (act-∙ (g ∙ x) (g ⁻¹) basepoint)
      (trans  (cong (act (g ⁻¹)) (trans (act-∙ g x basepoint) (fix (act g basepoint))))
              (act-invˡ g basepoint)))
```

**Faithful implies core-free**.  A member `x` of the core has all conjugates in
`H`; to see `x` fixes an arbitrary index `i`, reach `i` from the basepoint by
some `g` and slide the action of `g ∙ x` through the conjugate: the conjugate
stabilizes the basepoint, so `act x i ≡ i`.  Faithfulness then collapses `x`
to the identity class.

```agda
  faithful→coreFree : Faithful → core .proj₁ ⊆ trivialSubgroup 𝒢 .proj₁
  faithful→coreFree faith {x} x∈core = faith fix
    where
    fix : ∀ i → act x i ≡ i
    fix i = trans (cong (act x) (sym gb≡i))
      (trans  (sym (act-∙ g x basepoint))
        (trans  (act-cong (≈sym (conj-slide g x)) basepoint)
          (trans  (act-∙ (x ^ g) g basepoint)
            (trans  (cong (act g) (stab-in (core-mem-conj x∈core g)))
                    gb≡i))))
      where
      g : 𝕌[ 𝑮 ]
      g = reach i .proj₁

      gb≡i : act g basepoint ≡ i
      gb≡i = reach i .proj₂
```

--------------------------------------

[^1]: arXiv:1205.1927 ("the note"), proof of Lemma `lem:IE-must-have-wreaths`,
      vendored at `docs/papers/flrp/ieprops/`; the wreath product itself is
      [Classical.Structures.Group.Wreath][].

[^2]: This is the fact `ker φ = 1 ⟺ Core_G(H) = 1` that the wreath no-go argument of RP-4 turns on.
