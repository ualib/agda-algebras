---
layout: default
title : "Setoid.Congruences.Lattice module (The Agda Universal Algebra Library)"
date : "2026-06-01"
author: "agda-algebras development team"
---

#### The Congruence Lattice of a Setoid Algebra

This is the [Setoid.Congruences.Lattice][] module of the [Agda Universal Algebra Library][].

The congruences of an algebra `𝑨`, ordered by containment, form a complete lattice.
This module begins the formalization of that fact by promoting `Con 𝑨` to a
first-class ordered object: it defines the containment order `_⊆_`, the induced
equivalence `_≑_` of mutual containment, and the **meet** `θ ∧ φ`, which is the
relational intersection `θ ∩ φ`.  The intersection of two congruences is again a
congruence, and it is the greatest lower bound of the two arguments.  Thus we have a
partially ordered set which, with the meet operation, forms a semilattice.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Congruences.Lattice {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda Standard Library ---------------------------------------
open import Agda.Primitive           using () renaming ( Set to Type )
open import Data.Product             using ( _×_ ; _,_ ; proj₁ ; proj₂ ; swap )
open import Level                    using ( Level ; _⊔_ )
open import Relation.Binary          using ( Setoid ; IsEquivalence ; IsPartialOrder ; _⇒_ )
                                     renaming ( Rel to BinRel )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Lattice  using ( Infimum ; IsMeetSemilattice ; MeetSemilattice )

-- Imports from the Agda Universal Algebras Library ------------------------------
open import Setoid.Algebras.Basic     {𝑆 = 𝑆}  using  ( ov ; Algebra ; 𝕌[_] )
open import Setoid.Congruences.Basic  {𝑆 = 𝑆}  using  ( Con ; mkcon ; _∣≈_ ; reflexive
                                                      ; is-equivalence ; is-compatible )
private variable α ρ ℓ : Level
```

#### The containment order on congruences

For congruences `θ φ : Con 𝑨` we write `θ ⊆ φ` when the underlying relation of `θ`
is **contained** in that of `φ` ("contained" is with respect to subset inclusion on
`ℙ(A × A)`).  Classically this is the familiar (lattice) partial order on equivalence
relations, and it remains a partial order here — `_⊆_` is antisymmetric
**with respect to `_≑_`**, the equivalence of *mutual set containment*.  The only
subtlety is which equality counts as **equal congruences**.

The underlying relation of a congruence inhabits the `BinRel` type
(`BinRel A ℓ = A → A → Type ℓ`), so mutual containment yields back-and-forth maps
between the proof-types `proj₁ θ x y` and `proj₁ φ x y` rather than a proof that the
packaged congruences are *propositionally* equal.

Upgrading `_≑_` to propositional equality would need function extensionality with
propositional extensionality/univalence (and proof-irrelevance for the `IsCongruence`
witness), and that's simply not available under   `--safe --cubical-compatible`; so we
take `_≑_` as the equality of congruences, exactly as the `Setoid/` discipline
dictates.  Classically `_≑_` collapses to propositional equality via propositional
extensionality.

```agda
module _ {𝑨 : Algebra α ρ} where
  open Algebra 𝑨 using () renaming ( Domain to A )
  open Setoid A using () renaming ( _≈_ to _≈ᴬ_ )

  -- θ ⊆ φ : the relation of θ is contained in the relation of φ.
  _⊆_ : Con 𝑨 ℓ → Con 𝑨 ℓ → Type (α ⊔ ℓ)
  θ ⊆ φ = proj₁ θ ⇒ proj₁ φ
  infix 4 _⊆_

  -- θ ≑ φ : mutual containment (the equivalence the partial order is taken over).
  -- (the symbol ≑ is input as \doteqdot)
  _≑_ : Con 𝑨 ℓ → Con 𝑨 ℓ → Type (α ⊔ ℓ)
  θ ≑ φ = θ ⊆ φ × φ ⊆ θ
  infix 4 _≑_
```

The order is reflexive and transitive, and `_≑_` collapses it to a partial order.

```agda
  ⊆-refl : {θ : Con 𝑨 ℓ} → θ ⊆ θ
  ⊆-refl p = p

  ⊆-trans : {θ φ ψ : Con 𝑨 ℓ} → θ ⊆ φ → φ ⊆ ψ → θ ⊆ ψ
  ⊆-trans θ⊆φ φ⊆ψ p = φ⊆ψ (θ⊆φ p)

  -- A ≑-step entails a ⊆-step (the `reflexive` field of a preorder).
  ⊆-reflexive : {θ φ : Con 𝑨 ℓ} → θ ≑ φ → θ ⊆ φ
  ⊆-reflexive = proj₁

  -- Antisymmetry holds up to mutual containment, by definition of _≑_.
  ⊆-antisym : {θ φ : Con 𝑨 ℓ} → θ ⊆ φ → φ ⊆ θ → θ ≑ φ
  ⊆-antisym θ⊆φ φ⊆θ = θ⊆φ , φ⊆θ

  -- The components are written out directly rather than via ⊆-refl/⊆-trans:
  -- because _⊆_ is a defined relation (not an injective type former), Agda
  -- cannot recover the implicit congruence arguments of those lemmas from the
  -- expected component types, so we inline the (trivial) proofs here.
  ≑-refl : {θ : Con 𝑨 ℓ} → θ ≑ θ
  ≑-refl = (λ z → z) , (λ z → z)

  ≑-sym : {θ φ : Con 𝑨 ℓ} → θ ≑ φ → φ ≑ θ
  ≑-sym = swap

  ≑-trans : {θ φ ψ : Con 𝑨 ℓ} → θ ≑ φ → φ ≑ ψ → θ ≑ ψ
  ≑-trans (θ⊆φ , φ⊆θ) (φ⊆ψ , ψ⊆φ) = (λ p → φ⊆ψ (θ⊆φ p)) , (λ p → φ⊆θ (ψ⊆φ p))

  -- The implicit congruence (and level) arguments of the helper lemmas are bound
  -- by lambdas and forwarded explicitly: they cannot be inferred through the
  -- (non-injective) `Con 𝑨 ℓ` carrier type at these function-typed fields.
  ≑-isEquivalence : IsEquivalence (_≑_ {ℓ})
  ≑-isEquivalence {ℓ} = record
    { refl = λ {θ} → ≑-refl {ℓ} {θ}
    ; sym = λ {θ} {φ} → ≑-sym {ℓ} {θ} {φ}
    ; trans = λ {θ} {φ} {ψ} → ≑-trans  {ℓ} {θ} {φ} {ψ}
    }

  ⊆-isPartialOrder : IsPartialOrder (_≑_ {ℓ}) _⊆_
  ⊆-isPartialOrder {ℓ} = record
    { isPreorder = record  { isEquivalence = ≑-isEquivalence {ℓ}
                           ; reflexive = λ {θ} {φ} → ⊆-reflexive {ℓ} {θ} {φ}
                           ; trans = λ {θ} {φ} {ψ} → ⊆-trans {ℓ} {θ} {φ} {ψ}
                           }
    ; antisym = λ {θ} {φ} → ⊆-antisym {ℓ} {θ} {φ}
    }
```

#### Meet: the intersection of two congruences

The intersection `θ ∩ φ` holds at `(x , y)` exactly when both `θ` and `φ` do.  It
is again a congruence: it contains the setoid equality (reflexivity), it is an
equivalence relation (componentwise), and it is compatible with every basic
operation (componentwise, using the compatibility of `θ` and of `φ`).  We define
the underlying relation first, then bundle the `IsCongruence` proof.

```agda
  -- The underlying relation of the meet: pointwise conjunction.
  meetRel : Con 𝑨 ℓ → Con 𝑨 ℓ → BinRel 𝕌[ 𝑨 ] ℓ
  meetRel θ φ x y = proj₁ θ x y × proj₁ φ x y

  _∧_ : Con 𝑨 ℓ → Con 𝑨 ℓ → Con 𝑨 ℓ
  θ ∧ φ = meetRel θ φ , mkcon m-reflexive m-isEquivalence m-compatible
    where
    θc = proj₂ θ
    φc = proj₂ φ
    θe = is-equivalence θc
    φe = is-equivalence φc

    -- The meet contains the setoid equality because θ and φ both do.
    m-reflexive : ∀ {a₀ a₁} → a₀ ≈ᴬ a₁ → meetRel θ φ a₀ a₁
    m-reflexive e = reflexive θc e , reflexive φc e

    -- The meet is an equivalence relation, proved componentwise.
    m-isEquivalence : IsEquivalence (meetRel θ φ)
    m-isEquivalence = record
     { refl   = IsEquivalence.refl θe , IsEquivalence.refl φe
     ; sym    = λ (p , q) → IsEquivalence.sym θe p , IsEquivalence.sym φe q
     ; trans  = λ (p , q) (p′ , q′) → IsEquivalence.trans θe p p′ , IsEquivalence.trans φe q q′
     }

    -- The meet is compatible with every basic operation, componentwise.
    m-compatible : 𝑨 ∣≈ meetRel θ φ
    m-compatible 𝑓 uv = is-compatible θc 𝑓 (λ i → proj₁ (uv i))
                      , is-compatible φc 𝑓 (λ i → proj₂ (uv i))
  infixr 7 _∧_
```

The meet is the *greatest lower bound* of its two arguments: it is below each of
them, and it is above any common lower bound.  These three facts are exactly the
`Infimum` of `_⊆_` at `_∧_`.

```agda
  ∧-lowerˡ : {θ φ : Con 𝑨 ℓ} → θ ∧ φ ⊆ θ
  ∧-lowerˡ = proj₁

  ∧-lowerʳ : {θ φ : Con 𝑨 ℓ} → θ ∧ φ ⊆ φ
  ∧-lowerʳ = proj₂

  ∧-greatest : {θ φ ψ : Con 𝑨 ℓ} → ψ ⊆ θ → ψ ⊆ φ → ψ ⊆ θ ∧ φ
  ∧-greatest ψ⊆θ ψ⊆φ p = ψ⊆θ p , ψ⊆φ p

  -- As above, the implicit congruence arguments of ∧-lowerˡ/ʳ and ∧-greatest
  -- are not inferable from the expected component types, so we inline them.
  ∧-infimum : Infimum (_⊆_ {ℓ}) _∧_
  ∧-infimum θ φ = proj₁ , proj₂ , λ ψ ψ⊆θ ψ⊆φ p → ψ⊆θ p , ψ⊆φ p

  ∧-isMeetSemilattice : IsMeetSemilattice (_≑_ {ℓ}) _⊆_ _∧_
  ∧-isMeetSemilattice {ℓ} = record { isPartialOrder = ⊆-isPartialOrder {ℓ} ; infimum = ∧-infimum {ℓ} }
```

#### The poset and meet-semilattice of congruences

Finally we assemble the standard-library bundles.  At a fixed relation level `ℓ`,
`Con-Poset 𝑨` is the poset `(Con 𝑨, ≑, ⊆)` and `Con-MeetSemilattice 𝑨` equips it
with the meet `_∧_`.  (The full lattice and complete lattice, with the join and
the bounds `⊥`/`⊤`, are built in the subsequent steps of #271.)

```agda
module _ (𝑨 : Algebra α ρ) {ℓ : Level} where
 Con-Poset : Poset (α ⊔ ρ ⊔ ov ℓ) (α ⊔ ℓ) (α ⊔ ℓ)
 Con-Poset = record  { Carrier = Con 𝑨 ℓ ; _≈_ = _≑_ ; _≤_ = _⊆_
                     ; isPartialOrder  = ⊆-isPartialOrder }

 Con-MeetSemilattice : MeetSemilattice (α ⊔ ρ ⊔ ov ℓ) (α ⊔ ℓ) (α ⊔ ℓ)
 Con-MeetSemilattice = record  { Carrier = Con 𝑨 ℓ
                               ; _≈_ = _≑_
                               ; _≤_ = _⊆_
                               ; _∧_ = _∧_
                               ; isMeetSemilattice  = ∧-isMeetSemilattice
                               }
```

--------------------------------------

<span style="float:left;">[← Setoid.Congruences](Setoid.Congruences.html)</span>
<span style="float:right;">[Setoid.Homomorphisms →](Setoid.Homomorphisms.html)</span>

{% include UALib.Links.md %}
