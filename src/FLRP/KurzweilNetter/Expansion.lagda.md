---
layout: default
file: "src/FLRP/KurzweilNetter/Expansion.lagda.md"
title: "FLRP.KurzweilNetter.Expansion module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### The expansion step: cutting the coset congruences down to the invariant partitions

This is the [FLRP.KurzweilNetter.Expansion][] module of the [Agda Universal Algebra Library][].

This is the heart of the Kurzweil–Netter construction.  The transitive `Sᵐ`-set on
`Sᵐ / D` has (decidable) congruence lattice isomorphic to the interval `[D , Sᵐ]`
([FLRP.Bridge][]), which is dually isomorphic to the partition lattice `Eq(m)`
([FLRP.KurzweilInterval][]).

**Expanding** the coset algebra by the lifted maps `x ↦ x ∘ t`, one per member `t`
of a given family of index maps, cuts the congruences down to the partitions
*invariant* under the family ([FLRP.KurzweilNetter.Invariance][]): the main result
here is the order isomorphism

`expansionIso : DecCon 𝑬 ≅ `(invariant partitions of `Eq(m)`, order reversed),

where `𝑬`{.AgdaBound} is the expanded coset algebra.

The family of index maps is an *abstract parameter* `tr : Fin T → Fin m → Fin m`;
this module knows nothing about the algebra being represented; instantiating `tr`
at the basic translations of [FLRP.KurzweilNetter.Translations][] is the business
of [FLRP.KurzweilNetter.Duality][].

Three design points, each forced by a constraint worth recording.

+  **The signature is an enumerated symbol type, not `Sig-Unary 𝕌[ Sᵐ ]`**.
   The carrier of the power is a function type `Fin m → S`, and a
   `FiniteSignature`{.AgdaRecord} requires its symbols to be enumerated up to
   propositional equality, unprovable for a function type under  `--safe`
   (it is function extensionality).  So the expanded algebra's symbols are
   `Fin N ⊎ Fin T`{.AgdaDatatype}: `inj₁ ν` acts by left translation by the `ν`-th
   *enumerated* group element, `inj₂ τ` by composition with `tr τ`.  Compatibility
   with the enumerated actions still forces compatibility with *every* group
   element, because congruences respect the coset equality and the enumeration is
   surjective up to the pointwise equality of the power (`forget`{.AgdaFunction}
   below), so nothing is lost.

+  **The two halves of the invariance transfer have different prices**.

   That an invariant partition's subgroup `K_π` is closed under the lifts is one
   line (`Inv→K-closed`{.AgdaFunction}).  The converse asserts that a congruence
   of the expanded algebra has an *invariant* partition; this needs the
   indicator-tuple argument of `K-reflects`{.AgdaFunction} of
   [Classical.Structures.Group.PartitionSubgroup][], and with it the
   *nontriviality witness* `s₀ ≉ ε` of the base group
   (`K-closed→Inv`{.AgdaFunction}).  This is one of the few places the base
   group's properties enter the proof at all.

+  **Kurzweil surjectivity enters in its decidable form**.

   The passage from an arbitrary congruence to a partition routes through Entry 4
   of [FLRP.Assumptions][] in the working form
   `KurzweilSurjectivityᵈ`{.AgdaFunction} (the classical half of Kurzweil's
   lemma, true for `𝒮` finite nonabelian simple), taken as a module parameter.
   Every interval element this construction manipulates is the base-coset class
   of a *decidable* congruence, delivered with its decider by the Layer-D bridge
   map `toᵈ`{.AgdaFunction}, so the semantic form is never needed; that matters,
   because the semantic form is unprovable outright (the no-go of
   [FLRP.KurzweilInterval][]).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilNetter.Expansion where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base                         using  ( if_then_else_ )
open import Data.Empty                             using  ( ⊥-elim )
open import Data.Fin.Base                          using  ( Fin ; splitAt ; join )
open import Data.Fin.Properties                    using  ( all? ; splitAt-join )
                                                   renaming ( _≟_ to _≟ᶠ_ )
open import Data.Nat.Base                          using  ( ℕ ; _+_ )
open import Data.Product                           using  ( Σ-syntax ; _,_
                                                          ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using  ( _⊎_ ; inj₁ ; inj₂ )
open import Function                               using  ( _∘_ )
open import Level                                  using  ( 0ℓ )
open import Relation.Binary                        using  ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality as ≡ using  ( _≡_ ; cong )
open import Relation.Nullary                       using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable             using  ( does ; dec-true ; dec-false )
open import Relation.Unary                         using  ( _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Finite              using  ( Sig-Unary-FiniteSignature )
open import Classical.Signatures.Group               using  ( ∙-Op )
open import Classical.Signatures.Unary               using  ( Sig-Unary )
open import Classical.Structures.Group.Basic         using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Cosets        using  ( module Coset )
open import Classical.Structures.Group.GSet          using  ( module CosetAction )
open import Classical.Structures.Interpret           using  ( interp-cong )
open import Classical.Structures.Lattice.Partitions  using  ( SameBlock ; _⊑_ ; _≈ᵖ_ )
open import FLRP.Bridge                              using  ( module Bridge )
open import FLRP.KurzweilInterval                    using  ( module KurzweilInterval )
open import FLRP.KurzweilNetter.Invariance           using  ( Inv )
open import FLRP.Representable                       using  ( _⊆ᵈ_ ; _≑ᵈ_ )
open import Order.Iso                                using  ( OrderIso )
open import Overture                                 using  ( Signature )
open import Setoid.Algebras.Basic                    using  ( Algebra ; 𝕌[_] ; 𝔻[_]
                                                            ; mkAlgebra )
open import Setoid.Algebras.Finite                   using  ( FiniteAlgebra )
open import Setoid.Algebras.Products.Finite          using  ( power-FiniteAlgebra )
open import Setoid.Congruences.Basic                 using  ( _∣≈_ ; is-equivalence
                                                            ; mkcon ; is-compatible )
                                                     renaming (reflexive to con-reflexive)
open import Setoid.Congruences.Certificates.Schema   using  ( ParentVec ; parent )
open import Setoid.Congruences.Finite.Basic          using  ( DecCon ; ConRel )
open import Setoid.Signatures.Finite                 using  ( FiniteSignature )
```
-->

#### The expansion module

`KNExpansion`{.AgdaModule} fixes the base group with its finiteness and
nontriviality witnesses, the exponent `m`, the abstract family `tr` of index maps,
and the decidable Kurzweil surjectivity hypothesis at `m`.

```agda
module KNExpansion
  (𝒮@(𝑺 , _)  : Group 0ℓ 0ℓ)  (open Setoid 𝔻[ 𝑺 ] using (_≈_))
                               (open Group-Op 𝒮 using (ε))
  (𝑭ₛ         : FiniteAlgebra 𝑺)
  (s₀         : 𝕌[ 𝑺 ])
  (s₀≉ε       : ¬ s₀ ≈ ε)
  (m T        : ℕ)
  (tr         : Fin T → Fin m → Fin m)
  (surj       : KurzweilInterval.KurzweilSurjectivityᵈ 𝒮 m)
  where

  -- Sⁿ = Sᵐ, Diag, K, the interval, kurzweilIntervalIso; the power kit's
  -- pointwise lemmas are renamed to match this module's ∙ₚ/εₚ/⁻¹ₚ convention.
  open KurzweilInterval 𝒮 m renaming  ( ⊗-pointwise    to ∙ₚ-pointwise
                                       ; e-pointwise    to εₚ-pointwise
                                       ; inv-pointwise  to ⁻¹ₚ-pointwise )

  open Setoid 𝔻[ 𝑺 ] using ( refl ; sym ; trans ; reflexive)

  open Setoid 𝔻[ Sⁿ ] using () renaming ( _≈_ to _≈ₚ_ ; refl to ≈ₚ-refl )
  open Group-Op 𝒮  using ( _∙_ ; _⁻¹ )
  open Group-Op 𝑺ⁿ using ( ∙-cong ) renaming ( _∙_ to _∙ₚ_ ; ε to εₚ ; _⁻¹ to _⁻¹ₚ )

  open Coset 𝑺ⁿ Diag Diag-isSubgroup using ( _∼_ ; ≈⇒∼ ; ∼-congˡ ; ∼-dec ; cosetSetoid )
  open CosetAction 𝑺ⁿ Diag Diag-isSubgroup using ( cosetAlgebra )

  private
    G : Type 0ℓ
    G = 𝕌[ Sⁿ ]
```

#### Decidability of the diagonal

Membership in the diagonal is a finite conjunction of decidable base-group
equalities, so it is decidable; the partition subgroups have their decider
`K-dec`{.AgdaFunction} upstream in [FLRP.KurzweilInterval][], shared with the
decidable interval isomorphism.

```agda
  -- The diagonal has decidable membership.
  Diag-dec : ∀ x → Dec (x ∈ Diag)
  Diag-dec x = all? (λ i → all? (λ j → 𝑭ₛ ._≟_ (x i) (x j)))
    where open FiniteAlgebra
```

#### Finiteness of the power

The power `Sᵐ` is a finite algebra by [Setoid.Algebras.Products.Finite][]; its
enumeration is the symbol set of the expanded signature's group half.

```agda
  -- The power Sᵐ is a finite algebra.
  Sᵐ-FiniteAlgebra : FiniteAlgebra Sⁿ
  Sᵐ-FiniteAlgebra = power-FiniteAlgebra {n = m} 𝑭ₛ

  private
    N : ℕ
    N = FiniteAlgebra.card Sᵐ-FiniteAlgebra

    gEnum : Fin N → G
    gEnum = FiniteAlgebra.enum Sᵐ-FiniteAlgebra

    gEnum-sur : ∀ (x : G) → Σ[ ν ∈ Fin N ] gEnum ν ≈ₚ x
    gEnum-sur = FiniteAlgebra.enum-sur Sᵐ-FiniteAlgebra
```

#### The expanded signature and algebra

The expanded algebra lives on the same coset setoid as
`cosetAlgebra`{.AgdaFunction}; its symbols are the enumerated group elements
(acting by left translation) together with the family indices (acting by
composition).  Left translation respects coset equality by
`∼-congˡ`{.AgdaFunction}; composition respects it because `(x ∘ t)⁻¹ ∙ (y ∘ t)`
agrees pointwise with `(x⁻¹ ∙ y) ∘ t`, and a tuple constant on all coordinates is
constant on the coordinates `t` selects.

```agda
  -- The expanded signature: one unary symbol per enumerated group element and
  -- per family member.
  Sig-Exp : Signature 0ℓ 0ℓ
  Sig-Exp = Sig-Unary (Fin N ⊎ Fin T)

  -- The expanded signature is finite finitary.
  Sig-Exp-FiniteSignature : FiniteSignature Sig-Exp
  Sig-Exp-FiniteSignature =
    Sig-Unary-FiniteSignature (N + T) (splitAt N) (λ s → join N T s , splitAt-join N T s)

  private
    -- (x ∘ t)⁻¹ ∙ (y ∘ t) agrees pointwise with (x⁻¹ ∙ y) ∘ t.
    quot-comp : (x y : G) (t : Fin m → Fin m) (i : Fin m)
      → ((x ∘ t ⁻¹ₚ) ∙ₚ (y ∘ t)) i ≈ ((x ⁻¹ₚ ∙ₚ y) ∘ t) i
    quot-comp x y t i = trans lhs (sym rhs)
      where
      -- both sides normalize to this middle form
      mid : 𝕌[ 𝑺 ]
      mid = (x (t i)) ⁻¹ ∙ y (t i)

      lhs : ((x ∘ t) ⁻¹ₚ ∙ₚ (y ∘ t)) i ≈ mid
      lhs = trans (∙ₚ-pointwise ((x ∘ t) ⁻¹ₚ) (y ∘ t) i)
              (interp-cong 𝑺 ∙-Op
                (λ { Fin.zero → ⁻¹ₚ-pointwise (x ∘ t) i ; (Fin.suc Fin.zero) → refl }))

      rhs : ((x ⁻¹ₚ ∙ₚ y) ∘ t) i ≈ mid
      rhs = trans (∙ₚ-pointwise (x ⁻¹ₚ) y (t i))
              (interp-cong 𝑺 ∙-Op
                (λ { Fin.zero → ⁻¹ₚ-pointwise x (t i) ; (Fin.suc Fin.zero) → refl }))

    -- composition with an index map respects coset equality
    lift-cong : (t : Fin m → Fin m) {x y : G} → x ∼ y → (x ∘ t) ∼ (y ∘ t)
    lift-cong t {x} {y} x∼y =
      Diag-respects (λ i → sym (quot-comp x y t i)) (λ i j → x∼y (t i) (t j))

  -- The expanded coset algebra.
  expandedAlgebra : Algebra {𝑆 = Sig-Exp} 0ℓ 0ℓ
  expandedAlgebra = mkAlgebra cosetSetoid op op-cong
    where
    op : (s : Fin N ⊎ Fin T) → (Fin 1 → G) → G
    op (inj₁ ν) a = gEnum ν ∙ₚ a Fin.zero
    op (inj₂ τ) a = a Fin.zero ∘ tr τ

    op-cong : (s : Fin N ⊎ Fin T) {u v : Fin 1 → G}
      → (∀ i → u i ∼ v i) → op s u ∼ op s v
    op-cong (inj₁ ν) h = ∼-congˡ (gEnum ν) (h Fin.zero)
    op-cong (inj₂ τ) h = lift-cong (tr τ) (h Fin.zero)

  -- The expanded algebra is finite: same carrier, same coset equality.
  expandedAlgebra-FiniteAlgebra : FiniteAlgebra expandedAlgebra
  expandedAlgebra-FiniteAlgebra = record
    { _≟_       = ∼-dec Diag-dec
    ; card      = N
    ; enum      = gEnum
    ; enum-sur  = λ x → proj₁ (gEnum-sur x) , ≈⇒∼ (gEnum-sur x .proj₂)
    }
```

#### The invariance transfer

Invariance of a partition and closure of its subgroup under composition are
interchangeable.  The forward direction is immediate; the converse is the
indicator-tuple argument, and consumes the nontriviality witness.

```agda
  -- An invariant partition's subgroup is closed under composition.
  Inv→K-closed : (t : Fin m → Fin m) (pv : ParentVec m) → Inv t pv
    → ∀ {z} → z ∈ K pv → (z ∘ t) ∈ K pv
  Inv→K-closed t pv inv zk sb = zk (inv sb)

  -- Closure of the subgroup under composition forces invariance.
  K-closed→Inv : (t : Fin m → Fin m) (pv : ParentVec m)
    → (∀ {z} → z ∈ K pv → (z ∘ t) ∈ K pv) → Inv t pv
  K-closed→Inv t pv closed {i} {j} sb = decide (parent pv (t i) ≟ᶠ parent pv (t j))
    where
    -- the indicator of the pv-block of t i
    ind : G
    ind k = if does (parent pv k ≟ᶠ parent pv (t i)) then s₀ else ε

    ind∈K : ind ∈ K pv
    ind∈K sb' =
      reflexive (≡.cong (λ z → if does (z ≟ᶠ parent pv (t i)) then s₀ else ε) sb')

    decide : Dec (SameBlock pv (t i) (t j)) → SameBlock pv (t i) (t j)
    decide (yes e)   = e
    decide (no ¬e)   = ⊥-elim (s₀≉ε s₀≈ε)
      where
      ind-i : ind (t i) ≡ s₀
      ind-i = cong (λ b → if b then s₀ else ε)
                   (dec-true (parent pv (t i) ≟ᶠ parent pv (t i)) ≡.refl)

      ind-j : ind (t j) ≡ ε
      ind-j = cong (λ b → if b then s₀ else ε)
                   (dec-false (parent pv (t j) ≟ᶠ parent pv (t i)) (λ e → ¬e (≡.sym e)))

      s₀≈ε : s₀ ≈ ε
      s₀≈ε = trans (reflexive (≡.sym ind-i))
                    (trans (closed ind∈K sb) (reflexive ind-j))
```

#### Forgetting and extending

A congruence of the expanded algebra is in particular a congruence of the coset
algebra.  Compatibility with an *arbitrary* group element's action transfers from
the enumerated actions through surjectivity of the enumeration, one coset
rewriting on each side.  Conversely a coset congruence whose relation is closed
under the lifts extends to the expanded algebra.  Both directions keep the
relation and its decision procedure definitionally unchanged; only the
compatibility proof is rebuilt, which is what lets the round trips below stay at
the relation level.

```agda
  -- A congruence of the expanded algebra is a congruence of the coset algebra.
  forget : DecCon expandedAlgebra 0ℓ → DecCon cosetAlgebra 0ℓ
  forget ((θ , θcon) , θ?) = (θ , mkcon (con-reflexive θcon) (is-equivalence θcon) compat) , θ?
    where
    θ-refl : ∀ {x y} → x ∼ y → θ x y
    θ-refl = con-reflexive θcon

    θ-sym : ∀ {x y} → θ x y → θ y x
    θ-sym = IsEquivalence.sym (is-equivalence θcon)

    θ-trans : ∀ {x y z} → θ x y → θ y z → θ x z
    θ-trans = IsEquivalence.trans (is-equivalence θcon)

    compat : cosetAlgebra ∣≈ θ
    compat g {u} {v} h =
      θ-trans (θ-sym (step (u Fin.zero)))
        (θ-trans (is-compatible θcon (inj₁ ν) {u} {v} h) (step (v Fin.zero)))
      where
      ν : Fin N
      ν = gEnum-sur g .proj₁

      -- the enumerated action agrees with g's action, coset-wise
      step : (x : G) → θ (gEnum ν ∙ₚ x) (g ∙ₚ x)
      step x = θ-refl (≈⇒∼ (∙-cong (gEnum-sur g .proj₂) ≈ₚ-refl))

  -- A coset congruence closed under the lifts is a congruence of the expanded
  -- algebra.
  extend : (d : DecCon cosetAlgebra 0ℓ)
    → ((τ : Fin T) → ∀ {x y} → ConRel d x y → ConRel d (x ∘ tr τ) (y ∘ tr τ))
    → DecCon expandedAlgebra 0ℓ
  extend ((θ , θcon) , θ?) compτ =
    (θ , mkcon (con-reflexive θcon) (is-equivalence θcon) compat) , θ?
    where
    compat : expandedAlgebra ∣≈ θ
    compat (inj₁ ν) {u} {v} h = is-compatible θcon (gEnum ν) {u} {v} h
    compat (inj₂ τ) {u} {v} h = compτ τ (h Fin.zero)
```

#### From congruences to invariant partitions and back

The forward passage composes the WP-3 bridge with the surjectivity hypothesis.
The congruence's base-coset class, carried with the congruence's own decision
procedure through the bridge's Layer-D map, is a decidable interval element;
the hypothesis hands over a partition, and closure of the class under the lifts
(one compatibility instance at `ε`) makes that partition invariant through the
indicator argument.

```agda
  private
    module B = Bridge 𝑺ⁿ Diag Diag-isSubgroup

  -- The decidable interval element of an expanded congruence: its base-coset
  -- class, with the congruence's own decision procedure.
  intervalOfᵈ : DecCon expandedAlgebra 0ℓ → Intervalᵈ
  intervalOfᵈ θE = B.toᵈ (forget θE)

  -- The underlying interval element (the base-coset class alone).
  intervalOf : DecCon expandedAlgebra 0ℓ → Interval≈
  intervalOf θE = intervalOfᵈ θE .proj₁

  -- The partition the surjectivity hypothesis attaches to it.
  partOf : DecCon expandedAlgebra 0ℓ → ParentVec m
  partOf θE = surj (intervalOfᵈ θE) .proj₁

  private
    partOf-in : (θE : DecCon expandedAlgebra 0ℓ) → set (intervalOf θE) ⊆ K (partOf θE)
    partOf-in θE = surj (intervalOfᵈ θE) .proj₂ .proj₁

    partOf-out : (θE : DecCon expandedAlgebra 0ℓ) → K (partOf θE) ⊆ set (intervalOf θE)
    partOf-out θE = surj (intervalOfᵈ θE)  .proj₂ .proj₂

    -- the base-coset class is closed under the lifts
    classClosed : (θE : DecCon expandedAlgebra 0ℓ) (τ : Fin T)
      → ∀ {g} → g ∈ set (intervalOf θE) → (g ∘ tr τ) ∈ set (intervalOf θE)
    classClosed ((θ , θcon) , θ?) τ {g} εθg =
      θ-trans (θ-refl (≈⇒∼ ε∘t≈ε)) (is-compatible θcon (inj₂ τ) {λ _ → εₚ} {λ _ → g} (λ _ → εθg))
      where
      θ-refl : ∀ {x y} → x ∼ y → θ x y
      θ-refl = con-reflexive θcon

      θ-trans : ∀ {x y z} → θ x y → θ y z → θ x z
      θ-trans = IsEquivalence.trans (is-equivalence θcon)

      -- the identity tuple is fixed by the lift, up to pointwise equality
      ε∘t≈ε : εₚ ≈ₚ (εₚ ∘ tr τ)
      ε∘t≈ε i = trans (εₚ-pointwise i) (sym (εₚ-pointwise (tr τ i)))

  -- The partition of an expanded congruence is invariant under the family.
  partOf-invariant : (θE : DecCon expandedAlgebra 0ℓ) (τ : Fin T)
    → Inv (tr τ) (partOf θE)
  partOf-invariant θE τ = K-closed→Inv (tr τ) (partOf θE) closed
    where
    closed : ∀ {z} → z ∈ K (partOf θE) → (z ∘ tr τ) ∈ K (partOf θE)
    closed zk = partOf-in θE (classClosed θE τ (partOf-out θE zk))
```

The backward passage is the bridge's inverse at the partition subgroup, whose
membership is decidable (`K-dec`{.AgdaFunction}), extended by the lifts, the
lift-compatibility supplied by the easy half of the invariance transfer.

```agda
  private
    -- the coset relation of an invariant partition is closed under the lifts
    θK-comp : (pv : ParentVec m) → ((τ : Fin T) → Inv (tr τ) pv) → (τ : Fin T)
      → ∀ {x y} → ConRel (B.fromᵈ (toInterval pv , K-dec 𝑭ₛ pv)) x y
      → ConRel (B.fromᵈ (toInterval pv , K-dec 𝑭ₛ pv)) (x ∘ tr τ) (y ∘ tr τ)
    θK-comp pv invτ τ {x} {y} mem =
      K-respects pv (λ i → sym (quot-comp x y (tr τ) i))
        (Inv→K-closed (tr τ) pv (invτ τ) mem)
```

#### The invariant-partition poset and the expansion isomorphism

**The right-hand side of the expansion isomorphism**: partitions invariant under
the whole family, compared by the kernel equality and the reversed refinement of
their underlying partitions (reversed because a larger congruence has a larger
subgroup, hence a *finer* partition).

```agda
  -- A partition invariant under the whole family.
  InvPart : Type 0ℓ
  InvPart = Σ[ pv ∈ ParentVec m ] ((τ : Fin T) → Inv (tr τ) pv)

  infix 4 _≈ᵛ_ _≥ᵛ_

  -- Kernel equality of the underlying partitions.
  _≈ᵛ_ : InvPart → InvPart → Type 0ℓ
  (P , _) ≈ᵛ (Q , _) = P ≈ᵖ Q

  -- The reversed refinement order.
  _≥ᵛ_ : InvPart → InvPart → Type 0ℓ
  (P , _) ≥ᵛ (Q , _) = Q ⊑ P
```

The two maps of the isomorphism.

```agda
  -- A congruence of the expanded algebra yields an invariant partition ...
  toInvPart : DecCon expandedAlgebra 0ℓ → InvPart
  toInvPart θE = partOf θE , partOf-invariant θE

  -- ... and an invariant partition yields a congruence of the expanded algebra.
  fromInvPart : InvPart → DecCon expandedAlgebra 0ℓ
  fromInvPart (pv , invτ) = extend (B.fromᵈ (toInterval pv , K-dec 𝑭ₛ pv)) (θK-comp pv invτ)
```

**Monotonicity**.  Forward: a containment of congruences passes through the bridge
to an inclusion of base-coset classes, which the order-reflection argument of
[Classical.Structures.Group.PartitionSubgroup][] flips to reversed refinement of
the attached partitions (this is the mono-flip step of
`kurzweilIntervalIso`{.AgdaFunction}, taken directly at the decidable elements
this module manipulates).  Backward: reversed refinement is an inclusion of
partition subgroups (`K-antitone`{.AgdaFunction}), which the bridge's inverse
forwards.

```agda
  private
    -- Inclusion of base-coset classes reflects to reversed refinement of the
    -- attached partitions.
    partOf-flip : {θE φE : DecCon expandedAlgebra 0ℓ}
      → intervalOf θE ≤ᵢ intervalOf φE → partOf φE ⊑ partOf θE
    partOf-flip {θE} {φE} le =
      K-reflects s₀ s₀≉ε {pu = partOf φE} {pw = partOf θE}
        λ k → partOf-in φE (le (partOf-out θE k))

  toInvPart-mono : (θE φE : DecCon expandedAlgebra 0ℓ)
    → (∀ {x y} → ConRel θE x y → ConRel φE x y) → toInvPart θE ≥ᵛ toInvPart φE
  toInvPart-mono θE φE sub =
    partOf-flip {θE} {φE} (B.to-mono {forget θE .proj₁} {forget φE .proj₁} sub)

  fromInvPart-mono : (P Q : InvPart) → P ≥ᵛ Q
    → ∀ {x y} → ConRel (fromInvPart P) x y → ConRel (fromInvPart Q) x y
  fromInvPart-mono (pu , _) (pw , _) w⊑u =
    B.from-mono {toInterval pu} {toInterval pw} (K-antitone {pu = pw} {pw = pu} w⊑u)
```

**The round trips**.  On congruences: the relation of the back-and-forth is the
coset relation of `K_{partOf θE}`, which the surjectivity certificates identify
with the base-coset class, and the bridge's round trip identifies with the
original relation.  On partitions: the interval element of the back-and-forth
has the *same* base-coset class as the bridge's image of the partition
subgroup (forgetting and extending leave the relation untouched), so the
bridge's other round trip and injectivity of `K` close the loop.

```agda
  fromInvPart-toInvPart : (θE : DecCon expandedAlgebra 0ℓ)
    → fromInvPart (toInvPart θE) ≑ᵈ θE
  fromInvPart-toInvPart θE = fwd , bwd
    where
    conF = forget θE .proj₁

    fwd : ∀ {x y} → ConRel (fromInvPart (toInvPart θE)) x y → ConRel θE x y
    fwd p = B.from∘to conF .proj₁ (partOf-out θE p)

    bwd : ∀ {x y} → ConRel θE x y → ConRel (fromInvPart (toInvPart θE)) x y
    bwd p = partOf-in θE (B.from∘to conF .proj₂ p)

  toInvPart-fromInvPart : (P : InvPart) → toInvPart (fromInvPart P) ≈ᵛ P
  toInvPart-fromInvPart (pv , invτ) =
    K-injective s₀ s₀≉ε {pu = partOf θP} {pw = pv} Kpv⊆KP KP⊆Kpv
    where
    θP = fromInvPart (pv , invτ)

    -- the base-coset class of the round trip is the bridge image of K pv,
    -- definitionally (extend and forget keep the relation)
    KP⊆Kpv : K (partOf θP) ⊆ K pv
    KP⊆Kpv q = B.to∘from (toInterval pv) .proj₁ (partOf-out θP q)

    Kpv⊆KP : K pv ⊆ K (partOf θP)
    Kpv⊆KP q = partOf-in θP (B.to∘from (toInterval pv) .proj₂ q)

  -- The expansion isomorphism: congruences of the expanded coset algebra
  -- correspond to the family-invariant partitions, order reversed.
  expansionIso : OrderIso  (_≑ᵈ_ {𝑨 = expandedAlgebra} {ℓ = 0ℓ})
                           (_⊆ᵈ_ {𝑨 = expandedAlgebra} {ℓ = 0ℓ})
                           _≈ᵛ_ _≥ᵛ_
  expansionIso = record
    { to         = toInvPart
    ; from       = fromInvPart
    ; to-mono    = λ {θE} {φE} → toInvPart-mono θE φE
    ; from-mono  = λ {P} {Q} → fromInvPart-mono P Q
    ; to∘from    = toInvPart-fromInvPart
    ; from∘to    = fromInvPart-toInvPart
    }
```

--------------------------------------
