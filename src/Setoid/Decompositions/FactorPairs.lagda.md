---
layout: default
file: "src/Setoid/Decompositions/FactorPairs.lagda.md"
title: "Setoid.Decompositions.FactorPairs module (The Agda Universal Algebra Library)"
date: "2026-10-13"
author: "the agda-algebras development team"
---

### Factor pairs of congruences

This is the [Setoid.Decompositions.FactorPairs][] module of the [Agda Universal Algebra Library][].

An algebra `𝑨` is a direct product `𝑩 × 𝑪` exactly when two of its congruences
split it into two independent coordinates.  McKenzie, McNulty, and Taylor make
this precise in *Algebras, Lattices, Varieties* I (ALV below), §4.4.

> **Definition 4.28** (2, 3).  Let `α` and `β` be equivalence relations on a set
> `A`.  We write `0_A = α × β` and call `⟨α, β⟩` a *pair of complementary factor
> relations* iff `α ∧ β = 0_A` and `α ∨ β = 1_A` and moreover `α` and `β` permute.
> Let `α` and `β` be congruences of an algebra `𝑨`.  Then `⟨α, β⟩` is a *pair of
> complementary factor congruences* of `𝑨` iff `0_A = α × β`.
>
> **Theorem 4.29.**  A pair `⟨φ₀, φ₁⟩` of congruences of an algebra gives a direct
> representation iff `0_A = φ₀ × φ₁`.

Here "gives a direct representation" means that the natural map
`x ↦ (x/φ₀ , x/φ₁)` is an isomorphism `𝑨 ≅ 𝑨/φ₀ × 𝑨/φ₁`, and ALV's proof is the
observation that the map is injective iff `φ₀ ∧ φ₁ = 0_A` and onto iff
`φ₀ ∘ φ₁ = 1_A`.  This module formalizes the definition, the theorem, and its
converse.

+  `IsFactorPair`{.AgdaRecord} is Definition 4.28, with its three conditions: the
   meet is the diagonal, the join is the total relation, and the two congruences
   permute (`Permutes`{.AgdaFunction} of [Setoid.Congruences.Permutability][]).
+  `IsProduct₂`{.AgdaRecord} `R θ φ` is the binary case of the product of
   congruences of ALV §5.2: `ψ = θ × φ` means that `ψ = θ ∧ φ` and
   `θ ∘ φ = 1_A`.  For `ψ = 0_A` it is the composite form of a factor pair, in
   which the join, a generated congruence, is replaced by the composite, a
   relation one can compute with; `factorPair→product₂`{.AgdaFunction} and
   `product₂→factorPair`{.AgdaFunction} prove the two forms equivalent.
+  `factorPair→≅`{.AgdaFunction} is Theorem 4.29 from right to left,
   `𝑨 ≅ (𝑨 ╱ θ) ×ᴬ (𝑨 ╱ φ)`, and `natmap₂-bijective→factorPair`{.AgdaFunction}
   is its converse.
+  `≅×→factorPair`{.AgdaFunction} goes the other way round: for any isomorphism
   `𝑨 ≅ 𝑩 ×ᴬ 𝑪`, the kernels of the two coordinate maps form a factor pair, and
   `𝑩` and `𝑪` are the quotients by them (`≅×-factor≅ˡ`{.AgdaFunction},
   `≅×-factor≅ʳ`{.AgdaFunction}).
+  `product₂-decˡ`{.AgdaFunction} records a constructive fact that the finite
   theory of [Setoid.Decompositions.Finite][] rests on: if `ψ = θ × φ` and `ψ` is
   decidable, then so is `θ`, given one element of the carrier.  In particular the
   factor congruences of an algebra with decidable equality are decidable, with no
   finiteness or classical assumption.

The products of arbitrary families of congruences are in
[Setoid.Decompositions.Products][], and indecomposability in
[Setoid.Decompositions.Indecomposable][].

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Decompositions.FactorPairs where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive               using () renaming ( Set to Type )
open import Data.Product                 using ( _,_ ; proj₁ ; proj₂ ; swap )
open import Function                     using ( id ) renaming ( Func to _⟶_ )
open import Level                        using ( Level ; _⊔_ )
open import Relation.Binary              using ( Setoid ; IsEquivalence ; _⇒_ )
                                         renaming ( Rel to BinaryRel )
open import Relation.Nullary             using ( Dec )
open import Relation.Nullary.Decidable   using ( map′ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                            using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras                     using ( Algebra ; 𝕌[_] ; 𝔻[_] ; _×ᴬ_ )
open import Setoid.Congruences.Basic            using ( Con ; _╱_ ; is-equivalence
                                                      ; reflexive )
open import Setoid.Congruences.Generation       using ( _∨_ )
open import Setoid.Congruences.Lattice          using ( _∧_ ; _≑_ )
open import Setoid.Congruences.Monolith         using ( BelowDiagonal ; Trivial )
open import Setoid.Congruences.Permutability    using ( _∘_ ; Permutes ; ∘⊆∨
                                                      ; permutes→∨⊆∘ )
open import Setoid.Functions                    using ( IsInjective ; IsSurjective
                                                      ; Image_∋_ )
open import Setoid.Homomorphisms.Basic          using ( hom ; 𝒾𝒹 )
open import Setoid.Homomorphisms.Isomorphisms   using ( _≅_ ; Bijective→≅ ; ≅toInjective )
open import Setoid.Homomorphisms.Kernels        using ( kercon ; πhom )
open import Setoid.Homomorphisms.Noether        using ( FirstIsoTheorem )
open import Setoid.Homomorphisms.Products       using ( ×-hom-co ; ×-proj₁ ; ×-proj₂ )
open import Setoid.Homomorphisms.Properties     using ( ⊙-hom )

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )
open _≅_ using ( to ; from ; to∼from )

private variable α ρ β ρᵇ ℓ ℓ′ ℓ″ : Level
```
-->

#### The product of two congruences

Fix an algebra `𝑨` and congruences `θ` and `φ`.  ALV §5.2 calls a congruence `ψ`
the *product* of `θ` and `φ`, written `ψ = θ × φ`, when the natural map
`𝑨/ψ → 𝑨/θ × 𝑨/φ` is a bijection; Lemma 1 there shows that this happens exactly
when `ψ = θ ∧ φ` and `θ ∘ φ = 1_A` ("that `θ₀` and `θ₁` permute, and that their
join is `1`").  We take that characterization as the definition, stated for the
relation `R` of `ψ` so that `ψ` may be the diagonal `0_A`, which is the setoid
equality `_≈_` itself.

The record `IsProduct₂`{.AgdaRecord} `R θ φ` therefore has three fields: `R` is
contained in the meet (`to-meet`{.AgdaField}), the meet is contained in `R`
(`from-meet`{.AgdaField}), and every pair is related by the composite
(`composite`{.AgdaField}), whose witness `z` with `x θ z φ y` is the element
"with the first coordinate of `x` and the second coordinate of `y`".

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- ψ = θ × φ (ALV §5.2), for the relation R of ψ: R = θ ∧ φ and θ ∘ φ = 1_A.
  record IsProduct₂ (R : BinaryRel 𝕌[ 𝑨 ] ℓ′) (θ φ : Con 𝑨 ℓ) : Type (α ⊔ ℓ ⊔ ℓ′) where
    field
      to-meet    : ∀ {x y} → R x y → proj₁ (θ ∧ φ) x y
      from-meet  : ∀ {x y} → proj₁ (θ ∧ φ) x y → R x y
      composite  : ∀ x y → (θ ∘ φ) x y

  open IsProduct₂ public
```

A factor pair in the sense of Definition 4.28 is a pair of congruences whose meet
is the diagonal, whose join is the total relation, and which permute.  The join
`_∨_`{.AgdaFunction} is the generated congruence of
[Setoid.Congruences.Generation][] and permutation is the single inclusion
`Permutes`{.AgdaFunction}, which implies the textbook equation by
`Permutes-sym`{.AgdaFunction}.

```agda
  -- ⟨θ , φ⟩ is a pair of complementary factor congruences (ALV Definition 4.28).
  record IsFactorPair (θ φ : Con 𝑨 ℓ) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ ℓ) where
    field
      meet-zero  : BelowDiagonal 𝑨 (θ ∧ φ)               -- θ ∧ φ = 0_A
      join-one   : ∀ x y → proj₁ (θ ∨ φ) x y             -- θ ∨ φ = 1_A
      permute    : Permutes θ φ                          -- θ ∘ φ = φ ∘ θ

  open IsFactorPair public
```

#### The two forms of a factor pair

The composite of a factor pair is the total relation, because the two congruences
permute and so their join *is* their composite (`permutes→∨⊆∘`{.AgdaFunction} of
[Setoid.Congruences.Permutability][]).  Conversely a total composite gives the
total join, which contains it (`∘⊆∨`{.AgdaFunction}), and permutation, since then
both composites are total.  So a factor pair is the same thing as a product
decomposition `0_A = θ × φ` of the diagonal; this is ALV's remark after
Definition 4.28 and the content of its proof of Theorem 4.29.

The swapped composite `φ ∘ θ` of a product is total along with `θ ∘ φ`, since
the converse of a composite of congruences is the composite in the other order
(`composite-swap`{.AgdaFunction}).

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
  private variable θ θ′ φ φ′ : Con 𝑨 ℓ

  -- In ψ = θ × φ, the composite in the other order is total too.
  composite-swap : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′} → IsProduct₂ R θ φ → ∀ x y → (φ ∘ θ) x y
  composite-swap {θ = θ} {φ = φ} p x y =
    let (z , yθz , zφx) = composite p y x
    in  z , IsEquivalence.sym (is-equivalence (proj₂ φ)) zφx
          , IsEquivalence.sym (is-equivalence (proj₂ θ)) yθz

  -- The diagonal is below every meet of congruences.
  ≈→meet : ∀ {x y} → x ≈ y → proj₁ (θ ∧ φ) x y
  ≈→meet {θ = θ} {φ = φ} x≈y = reflexive (proj₂ θ) x≈y , reflexive (proj₂ φ) x≈y

  -- A factor pair (Definition 4.28) is a product decomposition 0_A = θ × φ.
  factorPair→product₂ : IsFactorPair θ φ → IsProduct₂ _≈_ θ φ
  factorPair→product₂ {θ = θ} {φ = φ} fp = record
    { to-meet    = ≈→meet {θ = θ} {φ = φ}
    ; from-meet  = meet-zero fp
    ; composite  = λ x y → permutes→∨⊆∘ θ φ (permute fp) (join-one fp x y)
    }

  -- A product decomposition 0_A = θ × φ is a factor pair.
  product₂→factorPair : IsProduct₂ _≈_ θ φ → IsFactorPair θ φ
  product₂→factorPair {θ = θ} {φ = φ} p = record
    { meet-zero  = from-meet p
    ; join-one   = λ x y → ∘⊆∨ θ φ (composite p x y)
    ; permute    = λ {x} {y} _ → composite-swap p x y
    }
```

Both forms are symmetric in the two factors, and both respect the equality `_≑_`
of congruences (mutual containment); the product form also respects replacing
`R` by an equivalent relation.  `product₂-sym`{.AgdaFunction},
`factorPair-sym`{.AgdaFunction}, `product₂-≑`{.AgdaFunction}, and
`product₂-resp`{.AgdaFunction} record these facts.

```agda
  -- ψ = θ × φ implies ψ = φ × θ.
  product₂-sym : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′} → IsProduct₂ R θ φ → IsProduct₂ R φ θ
  product₂-sym p = record
    { to-meet    = λ r → swap (to-meet p r)
    ; from-meet  = λ m → from-meet p (swap m)
    ; composite  = composite-swap p
    }

  -- ⟨θ , φ⟩ is a factor pair iff ⟨φ , θ⟩ is.
  factorPair-sym : IsFactorPair θ φ → IsFactorPair φ θ
  factorPair-sym fp = product₂→factorPair (product₂-sym (factorPair→product₂ fp))

  -- The product of two congruences respects ≑ in each factor.
  product₂-≑ : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}
    → θ ≑ θ′ → φ ≑ φ′ → IsProduct₂ R θ φ → IsProduct₂ R θ′ φ′
  product₂-≑ (θ⊆θ′ , θ′⊆θ) (φ⊆φ′ , φ′⊆φ) p = record
    { to-meet    = λ r → let (a , b) = to-meet p r in θ⊆θ′ a , φ⊆φ′ b
    ; from-meet  = λ (a , b) → from-meet p (θ′⊆θ a , φ′⊆φ b)
    ; composite  = λ x y → let (z , a , b) = composite p x y in z , θ⊆θ′ a , φ⊆φ′ b
    }

  -- The product of two congruences respects equivalence of the relation R.
  product₂-resp : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{R′ : BinaryRel 𝕌[ 𝑨 ] ℓ″}
    → R ⇒ R′ → R′ ⇒ R → IsProduct₂ R θ φ → IsProduct₂ R′ θ φ
  product₂-resp R⇒R′ R′⇒R p = record
    { to-meet    = λ r → to-meet p (R′⇒R r)
    ; from-meet  = λ m → R⇒R′ (from-meet p m)
    ; composite  = composite p
    }
```

In a product `ψ = θ × φ` one factor is trivial exactly when the other is
already below `ψ`: if `𝑨 ╱ θ` is trivial then `φ = θ ∧ φ ⊆ ψ`, and if `φ ⊆ ψ` then
every `x θ z φ y` gives `z ψ y`, hence `z θ y` and `x θ y`.  For a factor pair
(`ψ = 0_A`) this says that `θ = 1_A` iff `φ = 0_A`: the trivial factor of a
direct decomposition is the one whose complement is the diagonal.

```agda
  -- If 𝑨 ╱ θ is trivial, then φ is below ψ.
  product₂-trivialˡ→ : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}
    → IsProduct₂ R θ φ → Trivial (𝑨 ╱ θ) → proj₁ φ ⇒ R
  product₂-trivialˡ→ p θ1 {x} {y} xφy = from-meet p (θ1 x y , xφy)

  -- If φ is below ψ, then 𝑨 ╱ θ is trivial.
  product₂-→trivialˡ : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}
    → IsProduct₂ R θ φ → proj₁ φ ⇒ R → Trivial (𝑨 ╱ θ)
  product₂-→trivialˡ {θ = θ} p φ⇒R x y =
    let (z , xθz , zφy) = composite p x y
    in  IsEquivalence.trans (is-equivalence (proj₂ θ)) xθz (proj₁ (to-meet p (φ⇒R zφy)))
```

#### Theorem 4.29: the decomposition isomorphism

The natural map `natmap₂ θ φ`{.AgdaFunction} sends `x` to the pair of its classes,
`(x/θ , x/φ)`; it is the pairing (`×-hom-co`{.AgdaFunction}) of the two quotient
maps.  Two elements have the same image exactly when they are related by both `θ`
and `φ`, so the map is injective iff `θ ∧ φ = 0_A`; this holds *definitionally*,
as in the subdirect case of [Setoid.Subalgebras.Subdirect.Basic][].  A pair of
classes `(a/θ , b/φ)` has a preimage `z` exactly when `a θ z φ b`, so the map is
onto iff `θ ∘ φ = 1_A`.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (θ φ : Con 𝑨 ℓ) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
  private
    φsym : ∀ {x y} → proj₁ φ x y → proj₁ φ y x
    φsym = IsEquivalence.sym (is-equivalence (proj₂ φ))

  -- The natural map x ↦ (x/θ , x/φ).
  natmap₂ : hom 𝑨 ((𝑨 ╱ θ) ×ᴬ (𝑨 ╱ φ))
  natmap₂ = ×-hom-co (πhom 𝒾𝒹 θ) (πhom 𝒾𝒹 φ)

  -- Injectivity of the natural map is the condition θ ∧ φ = 0_A, definitionally.
  natmap₂-injective : BelowDiagonal 𝑨 (θ ∧ φ) → IsInjective (proj₁ natmap₂)
  natmap₂-injective = id

  natmap₂-injective⁻ : IsInjective (proj₁ natmap₂) → BelowDiagonal 𝑨 (θ ∧ φ)
  natmap₂-injective⁻ = id

  -- The natural map is onto when θ ∘ φ = 1_A ...
  natmap₂-surjective : (∀ x y → (θ ∘ φ) x y) → IsSurjective (proj₁ natmap₂)
  natmap₂-surjective c {a , b} = let (z , aθz , zφb) = c a b in Image_∋_.eq z (aθz , φsym zφb)

  -- ... and only then.
  natmap₂-surjective⁻ : IsSurjective (proj₁ natmap₂) → ∀ x y → (θ ∘ φ) x y
  natmap₂-surjective⁻ s x y = preimage (s {x , y})
    where
    preimage : Image (proj₁ natmap₂) ∋ (x , y) → (θ ∘ φ) x y
    preimage (Image_∋_.eq z (xθz , yφz)) = z , xθz , φsym yφz
```

Theorem 4.29 follows: a factor pair makes the natural map a bijective
homomorphism, hence an isomorphism `𝑨 ≅ (𝑨 ╱ θ) ×ᴬ (𝑨 ╱ φ)`
(`factorPair→≅`{.AgdaFunction}), and conversely a bijective natural map makes the
pair a factor pair (`natmap₂-bijective→factorPair`{.AgdaFunction}).

```agda
  -- ALV Theorem 4.29, (⇐): a factor pair gives the direct representation 𝑨 ≅ 𝑨/θ × 𝑨/φ.
  factorPair→≅ : IsFactorPair θ φ → 𝑨 ≅ ((𝑨 ╱ θ) ×ᴬ (𝑨 ╱ φ))
  factorPair→≅ fp = Bijective→≅ natmap₂  (natmap₂-injective (meet-zero fp))
                                         (natmap₂-surjective (composite (factorPair→product₂ fp)))

  -- ALV Theorem 4.29, (⇒): if the natural map is bijective, ⟨θ , φ⟩ is a factor pair.
  natmap₂-bijective→factorPair : IsInjective (proj₁ natmap₂) → IsSurjective (proj₁ natmap₂)
    → IsFactorPair θ φ
  natmap₂-bijective→factorPair inj surj = product₂→factorPair record
    { to-meet    = ≈→meet {θ = θ} {φ = φ}
    ; from-meet  = natmap₂-injective⁻ inj
    ; composite  = natmap₂-surjective⁻ surj
    }
```

#### Every direct decomposition comes from a factor pair

Conversely, let `f : 𝑨 ≅ 𝑩 ×ᴬ 𝑪` be any isomorphism onto a binary product.  The
kernels `≅×-kerˡ f`{.AgdaFunction} and `≅×-kerʳ f`{.AgdaFunction} of its two
coordinate maps form a factor pair (ALV §5.2: "an isomorphism `f : 𝑨 → ∏ 𝑩ᵢ` is
determined within isomorphism by certain congruences `αᵢ` on `𝑨`, namely
`αᵢ = ker pᵢ ∘ f`").  Their meet is the kernel of `f` itself, the diagonal; and
any two elements `x` and `y` are linked by the element `z` whose image has the
first coordinate of `f x` and the second coordinate of `f y`.  The two factors are
taken at the same levels, so that the two kernels are congruences at one level.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {𝑩 𝑪 : Algebra {𝑆 = 𝑆} β ρᵇ}
         (f : 𝑨 ≅ (𝑩 ×ᴬ 𝑪)) where
  open Setoid 𝔻[ 𝑩 ] using () renaming ( sym to symᵇ )

  -- The coordinate maps of f.
  ≅×-coordˡ : hom 𝑨 𝑩
  ≅×-coordˡ = ⊙-hom (to f) ×-proj₁

  ≅×-coordʳ : hom 𝑨 𝑪
  ≅×-coordʳ = ⊙-hom (to f) ×-proj₂

  -- Their kernels, ker (p₁ ∘ f) and ker (p₂ ∘ f).
  ≅×-kerˡ : Con 𝑨 ρᵇ
  ≅×-kerˡ = kercon ≅×-coordˡ

  ≅×-kerʳ : Con 𝑨 ρᵇ
  ≅×-kerʳ = kercon ≅×-coordʳ

  -- The kernels of the coordinate maps of 𝑨 ≅ 𝑩 × 𝑪 decompose the diagonal.
  ≅×→product₂ : IsProduct₂ (Setoid._≈_ 𝔻[ 𝑨 ]) ≅×-kerˡ ≅×-kerʳ
  ≅×→product₂ = record
    { to-meet    = λ x≈y → cong (proj₁ ≅×-coordˡ) x≈y , cong (proj₁ ≅×-coordʳ) x≈y
    ; from-meet  = ≅toInjective f
    ; composite  = linked
    }
    where
    linked : ∀ x y → (≅×-kerˡ ∘ ≅×-kerʳ) x y
    linked x y = z , Setoid.sym 𝔻[ 𝑩 ] (proj₁ fz≈) , proj₂ fz≈
      where
      z = from f .proj₁ ⟨$⟩ (proj₁ (to f .proj₁ ⟨$⟩ x) , proj₂ (to f .proj₁ ⟨$⟩ y))
      fz≈ = to∼from f (proj₁ (to f .proj₁ ⟨$⟩ x) , proj₂ (to f .proj₁ ⟨$⟩ y))

  -- ... so they form a factor pair.
  ≅×→factorPair : IsFactorPair ≅×-kerˡ ≅×-kerʳ
  ≅×→factorPair = product₂→factorPair ≅×→product₂
```

Each factor is recovered as the quotient by the kernel of its coordinate map, by
the first isomorphism theorem (`FirstIsoTheorem`{.AgdaFunction} of
[Setoid.Homomorphisms.Noether][]), once the coordinate map is known to be onto.
The first coordinate map hits `b` at the preimage of `(b , c)`, for any element
`c` of the other factor, so each statement takes an element of the other factor.
(Some element is needed: if `𝑪` is empty then so is `𝑨`, while `𝑩` need not be.)

```agda
  -- 𝑩 ≅ 𝑨 ╱ ker (p₁ ∘ f), given an element of 𝑪.
  ≅×-factor≅ˡ : 𝕌[ 𝑪 ] → (𝑨 ╱ ≅×-kerˡ) ≅ 𝑩
  ≅×-factor≅ˡ c = FirstIsoTheorem ≅×-coordˡ onto
    where
    onto : IsSurjective (proj₁ ≅×-coordˡ)
    onto {b} = Image_∋_.eq (from f .proj₁ ⟨$⟩ (b , c)) (symᵇ (proj₁ (to∼from f (b , c))))

  -- 𝑪 ≅ 𝑨 ╱ ker (p₂ ∘ f), given an element of 𝑩.
  ≅×-factor≅ʳ : 𝕌[ 𝑩 ] → (𝑨 ╱ ≅×-kerʳ) ≅ 𝑪
  ≅×-factor≅ʳ b = FirstIsoTheorem ≅×-coordʳ onto
    where
    onto : IsSurjective (proj₁ ≅×-coordʳ)
    onto {c} = Image_∋_.eq (from f .proj₁ ⟨$⟩ (b , c))
                           (Setoid.sym 𝔻[ 𝑪 ] (proj₂ (to∼from f (b , c))))
```

#### Factor congruences are decidable

Fix a product `ψ = θ × φ` and an element `u`.  Every `x` determines the element
`coordˡ`{.AgdaFunction}` x` with `x θ coordˡ x φ u`; think of it as the element
with the `θ`-coordinate of `x` and the `φ`-coordinate of `u`.  Then `x θ y` holds
exactly when `coordˡ x ψ coordˡ y`: the two are `θ`-related through `x` and `y`,
and `φ`-related through `u`, so related by `θ ∧ φ = ψ`; and conversely `ψ ⊆ θ`.
So **`θ` is decidable as soon as `ψ` is**, and the decision costs one evaluation of
`ψ`.  With `ψ = 0_A` this says that the factor congruences of an algebra with
decidable equality are decidable.

The point matters for finite algebras.  Their semantic congruences need not be
decidable (see ADR-008 and [Setoid.Congruences.Finite.Basic][]), so a complete
list of *decidable* congruences says nothing, in general, about the semantic
ones.  But it does say everything about the factor pairs, which is what
[Setoid.Decompositions.Finite][] uses to decide direct indecomposability with no
classical assumption.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}
         {θ φ : Con 𝑨 ℓ} (p : IsProduct₂ R θ φ) (u : 𝕌[ 𝑨 ]) where
  private
    θsym = IsEquivalence.sym (is-equivalence (proj₂ θ))
    θtrans = IsEquivalence.trans (is-equivalence (proj₂ θ))
    φsym = IsEquivalence.sym (is-equivalence (proj₂ φ))
    φtrans = IsEquivalence.trans (is-equivalence (proj₂ φ))

  -- The element with the θ-coordinate of x and the φ-coordinate of u.
  coordˡ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  coordˡ x = proj₁ (composite p x u)

  -- θ-related elements have ψ-related coordinates ...
  θ→coordˡ : ∀ {x y} → proj₁ θ x y → R (coordˡ x) (coordˡ y)
  θ→coordˡ {x} {y} xθy =
    let (_ , xθx′ , x′φu) = composite p x u
        (_ , yθy′ , y′φu) = composite p y u
    in  from-meet p ( θtrans (θsym xθx′) (θtrans xθy yθy′)
                    , φtrans x′φu (φsym y′φu) )

  -- ... and conversely.
  coordˡ→θ : ∀ {x y} → R (coordˡ x) (coordˡ y) → proj₁ θ x y
  coordˡ→θ {x} {y} r =
    let (_ , xθx′ , _) = composite p x u
        (_ , yθy′ , _) = composite p y u
    in  θtrans xθx′ (θtrans (proj₁ (to-meet p r)) (θsym yθy′))

  -- If ψ is decidable, then so is its factor θ.
  product₂-decˡ : (∀ x y → Dec (R x y)) → ∀ x y → Dec (proj₁ θ x y)
  product₂-decˡ R? x y = map′ coordˡ→θ θ→coordˡ (R? (coordˡ x) (coordˡ y))
```

By symmetry the same holds for the other factor.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}
         {θ φ : Con 𝑨 ℓ} where
  -- If ψ = θ × φ is decidable, then so is φ.
  product₂-decʳ : IsProduct₂ R θ φ → 𝕌[ 𝑨 ] → (∀ x y → Dec (R x y))
    → ∀ x y → Dec (proj₁ φ x y)
  product₂-decʳ p u = product₂-decˡ (product₂-sym p) u
```
