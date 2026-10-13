---
layout: default
file: "src/Setoid/Decompositions/StrictRefinement.lagda.md"
title: "Setoid.Decompositions.StrictRefinement module (The Agda Universal Algebra Library)"
date: "2026-10-13"
author: "the agda-algebras development team"
---

### The strict refinement property and unique factorization

This is the [Setoid.Decompositions.StrictRefinement][] module of the [Agda Universal Algebra Library][].

The integers factor uniquely into primes, and so, by the theorem of Wedderburn
and Remak, do finite groups into directly indecomposable groups.  McKenzie,
McNulty, and Taylor, *Algebras, Lattices, Varieties* I (ALV below), Chapter 5, is
the study of when an algebra factors uniquely, in this sense.

> **§5.1.**  We say that `𝑨` has the *unique factorization property* (UFP), or is
> *uniquely factorable*, iff (i) `𝑨` is isomorphic to a product of directly
> indecomposable algebras, and (ii) this representation is unique; that is, if
> `𝑨 ≅ ∏_{i∈I} 𝑩ᵢ ≅ ∏_{j∈J} 𝑪ⱼ` for some index sets `I` and `J` and for directly
> indecomposable algebras `𝑩ᵢ` and `𝑪ⱼ`, then there is a bijection `φ : I → J`
> such that `𝑩ᵢ ≅ 𝑪_{φ(i)}` for all `i`.
>
> **§5.6.**  The *strict refinement property* for `𝑨` asserts that if
> `0 = ∏_{i∈I} βᵢ = ∏_{j∈J} γⱼ` for congruences `βᵢ`, `γⱼ` on `𝑨`, then there exist
> congruences `δᵢⱼ` (`i ∈ I`, `j ∈ J`) such that, for all `i` and `j`,
> `βᵢ = ∏_{j∈J} δᵢⱼ` and `γⱼ = ∏_{i∈I} δᵢⱼ`.
>
> **Theorem 5.16.**  If `𝑨` has the strict refinement property, then `𝑨` has the
> refinement property.  If, moreover, `0 = ∏_{i∈I} αᵢ = ∏_{j∈J} βⱼ` in `Con 𝑨`, with
> each `αᵢ` and each `βⱼ` indecomposable, then `{αᵢ : i ∈ I} = {βⱼ : j ∈ J}`.
>
> **Corollary.**  If `∏_{i∈I} 𝑩ᵢ` has the strict refinement property, all `𝑩ᵢ` and
> all `𝑪ⱼ` are directly indecomposable and `f : ∏ 𝑩ᵢ → ∏ 𝑪ⱼ` is an isomorphism,
> then there exists a bijection `λ : J → I` and a family of isomorphisms
> `fⱼ : 𝑩_{λ(j)} → 𝑪ⱼ` [such that `f` acts coordinatewise through them].

The products here are products of congruences in the sense of ALV §5.2
([Setoid.Decompositions.Products][]).  This module formalizes the following:

+  `HasStrictRefinement`{.AgdaFunction} `ι ℓ 𝑨` is the strict refinement property
   as ALV states it, for index types at a level `ι` and congruences at level `ℓ`;
   `HasFiniteStrictRefinement`{.AgdaFunction} is its restriction to finite index
   sets, which ALV's Theorem 5.17 (ii) proves equivalent to it, and which follows
   from it at every level (`strict→finite`{.AgdaFunction}).
+  The second sentence of Theorem 5.16, for finite index sets
   (`srp-unique`{.AgdaFunction}): two decompositions of `0_A` into finitely many
   indecomposable congruences consist of the same congruences, up to `≑` and a
   bijection of the indices; so they have the same length (`srp-length`{.AgdaFunction}).
+  Condition (ii) of unique factorization from the strict refinement property,
   for finite index sets (`srp→unique`{.AgdaFunction}, the Corollary in the form
   that matters: the factors match up to isomorphism along a bijection).
+  `IsUniquelyFactorable`{.AgdaRecord}, the unique factorization property of §5.1
   for finite index sets, and the theorem the section is aiming for: **a finite
   algebra with the strict refinement property is uniquely factorable**
   (`finite-srp→uniquelyFactorable`{.AgdaFunction}, and
   `finitary-srp→uniquelyFactorable`{.AgdaFunction} over a finite signature),
   existence coming from [Setoid.Decompositions.Finite][].

The index sets are finite (`Fin n`) because the factors must be found: in an
indecomposable congruence `αᵢ = ∏ⱼ δᵢⱼ`, the one index `j` with `δᵢⱼ ≠ 1` is
located by recursion on the list of factors, splitting off one factor at a time
by the binary indecomposability of `αᵢ`.  For a finite algebra nothing is lost,
since a product of infinitely many nontrivial algebras is infinite; ALV's
definition with arbitrary index sets is kept, so that the restriction is visible.

Two theorems that this chapter of ALV is known for are stated here, with
references, but not formalized.

+  **Jónsson and Tarski** (*Direct Decompositions of Finite Algebraic Systems*,
   Notre Dame Mathematical Lectures 5, 1947): every finite algebra with zero is
   uniquely factorable, where an *algebra with zero* has a binary operation `+`
   and a one-element subuniverse `{0}` with `0 + x ≈ x + 0 ≈ x` (ALV §5.4, the
   Jónsson–Tarski Unique Factorization Theorem 5.8).
+  **Lovász** ("Operations with structures", Acta Mathematica Academiae
   Scientiarum Hungaricae 18, 1967): for finite algebras, `𝑨ᵏ ≅ 𝑩ᵏ` with `k > 0`
   implies `𝑨 ≅ 𝑩`, and if `𝑪` has a one-element subuniverse then
   `𝑨 × 𝑪 ≅ 𝑩 × 𝑪` implies `𝑨 ≅ 𝑩` (ALV §5.7, Corollaries 2 and 3 of
   Theorem 5.23).  The cancellation law needs the one-element subuniverse.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Decompositions.StrictRefinement where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Data.Empty                              using ( ⊥-elim )
open import Data.Fin.Base                           using ( Fin ; zero ; suc )
open import Data.Fin.Permutation                    using ( Permutation ; permutation
                                                          ; _⟨$⟩ʳ_ ; ↔⇒≡ )
open import Data.Fin.Properties                     using ( _≟_ )
open import Data.Nat.Base                           using ( ℕ ; zero ; suc )
open import Data.Product                            using ( _×_ ; _,_ ; proj₁ ; proj₂
                                                          ; Σ-syntax )
open import Data.Sum.Base                           using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                                   using ( Level ; _⊔_ ; lift ; lower )
                                                    renaming ( suc to lsuc )
open import Relation.Binary                         using ( Setoid )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; _≢_ ; refl ; subst ; cong
                                                          ; sym )
open import Relation.Nullary                        using ( yes ; no )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                              using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras                       using ( Algebra ; ov ; 𝕌[_] ; 𝔻[_] ; ⨅ )
open import Setoid.Algebras.Finite                using ( FiniteAlgebra )
open import Setoid.Congruences.Basic              using ( Con ; _╱_ )
open import Setoid.Congruences.Finite             using ( FiniteCongruencesᵈ
                                                        ; FiniteAlgebra→FiniteCongruencesᵈ )
open import Setoid.Congruences.Lattice            using ( _≑_ )
open import Setoid.Congruences.Monolith           using ( Trivial )
open import Setoid.Decompositions.Finite          using ( finite-decomposition≅ )
open import Setoid.Signatures.Finite              using ( FiniteSignature )
open import Setoid.Subalgebras.Subdirect.Basic    using ( 𝑨╱ )
open import Setoid.Decompositions.Indecomposable  using ( IsDirectlyIndecomposable
                                                        ; nontrivial ; IsIndecomposable
                                                        ; quotient-nontrivial ; product-trivial
                                                        ; directly→indecomposable
                                                        ; ≅-indecomposable ; ≑→╱≅ )
open import Setoid.Decompositions.Products        using ( IsProduct ; to-⋂ ; from-⋂
                                                        ; interpolate ; product-empty→total
                                                        ; ⋂-tail ; product-split
                                                        ; product-reindex ; ≅⨅-ker
                                                        ; ≅⨅→product ; ≅⨅-factor≅ )
open import Setoid.Homomorphisms.Isomorphisms     using ( _≅_ ; ≅-sym ; ≅-trans )

private variable α ρ β ρᵇ ι ℓ : Level
```
-->

#### The strict refinement property

`HasStrictRefinement`{.AgdaFunction} `ι ℓ 𝑨` is ALV's definition, for families of
congruences at level `ℓ` indexed by types at level `ι`: any two decompositions
`0_A = ∏ β = ∏ γ` have a common refinement `δ`, whose rows decompose the members
of `β` and whose columns decompose the members of `γ`.  These "compatibility
conditions" are the point of the definition: each `βᵢ` is *the product* of the
`i`-th row, not merely its meet.

`HasFiniteStrictRefinement`{.AgdaFunction} `ℓ 𝑨` asks the same of decompositions
indexed by finite sets `Fin m` and `Fin n`.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where

  -- The strict refinement property (ALV §5.6).
  HasStrictRefinement : (ι ℓ : Level) → Algebra {𝑆 = 𝑆} α ρ → Type (α ⊔ ρ ⊔ lsuc ι ⊔ ov {𝑆 = 𝑆} ℓ)
  HasStrictRefinement ι ℓ 𝑨 =
    {I J : Type ι} (β : I → Con 𝑨 ℓ) (γ : J → Con 𝑨 ℓ)
    → IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) β → IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) γ
    → Σ[ δ ∈ (I → J → Con 𝑨 ℓ) ]  (∀ i → IsProduct (proj₁ (β i)) (δ i))
                                × (∀ j → IsProduct (proj₁ (γ j)) (λ i → δ i j))

  -- The strict refinement property for finite index sets (ALV Theorem 5.17 (ii)).
  HasFiniteStrictRefinement : (ℓ : Level) → Algebra {𝑆 = 𝑆} α ρ → Type (α ⊔ ρ ⊔ ov {𝑆 = 𝑆} ℓ)
  HasFiniteStrictRefinement ℓ 𝑨 =
    {m n : ℕ} (β : Fin m → Con 𝑨 ℓ) (γ : Fin n → Con 𝑨 ℓ)
    → IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) β → IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) γ
    → Σ[ δ ∈ (Fin m → Fin n → Con 𝑨 ℓ) ]  (∀ i → IsProduct (proj₁ (β i)) (δ i))
                                        × (∀ j → IsProduct (proj₁ (γ j)) (λ i → δ i j))
```

The property at any index level gives the finite one: a decomposition indexed by
`Fin m` is reindexed by `Lift ι (Fin m)`, refined there, and the refinement is
reindexed back (`product-reindex`{.AgdaFunction}, along `lift` and `lower`).

```agda
  -- The strict refinement property gives its finite form.
  strict→finite : {𝑨 : Algebra {𝑆 = 𝑆} α ρ} → HasStrictRefinement ι ℓ 𝑨 → HasFiniteStrictRefinement ℓ 𝑨
  strict→finite {ι = ι} srp {m} {n} β γ pβ pγ =
    let (δ , pδβ , pδγ) = srp (λ i → β (lower i)) (λ j → γ (lower j))
                              (product-reindex lower lift (λ _ → refl) (λ _ → refl) pβ)
                              (product-reindex lower lift (λ _ → refl) (λ _ → refl) pγ)
    in  (λ i j → δ (lift i) (lift j))
      , (λ i → product-reindex lift lower (λ _ → refl) (λ _ → refl) (pδβ (lift i)))
      , (λ j → product-reindex lift lower (λ _ → refl) (λ _ → refl) (pδγ (lift j)))
```

#### An indecomposable product has one nontrivial factor

The heart of Theorem 5.16 is the following observation.  If an indecomposable
congruence `θ` is a product `∏_{j<n} δⱼ`, then exactly one factor `δⱼ` is not
total, and `θ = δⱼ`.  Split the product as `θ = δ₀ × ⋂_{j>0} δⱼ`
(`product-split`{.AgdaFunction}); by indecomposability one of the two is total.
If the meet of the rest is total, then so is every later factor, and `θ = δ₀`.
If `δ₀` is total, then `θ` is the product of the rest, and we recurse.  An empty
product would make `θ` total, contradicting `|A/θ| > 1`.

The statement records the index `j`, that `θ ≑ δⱼ`, and that every other factor
is total.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- An indecomposable product of a list of congruences has exactly one non-total factor.
  indecomposable-product : {n : ℕ} {θ : Con 𝑨 ℓ} {δ : Fin n → Con 𝑨 ℓ}
    → IsIndecomposable θ → IsProduct (proj₁ θ) δ
    → Σ[ j ∈ Fin n ] (θ ≑ δ j) × (∀ k → k ≢ j → Trivial (𝑨 ╱ δ k))
  indecomposable-product {n = zero} ind p =
    let (a , b , ¬ab) = quotient-nontrivial ind in ⊥-elim (¬ab (product-empty→total p a b))
  indecomposable-product {n = suc n} {θ} {δ} ind p =
    step (product-trivial ind (δ zero) (⋂-tail δ) (product-split p))
    where
    -- An element, for interpolating the shorter product.
    u : 𝕌[ 𝑨 ]
    u = proj₁ (quotient-nontrivial ind)

    -- If δ₀ is total, θ is the product of the remaining factors.
    rest : Trivial (𝑨 ╱ δ zero) → IsProduct (proj₁ θ) (λ k → δ (suc k))
    rest δ₀-total = record
      { to-⋂         = λ r k → to-⋂ p r (suc k)
      ; from-⋂       = λ {x} {y} h → from-⋂ p λ { zero → δ₀-total x y ; (suc k) → h k }
      ; interpolate  = λ a → let (b , ab) = interpolate p λ { zero → u ; (suc k) → a k }
                             in  b , λ k → ab (suc k)
      }

    step : Trivial (𝑨 ╱ δ zero) ⊎ Trivial (𝑨 ╱ ⋂-tail δ)
      → Σ[ j ∈ Fin (suc n) ] (θ ≑ δ j) × (∀ k → k ≢ j → Trivial (𝑨 ╱ δ k))
    step (inj₂ tail-total) =
      zero , ((λ r → to-⋂ p r zero) , λ {x} {y} r → from-⋂ p λ { zero → r
                                                                ; (suc k) → tail-total x y (lift k) })
           , λ { zero 0≢0 → ⊥-elim (0≢0 refl) ; (suc k) _ → λ a b → tail-total a b (lift k) }
    step (inj₁ head-total) =
      let (j , θ≑ , others) = indecomposable-product ind (rest head-total)
      in  suc j , θ≑ , λ { zero _ → head-total
                         ; (suc k) k≢j → others k λ k≡j → k≢j (cong suc k≡j) }
```

#### Theorem 5.16: decompositions into indecomposables coincide

Now let `0_A = ∏_{i<m} αᵢ = ∏_{j<n} βⱼ` with every `αᵢ` and `βⱼ` indecomposable,
and refine the two decompositions by the strict refinement property:
`αᵢ = ∏ⱼ δᵢⱼ` and `βⱼ = ∏ᵢ δᵢⱼ`.  By the lemma, each row `i` has exactly one
non-total entry, in column `σ i`, with `αᵢ ≑ δ_{i,σ i}`; and each column `j` has
exactly one non-total entry, in row `τ j`, with `βⱼ ≑ δ_{τ j,j}`.  The entry
`δ_{i,σ i}` is not total, because `αᵢ` is not; so it is the one non-total entry of
column `σ i`, and `τ (σ i) = i`.  Symmetrically `σ (τ j) = j`.  So `σ` is a
bijection, and `αᵢ ≑ δ_{i,σ i} ≑ β_{σ i}`: the two decompositions consist of the
same congruences, which is the second sentence of Theorem 5.16 (ALV writes it as
the equation of sets `{αᵢ} = {βⱼ}`).

```agda
  -- ALV Theorem 5.16, second sentence (finite index sets): two decompositions of the
  -- diagonal into indecomposable congruences consist of the same congruences.
  srp-unique : HasFiniteStrictRefinement ℓ 𝑨
    → {m n : ℕ} (αs : Fin m → Con 𝑨 ℓ) (βs : Fin n → Con 𝑨 ℓ)
    → IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) αs → IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) βs
    → (∀ i → IsIndecomposable (αs i)) → (∀ j → IsIndecomposable (βs j))
    → Σ[ σ ∈ Permutation m n ] (∀ i → αs i ≑ βs (σ ⟨$⟩ʳ i))
  srp-unique srp {m} {n} αs βs pα pβ indα indβ = permutation σ τ στ τσ , matched
    where
    refinement = srp αs βs pα pβ
    δ = proj₁ refinement

    row : ∀ i → Σ[ j ∈ _ ] (αs i ≑ δ i j) × (∀ k → k ≢ j → Trivial (𝑨 ╱ δ i k))
    row i = indecomposable-product (indα i) (proj₁ (proj₂ refinement) i)

    column : ∀ j → Σ[ i ∈ _ ] (βs j ≑ δ i j) × (∀ k → k ≢ i → Trivial (𝑨 ╱ δ k j))
    column j = indecomposable-product (indβ j) (proj₂ (proj₂ refinement) j)

    σ : Fin m → Fin n
    σ i = proj₁ (row i)

    τ : Fin n → Fin m
    τ j = proj₁ (column j)

    -- The entry at row i, column σ i, is not total, since αᵢ is not.
    row-entry-nontrivial : ∀ i → Trivial (𝑨 ╱ δ i (σ i)) → Trivial (𝑨 ╱ αs i)
    row-entry-nontrivial i t a b = proj₂ (proj₁ (proj₂ (row i))) (t a b)

    column-entry-nontrivial : ∀ j → Trivial (𝑨 ╱ δ (τ j) j) → Trivial (𝑨 ╱ βs j)
    column-entry-nontrivial j t a b = proj₂ (proj₁ (proj₂ (column j))) (t a b)

    -- So it is the one non-total entry of its column: τ (σ i) = i.
    τσ : ∀ i → τ (σ i) ≡ i
    τσ i with τ (σ i) ≟ i
    ... | yes eq = eq
    ... | no ne  =
      let (a , b , ¬ab) = quotient-nontrivial (indα i)
      in  ⊥-elim (¬ab (row-entry-nontrivial i (proj₂ (proj₂ (column (σ i))) i (λ e → ne (sym e))) a b))

    -- Symmetrically, σ (τ j) = j.
    στ : ∀ j → σ (τ j) ≡ j
    στ j with σ (τ j) ≟ j
    ... | yes eq = eq
    ... | no ne  =
      let (a , b , ¬ab) = quotient-nontrivial (indβ j)
      in  ⊥-elim (¬ab (column-entry-nontrivial j (proj₂ (proj₂ (row (τ j))) j (λ e → ne (sym e))) a b))

    -- αᵢ ≑ δ_{i,σ i} ≑ β_{σ i}.
    matched : ∀ i → αs i ≑ βs (σ i)
    matched i = (λ r → proj₂ β≑δ (proj₁ α≑δ r)) , λ r → proj₂ α≑δ (proj₁ β≑δ r)
      where
      α≑δ : αs i ≑ δ i (σ i)
      α≑δ = proj₁ (proj₂ (row i))
      β≑δ : βs (σ i) ≑ δ i (σ i)
      β≑δ = subst (λ k → βs (σ i) ≑ δ k (σ i)) (τσ i) (proj₁ (proj₂ (column (σ i))))

  -- In particular the two decompositions have the same length.
  srp-length : HasFiniteStrictRefinement ℓ 𝑨
    → {m n : ℕ} (αs : Fin m → Con 𝑨 ℓ) (βs : Fin n → Con 𝑨 ℓ)
    → IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) αs → IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) βs
    → (∀ i → IsIndecomposable (αs i)) → (∀ j → IsIndecomposable (βs j))
    → m ≡ n
  srp-length srp αs βs pα pβ indα indβ = ↔⇒≡ (proj₁ (srp-unique srp αs βs pα pβ indα indβ))
```

#### Unique factorization

The Corollary of Theorem 5.16 transfers the theorem from congruences to algebras.
Given `𝑨 ≅ ⨅ ℬ ≅ ⨅ 𝒞` with directly indecomposable factors, the kernels of the
coordinate maps decompose the diagonal (`≅⨅→product`{.AgdaFunction}), each factor
is the quotient by its kernel (`≅⨅-factor≅`{.AgdaFunction}), so each kernel is
indecomposable (invariance under isomorphism and Lemma 2 of §5.2); Theorem 5.16
matches the kernels along a bijection `σ`, and matched kernels have isomorphic
quotients (`≑→╱≅`{.AgdaFunction}).  So `ℬ i ≅ 𝑨/κᵢ ≅ 𝑨/λ_{σ i} ≅ 𝒞 (σ i)`, which
is condition (ii) of the unique factorization property.  (Recovering the factors
as quotients takes an element of each factor, which nontriviality supplies.)

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- (ALV §5.1 (ii), Theorem 5.16 and its Corollary, finite index sets.)  If 𝑨 has the
  -- strict refinement property, two factorizations of 𝑨 into directly indecomposable
  -- algebras match up to isomorphism along a bijection of their indices.
  srp→unique : HasFiniteStrictRefinement ρᵇ 𝑨
    → {m n : ℕ} (ℬ : Fin m → Algebra {𝑆 = 𝑆} β ρᵇ) (𝒞 : Fin n → Algebra {𝑆 = 𝑆} β ρᵇ)
    → 𝑨 ≅ ⨅ ℬ → 𝑨 ≅ ⨅ 𝒞
    → (∀ i → IsDirectlyIndecomposable ρᵇ (ℬ i)) → (∀ j → IsDirectlyIndecomposable ρᵇ (𝒞 j))
    → Σ[ σ ∈ Permutation m n ] (∀ i → ℬ i ≅ 𝒞 (σ ⟨$⟩ʳ i))
  srp→unique srp ℬ 𝒞 f g indℬ ind𝒞 =
    let (σ , matched) = srp-unique srp (≅⨅-ker f) (≅⨅-ker g) (≅⨅→product f) (≅⨅→product g)
                                   indκ indλ
    in  σ , λ i → ≅-trans (≅-trans (ℬ≅ i) (≑→╱≅ (matched i))) (𝒞≅ (σ ⟨$⟩ʳ i))
    where
    -- Each factor is the quotient by the kernel of its coordinate map.
    ℬ≅ : ∀ i → ℬ i ≅ (𝑨 ╱ ≅⨅-ker f i)
    ℬ≅ i = ≅-sym (≅⨅-factor≅ f _≟_ (λ k → proj₁ (nontrivial (indℬ k))) i)

    𝒞≅ : ∀ j → (𝑨 ╱ ≅⨅-ker g j) ≅ 𝒞 j
    𝒞≅ j = ≅⨅-factor≅ g _≟_ (λ k → proj₁ (nontrivial (ind𝒞 k))) j

    -- So the kernels are indecomposable congruences.
    indκ : ∀ i → IsIndecomposable (≅⨅-ker f i)
    indκ i = directly→indecomposable (≅⨅-ker f i) (≅-indecomposable (ℬ≅ i) (indℬ i))

    indλ : ∀ j → IsIndecomposable (≅⨅-ker g j)
    indλ j = directly→indecomposable (≅⨅-ker g j) (≅-indecomposable (≅-sym (𝒞≅ j)) (ind𝒞 j))
```

`IsUniquelyFactorable`{.AgdaRecord} `β ρᵇ 𝑨` is the unique factorization property
of ALV §5.1, for finite index sets and for factors at the levels `(β , ρᵇ)`: a
factorization into directly indecomposable algebras exists
(`factorization`{.AgdaField}), and any two such factorizations match up to
isomorphism along a bijection of their indices (`uniqueness`{.AgdaField}).

A finite algebra has a factorization, by [Setoid.Decompositions.Finite][], into
quotients of itself, which live at the levels `(α , W)` with
`W = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ` the working level of the congruence list; with the strict
refinement property at that level it is uniquely factorable.  This is the
theorem of the section: **a finite algebra with the strict refinement property
is uniquely factorable**.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where
  -- The unique factorization property (ALV §5.1), for finite index sets.
  record IsUniquelyFactorable (β ρᵇ : Level) (𝑨 : Algebra {𝑆 = 𝑆} α ρ)
    : Type (α ⊔ ρ ⊔ ov {𝑆 = 𝑆} (β ⊔ ρᵇ)) where
    field
      factorization  : Σ[ n ∈ ℕ ] Σ[ ℬ ∈ (Fin n → Algebra {𝑆 = 𝑆} β ρᵇ) ]
                         (𝑨 ≅ ⨅ ℬ) × (∀ i → IsDirectlyIndecomposable ρᵇ (ℬ i))
      uniqueness     : {m n : ℕ} (ℬ : Fin m → Algebra {𝑆 = 𝑆} β ρᵇ) (𝒞 : Fin n → Algebra {𝑆 = 𝑆} β ρᵇ)
                       → 𝑨 ≅ ⨅ ℬ → 𝑨 ≅ ⨅ 𝒞
                       → (∀ i → IsDirectlyIndecomposable ρᵇ (ℬ i))
                       → (∀ j → IsDirectlyIndecomposable ρᵇ (𝒞 j))
                       → Σ[ σ ∈ Permutation m n ] (∀ i → ℬ i ≅ 𝒞 (σ ⟨$⟩ʳ i))

  open IsUniquelyFactorable public

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where
  -- A finite algebra with the strict refinement property is uniquely factorable.
  finite-srp→uniquelyFactorable : FiniteAlgebra 𝑨 → FiniteCongruencesᵈ 𝑨 → 𝕌[ 𝑨 ]
    → HasFiniteStrictRefinement (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) 𝑨 → IsUniquelyFactorable α (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) 𝑨
  finite-srp→uniquelyFactorable 𝑭 𝑪 u srp = record
    { factorization  = let (n , θ , iso , ind) = finite-decomposition≅ 𝑭 𝑪 u in n , 𝑨╱ θ , iso , ind
    ; uniqueness     = srp→unique srp
    }
```

Over a finite signature the complete list always exists
([Setoid.Decompositions.Finite][]), so the theorem needs only the finiteness of
the algebra and of its signature.

```agda
  -- A nonempty finite finitary algebra with the strict refinement property is
  -- uniquely factorable.
  finitary-srp→uniquelyFactorable : FiniteAlgebra 𝑨 → FiniteSignature 𝑆 → 𝕌[ 𝑨 ]
    → HasFiniteStrictRefinement (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) 𝑨 → IsUniquelyFactorable α (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) 𝑨
  finitary-srp→uniquelyFactorable 𝑭 𝑺 =
    finite-srp→uniquelyFactorable 𝑭 (FiniteAlgebra→FiniteCongruencesᵈ 𝑭 𝑺)
```
