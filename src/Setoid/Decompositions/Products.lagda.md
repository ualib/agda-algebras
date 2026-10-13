---
layout: default
file: "src/Setoid/Decompositions/Products.lagda.md"
title: "Setoid.Decompositions.Products module (The Agda Universal Algebra Library)"
date: "2026-10-13"
author: "the agda-algebras development team"
---

### Products of congruences

This is the [Setoid.Decompositions.Products][] module of the [Agda Universal Algebra Library][].

[Setoid.Decompositions.FactorPairs][] treats direct decompositions with two
factors.  This module treats any number of factors, following McKenzie, McNulty,
and Taylor, *Algebras, Lattices, Varieties* I (ALV below), §4.4 and §5.2.

> **Definition 4.30.**  For any system `⟨φᵢ : i ∈ I⟩` of congruences of an algebra
> `𝑨` we write `0_A = ∏_{i∈I} φᵢ` iff `0_A = ⋂{φᵢ : i ∈ I}` and for every
> `x̄ = ⟨xᵢ : i ∈ I⟩ ∈ A^I` there is an element `x ∈ A` such that `(x, xᵢ) ∈ φᵢ`
> for all `i ∈ I`.
>
> **Theorem 4.31.**  A system `⟨φᵢ : i ∈ I⟩` of congruences of an algebra `𝑨`
> constitutes a direct representation iff `0_A = ∏_{i∈I} φᵢ`.
>
> **§5.2, Lemma 1.**  [For `ψ ∈ Con 𝑨` and a family `Γ` of congruences
> `θ ≥ ψ`, the natural map `f : 𝑨/ψ → ∏_{θ∈Γ} 𝑨/θ`] is one-to-one if and only if
> `⋂Γ = ψ`.  It is onto iff `Γ` satisfies
> (1) `(∀ a ∈ A^Γ)(∃ b ∈ A)(∀ θ ∈ Γ) (a_θ, b) ∈ θ`.

When both conditions of Lemma 1 hold, ALV says that `ψ` is the *product* of the
congruences in `Γ`, `ψ = ∏ Γ`.  The record `IsProduct`{.AgdaRecord} `R θ` of this
module is that definition for an indexed family `θ : I → Con 𝑨 ℓ` and the
relation `R` of `ψ`; its fields are the two halves of `R = ⋂ θ` and the
interpolation condition (1).  For `R` the setoid equality it is Definition 4.30,
`0_A = ∏ θ`, and the module proves the following:

+  Theorem 4.31 in both directions: `product→≅`{.AgdaFunction} gives the
   isomorphism `𝑨 ≅ ⨅ (𝑨╱ θ)`, and `natmap-bijective→product`{.AgdaFunction} the
   converse;
+  the decomposition `0_A = ∏ ker (pᵢ ∘ f)` of the diagonal induced by any
   isomorphism `f : 𝑨 ≅ ⨅ ℬ` (`≅⨅→product`{.AgdaFunction}), with each factor
   `ℬ i` recovered as the quotient `𝑨 ╱ ker (pᵢ ∘ f)`
   (`≅⨅-factor≅`{.AgdaFunction});
+  the parts of ALV §5.2, Lemma 3, that the theory of unique factorization uses:
   a product may be reindexed along a bijection (`product-reindex`{.AgdaFunction},
   part iii), split into its first factor and the rest
   (`product-split`{.AgdaFunction}), and assembled from the products of the two
   factors of a binary product (`product-combine`{.AgdaFunction}, part ii).

The natural map into the product and the separation property are those of
subdirect representations, `natmap`{.AgdaFunction} and
`Separates`{.AgdaFunction} of [Setoid.Subalgebras.Subdirect.Basic][]: a direct
representation is a subdirect one whose natural map is also onto.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Decompositions.Products where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Data.Fin.Base                           using ( Fin ; zero ; suc ; splitAt ; join )
open import Data.Fin.Properties                     using ( splitAt-join ; join-splitAt )
open import Data.Nat.Base                           using ( ℕ ; suc )
open import Data.Product                            using ( _,_ ; proj₁ ; proj₂ ; Σ-syntax )
open import Data.Sum.Base                           using ( inj₁ ; inj₂ ; [_,_]′ )
open import Function                                using () renaming ( Func to _⟶_ )
open import Level                                   using ( Level ; _⊔_ ; Lift ; lift
                                                          ; lower )
open import Relation.Binary                         using ( Setoid ; IsEquivalence ; _⇒_ )
                                                    renaming ( Rel to BinaryRel )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; subst )
open import Relation.Binary.Definitions             using ( DecidableEquality )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                            using ( 𝓞 ; 𝓥 ; Signature ; update
                                                      ; update-id )
open import Setoid.Algebras                     using ( Algebra ; 𝕌[_] ; 𝔻[_] ; ⨅ )
open import Setoid.Congruences.Basic            using ( Con ; _╱_ ; is-equivalence
                                                      ; reflexive )
open import Setoid.Congruences.Lattice          using ( _≑_ )
open import Setoid.Congruences.Monolith         using ( ⋂ )
open import Setoid.Congruences.Permutability    using ( _∘_ )
open import Setoid.Decompositions.FactorPairs   using ( IsProduct₂ ; to-meet ; from-meet
                                                      ; composite )
open import Setoid.Functions                    using ( IsInjective ; IsSurjective
                                                      ; Image_∋_ )
open import Setoid.Homomorphisms.Isomorphisms   using ( _≅_ ; Bijective→≅ ; ≅toInjective )
open import Setoid.Homomorphisms.Kernels        using ( kercon )
open import Setoid.Homomorphisms.Noether        using ( FirstIsoTheorem )
open import Setoid.Subalgebras.Subdirect.Basic  using ( 𝑨╱ ; natmap ; coord )

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )
open _≅_ using ( to ; from ; to∼from )

private variable α ρ β ρᵇ ι ι′ ℓ ℓ′ ℓ″ : Level
```
-->

#### The product of a family of congruences

Fix an algebra `𝑨`, an index type `I`, a family `θ : I → Con 𝑨 ℓ`, and a relation
`R`.  `IsProduct`{.AgdaRecord} `R θ` says that `R` is the meet of the family
(`to-⋂`{.AgdaField} and `from-⋂`{.AgdaField}) and that the family satisfies the
interpolation condition (1) of Lemma 1 (`interpolate`{.AgdaField}): every
`I`-tuple of elements has a common "interpolant" `b`, related to the `i`-th entry
by `θ i` for every `i`.  The interpolant is the element whose `i`-th coordinate is
the `i`-th coordinate of the `i`-th entry.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- ψ = ∏ θ (ALV §5.2, after Lemma 1), for the relation R of ψ; with R the setoid
  -- equality, 0_A = ∏ θ (ALV Definition 4.30).
  record IsProduct {I : Type ι} (R : BinaryRel 𝕌[ 𝑨 ] ℓ′) (θ : I → Con 𝑨 ℓ)
    : Type (ι ⊔ α ⊔ ℓ ⊔ ℓ′) where
    field
      to-⋂         : ∀ {x y} → R x y → ∀ i → proj₁ (θ i) x y
      from-⋂       : ∀ {x y} → (∀ i → proj₁ (θ i) x y) → R x y
      interpolate  : (a : I → 𝕌[ 𝑨 ]) → Σ[ b ∈ 𝕌[ 𝑨 ] ] (∀ i → proj₁ (θ i) (a i) b)

  open IsProduct public
```

Like its binary case, the product respects mutual containment `_≑_` of the
factors, pointwise, and equivalence of the relation `R`.

```agda
  -- The product respects ≑ in each factor.
  product-≑ : {I : Type ι}{R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ θ′ : I → Con 𝑨 ℓ}
    → (∀ i → θ i ≑ θ′ i) → IsProduct R θ → IsProduct R θ′
  product-≑ θ≑θ′ p = record
    { to-⋂         = λ r i → proj₁ (θ≑θ′ i) (to-⋂ p r i)
    ; from-⋂       = λ h → from-⋂ p (λ i → proj₂ (θ≑θ′ i) (h i))
    ; interpolate  = λ a → let (b , ab) = interpolate p a in b , λ i → proj₁ (θ≑θ′ i) (ab i)
    }

  -- The product respects equivalence of the relation R.
  product-resp : {I : Type ι}{R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{R′ : BinaryRel 𝕌[ 𝑨 ] ℓ″}
    {θ : I → Con 𝑨 ℓ} → R ⇒ R′ → R′ ⇒ R → IsProduct R θ → IsProduct R′ θ
  product-resp R⇒R′ R′⇒R p = record
    { to-⋂         = λ r → to-⋂ p (R′⇒R r)
    ; from-⋂       = λ h → R⇒R′ (from-⋂ p h)
    ; interpolate  = interpolate p
    }
```

#### Theorem 4.31: direct representations

The natural map `natmap θ`{.AgdaFunction} of [Setoid.Subalgebras.Subdirect.Basic][]
sends `x` to the tuple of its classes.  Its injectivity is, definitionally, the
separation property `R = ⋂ θ` for `R` the setoid equality; its surjectivity is
the interpolation condition, since a tuple `a` of classes has the preimage `b`
exactly when `(aᵢ , b) ∈ θ i` for every `i`.  So `0_A = ∏ θ` is the assertion that
the natural map is a bijective homomorphism, which is Theorem 4.31.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {I : Type ι} (θ : I → Con 𝑨 ℓ) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )

  -- Interpolation makes the natural map onto ...
  natmap-surjective : ((a : I → 𝕌[ 𝑨 ]) → Σ[ b ∈ 𝕌[ 𝑨 ] ] (∀ i → proj₁ (θ i) (a i) b))
    → IsSurjective (proj₁ (natmap θ))
  natmap-surjective int {t} = let (b , tb) = int t in Image_∋_.eq b tb

  -- ... and an onto natural map interpolates.
  natmap-surjective⁻ : IsSurjective (proj₁ (natmap θ))
    → (a : I → 𝕌[ 𝑨 ]) → Σ[ b ∈ 𝕌[ 𝑨 ] ] (∀ i → proj₁ (θ i) (a i) b)
  natmap-surjective⁻ s a = preimage (s {a})
    where
    preimage : Image (proj₁ (natmap θ)) ∋ a → Σ[ b ∈ 𝕌[ 𝑨 ] ] (∀ i → proj₁ (θ i) (a i) b)
    preimage (Image_∋_.eq b ab) = b , ab

  -- ALV Theorem 4.31 (⇐): if 0_A = ∏ θ, then 𝑨 ≅ ∏ 𝑨/θᵢ.
  product→≅ : IsProduct _≈_ θ → 𝑨 ≅ ⨅ (𝑨╱ θ)
  product→≅ p = Bijective→≅ (natmap θ) (from-⋂ p) (natmap-surjective (interpolate p))

  -- ALV Theorem 4.31 (⇒): if the natural map is bijective, then 0_A = ∏ θ.
  natmap-bijective→product : IsInjective (proj₁ (natmap θ)) → IsSurjective (proj₁ (natmap θ))
    → IsProduct _≈_ θ
  natmap-bijective→product inj surj = record
    { to-⋂         = λ x≈y i → reflexive (proj₂ (θ i)) x≈y
    ; from-⋂       = inj
    ; interpolate  = natmap-surjective⁻ surj
    }
```

#### The decomposition induced by an isomorphism with a product

Conversely, any isomorphism `f : 𝑨 ≅ ⨅ ℬ` determines the congruences
`≅⨅-ker f i = ker (pᵢ ∘ f)`{.AgdaFunction}, and they decompose the diagonal
(ALV §5.2: "to each direct product representation `f : 𝑨 ≅ ∏ 𝑨ᵢ` there corresponds
a product decomposition `0 = ∏ αᵢ` in `Con 𝑨`, where `αᵢ` is the kernel of
`pᵢ ∘ f`").  Their meet is the kernel of `f`, which is the diagonal because `f` is
injective, and a tuple `a` is interpolated by the preimage of the tuple whose
`i`-th coordinate is the `i`-th coordinate of `f (a i)`.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {I : Type ι}
         {ℬ : I → Algebra {𝑆 = 𝑆} β ρᵇ} (f : 𝑨 ≅ ⨅ ℬ) where

  -- The kernel of the i-th coordinate map of f.
  ≅⨅-ker : I → Con 𝑨 ρᵇ
  ≅⨅-ker i = kercon (coord ℬ (to f) i)

  -- The kernels of the coordinate maps of 𝑨 ≅ ⨅ ℬ decompose the diagonal.
  ≅⨅→product : IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) ≅⨅-ker
  ≅⨅→product = record
    { to-⋂         = λ x≈y i → cong (proj₁ (coord ℬ (to f) i)) x≈y
    ; from-⋂       = ≅toInjective f
    ; interpolate  = λ a → from f .proj₁ ⟨$⟩ tuple a
                         , λ i → Setoid.sym 𝔻[ ℬ i ] (to∼from f (tuple a) i)
    }
    where
    tuple : (I → 𝕌[ 𝑨 ]) → 𝕌[ ⨅ ℬ ]
    tuple a i = (to f .proj₁ ⟨$⟩ a i) i
```

Each factor `ℬ i` is recovered as the quotient `𝑨 ╱ ≅⨅-ker f i`, by the first
isomorphism theorem, once the `i`-th coordinate map is onto.  It hits `b` at the
preimage of a tuple with `b` in coordinate `i`, which is built from a default
tuple by `update`{.AgdaFunction} of [Overture.Functions][]; this is where the
statement asks for decidable equality on the index type and an element of every
factor (exactly the hypotheses of `ProjAlgIsOnto`{.AgdaFunction} of
[Setoid.Algebras.Products][]).

```agda
  -- ℬ i ≅ 𝑨 ╱ ker (pᵢ ∘ f), given decidable equality of indices and an element of
  -- every factor.
  ≅⨅-factor≅ : DecidableEquality I → (∀ i → 𝕌[ ℬ i ]) → ∀ i → (𝑨 ╱ ≅⨅-ker i) ≅ ℬ i
  ≅⨅-factor≅ _≟_ elts i = FirstIsoTheorem (coord ℬ (to f) i) onto
    where
    open Setoid 𝔻[ ℬ i ] using ( sym ; trans ) renaming ( reflexive to ≡→≈ )
    onto : IsSurjective (proj₁ (coord ℬ (to f) i))
    onto {b} = Image_∋_.eq (from f .proj₁ ⟨$⟩ t)
                           (sym (trans (to∼from f t i) (≡→≈ (update-id _≟_ elts (i ≟ i)))))
      where
      t : 𝕌[ ⨅ ℬ ]
      t j = update _≟_ elts elts (i , b) j (j ≟ i)
```

#### Manipulating products (ALV §5.2, Lemma 3)

ALV's Lemma 3 records that the product of congruences is "completely commutative
and associative", along with other bookkeeping facts.  We prove the instances the
unique factorization theory needs.  First, a product may be **reindexed** along a
bijection of index types (part iii).

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- A product can be reindexed along a bijection σ : J → I with inverse τ.
  product-reindex : {I : Type ι}{J : Type ι′}{R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ : I → Con 𝑨 ℓ}
    (σ : J → I) (τ : I → J) → (∀ i → σ (τ i) ≡ i) → (∀ j → τ (σ j) ≡ j)
    → IsProduct R θ → IsProduct R (λ j → θ (σ j))
  product-reindex {θ = θ} σ τ στ τσ p = record
    { to-⋂         = λ r j → to-⋂ p r (σ j)
    ; from-⋂       = λ {x} {y} h → from-⋂ p (λ i → subst (λ k → proj₁ (θ k) x y) (στ i) (h (τ i)))
    ; interpolate  = λ a → let (b , ab) = interpolate p (λ i → a (τ i))
                           in  b , λ j → subst (λ k → proj₁ (θ (σ j)) (a k) b) (τσ j) (ab (σ j))
    }
```

The empty product is the total relation: an empty family has the total relation
as its meet, and interpolation for the empty family asks only for some element of
the carrier.  (So `𝑨` itself is the product of no factors exactly when it is
trivial and nonempty, the textbook convention that the empty product of algebras
is the one-element algebra.)  A single congruence is the product of the
one-element family consisting of itself.

```agda
  -- The empty product is total ...
  product-empty→total : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ : Fin 0 → Con 𝑨 ℓ}
    → IsProduct R θ → ∀ x y → R x y
  product-empty→total p x y = from-⋂ p λ ()

  -- ... and a total relation on a nonempty carrier is the empty product.
  total→product-empty : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ : Fin 0 → Con 𝑨 ℓ}
    → 𝕌[ 𝑨 ] → (∀ x y → R x y) → IsProduct R θ
  total→product-empty u R-total = record
    { to-⋂         = λ _ ()
    ; from-⋂       = λ {x} {y} _ → R-total x y
    ; interpolate  = λ _ → u , λ ()
    }

  -- θ is the product of the one-element family ⟨θ⟩.
  product-singleton : (θ : Con 𝑨 ℓ) → IsProduct (proj₁ θ) (λ (_ : Fin 1) → θ)
  product-singleton θ = record
    { to-⋂         = λ r _ → r
    ; from-⋂       = λ h → h zero
    ; interpolate  = λ a → a zero , λ { zero → IsEquivalence.refl (is-equivalence (proj₂ θ)) }
    }
```

A product over `Fin (suc n)` **splits** into its first factor and the meet of the
rest, as a binary product: `ψ = θ₀ × ⋂ᵢ θᵢ₊₁` (a case of parts ii and iii of
Lemma 3).  The meet of the rest is the meet `⋂`{.AgdaFunction} of
[Setoid.Congruences.Monolith][], whose index must live at the level of the
congruences, so it ranges over `Lift ℓ (Fin n)`; `⋂-tail`{.AgdaFunction} names it.
The rest is itself a product of the remaining factors, provided the carrier is
nonempty (needed only when no factor remains).

```agda
  -- The meet of all factors but the first.
  ⋂-tail : {n : ℕ} → (Fin (suc n) → Con 𝑨 ℓ) → Con 𝑨 ℓ
  ⋂-tail {ℓ = ℓ} {n = n} θ = ⋂ 𝑨 {I = Lift ℓ (Fin n)} (λ i → θ (suc (lower i)))

  -- ψ = ∏ᵢ θᵢ over Fin (suc n) gives ψ = θ₀ × ⋂ᵢ θᵢ₊₁.
  product-split : {n : ℕ}{R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ : Fin (suc n) → Con 𝑨 ℓ}
    → IsProduct R θ → IsProduct₂ R (θ zero) (⋂-tail θ)
  product-split {θ = θ} p = record
    { to-meet    = λ r → to-⋂ p r zero , λ i → to-⋂ p r (suc (lower i))
    ; from-meet  = λ (h₀ , h) → from-⋂ p λ { zero → h₀ ; (suc k) → h (lift k) }
    ; composite  = linked
    }
    where
    linked : ∀ x y → (θ zero ∘ ⋂-tail θ) x y
    linked x y =
      let (b , ab) = interpolate p λ { zero → x ; (suc _) → y }
      in  b , ab zero , λ i → IsEquivalence.sym (is-equivalence (proj₂ (θ (suc (lower i)))))
                                                (ab (suc (lower i)))

  -- The meet of the remaining factors is their product (given an element).
  product-tail : {n : ℕ}{R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ : Fin (suc n) → Con 𝑨 ℓ}
    → 𝕌[ 𝑨 ] → IsProduct R θ → IsProduct (proj₁ (⋂-tail θ)) (λ k → θ (suc k))
  product-tail u p = record
    { to-⋂         = λ h k → h (lift k)
    ; from-⋂       = λ h i → h (lower i)
    ; interpolate  = λ a → let (b , ab) = interpolate p λ { zero → u ; (suc k) → a k }
                           in  b , λ k → ab (suc k)
    }
```

Conversely, products **combine**: if `ψ = θ₀ × θ₁`, `θ₀ = ∏ F`, and `θ₁ = ∏ G`,
then `ψ` is the product of the families `F` and `G` together, indexed by the sum
`I ⊎ J` of their index types (Lemma 3, part ii).  The meets agree because
`θ₀ ∧ θ₁` is the meet of the meets.  To interpolate a tuple, interpolate its two
halves by `b₀` and `b₁`, and then link `b₀` to `b₁` through `θ₀ ∘ θ₁ = 1_A`: the
linking element is `θ₀`-related to `b₀`, so related to the first half by every
`F i ⊇ θ₀`, and likewise for the second half.

```agda
  -- If ψ = θ₀ × θ₁, θ₀ = ∏ F and θ₁ = ∏ G, then ψ = ∏ (F ⊎ G).
  product-combine : {I : Type ι}{J : Type ι′}{R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ₀ θ₁ : Con 𝑨 ℓ}
    {F : I → Con 𝑨 ℓ}{G : J → Con 𝑨 ℓ}
    → IsProduct₂ R θ₀ θ₁ → IsProduct (proj₁ θ₀) F → IsProduct (proj₁ θ₁) G
    → IsProduct R [ F , G ]′
  product-combine {θ₀ = θ₀} {θ₁} {F} {G} p pF pG = record
    { to-⋂         = λ r → let (r₀ , r₁) = to-meet p r
                           in  λ { (inj₁ i) → to-⋂ pF r₀ i ; (inj₂ j) → to-⋂ pG r₁ j }
    ; from-⋂       = λ h → from-meet p (from-⋂ pF (λ i → h (inj₁ i)) , from-⋂ pG (λ j → h (inj₂ j)))
    ; interpolate  = interpolate-⊎
    }
    where
    interpolate-⊎ : (a : _ → 𝕌[ 𝑨 ]) → Σ[ b ∈ 𝕌[ 𝑨 ] ] _
    interpolate-⊎ a =
      let (b₀ , ab₀)      = interpolate pF (λ i → a (inj₁ i))
          (b₁ , ab₁)      = interpolate pG (λ j → a (inj₂ j))
          (z , b₀θ₀z , zθ₁b₁) = composite p b₀ b₁
      in  z , λ { (inj₁ i) → transF i (ab₀ i) (to-⋂ pF b₀θ₀z i)
                ; (inj₂ j) → transG j (ab₁ j) (to-⋂ pG (symθ₁ zθ₁b₁) j) }
      where
      transF = λ i → IsEquivalence.trans (is-equivalence (proj₂ (F i)))
      transG = λ j → IsEquivalence.trans (is-equivalence (proj₂ (G j)))
      symθ₁  = IsEquivalence.sym (is-equivalence (proj₂ θ₁))
```

Reindexing the combined family along the bijection `Fin (m + n) ≅ Fin m ⊎ Fin n`
(the standard library's `splitAt`{.AgdaFunction} and `join`{.AgdaFunction}; the
combined family is `[ F , G ]′`{.AgdaFunction}) gives
the version for lists of factors, `product-++`{.AgdaFunction}, the form in which
decompositions into finitely many factors are assembled.

```agda
  -- The Fin-indexed form of product-combine: concatenate the two lists of factors.
  product-++ : {m n : ℕ}{R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ₀ θ₁ : Con 𝑨 ℓ}
    {F : Fin m → Con 𝑨 ℓ}{G : Fin n → Con 𝑨 ℓ}
    → IsProduct₂ R θ₀ θ₁ → IsProduct (proj₁ θ₀) F → IsProduct (proj₁ θ₁) G
    → IsProduct R (λ k → [ F , G ]′ (splitAt m k))
  product-++ {m = m} {n} p pF pG =
    product-reindex (splitAt m) (join m n) (splitAt-join m n) (join-splitAt m n)
                    (product-combine p pF pG)
```
