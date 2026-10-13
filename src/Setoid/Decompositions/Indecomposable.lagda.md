---
layout: default
file: "src/Setoid/Decompositions/Indecomposable.lagda.md"
title: "Setoid.Decompositions.Indecomposable module (The Agda Universal Algebra Library)"
date: "2026-10-13"
author: "the agda-algebras development team"
---

### Directly indecomposable algebras

This is the [Setoid.Decompositions.Indecomposable][] module of the [Agda Universal Algebra Library][].

The atoms of direct factorization are the algebras that cannot be factored.
McKenzie, McNulty, and Taylor, *Algebras, Lattices, Varieties* I (ALV below),
define them twice, once for algebras and once for congruences.

> **Definition 4.37.**  An algebra `𝑨` is called *directly indecomposable* iff it
> is nontrivial and is not isomorphic to a product of two nontrivial algebras.
>
> (§5.1, restated.)  `𝑨` is directly indecomposable iff `|A| > 1`, and
> `𝑨 ≅ 𝑩 × 𝑪` implies `|B| = 1` or `|C| = 1`.
>
> **§5.2, Lemma 2.**  For all `θ ∈ Con 𝑨`, `𝑨/θ` is directly indecomposable iff
> `θ ≠ 1`, and `θ = θ₀ × θ₁` implies `θ₀ = 1` or `θ₁ = 1`.  Thus we will call a
> congruence `θ` *indecomposable* iff it satisfies these conditions.

ALV also notes, after Definition 4.37, that the directly indecomposable algebras
"can be characterized as those that have precisely two factor congruences, `0_A`
and `1_A`".  That characterization is the definition we adopt,
`IsDirectlyIndecomposable`{.AgdaRecord} `ℓ 𝑨`: `𝑨` is nontrivial, and of every
factor pair `⟨θ , φ⟩` of congruences at level `ℓ`, one member is the total
congruence, that is, one of the factors `𝑨 ╱ θ` and `𝑨 ╱ φ` is trivial.  It
quantifies over congruences rather than over all pairs of algebras, which keeps it
at one universe level and makes it decidable for finite algebras
([Setoid.Decompositions.Finite][]).  The module then proves the following:

+  `IsIndecomposable`{.AgdaRecord} is ALV's indecomposable congruence, and
   `indecomposable→directly`{.AgdaFunction} and
   `directly→indecomposable`{.AgdaFunction} are Lemma 2, through the
   correspondence between the congruences of `𝑨 ╱ θ` and the congruences of `𝑨`
   above `θ`;
+  direct indecomposability is invariant under isomorphism
   (`≅-indecomposable`{.AgdaFunction}), by pulling factor pairs back along the
   isomorphism;
+  it agrees with Definition 4.37 in the form of §5.1:
   `indecomposable→trivial-factor`{.AgdaFunction} says that every decomposition
   `𝑨 ≅ 𝑩 ×ᴬ 𝑪` has a trivial factor, and
   `trivial-factor→indecomposable`{.AgdaFunction} is the converse.

On "nontrivial": following [Setoid.Congruences.Monolith][], `Nontrivial 𝑨` is the
positive statement that two elements are distinct, and `|A/θ| > 1` is
`Nontrivial (𝑨 ╱ θ)`, two elements unrelated by `θ`; "`θ = 1`" is
`Trivial (𝑨 ╱ θ)`, "`θ` relates every pair".  Since `𝑨 ╱ θ` has the carrier of `𝑨`
and the equality `θ`, these are definitional readings, not lemmas.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Decompositions.Indecomposable where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; map )
open import Function                               using () renaming ( Func to _⟶_ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid ; IsEquivalence ; _⇒_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                            using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras                     using ( Algebra ; ov ; 𝕌[_] ; 𝔻[_]
                                                      ; _×ᴬ_ )
open import Setoid.Congruences.Basic            using ( Con ; mkcon ; _╱_ ; reflexive
                                                      ; is-equivalence ; is-compatible )
open import Setoid.Congruences.Lattice          using ( _≑_ )
open import Setoid.Congruences.Monolith         using ( Nontrivial ; Trivial )
open import Setoid.Congruences.Permutability    using ( _∘_ )
open import Setoid.Decompositions.FactorPairs   using ( IsProduct₂ ; to-meet ; from-meet
                                                      ; composite ; IsFactorPair
                                                      ; factorPair→product₂
                                                      ; product₂→factorPair ; factorPair→≅
                                                      ; ≅×-kerˡ ; ≅×-kerʳ ; ≅×→factorPair
                                                      ; ≅×-factor≅ˡ ; ≅×-factor≅ʳ )
open import Setoid.Homomorphisms.Basic          using ( hom ; mkIsHom )
open import Setoid.Homomorphisms.Kernels        using ( pullbackCon )
open import Setoid.Homomorphisms.Isomorphisms   using ( _≅_ ; mkiso ; ≅toInjective )

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )
open _≅_ using ( to ; from ; to∼from )

private variable α ρ β ρᵇ ℓ : Level
```
-->

#### The definitions

`IsDirectlyIndecomposable`{.AgdaRecord} `ℓ 𝑨` is direct indecomposability, stated
with factor pairs of congruences at level `ℓ`: `𝑨` is nontrivial
(`nontrivial`{.AgdaField}), and every factor pair has a trivial factor
(`factor-trivial`{.AgdaField}).  `IsIndecomposable`{.AgdaRecord} `θ` is ALV's
indecomposable congruence: `𝑨 ╱ θ` is nontrivial
(`quotient-nontrivial`{.AgdaField}), and every product decomposition
`θ = θ₀ × θ₁` has a total factor (`product-trivial`{.AgdaField}).

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where

  -- 𝑨 is directly indecomposable (ALV Definition 4.37, in its factor-congruence form).
  record IsDirectlyIndecomposable (ℓ : Level) (𝑨 : Algebra {𝑆 = 𝑆} α ρ)
    : Type (α ⊔ ρ ⊔ ov {𝑆 = 𝑆} ℓ) where
    field
      nontrivial      : Nontrivial 𝑨
      factor-trivial  : (θ φ : Con 𝑨 ℓ) → IsFactorPair θ φ → Trivial (𝑨 ╱ θ) ⊎ Trivial (𝑨 ╱ φ)

  open IsDirectlyIndecomposable public

  -- θ is an indecomposable congruence (ALV §5.2, after Lemma 2).
  record IsIndecomposable {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (θ : Con 𝑨 ℓ)
    : Type (α ⊔ ρ ⊔ ov {𝑆 = 𝑆} ℓ) where
    field
      quotient-nontrivial  : Nontrivial (𝑨 ╱ θ)
      product-trivial      : (θ₀ θ₁ : Con 𝑨 ℓ) → IsProduct₂ (proj₁ θ) θ₀ θ₁
                             → Trivial (𝑨 ╱ θ₀) ⊎ Trivial (𝑨 ╱ θ₁)

  open IsIndecomposable public
```

#### Lemma 2: indecomposable congruences

The congruences of a quotient `𝑨 ╱ θ` are the congruences of `𝑨` that contain `θ`,
with the same relations: `𝑨 ╱ θ` has the carrier and the operations of `𝑨`, and
its equality is `θ`, so a congruence of `𝑨 ╱ θ` is a compatible equivalence
relation containing `θ`, which in turn contains the equality of `𝑨`.
`╱-lift`{.AgdaFunction} and `╱-lower`{.AgdaFunction} pass between the two (this is
the special case of the Correspondence Theorem, ALV Theorem 4.12, in which the
congruences are not even renamed).

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (θ : Con 𝑨 ℓ) where

  -- A congruence of 𝑨 ╱ θ is a congruence of 𝑨 (and it contains θ).
  ╱-lift : Con (𝑨 ╱ θ) ℓ → Con 𝑨 ℓ
  ╱-lift (φ , φc) = φ , mkcon (λ e → reflexive φc (reflexive (proj₂ θ) e))
                              (is-equivalence φc) (is-compatible φc)

  -- A congruence of 𝑨 containing θ is a congruence of 𝑨 ╱ θ.
  ╱-lower : (φ : Con 𝑨 ℓ) → proj₁ θ ⇒ proj₁ φ → Con (𝑨 ╱ θ) ℓ
  ╱-lower (φ , φc) θ⇒φ = φ , mkcon θ⇒φ (is-equivalence φc) (is-compatible φc)
```

Under this correspondence a factor pair `⟨φ₀ , φ₁⟩` of `𝑨 ╱ θ`, a product
decomposition of the diagonal `θ` of `𝑨 ╱ θ`, is literally a product decomposition
`θ = φ₀ × φ₁` in `𝑨`, and the quotients `(𝑨 ╱ θ) ╱ φᵢ` and `𝑨 ╱ φᵢ` are trivial
together.  Lemma 2 follows in both directions.

```agda
  -- ALV §5.2, Lemma 2 (⇐): if θ is indecomposable, then 𝑨 ╱ θ is directly indecomposable.
  indecomposable→directly : IsIndecomposable θ → IsDirectlyIndecomposable ℓ (𝑨 ╱ θ)
  indecomposable→directly ind = record
    { nontrivial      = quotient-nontrivial ind
    ; factor-trivial  = λ φ₀ φ₁ fp → product-trivial ind (╱-lift φ₀) (╱-lift φ₁)
                                                       (in-𝑨 (factorPair→product₂ fp))
    }
    where
    in-𝑨 : {φ₀ φ₁ : Con (𝑨 ╱ θ) ℓ} → IsProduct₂ (proj₁ θ) φ₀ φ₁
      → IsProduct₂ (proj₁ θ) (╱-lift φ₀) (╱-lift φ₁)
    in-𝑨 p = record { to-meet = to-meet p ; from-meet = from-meet p ; composite = composite p }

  -- ALV §5.2, Lemma 2 (⇒): if 𝑨 ╱ θ is directly indecomposable, then θ is indecomposable.
  directly→indecomposable : IsDirectlyIndecomposable ℓ (𝑨 ╱ θ) → IsIndecomposable θ
  directly→indecomposable di = record
    { quotient-nontrivial  = nontrivial di
    ; product-trivial      = λ θ₀ θ₁ p →
        factor-trivial di (╱-lower θ₀ (λ r → proj₁ (to-meet p r)))
                          (╱-lower θ₁ (λ r → proj₂ (to-meet p r)))
                          (product₂→factorPair (in-𝑨╱θ p))
    }
    where
    in-𝑨╱θ : {θ₀ θ₁ : Con 𝑨 ℓ}(p : IsProduct₂ (proj₁ θ) θ₀ θ₁)
      → IsProduct₂ (proj₁ θ) (╱-lower θ₀ (λ r → proj₁ (to-meet p r)))
                             (╱-lower θ₁ (λ r → proj₂ (to-meet p r)))
    in-𝑨╱θ p = record { to-meet = to-meet p ; from-meet = from-meet p ; composite = composite p }
```

#### Invariance under isomorphism

Nontriviality and triviality transport along an isomorphism, and so do factor
pairs, by pulling them back (`pullbackCon`{.AgdaFunction} of
[Setoid.Homomorphisms.Kernels][]): if `f : 𝑨 ≅ 𝑩` and `𝑩 = θ × φ`, then the
inverse images of `θ` and `φ` decompose `𝑨`, their meet being the kernel of `f`
and every pair being linked through the preimage of a linking element in `𝑩`.
Hence direct indecomposability is invariant under isomorphism
(`≅-indecomposable`{.AgdaFunction}).  Mutually contained congruences also give
isomorphic quotients (`≑→╱≅`{.AgdaFunction}), by the identity map.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}
         (f : 𝑨 ≅ 𝑩) where
  open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᵇ_ ; sym to symᵇ ; trans to transᵇ )
  private
    f⟨_⟩ : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]
    f⟨ a ⟩ = to f .proj₁ ⟨$⟩ a
    f⁻¹⟨_⟩ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
    f⁻¹⟨ b ⟩ = from f .proj₁ ⟨$⟩ b

  -- Nontriviality transports along an isomorphism.
  ≅-nontrivial : Nontrivial 𝑨 → Nontrivial 𝑩
  ≅-nontrivial (a , a′ , a≉a′) = f⟨ a ⟩ , f⟨ a′ ⟩ , λ e → a≉a′ (≅toInjective f e)

  -- Triviality transports along an isomorphism.
  ≅-trivial : Trivial 𝑨 → Trivial 𝑩
  ≅-trivial triv b b′ =
    transᵇ (symᵇ (to∼from f b)) (transᵇ (cong (to f .proj₁) (triv f⁻¹⟨ b ⟩ f⁻¹⟨ b′ ⟩))
                                         (to∼from f b′))

  -- A product decomposition of the diagonal of 𝑩 pulls back to one of 𝑨.
  ≅-pullback-product₂ : {θ φ : Con 𝑩 ℓ} → IsProduct₂ _≈ᵇ_ θ φ
    → IsProduct₂ (Setoid._≈_ 𝔻[ 𝑨 ]) (pullbackCon (to f) θ) (pullbackCon (to f) φ)
  ≅-pullback-product₂ {θ = θ} {φ} p = record
    { to-meet    = λ e → let fe = cong (to f .proj₁) e
                         in  reflexive (proj₂ θ) fe , reflexive (proj₂ φ) fe
    ; from-meet  = λ m → ≅toInjective f (from-meet p m)
    ; composite  = linked
    }
    where
    linked : ∀ x y → (pullbackCon (to f) θ ∘ pullbackCon (to f) φ) x y
    linked x y =
      let (z , fxθz , zφfy) = composite p f⟨ x ⟩ f⟨ y ⟩
      in  f⁻¹⟨ z ⟩
          , IsEquivalence.trans (is-equivalence (proj₂ θ)) fxθz
                                (reflexive (proj₂ θ) (symᵇ (to∼from f z)))
          , IsEquivalence.trans (is-equivalence (proj₂ φ))
                                (reflexive (proj₂ φ) (to∼from f z)) zφfy

  -- If 𝑨 ╱ f⁻¹θ is trivial, then so is 𝑩 ╱ θ.
  ≅-pullback-trivial : (θ : Con 𝑩 ℓ) → Trivial (𝑨 ╱ pullbackCon (to f) θ) → Trivial (𝑩 ╱ θ)
  ≅-pullback-trivial θ t b b′ =
    θtrans (reflexive (proj₂ θ) (symᵇ (to∼from f b)))
           (θtrans (t f⁻¹⟨ b ⟩ f⁻¹⟨ b′ ⟩) (reflexive (proj₂ θ) (to∼from f b′)))
    where θtrans = IsEquivalence.trans (is-equivalence (proj₂ θ))

  -- Direct indecomposability is invariant under isomorphism.
  ≅-indecomposable : IsDirectlyIndecomposable ℓ 𝑨 → IsDirectlyIndecomposable ℓ 𝑩
  ≅-indecomposable di = record
    { nontrivial      = ≅-nontrivial (nontrivial di)
    ; factor-trivial  = λ θ φ fp →
        map (≅-pullback-trivial θ) (≅-pullback-trivial φ)
            (factor-trivial di (pullbackCon (to f) θ) (pullbackCon (to f) φ)
                               (product₂→factorPair (≅-pullback-product₂ (factorPair→product₂ fp))))
    }

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where
  -- The identity map 𝑨 ╱ θ → 𝑨 ╱ φ is a homomorphism when θ ⊆ φ.
  ╱-id-hom : {θ φ : Con 𝑨 ℓ} → proj₁ θ ⇒ proj₁ φ → hom (𝑨 ╱ θ) (𝑨 ╱ φ)
  ╱-id-hom {θ = θ} {φ} θ⇒φ = F , mkIsHom (IsEquivalence.refl (is-equivalence (proj₂ φ)))
    where
    F : 𝔻[ 𝑨 ╱ θ ] ⟶ 𝔻[ 𝑨 ╱ φ ]
    F ⟨$⟩ x = x
    F .cong = θ⇒φ

  -- Mutually contained congruences have isomorphic quotients.
  ≑→╱≅ : {θ φ : Con 𝑨 ℓ} → θ ≑ φ → (𝑨 ╱ θ) ≅ (𝑨 ╱ φ)
  ≑→╱≅ {θ = θ} {φ} (θ⇒φ , φ⇒θ) =
    mkiso (╱-id-hom θ⇒φ) (╱-id-hom φ⇒θ)
          (λ _ → IsEquivalence.refl (is-equivalence (proj₂ φ)))
          (λ _ → IsEquivalence.refl (is-equivalence (proj₂ θ)))
```

#### Agreement with Definition 4.37

Finally, the definition agrees with ALV's own.  If `𝑨` is directly indecomposable
and `f : 𝑨 ≅ 𝑩 ×ᴬ 𝑪`, the kernels of the two coordinate maps of `f` form a factor
pair ([Setoid.Decompositions.FactorPairs][]), so one of them is total, and the
corresponding factor, isomorphic to the quotient by it, is trivial.  (Recovering
the factor as a quotient takes an element of the other factor; it is the image of
any element of `𝑨`, which is nonempty since it is nontrivial.)  Conversely, if
every decomposition `𝑨 ≅ 𝑩 ×ᴬ 𝑪` has a trivial factor, then so does the
decomposition `𝑨 ≅ (𝑨 ╱ θ) ×ᴬ (𝑨 ╱ φ)` given by any factor pair (Theorem 4.29).

The factors range over algebras at one pair of levels in each statement: the
kernels of the coordinate maps are congruences at the factors' equality level,
which is where the factor pairs are taken.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- (ALV §5.1) If 𝑨 is directly indecomposable and 𝑨 ≅ 𝑩 × 𝑪, then 𝑩 or 𝑪 is trivial.
  indecomposable→trivial-factor : IsDirectlyIndecomposable ρᵇ 𝑨
    → {𝑩 𝑪 : Algebra {𝑆 = 𝑆} β ρᵇ} → 𝑨 ≅ (𝑩 ×ᴬ 𝑪) → Trivial 𝑩 ⊎ Trivial 𝑪
  indecomposable→trivial-factor di f =
    let (a , _) = nontrivial di
        (b , c) = to f .proj₁ ⟨$⟩ a
    in  map (≅-trivial (≅×-factor≅ˡ f c)) (≅-trivial (≅×-factor≅ʳ f b))
            (factor-trivial di (≅×-kerˡ f) (≅×-kerʳ f) (≅×→factorPair f))

  -- (ALV §5.1) If 𝑨 is nontrivial and every 𝑨 ≅ 𝑩 × 𝑪 has a trivial factor, then 𝑨 is
  -- directly indecomposable.
  trivial-factor→indecomposable : Nontrivial 𝑨
    → ({𝑩 𝑪 : Algebra {𝑆 = 𝑆} α ℓ} → 𝑨 ≅ (𝑩 ×ᴬ 𝑪) → Trivial 𝑩 ⊎ Trivial 𝑪)
    → IsDirectlyIndecomposable ℓ 𝑨
  trivial-factor→indecomposable nt split = record
    { nontrivial      = nt
    ; factor-trivial  = λ θ φ fp → split (factorPair→≅ θ φ fp)
    }
```
