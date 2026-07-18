---
layout: default
file: "src/Classical/Structures/Group/Product.lagda.md"
title: "Classical.Structures.Group.Product module"
date: "2026-07-18"
author: "the agda-algebras development team"
---

### Binary direct products of groups

This is the [Classical.Structures.Group.Product][] module of the [Agda Universal Algebra Library][].

For groups `𝒢`{.AgdaBound} and `𝒦`{.AgdaBound} presented as Σ-typed structures over
[`Sig-Group`][Classical.Signatures.Group], this module constructs the **binary direct
product** `𝒢 ×ᵍ 𝒦`{.AgdaFunction}: the algebra on the product setoid whose operations
act componentwise, together with componentwise proofs of the five group laws.  The
library's indexed product `⨅`{.AgdaFunction} of [Setoid.Algebras.Products][] would
give a product with a *function-typed* carrier `∀ i → 𝕌[ 𝒜 i ]`; the binary product
here instead has the pair carrier `G × K`, which is the form the fattening arguments
of the FLRP program consume (a fattened subgroup is literally a predicate composed
with `proj₁`{.AgdaFunction}).  The construction is level-general
(`Group α ρ → Group β σ → Group (α ⊔ β) (ρ ⊔ σ)`), since full generality costs
nothing here.

Besides the product itself, the module provides the ingredients of the *fattening
lemma* `[H × K, G × K] ≅ [H, G]` (the remark following Lemma `lemma:ie-prop-and-neg`
in the note vendored at `docs/papers/flrp/ieprops/`; see
`docs/notes/flrp-research-roadmap.md` § 4):

+  the **fattened subgroup predicates** `H ×ᶠ 𝒦`{.AgdaFunction} (subgroup in the
   first coordinate, full second factor) and `𝒢 ᶠ× J`{.AgdaFunction} (mirrored), each
   an `IsSubgroup`{.AgdaRecord} of the product whenever the input is one — the
   superscript `ᶠ` points at the factor that is taken *full*;
+  the **slice toolkit** (`Slice₁`{.AgdaModule}, `Slice₂`{.AgdaModule}): for a
   respecting subgroup `M` of the product lying above a fattened subgroup, membership
   does not depend on the fattened coordinate — `(g , k) ∈ M ⟺ (g , ε) ∈ M` —
   because `(g , k) ≈ (g , ε) ∙ (ε , k)` and `(ε , k)` lies in `H ×ᶠ 𝒦 ⊆ M`; hence
   the restriction of `M` to one coordinate is again a respecting subgroup.

The order-isomorphism packaging of the fattening lemma lives in `FLRP.Enforceable`,
which consumes exactly these lemmas; everything here is plain group theory, kept in
the `Classical/` tree per the roadmap's placement discipline.

Following the Cubical-port discipline, the underlying equivalence of the product is
isolated in `×ᵍ-setoid`{.AgdaFunction} — the pointwise pair of the component
equivalences — so it can be mechanically substituted on the eventual port.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Product where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                  using ( _,_ ; _×_ ; proj₁ ; proj₂ )
open import Data.Fin.Base                 using ( Fin )
open import Data.Fin.Patterns             using ( 0F ; 1F )
open import Function                      using ( _∘_ ; Func )
open import Level                         using ( Level ; _⊔_ )
open import Relation.Binary               using ( Setoid )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Unary                using ( Pred ; _∈_ ; _⊆_ )

import Algebra.Properties.Group as GroupProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group           using ( ⟨_⟩ᵍᵖ )
open import Classical.Signatures.Group        using ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.Group.Basic  using ( Group ; module Group-Op ; _⊨ᵍᵖ_ )
open import Classical.Structures.Group.Subgroups
                                              using ( IsSubgroup ; mkIsSubgroup
                                                    ; sub-∙-closed ; sub-⁻¹-closed )
open import Classical.Structures.Interpret    using ( interp-cong )
open import Classical.Theories.Group          using ( Th-Group )
open import Overture.Signatures               using ( OperationSymbolsOf ; ArityOf )
open import Overture.Operations               using ( Op )
open import Overture.Terms                    using ( Term ; ℊ ; node )

open import Setoid.Algebras.Basic {𝑆 = Sig-Group}
                                              using ( Algebra ; 𝕌[_] ; 𝔻[_] ; _^_
                                                    ; mkAlgebra )
open import Setoid.Subalgebras.Subuniverses {𝑆 = Sig-Group} using ( Subuniverses )
open import Setoid.Terms                      using ( module Environment )

open Func renaming ( to to _⟨$⟩_ )

private variable α ρ β σ ℓ ℓᴹ χ : Level
```
-->

#### The fattened subgroup predicates

The fattened predicates are pure predicate transformers — they mention no group
structure beyond the carrier of the full factor — so they are defined up front, ahead
of the product construction that proves them subgroups.  `H ×ᶠ 𝒦`{.AgdaFunction}
holds at a pair exactly when the first coordinate lies in `H`; the second coordinate
ranges over all of `𝒦` (the *fattened*, full factor, marked by `ᶠ`).  The mirror
`𝒢 ᶠ× J`{.AgdaFunction} fattens the first coordinate instead.

```agda
infix 7 _×ᶠ_ _ᶠ×_

-- The subgroup H of the first factor, fattened by the full group 𝒦.
_×ᶠ_ : {G : Type α} (H : Pred G ℓ) (𝒦 : Group β σ) → Pred (G × 𝕌[ proj₁ 𝒦 ]) ℓ
(H ×ᶠ 𝒦) p = H (proj₁ p)

-- The subgroup J of the second factor, fattened by the full group 𝒢.
_ᶠ×_ : (𝒢 : Group α ρ) {K : Type β} (J : Pred K ℓ) → Pred (𝕌[ proj₁ 𝒢 ] × K) ℓ
(𝒢 ᶠ× J) p = J (proj₂ p)
```

#### The product construction

`GroupProduct 𝒢 𝒦`{.AgdaModule} packages the whole development for a fixed pair of
groups; opening it provides the product algebra, the product group, the pointwise
descriptions of its curried operations, the subgroup lemmas for the fattened
predicates, and the slice toolkit.

```agda
module GroupProduct (𝒢 : Group α ρ) (𝒦 : Group β σ) where
  private
    𝑨 = proj₁ 𝒢
    𝑩 = proj₁ 𝒦
    G = 𝕌[ 𝑨 ]
    K = 𝕌[ 𝑩 ]

  open Setoid 𝔻[ 𝑨 ] using ()
    renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝔻[ 𝑩 ] using ()
    renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )
```

The carrier of the product is the pair type `G × K`, and its equivalence is the
pointwise pair of the component equivalences — this is the isolated-equality locus
for the Cubical port.

```agda
  ×ᵍ-setoid : Setoid (α ⊔ β) (ρ ⊔ σ)
  ×ᵍ-setoid = record
    { Carrier        = G × K
    ; _≈_            = λ p q → (proj₁ p ≈₁ proj₁ q) × (proj₂ p ≈₂ proj₂ q)
    ; isEquivalence  = record
        { refl   = refl₁ , refl₂
        ; sym    = λ e → sym₁ (proj₁ e) , sym₂ (proj₂ e)
        ; trans  = λ d e → trans₁ (proj₁ d) (proj₁ e) , trans₂ (proj₂ d) (proj₂ e)
        }
    }

  open Setoid ×ᵍ-setoid using ()
    renaming ( _≈_ to _≈ₓ_ ; refl to reflₓ ; sym to symₓ ; trans to transₓ )
```

Each operation symbol acts componentwise: the interpretation of `f` at a tuple of
pairs is the pair of the component interpretations at the projected tuples.  The
congruence proof is the pair of the component congruences, via the shared
`interp-cong`{.AgdaFunction} primitive.

```agda
  ×ᵍ-Algebra : Algebra (α ⊔ β) (ρ ⊔ σ)
  ×ᵍ-Algebra = mkAlgebra ×ᵍ-setoid interp interp-congruence
    where
    interp : (o : OperationSymbolsOf Sig-Group) → Op (ArityOf Sig-Group o) (G × K)
    interp o a = (o ^ 𝑨) (proj₁ ∘ a) , (o ^ 𝑩) (proj₂ ∘ a)

    interp-congruence : ∀ o {u v : ArityOf Sig-Group o → G × K}
      → (∀ i → u i ≈ₓ v i) → interp o u ≈ₓ interp o v
    interp-congruence o e =
      interp-cong 𝑨 o (λ i → proj₁ (e i)) , interp-cong 𝑩 o (λ i → proj₂ (e i))
```

#### Componentwise term interpretation

Satisfaction of the group theory transfers componentwise, and the engine is the
following term-induction lemma: the interpretation of any term in the product is
(setoid-)equal to the pair of its interpretations in the factors, under the projected
environments.  The variable case is definitional; the node case pairs the component
congruences applied to the induction hypotheses.

```agda
  private
    module EnvP = Environment ×ᵍ-Algebra
    module EnvG = Environment 𝑨
    module EnvK = Environment 𝑩

  interp-factor : {X : Type χ} (t : Term X) (η : X → G × K)
    → (EnvP.⟦ t ⟧ ⟨$⟩ η) ≈ₓ (EnvG.⟦ t ⟧ ⟨$⟩ (proj₁ ∘ η) , EnvK.⟦ t ⟧ ⟨$⟩ (proj₂ ∘ η))
  interp-factor (ℊ x) η = refl₁ , refl₂
  interp-factor (node f args) η =
      interp-cong 𝑨 f (λ i → proj₁ (interp-factor (args i) η))
    , interp-cong 𝑩 f (λ i → proj₂ (interp-factor (args i) η))
```

Every group equation now holds in the product by one uniform argument: factor the
two sides into components, apply the component groups' satisfaction proofs, and
refold.  No case analysis on the equation is needed.

```agda
  ×ᵍ-⊨ : ×ᵍ-Algebra ⊨ᵍᵖ Th-Group
  ×ᵍ-⊨ i η =
      trans₁  (proj₁ (interp-factor lhs η))
              (trans₁ (proj₂ 𝒢 i (proj₁ ∘ η)) (sym₁ (proj₁ (interp-factor rhs η))))
    , trans₂  (proj₂ (interp-factor lhs η))
              (trans₂ (proj₂ 𝒦 i (proj₂ ∘ η)) (sym₂ (proj₂ (interp-factor rhs η))))
    where
    lhs rhs : Term (Fin 3)
    lhs = proj₁ (Th-Group i)
    rhs = proj₂ (Th-Group i)

  -- The direct product group.
  ×ᵍ-Group : Group (α ⊔ β) (ρ ⊔ σ)
  ×ᵍ-Group = ×ᵍ-Algebra , ×ᵍ-⊨
```

#### Pointwise descriptions of the curried operations

The curried accessors of `Group-Op`{.AgdaModule} applied to the product agree, up to
`≈ₓ`, with the pairs of the component accessors.  (They are not definitionally equal:
the curried form routes the arguments through a canonical `pair` tuple, and `Fin`-
indexed tuples lack η under `--cubical-compatible`; each bridge is one
`interp-cong`{.AgdaFunction} per component, the standard resolution.)

```agda
  open Group-Op 𝒢 using ()
    renaming ( _∙_ to _∙₁_ ; ε to ε₁ ; _⁻¹ to _⁻¹₁
             ; idˡ-law to idˡ-law₁ ; idʳ-law to idʳ-law₁ ; invʳ-law to invʳ-law₁ )
  open Group-Op 𝒦 using ()
    renaming ( _∙_ to _∙₂_ ; ε to ε₂ ; _⁻¹ to _⁻¹₂
             ; idˡ-law to idˡ-law₂ ; idʳ-law to idʳ-law₂ ; invʳ-law to invʳ-law₂ )
  open Group-Op ×ᵍ-Group using ()
    renaming ( _∙_ to _∙ₓ_ ; ε to εₓ ; _⁻¹ to _⁻¹ₓ )

  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ using () renaming ( ε⁻¹≈ε to ε⁻¹≈ε₁ )
  open GroupProperties ⟨ 𝒦 ⟩ᵍᵖ using () renaming ( ε⁻¹≈ε to ε⁻¹≈ε₂ )

  -- The product multiplication is componentwise.
  ∙ₓ-pointwise : ∀ x y → (x ∙ₓ y) ≈ₓ (proj₁ x ∙₁ proj₁ y , proj₂ x ∙₂ proj₂ y)
  ∙ₓ-pointwise x y =
      interp-cong 𝑨 ∙-Op (λ { 0F → refl₁ ; 1F → refl₁ })
    , interp-cong 𝑩 ∙-Op (λ { 0F → refl₂ ; 1F → refl₂ })

  -- The product identity is the pair of identities.
  εₓ-pointwise : εₓ ≈ₓ (ε₁ , ε₂)
  εₓ-pointwise = interp-cong 𝑨 ε-Op (λ ()) , interp-cong 𝑩 ε-Op (λ ())

  -- The product inverse is componentwise.
  ⁻¹ₓ-pointwise : ∀ x → (x ⁻¹ₓ) ≈ₓ (proj₁ x ⁻¹₁ , proj₂ x ⁻¹₂)
  ⁻¹ₓ-pointwise x =
      interp-cong 𝑨 ⁻¹-Op (λ { 0F → refl₁ })
    , interp-cong 𝑩 ⁻¹-Op (λ { 0F → refl₂ })
```

#### The fattened predicates are subgroups

A fattened predicate is a subuniverse of the product *definitionally*: the first
component of an interpreted operation of the product is the corresponding interpreted
operation of the first factor, so closure is inherited with no equational reasoning
at all.  Respecting the product equality is likewise inherited from the respected
factor.

```agda
  module _ {H : Pred G ℓ} where

    -- H ×ᶠ 𝒦 respects the product equality whenever H respects ≈₁.
    ×ᶠ-respects : H Respects _≈₁_ → (H ×ᶠ 𝒦) Respects _≈ₓ_
    ×ᶠ-respects resp e h = resp (proj₁ e) h

    -- H ×ᶠ 𝒦 is closed under the product operations whenever H is closed (definitional).
    ×ᶠ-isSubuniverse : H ∈ Subuniverses 𝑨 → (H ×ᶠ 𝒦) ∈ Subuniverses ×ᵍ-Algebra
    ×ᶠ-isSubuniverse H-sub f a im = H-sub f (proj₁ ∘ a) im

    -- Fattening a subgroup of 𝒢 by the full 𝒦 yields a subgroup of the product.
    ×ᶠ-isSubgroup : IsSubgroup 𝒢 H → IsSubgroup ×ᵍ-Group (H ×ᶠ 𝒦)
    ×ᶠ-isSubgroup H-sg = record
      { respects       = ×ᶠ-respects (IsSubgroup.respects H-sg)
      ; isSubuniverse  = ×ᶠ-isSubuniverse (IsSubgroup.isSubuniverse H-sg)
      }

  module _ {J : Pred K ℓ} where

    -- Mirror image: 𝒢 ᶠ× J respects the product equality whenever J respects ≈₂.
    ᶠ×-respects : J Respects _≈₂_ → (𝒢 ᶠ× J) Respects _≈ₓ_
    ᶠ×-respects resp e j = resp (proj₂ e) j

    -- 𝒢 ᶠ× J is closed under the product operations whenever J is closed (definitional).
    ᶠ×-isSubuniverse : J ∈ Subuniverses 𝑩 → (𝒢 ᶠ× J) ∈ Subuniverses ×ᵍ-Algebra
    ᶠ×-isSubuniverse J-sub f a im = J-sub f (proj₂ ∘ a) im

    -- Fattening a subgroup of 𝒦 by the full 𝒢 yields a subgroup of the product.
    ᶠ×-isSubgroup : IsSubgroup 𝒦 J → IsSubgroup ×ᵍ-Group (𝒢 ᶠ× J)
    ᶠ×-isSubgroup J-sg = record
      { respects       = ᶠ×-respects (IsSubgroup.respects J-sg)
      ; isSubuniverse  = ᶠ×-isSubuniverse (IsSubgroup.isSubuniverse J-sg)
      }
```

#### The slice toolkit, first coordinate

Fix a subgroup `H` of `𝒢` and a respecting subgroup `M` of the product with
`H ×ᶠ 𝒦 ⊆ M`.  Because `M` contains the whole column `{ε₁} × K` (the identity of
`𝒢` lies in `H`), membership in `M` is insensitive to the second coordinate:
`(g , k) ∈ M` iff `(g , ε₂) ∈ M`.  The two directions are
`slice-out`{.AgdaFunction} and `slice-in`{.AgdaFunction}; each multiplies by a
column element and rewrites along the pointwise description of `∙ₓ` — this is the
note's observation that `(g , k) ≈ (g , ε) ∙ (ε , k)` with `(ε , k) ∈ H ×ᶠ 𝒦 ⊆ M`.
Consequently the restriction `λ g → M (g , ε₂)` is a respecting subgroup of `𝒢`
containing `H`, and pulling it back along `proj₁` recovers `M` — the mutually
inverse maps of the fattening lemma.

```agda
  module Slice₁ (H : Pred G ℓ) (H-sg : IsSubgroup 𝒢 H)
    (M : Pred (G × K) ℓᴹ)
    (M-sub : M ∈ Subuniverses ×ᵍ-Algebra)
    (M-resp : M Respects _≈ₓ_)
    (HK⊆M : (H ×ᶠ 𝒦) ⊆ M)
    where

    -- M contains the column {ε₁} × K, because ε₁ ∈ H.
    ε-column : (k : K) → (ε₁ , k) ∈ M
    ε-column k = HK⊆M (IsSubgroup.ε-closed H-sg)

    -- Forgetting the second coordinate: (g , k) ∈ M implies (g , ε₂) ∈ M.
    slice-out : ∀ {g k} → (g , k) ∈ M → (g , ε₂) ∈ M
    slice-out {g} {k} m =
      M-resp  (transₓ (∙ₓ-pointwise (g , k) (ε₁ , k ⁻¹₂)) (idʳ-law₁ g , invʳ-law₂ k))
              (sub-∙-closed ×ᵍ-Group M M-sub m (ε-column (k ⁻¹₂)))

    -- Reinstating any second coordinate: (g , ε₂) ∈ M implies (g , k) ∈ M.
    slice-in : ∀ {g k} → (g , ε₂) ∈ M → (g , k) ∈ M
    slice-in {g} {k} m =
      M-resp  (transₓ (∙ₓ-pointwise (g , ε₂) (ε₁ , k)) (idʳ-law₁ g , idˡ-law₂ k))
              (sub-∙-closed ×ᵍ-Group M M-sub m (ε-column k))

    -- The restriction of M to the first coordinate.
    restrict₁ : Pred G ℓᴹ
    restrict₁ g = M (g , ε₂)

    -- The restriction is a respecting subgroup of 𝒢.
    restrict₁-isSubgroup : IsSubgroup 𝒢 restrict₁
    restrict₁-isSubgroup = mkIsSubgroup 𝒢 resp ∙-closed ε-closed ⁻¹-closed
      where
      resp : restrict₁ Respects _≈₁_
      resp e m = M-resp (e , refl₂) m

      ∙-closed : ∀ {x y} → restrict₁ x → restrict₁ y → restrict₁ (x ∙₁ y)
      ∙-closed {x} {y} mx my =
        M-resp  (transₓ (∙ₓ-pointwise (x , ε₂) (y , ε₂)) (refl₁ , idˡ-law₂ ε₂))
                (sub-∙-closed ×ᵍ-Group M M-sub mx my)

      ε-closed : restrict₁ ε₁
      ε-closed = ε-column ε₂

      ⁻¹-closed : ∀ {x} → restrict₁ x → restrict₁ (x ⁻¹₁)
      ⁻¹-closed {x} m =
        M-resp  (transₓ (⁻¹ₓ-pointwise (x , ε₂)) (refl₁ , ε⁻¹≈ε₂))
                (sub-⁻¹-closed ×ᵍ-Group M M-sub m)

    -- The restriction contains H (specialize HK⊆M to pairs (g , ε₂)).
    restrict₁-⊇H : H ⊆ restrict₁
    restrict₁-⊇H h = HK⊆M h

    -- Round trip: pulling the restriction back along proj₁ recovers M.
    restrict₁-pull-⊆ : (λ p → restrict₁ (proj₁ p)) ⊆ M
    restrict₁-pull-⊆ m = slice-in m

    restrict₁-pull-⊇ : M ⊆ (λ p → restrict₁ (proj₁ p))
    restrict₁-pull-⊇ m = slice-out m
```

#### The slice toolkit, second coordinate

The mirror of `Slice₁`{.AgdaModule}: for a respecting subgroup `M ⊇ 𝒢 ᶠ× J` of the
product, membership is insensitive to the *first* coordinate, the restriction
`λ k → M (ε₁ , k)` is a respecting subgroup of `𝒦` containing `J`, and pulling back
along `proj₂` recovers `M`.  The proofs are the coordinatewise mirrors of the ones
above.

```agda
  module Slice₂ (J : Pred K ℓ) (J-sg : IsSubgroup 𝒦 J)
    (M : Pred (G × K) ℓᴹ)
    (M-sub : M ∈ Subuniverses ×ᵍ-Algebra)
    (M-resp : M Respects _≈ₓ_)
    (GJ⊆M : (𝒢 ᶠ× J) ⊆ M)
    where

    -- M contains the row G × {ε₂}, because ε₂ ∈ J.
    ε-row : (g : G) → (g , ε₂) ∈ M
    ε-row g = GJ⊆M (IsSubgroup.ε-closed J-sg)

    -- Forgetting the first coordinate: (g , k) ∈ M implies (ε₁ , k) ∈ M.
    slice-out : ∀ {g k} → (g , k) ∈ M → (ε₁ , k) ∈ M
    slice-out {g} {k} m =
      M-resp  (transₓ (∙ₓ-pointwise (g , k) (g ⁻¹₁ , ε₂)) (invʳ-law₁ g , idʳ-law₂ k))
              (sub-∙-closed ×ᵍ-Group M M-sub m (ε-row (g ⁻¹₁)))

    -- Reinstating any first coordinate: (ε₁ , k) ∈ M implies (g , k) ∈ M.
    slice-in : ∀ {g k} → (ε₁ , k) ∈ M → (g , k) ∈ M
    slice-in {g} {k} m =
      M-resp  (transₓ (∙ₓ-pointwise (g , ε₂) (ε₁ , k)) (idʳ-law₁ g , idˡ-law₂ k))
              (sub-∙-closed ×ᵍ-Group M M-sub (ε-row g) m)

    -- The restriction of M to the second coordinate.
    restrict₂ : Pred K ℓᴹ
    restrict₂ k = M (ε₁ , k)

    -- The restriction is a respecting subgroup of 𝒦.
    restrict₂-isSubgroup : IsSubgroup 𝒦 restrict₂
    restrict₂-isSubgroup = mkIsSubgroup 𝒦 resp ∙-closed ε-closed ⁻¹-closed
      where
      resp : restrict₂ Respects _≈₂_
      resp e m = M-resp (refl₁ , e) m

      ∙-closed : ∀ {x y} → restrict₂ x → restrict₂ y → restrict₂ (x ∙₂ y)
      ∙-closed {x} {y} mx my =
        M-resp  (transₓ (∙ₓ-pointwise (ε₁ , x) (ε₁ , y)) (idʳ-law₁ ε₁ , refl₂))
                (sub-∙-closed ×ᵍ-Group M M-sub mx my)

      ε-closed : restrict₂ ε₂
      ε-closed = ε-row ε₁

      ⁻¹-closed : ∀ {x} → restrict₂ x → restrict₂ (x ⁻¹₂)
      ⁻¹-closed {x} m =
        M-resp  (transₓ (⁻¹ₓ-pointwise (ε₁ , x)) (ε⁻¹≈ε₁ , refl₂))
                (sub-⁻¹-closed ×ᵍ-Group M M-sub m)

    -- The restriction contains J.
    restrict₂-⊇J : J ⊆ restrict₂
    restrict₂-⊇J j = GJ⊆M j

    -- Round trip: pulling the restriction back along proj₂ recovers M.
    restrict₂-pull-⊆ : (λ p → restrict₂ (proj₂ p)) ⊆ M
    restrict₂-pull-⊆ m = slice-in m

    restrict₂-pull-⊇ : M ⊆ (λ p → restrict₂ (proj₂ p))
    restrict₂-pull-⊇ m = slice-out m
```

#### The product as a binary operation on groups

The infix form, for use at call sites.

```agda
infixr 7 _×ᵍ_

_×ᵍ_ : Group α ρ → Group β σ → Group (α ⊔ β) (ρ ⊔ σ)
𝒢 ×ᵍ 𝒦 = GroupProduct.×ᵍ-Group 𝒢 𝒦
```
