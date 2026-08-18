---
layout: default
file: "src/Classical/Structures/Group/Power.lagda.md"
title: "Classical.Structures.Group.Power module"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### Indexed products and powers of groups

This is the [Classical.Structures.Group.Power][] module of the [Agda Universal Algebra Library][].

For an indexed family `𝒢 : I → Group α ρ` of groups presented as Σ-typed structures
over [`Sig-Group`][Classical.Signatures.Group], this module constructs the
**indexed direct product** `⨅ᵍ`{.AgdaFunction}` 𝒢`, that is, the group on the product
algebra `⨅`{.AgdaFunction} of [Setoid.Algebras.Products][], whose carrier is the
function type `∀ i → 𝕌[ 𝑮 i ]` with pointwise operations and pointwise equality.

The five group laws transfer coordinatewise by `⊧-P-invar`{.AgdaFunction} of
[Setoid.Varieties.Properties][] (products preserve identities) so no term induction
is repeated here.

This construction generalizes the binary product `_×ᵍ_`{.AgdaFunction} of
[Classical.Structures.Group.Product][] rather than replacing it.[^1]

The power `𝒢 ^ᵍ n` is the constant-family product over
`I = Fin n`, so an element of `S ^ᵍ n` is literally a map `x : Fin n → S`, and
conditions such as "`x` is constant on the blocks of a partition of the index set"
are stated by comparing values of `x` at indices, with no tuple bookkeeping.

Besides the product and the power, the module provides

+  **pointwise descriptions of the curried operations**, `(x ⊗ y) i ≈ x i ∙ y i`
   and its companions for `ε` and `⁻¹`;[^2]
+  **coordinate projections as homomorphisms**, by instantiating the generic
   `⨅-proj`{.AgdaFunction} of [Setoid.Homomorphisms.Products][].

The underlying equivalence of the product is not redefined here.[^3]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Power where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base       using ( Fin )
open import Data.Fin.Patterns   using ( 0F ; 1F )
open import Data.Nat.Base       using ( ℕ )
open import Data.Product        using ( _,_ ; proj₁ ; proj₂ )
open import Function            using ( _∘_ )
open import Level               using ( Level ; _⊔_ )
open import Relation.Binary     using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Group        using  ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.Group.Basic  using  ( Group ; module Group-Op ; _⊨ᵍᵖ_ )
open import Classical.Structures.Interpret    using  ( interp-cong )
open import Classical.Theories.Group          using  ( Th-Group )
open import Setoid.Algebras.Basic             using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Products          using  ( ⨅ )
open import Setoid.Homomorphisms.Basic        using  ( hom )
open import Setoid.Homomorphisms.Products     using  ( ⨅-proj )
open import Setoid.Varieties.Properties       using  ( ⊧-P-invar )

private variable ι α ρ : Level
```
-->

#### The indexed product of a family of groups

`GroupFamilyProduct`{.AgdaModule}` 𝒢` packages the construction for a fixed family:
the product algebra, the transferred satisfaction proof, and the product group.
Each group equation holds in `⨅`{.AgdaFunction} because it holds in every coordinate;
this is `⊧-P-invar`{.AgdaFunction} applied to the family of satisfaction proofs, one
application per equation of `Th-Group`{.AgdaFunction}.

```agda
module GroupFamilyProduct {I : Type ι} (𝒢 : I → Group α ρ) where

  private
    𝑮 : I → Algebra {𝑆 = Sig-Group} α ρ
    𝑮 = proj₁ ∘ 𝒢

  -- Every group equation transfers to the product, coordinatewise.
  ⨅ᵍ-⊨ : ⨅ 𝑮 ⊨ᵍᵖ Th-Group
  ⨅ᵍ-⊨ eq = ⊧-P-invar {p = Th-Group eq .proj₁} {q = Th-Group eq .proj₂}
              𝑮 λ i → 𝒢 i .proj₂ eq

  -- The indexed direct product group.
  ⨅ᵍ-Group : Group (α ⊔ ι) (ρ ⊔ ι)
  ⨅ᵍ-Group = ⨅ 𝑮 , ⨅ᵍ-⊨
```

The top-level form, for use at call sites.

```agda
⨅ᵍ : {I : Type ι} → (I → Group α ρ) → Group (α ⊔ ι) (ρ ⊔ ι)
⨅ᵍ = GroupFamilyProduct.⨅ᵍ-Group
```

#### Powers: the constant-family product

`GroupPower`{.AgdaModule}` I 𝒢` is the product of the constant family at
`𝒢`{.AgdaBound} (the power `𝒢 ^ I`) together with the power-specific toolkit:
pointwise descriptions of the curried operations and the coordinate projections.

Opening it re-exports the `GroupFamilyProduct`{.AgdaModule} kit for the constant
family, so `⨅ᵍ-Group`{.AgdaFunction} names the power group itself.

```agda
module GroupPower (I : Type ι) (𝒢 : Group α ρ) where

  open GroupFamilyProduct (λ (_ : I) → 𝒢) public

  private
    𝑮 = 𝒢 .proj₁
    𝑮ᴵ = ⨅ᵍ-Group .proj₁

  open Setoid 𝔻[ 𝑮 ] using ( _≈_ ; refl )
```

The curried accessors of `Group-Op`{.AgdaModule} applied to the power agree, at
each coordinate, with the accessors of the base group applied to the coordinate
values.[^4]

```agda
  open Group-Op 𝒢         using ( _∙_ ; ε ; _⁻¹ )
  open Group-Op ⨅ᵍ-Group  using () renaming ( _∙_ to _⊗_ ; ε to e ; _⁻¹ to inv )

  -- The power multiplication is pointwise.
  ⊗-pointwise : ∀ x y i → (x ⊗ y) i ≈ x i ∙ y i
  ⊗-pointwise x y i = interp-cong 𝑮 ∙-Op λ { 0F → refl ; 1F → refl }

  -- The power identity is the constant identity tuple.
  e-pointwise : ∀ i → e i ≈ ε
  e-pointwise i = interp-cong 𝑮 ε-Op λ ()

  -- The power inverse is pointwise.
  inv-pointwise : ∀ x i → (inv x) i ≈ x i ⁻¹
  inv-pointwise x i = interp-cong 𝑮 ⁻¹-Op λ { 0F → refl }
```

Evaluation at a coordinate is a homomorphism from the power onto the base group —
the generic projection of [Setoid.Homomorphisms.Products][], instantiated at the
constant family.

```agda
  -- The i-th coordinate projection, as a homomorphism.
  proj-hom : (i : I) → hom 𝑮ᴵ 𝑮
  proj-hom = ⨅-proj λ (_ : I) → 𝑮
```

#### The finite power of a group

The power of a group by a natural number is the constant-family product over `Fin n`.
Since `Fin n` lives at level zero, the levels of the base group are preserved; in
particular the power of a `Group 0ℓ 0ℓ` is again a `Group 0ℓ 0ℓ`.

```agda
infixl 8 _^ᵍ_

_^ᵍ_ : Group α ρ → ℕ → Group α ρ
𝒢 ^ᵍ n = GroupPower.⨅ᵍ-Group (Fin n) 𝒢
```

---

[^1]:  The binary module deliberately keeps the *pair* carrier `G × K`, which is the
       form the FLRP fattening arguments consume, whereas the function-typed carrier
       here is the form Kurzweil's construction consumes.

[^2]:  This bridges the `Fin`-tuple η-gap exactly as in the binary module; the curried
       accessors route arguments through a canonical `pair` tuple, and `Fin`-indexed
       tuples lack η under `--cubical-compatible`; each bridge is one
       `interp-cong`{.AgdaFunction} per use.

[^3]:  Following the planned-Cubical-port discipline, the underlying equivalence of
       the product is not redefined here; it is the pointwise equivalence of
       `⨅`{.AgdaFunction}, so the equality locus to substitute on the eventual port
       is that of [Setoid.Algebras.Products][] alone.

[^4]:  They are not definitionally equal, for the same reason as in the binary
       module: the curried form routes the arguments through a canonical `pair`
       tuple, and `Fin`-indexed tuples lack η under `--cubical-compatible`; each
       bridge is one `interp-cong`{.AgdaFunction}.
