---
layout: default
file: "src/Classical/Categories/AdjoinUnit.lagda.md"
title: "Classical.Categories.AdjoinUnit module"
date: "2026-06-10"
author: "the agda-algebras development team"
---

### Free expansion: the free monoid on a semigroup, left adjoint to the reduct

This is the [Classical.Categories.AdjoinUnit][] module of the [Agda Universal Algebra Library][].

In this module is the *free expansion* along the symbol-adjoining signature inclusion
`Sig-Magma ↪ Sig-Monoid`, in its classical concrete instance — freely adjoining a
unit to a semigroup, i.e., the free monoid on a semigroup — proved to be left adjoint
to the reduct-derived forgetful functor, with unit, counit, both naturality squares,
and the two triangle identities, plus the explicit universal property (existence and
uniqueness of the extension).

`adjoinUnit 𝑺` enlarges the carrier by one fresh element; the carrier of the
expansion is `Maybe 𝕌[ 𝑺 ]`, with `nothing` the freshly adjoined unit (interpreting
`ε-Op`) and `just` the inclusion of the old elements.  The extended operation makes
`nothing` neutral on both sides and multiplies old elements in `𝑺`, so the monoid
unit laws hold by computation and associativity reduces to that of the semigroup.
This is the sharp contrast with `expand-ε` ([`Classical.Structures.Monoid`][]), which
interprets `ε-Op` as a *chosen element of the existing carrier* — a section of the
reduct (`opsToBareMonoid-section`), not its left adjoint.

(See `docs/notes/m4-5d-free-expansion.md` for the full comparison and for why this
module lives at the theory-satisfying (bundle) level; it is precisely the monoid
*equations* that collapse the free expansion to first-order normal forms (`Maybe`),
with no setoid quotient; the equation-free expansion on raw algebra categories needs
the term-algebra quotient and is deferred.)

The categorical scaffolding is the minimal self-contained vocabulary we need here:
the categories of semigroups and monoids are *full subcategories*
([`Setoid.Categories.FullSubcategory`][]) of the algebra categories
([`Alg`][Setoid.Categories.Algebra]) of their signatures.  A homomorphism of
theory-satisfying algebras is just a homomorphism of the underlying algebras.
The forgetful functor is [`reductF`][Classical.Categories.Reduct] restricted along
`monoid→semigroup`'s theory transfer.

This module lives in `Classical.Categories` because its objects are the `Classical`
bundles and its right adjoint's object map is `reduct`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Categories.AdjoinUnit where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Empty.Polymorphic                 using ( ⊥ )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Maybe.Base                        using ( Maybe ; just ; nothing )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Data.Unit.Polymorphic.Base             using ( ⊤ ; tt )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using  ( Setoid ; Reflexive ; Rel
                                                          ; Symmetric ; Transitive )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

open import Algebra.Definitions as stdlib-Algebra
  using (Associative; Commutative; LeftIdentity; RightIdentity; LeftZero; RightZero; Zero)


open Func using ( cong ) renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Categories.Forgetful     using ( magma↪monoid )
open import Classical.Categories.Reduct        using ( reductF )
open import Classical.Signatures.Magma         using ( Sig-Magma ; Op-Magma )
                                               renaming ( ∙-Op to ∙-Opᵐᵃ )
open import Classical.Signatures.Monoid        using ( Sig-Monoid ; Op-Monoid ; ∙-Op ; ε-Op )
open import Classical.Structures.Interpret     using ( interp-cong )
open import Classical.Structures.Magma         using ( hom-preserves-∙ )
open import Classical.Structures.Monoid        using ( Monoid ; _⊨ᵐᵒ_ ; module Monoid-Op
                                                     ; monoid→semigroup ; hom-preserves-ε )
open import Classical.Structures.Reduct        using ( reduct )
open import Classical.Structures.Semigroup     using ( Semigroup ; module Semigroup-Op )
                                               renaming ( _⊨_ to _⊨ˢᵍ_ )
open import Classical.Theories.Monoid          using ( Th-Monoid ; assoc ; idˡ ; idʳ )
open import Classical.Theories.Semigroup       using ( Th-Semigroup )
open import Overture.Signatures                using ( ArityOf )
open import Setoid.Algebras.Basic              using ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Homomorphisms.Basic         using ( hom ; IsHom )
open import Setoid.Homomorphisms.Properties    using ( ⊙-hom ; 𝒾𝒹 )
open import Setoid.Categories.Adjunction       using ( Adjunction )
open import Setoid.Categories.Category         using ( Category )
open import Setoid.Categories.FullSubcategory  using ( FullSubcategory ; FullSubcategoryF )
open import Setoid.Categories.Functor          using ( Functor )

import Setoid.Categories.Algebra as AlgCat

open Algebra using ( Domain ; Interp )

private variable α ρ : Level
```

#### The categories of semigroups and monoids

Each theory-satisfying classical structure is a full subcategory of the algebra
category of its signature, on the satisfaction predicate.  The objects are
*definitionally* the Σ-typed bundles `Semigroup α ρ` and `Monoid α ρ` of the
`Classical.Structures` modules, as the two `refl` lemmas certify.

```agda
Semigroups : (α ρ : Level) → Category (suc (α ⊔ ρ)) (α ⊔ ρ) (α ⊔ ρ)
Semigroups α ρ = FullSubcategory (AlgCat.Alg {𝑆 = Sig-Magma} α ρ) (_⊨ˢᵍ Th-Semigroup)

Monoids : (α ρ : Level) → Category (suc (α ⊔ ρ)) (α ⊔ ρ) (α ⊔ ρ)
Monoids α ρ = FullSubcategory (AlgCat.Alg {𝑆 = Sig-Monoid} α ρ) (_⊨ᵐᵒ Th-Monoid)

Semigroups-Obj : Category.Obj (Semigroups α ρ) ≡ Semigroup α ρ
Semigroups-Obj = refl

Monoids-Obj : Category.Obj (Monoids α ρ) ≡ Monoid α ρ
Monoids-Obj = refl
```

#### The forgetful functor

The right adjoint: `reductF magma↪monoid` restricted to the full subcategories,
with the theory transferred by the proof inside `monoid→semigroup`.  On objects it
*is* `monoid→semigroup`, definitionally.

```agda
forgetUnitF : Functor (Monoids α ρ) (Semigroups α ρ)
forgetUnitF = FullSubcategoryF (reductF magma↪monoid) (λ {𝑨} thm → proj₂ (monoid→semigroup (𝑨 , thm)))

module _ (ℳ : Monoid α ρ) where
  open Functor (forgetUnitF{α}{ρ}) using (F₀)

  forgetUnitF-F₀ : F₀ ℳ ≡ monoid→semigroup ℳ
  forgetUnitF-F₀ = refl
```

#### The free expansion of a semigroup

`AdjoinUnit 𝑺` constructs the free monoid `𝑨¹` on the semigroup `𝑺` (the classical
`S¹`).  The carrier is `Maybe 𝕌[ 𝑨 ]`; the setoid equality `_≈¹_` compares `just`s
in `𝑺`'s setoid and makes `nothing` equal only to itself.  The relation is defined by
pattern matching (rather than via `Data.Maybe.Relation.Binary.Pointwise`, whose
relation level is `α ⊔ ρ`) so that it sits at level `ρ` exactly and the construction
stays inside `Monoids α ρ` — an adjunction needs both functors between the *same*
two categories.

```agda
module AdjoinUnit {α ρ : Level} (𝑺 : Semigroup α ρ) where
  private 𝑨 = proj₁ 𝑺
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Semigroup-Op 𝑺 using ( _∙_ ; ∙-cong ; assoc-law )

  -- The carrier: the old elements (via just) plus one fresh element, nothing,
  -- which will interpret ε-Op.
  A¹ : Type α
  A¹ = Maybe 𝕌[ 𝑨 ]

  -- Setoid equality on A¹, at level ρ exactly.
  infix 4 _≈¹_
  _≈¹_ : Rel A¹ ρ
  just x ≈¹ just y = x ≈ y
  just _ ≈¹ nothing = ⊥
  nothing ≈¹ just _ = ⊥
  nothing ≈¹ nothing = ⊤

  -- The equivalence proofs.  ≈¹-refl takes its argument explicitly: _≈¹_ is a
  -- pattern-matching function, so the unifier cannot recover the argument from
  -- the goal (it would have to invert a non-injective function); the same gotcha
  -- forces the eta-expanded field assignments in 𝔻¹ below.
  ≈¹-refl : Reflexive _≈¹_
  ≈¹-refl {just _} = ≈refl
  ≈¹-refl {nothing} = tt

  ≈¹-sym : Symmetric _≈¹_
  ≈¹-sym {just _} {just _} x≈y = ≈sym x≈y
  ≈¹-sym {just _} {nothing} ()
  ≈¹-sym {nothing} {just _} ()
  ≈¹-sym {nothing} {nothing} _ = tt

  ≈¹-trans : Transitive _≈¹_
  ≈¹-trans {just _} {just _} {just _} x≈y y≈z = ≈trans x≈y y≈z
  ≈¹-trans {nothing} {nothing} {nothing} _ _ = tt
  -- Do we need the following cases?
  -- ≈¹-trans {just _} {just _} {nothing} _ ()
  -- ≈¹-trans {just _} {nothing} ()
  -- ≈¹-trans {nothing} {just _} ()
  -- ≈¹-trans {nothing} {nothing} {just _} _ ()

  𝔻¹ : Setoid α ρ
  𝔻¹ = record
    { Carrier = A¹
    ; _≈_ = _≈¹_
    ; isEquivalence = record  { refl = λ {x} → ≈¹-refl {x}
                              ; sym = λ {x y} → ≈¹-sym {x} {y}
                              ; trans = λ {x y z} → ≈¹-trans {x} {y} {z}
                              }
    }
```

The extended operation: `nothing` is neutral on either side, and old elements
multiply in `𝑺`.  This is where the construction differs from the *raw* free
expansion: the unit laws are baked into the case split, so no formal product
involving the fresh element survives as a new carrier element.

```agda
  infixl 7 _∙¹_
  _∙¹_ : A¹ → A¹ → A¹
  just x ∙¹ just y = just (x ∙ y)
  just x ∙¹ nothing = just x
  nothing ∙¹ t = t

  ∙¹-cong : {s s' t t' : A¹} → s ≈¹ s' → t ≈¹ t' → s ∙¹ t ≈¹ s' ∙¹ t'
  ∙¹-cong {just _} {just _} {just _} {just _} s≈s' t≈t' = ∙-cong s≈s' t≈t'
  ∙¹-cong {nothing} {nothing} _ t≈t' = t≈t'
  ∙¹-cong {just _} {just _} {nothing} {nothing} s≈s' _ = s≈s'
  -- Do we need the following cases?
  -- ∙¹-cong {just _} {just _} {just _} {nothing} _ ()
  -- ∙¹-cong {just _} {just _} {nothing} {just _} _ ()
  -- ∙¹-cong {just _} {nothing} ()
  -- ∙¹-cong {nothing} {just _} ()

  -- The Sig-Monoid algebra: ∙-Op is the extended operation, ε-Op the fresh element.
  𝑨¹ : Algebra {𝑆 = Sig-Monoid} α ρ
  𝑨¹ .Domain = 𝔻¹
  𝑨¹ .Interp ⟨$⟩ (∙-Op , args) = args 0F ∙¹ args 1F
  𝑨¹ .Interp ⟨$⟩ (ε-Op , _) = nothing
  𝑨¹ .Interp .cong {∙-Op , u} {.∙-Op , v} (refl , u≈v) =
    ∙¹-cong {u 0F} {v 0F} {u 1F} {v 1F} (u≈v 0F) (u≈v 1F)
  𝑨¹ .Interp .cong {ε-Op , _} {.ε-Op , _} (refl , _) = tt
```

`𝑨¹` satisfies the monoid theory.  The unit laws hold by computation on the `Maybe`
case split (the left law definitionally, the right one after a case on the
argument); associativity reduces to the semigroup's `assoc-law` when all three
arguments are old, and to reflexivity whenever `nothing` is involved.  Because the
interpretation is concrete, the term interpretations in `Th-Monoid` compute, so the
satisfaction proofs are exactly these curried lemmas (the `eqsToMonoid` pattern).

```agda
  ∙¹-assoc : Associative _≈¹_ _∙¹_
  ∙¹-assoc (just x) (just y) (just z) = assoc-law x y z
  ∙¹-assoc (just _) (just _) nothing = ≈refl
  ∙¹-assoc (just _) nothing (just _) = ≈refl
  ∙¹-assoc (just _) nothing nothing = ≈refl
  ∙¹-assoc nothing t u = ≈¹-refl {t ∙¹ u}

  ∙¹-idʳ : (t : A¹) → (t ∙¹ nothing) ≈¹ t
  ∙¹-idʳ (just _) = ≈refl
  ∙¹-idʳ nothing = tt

  𝑨¹⊨Th-Monoid : 𝑨¹ ⊨ᵐᵒ Th-Monoid
  𝑨¹⊨Th-Monoid assoc η = ∙¹-assoc (η 0F) (η 1F) (η 2F)
  𝑨¹⊨Th-Monoid idˡ η = ≈¹-refl {η 0F}
  𝑨¹⊨Th-Monoid idʳ η = ∙¹-idʳ (η 0F)
```

The free expansion, as the object map `Semigroup α ρ → Monoid α ρ`:

```agda
adjoinUnit : Semigroup α ρ → Monoid α ρ
adjoinUnit 𝑺 = 𝑨¹ , 𝑨¹⊨Th-Monoid
  where open AdjoinUnit 𝑺
```

#### The free functor

The morphism action maps a magma homomorphism over the `Maybe` carriers, sending the
fresh unit to the fresh unit.  Compatibility at `∙-Op` is the curried invariant
[`hom-preserves-∙`][Classical.Structures.Magma] on old elements and reflexivity
otherwise; at `ε-Op` it is definitional.

```agda
module _ (𝑺 𝑻 : Semigroup α ρ) where
  private
    𝑨 𝑩 : Algebra α ρ
    𝑨 = proj₁ 𝑺
    𝑩 = proj₁ 𝑻
  open AdjoinUnit 𝑺 using () renaming (𝔻¹ to 𝔻ˢ; A¹ to Aˢ; _∙¹_ to _∙ˢ_; 𝑨¹ to 𝑨ˢ)
  open AdjoinUnit 𝑻 using () renaming  ( 𝔻¹ to 𝔻ᵀ; _≈¹_ to _≈ᵀ_; _∙¹_ to _∙ᵀ_
                                       ; ≈¹-refl to ≈ᵀ-refl; 𝑨¹ to 𝑨ᵀ)
  open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᵇ_ ; refl to ≈ᵇ-refl )

  map¹ : Func 𝔻[ 𝑨 ] 𝔻[ 𝑩 ] → Func 𝔻ˢ 𝔻ᵀ
  map¹ h ⟨$⟩ just x  = just (h ⟨$⟩ x)
  map¹ h ⟨$⟩ nothing = nothing
  map¹ h .cong {just _} {just _} x≈y = cong h x≈y
  map¹ h .cong {nothing} {nothing} _ = tt
  map¹ h .cong {just _} {nothing} ()
  map¹ h .cong {nothing} {just _} ()

  -- map¹ preserves the extended operation.
  map¹-∙ : (f : hom 𝑨 𝑩) (s t : Aˢ)
    → map¹ (proj₁ f) ⟨$⟩ (s ∙ˢ t)  ≈ᵀ  (map¹ (proj₁ f) ⟨$⟩ s) ∙ᵀ (map¹ (proj₁ f) ⟨$⟩ t)
  map¹-∙ f (just x) (just y) = hom-preserves-∙ f x y
  map¹-∙ f (just _) nothing = ≈ᵇ-refl
  map¹-∙ f nothing t = ≈ᵀ-refl {map¹ (proj₁ f) ⟨$⟩ t}

  map¹-compatible : (f : hom 𝑨 𝑩) {o : Op-Monoid} {args : ArityOf Sig-Monoid o → Aˢ}
    → map¹ (proj₁ f) ⟨$⟩ (o ^ 𝑨ˢ) args ≈ᵀ (o ^ 𝑨ᵀ) (λ i → map¹ (proj₁ f) ⟨$⟩ args i)
  map¹-compatible f {∙-Op} {args} = map¹-∙ f (args 0F) (args 1F)
  map¹-compatible f {ε-Op} = tt

  adjoinUnit-hom : hom 𝑨 𝑩 → hom 𝑨ˢ 𝑨ᵀ
  adjoinUnit-hom f = map¹ (proj₁ f) , record { compatible = λ {o} → map¹-compatible f {o} }

  -- map¹ respects the pointwise hom-equality.
  adjoinUnit-resp : {f g : hom 𝑨 𝑩} → ((x : 𝕌[ 𝑨 ]) → proj₁ f ⟨$⟩ x ≈ᵇ proj₁ g ⟨$⟩ x)
    → (t : Aˢ) → map¹ (proj₁ f) ⟨$⟩ t ≈ᵀ map¹ (proj₁ g) ⟨$⟩ t
  adjoinUnit-resp f≋g (just x) = f≋g x
  adjoinUnit-resp f≋g nothing  = tt
```

The functor laws are pointwise on the `Maybe` carrier: on `just` both sides agree
definitionally, on `nothing` both sides are the fresh unit.

```agda
module _ (𝑺 : Semigroup α ρ) where
  open AdjoinUnit 𝑺 using (A¹; _≈¹_)
  open Setoid 𝔻[ proj₁ 𝑺 ] using () renaming ( refl to ≈ˢ-refl )

  adjoinUnit-id : (t : A¹) → map¹ 𝑺 𝑺 (proj₁ (𝒾𝒹 {𝑨 = proj₁ 𝑺})) ⟨$⟩ t ≈¹ t
  adjoinUnit-id (just _) = ≈ˢ-refl
  adjoinUnit-id nothing  = tt

module _ (𝑺 𝑻 𝑼 : Semigroup α ρ) (f : hom (proj₁ 𝑺) (proj₁ 𝑻)) (g : hom (proj₁ 𝑻) (proj₁ 𝑼)) where
  open AdjoinUnit 𝑺 using () renaming ( A¹ to Aˢ; _≈¹_ to _≈ˢ_ )
  open AdjoinUnit 𝑼 using () renaming ( _≈¹_ to _≈ᵁ_ )
  open Setoid 𝔻[ proj₁ 𝑼 ] using () renaming ( refl to ≈ᵘ-refl )

  adjoinUnit-∘ : (t : Aˢ)
    → map¹ 𝑺 𝑼 (proj₁ (⊙-hom f g)) ⟨$⟩ t ≈ᵁ map¹ 𝑻 𝑼 (proj₁ g) ⟨$⟩ (map¹ 𝑺 𝑻 (proj₁ f) ⟨$⟩ t)
  adjoinUnit-∘ (just _) = ≈ᵘ-refl
  adjoinUnit-∘ nothing  = tt

adjoinUnitF : Functor (Semigroups α ρ) (Monoids α ρ)
adjoinUnitF = record
  { F₀            = adjoinUnit
  ; F₁            = λ {𝑺} {𝑻} → adjoinUnit-hom 𝑺 𝑻
  ; F-resp-≈      = λ {𝑺} {𝑻} {f} {g} → adjoinUnit-resp 𝑺 𝑻 {f} {g}
  ; identity      = λ {𝑺} → adjoinUnit-id 𝑺
  ; homomorphism  = λ {𝑺} {𝑻} {𝑼} {f} {g} → adjoinUnit-∘ 𝑺 𝑻 𝑼 f g
  }
```

#### The unit

The unit `η_𝑺 : 𝑺 ⟶ U (F 𝑺)` is the inclusion `just` of the semigroup into the
reduct of its free expansion.  It is a magma homomorphism: `just` turns a product of
old elements into the corresponding product in the expansion, up to the `Fin 2`
η-bridge on `𝑺`'s side (one `interp-cong`).

```agda
module _ (𝑺 : Semigroup α ρ) where
  private 𝑨 = proj₁ 𝑺
  open AdjoinUnit 𝑺 using (𝔻¹; A¹; 𝑨¹; _≈¹_)
  open Setoid 𝔻[ 𝑨 ] using () renaming ( refl to ≈refl )

  unit-map : Func 𝔻[ 𝑨 ] 𝔻¹
  unit-map ⟨$⟩ x = just x
  unit-map .cong x≈y = x≈y

  unit-compatible : (o : Op-Magma) (args : ArityOf Sig-Magma o → 𝕌[ 𝑨 ])
    → unit-map ⟨$⟩ ((o ^ 𝑨) args) ≈¹ (o ^ reduct magma↪monoid 𝑨¹) (λ i → unit-map ⟨$⟩ args i)
  unit-compatible ∙-Opᵐᵃ args = interp-cong 𝑨 ∙-Opᵐᵃ (λ { 0F → ≈refl ; 1F → ≈refl })

  unit-hom : hom 𝑨 (reduct magma↪monoid 𝑨¹)
  unit-hom = unit-map , record { compatible = λ {o} {args} → unit-compatible o args }
```

#### The universal property

`extend` is the adjoint transpose: a semigroup homomorphism `f : 𝑺 ⟶ U 𝑴` into the
reduct of a monoid extends to a monoid homomorphism `F 𝑺 ⟶ 𝑴`, sending an old
element `just x` to `f x` and the fresh unit to `𝑴`'s `ε`.  It extends `f` along the
unit (`extend-factors`), and it is the *unique* such homomorphism
(`extend-unique`): on old elements any candidate is pinned by the triangle, and on
the fresh unit by [`hom-preserves-ε`][Classical.Structures.Monoid].  The monoid laws
of `𝑴` enter exactly where they must: `idʳ` and `idˡ` discharge the cases of
`extend-∙` in which the fresh unit participates in a product.

```agda
module _ (𝑺 : Semigroup α ρ) (𝑴 : Monoid α ρ) (f : hom (proj₁ 𝑺) (proj₁ (monoid→semigroup 𝑴))) where
  private
    𝑨 = proj₁ 𝑺
    𝑩 = proj₁ 𝑴
  open AdjoinUnit 𝑺 using (𝔻¹; A¹; _∙¹_; 𝑨¹)
  open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᵇ_ ; refl to ≈ᵇ-refl ; sym to ≈ᵇ-sym ; trans to ≈ᵇ-trans )
  open Monoid-Op 𝑴 using ( ε ; idˡ-law ; idʳ-law ) renaming ( _∙_ to _∙ᵐ_ )

  extend-map : Func 𝔻¹ 𝔻[ 𝑩 ]
  extend-map ⟨$⟩ just x  = proj₁ f ⟨$⟩ x
  extend-map ⟨$⟩ nothing = ε
  extend-map .cong {just _} {just _}  x≈y = cong (proj₁ f) x≈y
  extend-map .cong {nothing} {nothing} _ = ≈ᵇ-refl
  -- Do we need the following cases?
  -- extend-map .cong {just _} {nothing} ()
  -- extend-map .cong {nothing} {just _}  ()

  -- Formal products in the expansion become real products in 𝑴;
  -- the unit laws of 𝑴 absorb the cases involving the fresh unit.
  extend-∙ : (s t : A¹)
    → extend-map ⟨$⟩ (s ∙¹ t) ≈ᵇ (extend-map ⟨$⟩ s) ∙ᵐ (extend-map ⟨$⟩ t)
  extend-∙ (just x) (just y) = hom-preserves-∙ f x y
  extend-∙ (just x) nothing = ≈ᵇ-sym (idʳ-law (proj₁ f ⟨$⟩ x))
  extend-∙ nothing t = ≈ᵇ-sym (idˡ-law (extend-map ⟨$⟩ t))

  extend-compatible : (o : Op-Monoid) (args : ArityOf Sig-Monoid o → A¹)
    → extend-map ⟨$⟩ ((o ^ 𝑨¹) args) ≈ᵇ (o ^ 𝑩) (λ i → extend-map ⟨$⟩ args i)
  extend-compatible ∙-Op args =
    ≈ᵇ-trans (extend-∙ (args 0F) (args 1F)) (interp-cong 𝑩 ∙-Op (λ { 0F → ≈ᵇ-refl ; 1F → ≈ᵇ-refl }))
  extend-compatible ε-Op args = interp-cong 𝑩 ε-Op (λ ())

  extend : hom 𝑨¹ 𝑩
  extend = extend-map , record { compatible = λ {o} {args} → extend-compatible o args }

  -- The triangle: U (extend) ∘ unit ≋ f, definitionally.
  extend-factors : (x : 𝕌[ 𝑨 ]) → extend-map ⟨$⟩ (unit-map 𝑺 ⟨$⟩ x) ≈ᵇ proj₁ f ⟨$⟩ x
  extend-factors _ = ≈ᵇ-refl

  -- Uniqueness: any monoid homomorphism g : F 𝑺 ⟶ 𝑴 that extends f along the
  -- unit agrees with extend everywhere.
  extend-unique : (g : hom 𝑨¹ 𝑩) → ((x : 𝕌[ 𝑨 ]) → proj₁ g ⟨$⟩ just x ≈ᵇ proj₁ f ⟨$⟩ x)
    → (t : A¹) → proj₁ g ⟨$⟩ t ≈ᵇ extend-map ⟨$⟩ t
  extend-unique g g-factors (just x) = g-factors x
  extend-unique g g-factors nothing = hom-preserves-ε g
```

#### The counit and the adjunction

The counit `ε_𝑴 : F (U 𝑴) ⟶ 𝑴` is the extension of the identity: it evaluates the
free expansion of `𝑴`'s underlying semigroup back into `𝑴`, collapsing the fresh
unit onto `𝑴`'s own `ε`.

```agda
counit-hom : (𝑴 : Monoid α ρ) → hom (AdjoinUnit.𝑨¹ (monoid→semigroup 𝑴)) (proj₁ 𝑴)
counit-hom 𝑴 = extend (monoid→semigroup 𝑴) 𝑴 𝒾𝒹
```

Naturality of the counit and the first triangle identity, pointwise on the `Maybe`
carrier.  On `just` everything is definitional; on `nothing` the counit square is
unit-preservation of the monoid homomorphism, and the `zig` triangle is the
definitional fact that the counit sends the fresh unit of `F (U (F 𝑺))` to the fresh
unit of `F 𝑺`.

```agda
module _ (𝑴 𝑵 : Monoid α ρ) (g : hom (proj₁ 𝑴) (proj₁ 𝑵)) where
  open AdjoinUnit (monoid→semigroup 𝑴) using (A¹)
  open Setoid 𝔻[ proj₁ 𝑵 ] using () renaming ( _≈_ to _≈ⁿ_ ; refl to ≈ⁿ-refl ; sym to ≈ⁿ-sym )

  counit-natural¹ : (t : A¹)
    → proj₁ (counit-hom 𝑵) ⟨$⟩ (map¹ (monoid→semigroup 𝑴) (monoid→semigroup 𝑵) (proj₁ g) ⟨$⟩ t)
      ≈ⁿ proj₁ g ⟨$⟩ (proj₁ (counit-hom 𝑴) ⟨$⟩ t)
  counit-natural¹ (just _) = ≈ⁿ-refl
  counit-natural¹ nothing  = ≈ⁿ-sym (hom-preserves-ε g)

module _ (𝑺 : Semigroup α ρ) where
  open AdjoinUnit 𝑺 using (A¹; _≈¹_)
  open Setoid 𝔻[ proj₁ 𝑺 ] using () renaming ( refl to ≈ˢ-refl )
  F𝑺 : Monoid α ρ
  F𝑺 = adjoinUnit 𝑺

  zig¹ : (t : A¹)
    → proj₁ (counit-hom F𝑺) ⟨$⟩ (map¹ 𝑺 (monoid→semigroup F𝑺) (unit-map 𝑺) ⟨$⟩ t) ≈¹ t
  zig¹ (just _) = ≈ˢ-refl
  zig¹ nothing  = tt
```

The adjunction.  The remaining fields are definitional: naturality of the unit (both
sides send `x` to `just (f x)`) and the `zag` triangle (the counit collapses
`just x` to `x` on the nose).

```agda
adjoinUnit⊣forgetUnit : Adjunction (adjoinUnitF {α} {ρ}) (forgetUnitF {α} {ρ})
adjoinUnit⊣forgetUnit = record
  { unit            = unit-hom
  ; counit          = counit-hom
  ; unit-natural    = λ {𝑺} {𝑻} f x → Setoid.refl 𝔻[ proj₁ 𝑻 ]
  ; counit-natural  = λ {𝑴} {𝑵} → counit-natural¹ 𝑴 𝑵
  ; zig             = zig¹
  ; zag             = λ 𝑴 x → Setoid.refl 𝔻[ proj₁ 𝑴 ]
  }
```

--------------------------------------

{% include UALib.Links.md %}
