---
layout: default
title : "Overture.Relations module (The Agda Universal Algebra Library)"
date : "2026-05-07"
author: "the agda-algebras development team"
---

## Foundational relation infrastructure

This is the [Overture.Relations][] module of the [Agda Universal Algebra Library][].

This module collects the foundational definitions concerning binary relations on a type that are needed by both the canonical `Setoid/` tree and the planned `Classical/` tree.  Every definition in this module takes its arguments at the level of bare types and `BinRel`; none presupposes a setoid structure.  The Setoid-flavoured analogues — relations between setoid functions, kernels of setoid morphisms, etc. — live in `Setoid.Relations.*` and are built on top of, rather than parallel to, what is collected here.

The contents fall into four clusters.

+  **`Equivalence`**.  A Σ-bundle of a binary relation with a proof that it is an equivalence relation.  The setoid `_/_` quotient construction in `Setoid.Relations.Quotients` consumes this.
+  **Kernels and identity**.  `kerRel`, `kerRelOfEquiv`, `kernelRel`, and the trivial relation `0[_]`.  Used pervasively in `Setoid.Homomorphisms.{Factor,Kernels}` and `Setoid.Congruences`.
+  **Image-containment**.  `Im_⊆_`, the predicate that the image of a tuple lies inside a given subset.  Used in `Setoid.Subalgebras.Subuniverses` for the ar-tuple of an operation, which is a *raw* function from an arity type to the algebra's carrier — not a setoid function — so the bare-types version is what's needed at the call site.
+  **Compatibility**.  `_|:_` (and its long form `_preserves_`), expressing that an `Op I A` is compatible with a `BinRel A ρ`.  Used in `Setoid.Congruences._∣≈_` even on setoid algebras, since congruences of a setoid algebra are bare-types relations on its carrier that contain the setoid's `_≈_`.
+  **Pointwise lifting**.  `PointWise` and `depPointWise`, lifting a binary relation on a codomain (or a family of relations on a dependent codomain) to the function space.  Generalizes stdlib's `_≗_` (which fixes the codomain relation to `_≡_`).  Used in `Overture.Adjunction.Residuation` to express that the composite `g ∘ f ∘ g` agrees pointwise with `g`.

This module is a Category-A relocation under #303 (M2-6).  See [`src/Legacy/Base/DEPRECATED.md`](../Legacy/Base/DEPRECATED.md) for the full inventory and migration guidance.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Relations where

-- Imports from Agda primitives and the standard library.
open import Agda.Primitive   using ()           renaming ( Set to Type )
open import Data.Product     using ( _×_ ; _,_ ; Σ-syntax )
open import Function         using ( _∘_ )
open import Level            using ( Level ; Lift ; lift ; lower ; suc ; _⊔_ )
open import Relation.Binary  using ( IsEquivalence ; _=[_]⇒_ )
                             renaming ( Rel to BinRel )
open import Relation.Unary   using ( Pred ; _∈_ )

open import Relation.Binary.PropositionalEquality as ≡  using ( _≡_ )

-- Imports from agda-algebras.
open import Overture.Signatures  using ( 𝓞 ; 𝓥 )
open import Overture.Operations  using ( Op )

private variable
 a b ρ ℓ : Level
 𝓦 : Level   -- arity-tuple level, conventional name elsewhere in the library
```

### The `Equivalence` Σ-bundle

`Equivalence A {ρ}` packages a binary relation on `A` with a proof that the relation is an equivalence.  Compared to stdlib's `Relation.Binary.Bundles.Setoid`, which bundles a `Carrier` *and* an `_≈_` *and* an `IsEquivalence`, `Equivalence` fixes the carrier as a parameter and bundles only the relation with its proof — useful when one wants to vary the equivalence relation over a fixed carrier (the situation in quotient and congruence constructions).

```agda
Equivalence : Type a → {ρ : Level} → Type (a ⊔ suc ρ)
Equivalence A {ρ} = Σ[ r ∈ BinRel A ρ ] IsEquivalence r
```

Given `R : Equivalence A`, we use `(proj₁ R)` for the underlying relation and `(proj₂ R)` for the equivalence-relation proof, following the library convention.

### Equivalence classes

If `R` is a binary relation on `A`, the *`R`-block containing* `u : A` is the predicate that holds at `v` precisely when `R u v`.  The notation `[ u ] R` is shorthand for that predicate.

```agda
[_] : {A : Type a} → A → {ρ : Level} → BinRel A ρ → Pred A ρ
[ u ] R = R u

infix 60 [_]
```

### The identity relation

The *identity* (or *zero*) relation on `A` is `λ x y → Lift ρ (x ≡ y)`.  The `Lift` is there so that the relation's universe level can be parametrized independently of the carrier's level — useful when the relation has to live at a level dictated by surrounding context (e.g., congruence relations on an algebra at level `α ⊔ suc ρ`).

```agda
0[_]₌ : (A : Type a) → {ρ : Level} → BinRel A (a ⊔ ρ)
0[ A ]₌ {ρ} = λ x y → Lift ρ (x ≡ y)
```

```agda
0[_] : (A : Type a) → {ρ : Level} → BinRel A ρ → BinRel A (a ⊔ ρ)
0[_]{a} A {ρ} _≈_ = λ x y → Lift a (x ≈ y)
```

The identity relation is, of course, an equivalence relation; we package its `IsEquivalence` proof and the corresponding `Equivalence` bundle for convenience.

```agda
0[_]₌IsEquivalence : (A : Type a){ρ : Level} → IsEquivalence (0[ A ]₌ {ρ})
0[ A ]₌IsEquivalence {ρ} = record  { refl   = lift ≡.refl
                                  ; sym    = λ p   → lift (≡.sym (lower p))
                                  ; trans  = λ p q → lift (≡.trans (lower p) (lower q))
                                  }

0[_]IsEquivalence : (A : Type a){ρ : Level}{_≈_ : BinRel A ρ} → (IsEquivalence _≈_) → IsEquivalence (0[ A ] {ρ} _≈_)
0[ A ]IsEquivalence {ρ}{_≈_} eqv =
  record  { refl   = λ {x} → lift eqv-refl
          ; sym    = λ {x} {y} z → lift (eqv-sym (z .lower))
          ; trans  = λ {i} {j} {k} w z → lift (eqv-trans (w .lower) (z .lower))
          }
    where open IsEquivalence eqv renaming (refl to eqv-refl ; sym to eqv-sym ; trans to eqv-trans )


0[_]₌Equivalence : (A : Type a){ρ : Level} → Equivalence A {a ⊔ ρ}
0[ A ]₌Equivalence {ρ} = 0[ A ]₌ {ρ} , 0[ A ]₌IsEquivalence
```

### Kernels of raw functions

The *kernel* of `f : A → B` is the equivalence relation on `A` whose blocks are the fibres of `f`.  We give three formulations corresponding to three idiomatic uses elsewhere in the library: `kerRel` parametrizes the codomain equivalence (used when `B` has its own equivalence relation that the kernel should reflect, e.g. the carrier of a setoid algebra); `kernelRel` repackages the same content as a predicate on pairs (more convenient for some `Pred`-based constructions); and `kerRelOfEquiv` lifts an `IsEquivalence` proof on the codomain to one on the kernel.

```agda
module _ {A : Type a}{B : Type b} where

 kerRel : {ρ : Level} → BinRel B ρ → (A → B) → BinRel A ρ
 kerRel _≈_ g x y = g x ≈ g y

 kernelRel : {ρ : Level} → BinRel B ρ → (A → B) → Pred (A × A) ρ
 kernelRel _≈_ g (x , y) = g x ≈ g y

 open IsEquivalence

 kerRelOfEquiv :  {ρ : Level}{R : BinRel B ρ}
  →               IsEquivalence R → (h : A → B) → IsEquivalence (kerRel R h)

 kerRelOfEquiv eqR h = record  { refl   = refl   eqR
                               ; sym    = sym    eqR
                               ; trans  = trans  eqR
                               }
```

### Image-containment of a tuple

If `a : I → A` is a tuple of `A`-values indexed by `I`, and `B` is a subset of `A`, then `Im a ⊆ B` asserts that every component of the tuple lies in `B`.  This is the bare-types form of image-containment, in which `a` is a raw function rather than a setoid morphism.

```agda
Im_⊆_ : {A : Type a}{I : Type 𝓦}{ℓ : Level}
 →      (I → A) → Pred A ℓ → Type (𝓦 ⊔ ℓ)
Im a ⊆ B = ∀ i → a i ∈ B
```

A setoid analogue of `Im_⊆_`, taking a setoid function rather than a raw function, is given separately in `Setoid.Relations.Discrete`.  The two coexist because they have genuinely different type signatures and serve genuinely different call sites.


### Pointwise lifting of a binary relation

If `_≋_` is a binary relation on `B`, the *pointwise lift* of `_≋_` to the function space `A → B` holds at `f, g : A → B` precisely when `∀ x → f x ≋ g x`.  This construction is foundational across the library: it is the equality used in `Overture.Adjunction.Residuation` to express that the composite `g ∘ f ∘ g` agrees pointwise with `g`, and is the natural generalization of stdlib's `_≗_` (which fixes `_≋_ = _≡_`) to an arbitrary equivalence on the codomain.

```agda
module _ {A : Type a} where

 PointWise : {B : Type b} (_≋_ : BinRel B ρ) → BinRel (A → B) _
 PointWise {B = B} _≋_ = λ (f g : A → B) → ∀ x → f x ≋ g x
```

The dependent analogue lifts `_≋_` over a family `B : A → Type b`.

Here `_≋_` is a *family* of relations; for each index `x : A`, an instance `_≋_ {x}` is a binary relation on the fiber `B x`.  This is the standard dependent generalization — the relations on distinct fibers may be unrelated — and is what makes the lift usable with fiber-specific relations rather than restricting to relations uniform across types.

```agda
 depPointWise :  {B : A → Type b}
                 (_≋_ : ∀ {x} → BinRel (B x) ρ)
  →              BinRel ((a : A) → B a) _
 depPointWise {B = B} _≋_ = λ (f g : (a : A) → B a) → ∀ x → f x ≋ g x
```


### Compatibility of operations with relations

If `f : Op I A` is an `I`-ary operation on `A` and `R` is a binary relation on `A`, we say that `f` and `R` are *compatible* (equivalently, that `f` *preserves* `R`) when, for all tuples `u v : I → A`, the pointwise hypothesis `∀ i → R (u i) (v i)` implies `R (f u) (f v)`.  We provide both a long-form name `_preserves_` and the customary infix shorthand `_|:_`.

The lifting of a binary relation to the corresponding `I`-ary pointwise relation is itself useful and worth naming; we call it `eval-rel`.  A predicate-of-pairs counterpart `eval-pred` is provided for symmetry with `kernelRel`.

```agda
-- Lift a binary relation to the corresponding I-ary pointwise relation.
eval-rel : {A : Type a}{I : Type 𝓦} → BinRel A ρ → BinRel (I → A) (𝓦 ⊔ ρ)
eval-rel R u v = ∀ i → R (u i) (v i)

eval-pred : {A : Type a}{I : Type 𝓦} → Pred (A × A) ρ → BinRel (I → A) (𝓦 ⊔ ρ)
eval-pred P u v = ∀ i → (u i , v i) ∈ P

module _ {A : Type a}{I : Type 𝓦} where

 _preserves_ : Op I A → BinRel A ρ → Type (a ⊔ 𝓦 ⊔ ρ)
 f preserves R = ∀ u v → (eval-rel R) u v → R (f u) (f v)

 -- Infix shorthand for `preserves`.
 _|:_ : Op I A → BinRel A ρ → Type (a ⊔ 𝓦 ⊔ ρ)
 f |: R = (eval-rel R) =[ f ]⇒ R
```

The two formulations are logically equivalent.  The shorthand `_|:_` is what the Setoid tree uses pervasively; the long-form `_preserves_` is provided for prose-readability at consumption sites where the brevity of `|:` is more cryptic than helpful.

```agda
module _ {A : Type a}{I : Type 𝓦}{f : Op I A}{R : BinRel A ρ} where

 preserves→|: : f preserves R → f |: R
 preserves→|: c {u}{v} Ruv = c u v Ruv

 |:→preserves : f |: R → f preserves R
 |:→preserves c = λ u v Ruv → c Ruv
```

--------------------------------------

<span style="float:left;">[← Overture.Operations](Overture.Operations.html)</span>
<span style="float:right;">[Overture.Functions →](Overture.Functions.html)</span>

{% include UALib.Links.md %}
