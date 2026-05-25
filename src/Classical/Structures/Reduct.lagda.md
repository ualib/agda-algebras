---
layout: default
file: "src/Classical/Structures/Reduct.lagda.md"
title: "Classical.Structures.Reduct module"
date: "2026-05-23"
author: "the agda-algebras development team"
---

### <a id="classical-structures-reduct">Signature reducts along a container morphism</a>

This is the [Classical.Structures.Reduct][] module of the [Agda Universal Algebra Library][].

A *reduct* of an `𝑆₂`-algebra `𝑨` along a signature inclusion `𝑆₁ ↪ 𝑆₂` is the
`𝑆₁`-algebra with the same carrier whose operations are those of `𝑨` named by the
inclusion, interpreted exactly as in `𝑨`.  This is the first non-`proj₁` forgetful
projection in the hierarchy (per [ADR-002 v2 §5](../../docs/adr/002-classical-layer-design.md)):
`monoid→semigroup` and `group→monoid` are reducts (composed with an equation-reindex),
whereas `semigroup→magma`, `commutativeMonoid→monoid`, and `abelianGroup→group` are
`proj₁`.

We take the *container-morphism* form rather than an arity-equation form.  A signature
inclusion is a container morphism `(ι , κ)`: `ι` maps operation symbols of `𝑆₁` to
symbols of `𝑆₂` (covariantly), and `κ` maps the arity of `ι o` back to the arity of
`o` (contravariantly).  This induces the polynomial-functor natural transformation
`P_{𝑆₁} ⟹ P_{𝑆₂}`, and `reduct` is precomposition of the `𝑆₂`-structure map with it:
`Interp (reduct ι κ 𝑨) = Interp 𝑨 ∘ ⟨ι , κ⟩`.  Two payoffs over an
`ArityOf 𝑆₁ o ≡ ArityOf 𝑆₂ (ι o)` formulation: the interpretation is plain function
composition `args ∘ κ o` with no `subst`, keeping proof terms transport-free (and the
Cubical port mechanical); and for an arity-preserving inclusion `κ o` is `id`, so the
reduct preserves each retained symbol's interpretation *definitionally* — which is
exactly what discharges the downstream theory-reindex obligation cheaply.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓥 ; Signature )

module Classical.Structures.Reduct where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using ()             renaming ( Set to Type )
open import Data.Product    using ( _,_ )
open import Function        using ( _∘_ ; Func )
open import Level           using ( Level )
import Relation.Binary.PropositionalEquality as ≡

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures    using ( OperationSymbolsOf ; ArityOf )
open import Setoid.Algebras.Basic  using ( Algebra ; _^_ )

private variable
  α ρ 𝓞₁ 𝓞₂ : Level
```

#### <a id="the-reduct">The reduct of an algebra along a container morphism</a>

`reduct ι κ 𝑨` is the `𝑆₁`-algebra obtained from the `𝑆₂`-algebra `𝑨` by the
container morphism `(ι , κ)`.  The domain is unchanged; the interpretation of a
symbol `o` of `𝑆₁` is the interpretation of `ι o` in `𝑨`, with arguments reindexed
through `κ o`.  Both signatures are passed implicitly at the use site, recovered from
the types of `ι` and `κ`.

```agda
module _ {𝑆₁ : Signature 𝓞₁ 𝓥} {𝑆₂ : Signature 𝓞₂ 𝓥} where

  reduct :  (ι : OperationSymbolsOf 𝑆₁ → OperationSymbolsOf 𝑆₂)
            (κ : (o : OperationSymbolsOf 𝑆₁) → ArityOf 𝑆₂ (ι o) → ArityOf 𝑆₁ o)
         →  Algebra {𝑆 = 𝑆₂} α ρ → Algebra {𝑆 = 𝑆₁} α ρ
  reduct ι κ 𝑨 .Algebra.Domain                            = Algebra.Domain 𝑨
  reduct ι κ 𝑨 .Algebra.Interp ⟨$⟩ (o , args)             = (ι o ^ 𝑨) (args ∘ κ o)
  reduct ι κ 𝑨 .Algebra.Interp .cong {o , u} {.o , u'} (≡.refl , u≈v) =
    cong (Algebra.Interp 𝑨) (≡.refl , λ i → u≈v (κ o i))
```

--------------------------------------

{% include UALib.Links.md %}
