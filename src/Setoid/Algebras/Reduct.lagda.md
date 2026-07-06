---
layout: default
file: "src/Setoid/Algebras/Reduct.lagda.md"
title: "Setoid.Algebras.Reduct module"
date: "2026-05-23"
author: "the agda-algebras development team"
---

### Signature reducts along a signature morphism

This is the [Setoid.Algebras.Reduct][] module of the [Agda Universal Algebra Library][].

A *reduct* of an `𝑆₂`-algebra `𝑨` along a signature morphism `φ : 𝑆₁ → 𝑆₂` is the
`𝑆₁`-algebra with the same carrier whose operations are those of `𝑨` named by `φ`,
interpreted exactly as in `𝑨`.  Reduct is a construction of *general* universal algebra —
it acts on algebras over arbitrary signatures along an arbitrary signature morphism — so
its home is the `Setoid/` foundation, relocated here from `Classical/` by
[ADR-006](../../docs/adr/006-signature-morphism-category.md) (M4-16; see the Amendment).
Its principal *consumers*, however, are classical: it is the first non-`proj₁` forgetful
projection in the structure hierarchy (per
[ADR-002 v2](../../docs/adr/002-classical-layer-design.md) §5); `monoid→semigroup` and
`group→monoid` are reducts (composed with an equation-reindex), whereas `semigroup→magma`,
`commutativeMonoid→monoid`, and `abelianGroup→group` are `proj₁`.

We take the *container-morphism* form rather than an arity-equation form.  A signature
inclusion is a [`SigMorphism`][Overture.Signatures.Morphisms] `(ι , κ)`: `ι` maps operation
symbols of `𝑆₁` to symbols of `𝑆₂` (covariantly), and `κ` maps the arity of `ι o` back to
the arity of `o` (contravariantly).  This induces the polynomial-functor natural
transformation `P_{𝑆₁} ⟹ P_{𝑆₂}`, and `reduct φ` precomposes the `𝑆₂`-structure map with
it.  Two payoffs over an `ArityOf 𝑆₁ o ≡ ArityOf 𝑆₂ (ι o)` formulation:
1. the interpretation is plain function composition `args ∘ κ φ o` with no `subst`,
   keeping proof terms transport-free (and the Cubical port mechanical);
2. for an arity-preserving inclusion `κ φ o` is `id`, so the reduct preserves each
   retained symbol's interpretation *definitionally*, which is what discharges the
   downstream theory-reindex obligation cheaply.

The container morphism is packaged as follows: `reduct` consumes a `SigMorphism`,
with `reductBy` retaining the two-argument form as a thin wrapper.  Packaging
makes `reduct` a (contravariant) functor — `reduct-id` and `reduct-∘` below state
identity- and composition-preservation, both holding by `refl`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Algebras.Reduct where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Product                          using ( _,_ )
open import Function                              using ( _∘_ ; _∘₂_ ; Func )
open import Level                                 using ( Level )
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using  ( OperationSymbolsOf ; ArityOf )
open import Overture.Signatures.Morphisms  using  ( SigMorphism ; mkSigMorphism
                                                  ; ι ; κ ; id-morphism ; _∘ₛ_ )
open import Setoid.Algebras.Basic          using  ( Algebra ; _^_ ; 𝕌[_] )
private variable
  α ρ : Level
  𝑆 𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥
```
-->

#### The reduct of an algebra along a signature morphism

`reduct φ 𝑨` is the `𝑆₁`-algebra obtained from the `𝑆₂`-algebra `𝑨` by the signature
morphism `φ : SigMorphism 𝑆₁ 𝑆₂`.  The domain is unchanged; the interpretation of a symbol
`o` of `𝑆₁` is the interpretation of `ι φ o` in `𝑨`, with arguments reindexed through
`κ φ o`.  Both signatures are passed implicitly at the use site, recovered from the type of
`φ`.

```agda
reduct : SigMorphism 𝑆₁ 𝑆₂ → Algebra {𝑆 = 𝑆₂} α ρ → Algebra {𝑆 = 𝑆₁} α ρ
reduct φ 𝑨 .Algebra.Domain = Algebra.Domain 𝑨
reduct φ 𝑨 .Algebra.Interp ⟨$⟩ (o , args) = (ι φ o ^ 𝑨) (args ∘ κ φ o)
reduct φ 𝑨 .Algebra.Interp .cong {o , u} {.o , u'} (refl , u≈v) =
  cong (Algebra.Interp 𝑨) (refl , λ i → u≈v (κ φ o i))
```

The two-argument form is retained as a thin wrapper, so a call site that already holds `ι`
and `κ` separately need not assemble the record by hand.

```agda
reductBy : {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥}
  (ι : OperationSymbolsOf 𝑆₁ → OperationSymbolsOf 𝑆₂)
  (κ : (o : OperationSymbolsOf 𝑆₁) → ArityOf 𝑆₂ (ι o) → ArityOf 𝑆₁ o)
  → Algebra {𝑆 = 𝑆₂} α ρ → Algebra {𝑆 = 𝑆₁} α ρ
reductBy = reduct ∘₂ mkSigMorphism
```

#### Functoriality

`reduct` is functorial in the signature morphism, contravariantly: it preserves the identity
and turns a composite into the *reversed* composite of reducts.  Following the strict-first
discipline, each law is stated at the level of an operation's *interpretation function*
(`o ^ reduct … ≡ o ^ …`, with no argument tuple applied) and holds by `refl`; the conventional
`args`-applied functoriality statement is the corollary directly below each (also `refl` — it
is the strict law specialized to an argument tuple).  This is the strongest equality `--safe`
affords short of equating the *algebras* themselves, which would need funext for the
`Interp.cong` field.

```agda
reduct-id : {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {o : OperationSymbolsOf 𝑆}
  → o ^ reduct id-morphism 𝑨 ≡ o ^ 𝑨
reduct-id = refl

reduct-id-ptw : {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {o : OperationSymbolsOf 𝑆}
  (args : ArityOf 𝑆 o → 𝕌[ 𝑨 ]) → (o ^ reduct id-morphism 𝑨) args ≡ (o ^ 𝑨) args
reduct-id-ptw _ = refl

reduct-∘ : {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥}
  {φ : SigMorphism 𝑆₁ 𝑆₂} {ψ : SigMorphism 𝑆₂ 𝑆₃}
  {𝑨 : Algebra {𝑆 = 𝑆₃} α ρ} {o : OperationSymbolsOf 𝑆₁}
  → o ^ reduct (ψ ∘ₛ φ) 𝑨 ≡ o ^ reduct φ (reduct ψ 𝑨)
reduct-∘ = refl

reduct-∘-ptw : {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥}
  {φ : SigMorphism 𝑆₁ 𝑆₂} {ψ : SigMorphism 𝑆₂ 𝑆₃}
  {𝑨 : Algebra {𝑆 = 𝑆₃} α ρ} {o : OperationSymbolsOf 𝑆₁}
  (args : ArityOf 𝑆₁ o → 𝕌[ 𝑨 ])
  → (o ^ reduct (ψ ∘ₛ φ) 𝑨) args ≡ (o ^ reduct φ (reduct ψ 𝑨)) args
reduct-∘-ptw _ = refl
```
