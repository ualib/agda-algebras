---
layout: default
file: "src/Classical/Equations.lagda.md"
title: "Classical.Equations module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### Equations of Classical Structures

This is the [Classical.Equations][] module of the [Agda Universal Algebra Library][].
It is the syntactic dual of the standard library's `Algebra.Definitions` module.

The standard library's
[`Algebra.Definitions`](https://agda.github.io/agda-stdlib/v2.3/Algebra.Definitions.html)
provides a uniform inventory of equation predicates at the *evaluated* level.

For example, given a carrier `A`, an equivalence `_≈_`, and an operation,
`Associative _≈_ _∙_` is the type `∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)`.  This is
what stdlib's `IsSemigroup.assoc` returns and what users prove for concrete algebras.

This module is the *syntactic* dual; given a signature `𝑆` and operation
symbols within it (with arity proofs), `Associative ∙-Op refl` returns a function
from three variables to a *pair of `Sig-𝑆`-terms* — the LHS `(ℊ x ∙ ℊ y) ∙ ℊ z` and
the RHS `ℊ x ∙ (ℊ y ∙ ℊ z)`.  This is what `Th-X : Eq-X → Term (Fin n) × Term (Fin n)`
is built from, and is what feeds the equational-logic core (`Modᵗ`) for every
concrete theory under `Classical/Theories/`.

Both views are needed; neither subsumes the other.  `Algebra.Definitions` is what you
prove a *specific algebra* satisfies; `Classical.Equations` is what you state
*as part of a variety's defining theory*, before any algebra is in the picture.
The distinction is the same as the distinction between an equation
`(x · y) · z = x · (y · z)` as a *formula* (a string of symbols) versus the same
equation as a *proposition* about a particular algebraic structure (a thing that can
be proved).

The universal-algebra meta-theory operates on the formula view; the user proving
things about a specific algebra operates on the proposition view.  The relationship
between the two is mediated by interpretation: `Modᵗ Th-X 𝑨` says "for every equation
`(s, t)` in `Th-X`, the formula `s ≈ t` interpreted in 𝑨 holds for all environments."

The motivation for distinguishing the two views formally — beyond cleanliness — comes
from results like Bryant's *The laws of finite pointed groups*
(Bull. LMS 14 (1982), 119–123), which is a stark illustration of the fact that the
equational theory of a structure can depend substantively on the signature it lives
over, not just on the carrier and operations.  A formal account of equations as
syntactic objects, distinct from their evaluations in particular algebras, is what
makes that distinction expressible.

See [ADR-002 v2 §3](../../docs/adr/002-classical-layer-design.md) for more details about
the design rationale.

*Note for per-structure-theory authors*.  The arity-conformance evidence `refl`
typechecks only when the signature's arity function reduces definitionally to
`Fin n` on the operation symbol in question.  Define arity functions by direct
pattern matching on operation-symbol constructors (`ar-X ∙-Op = Fin 2`); avoid
indirect definitions (table lookups, conditionals) that would leave the arity opaque
to the type checker.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Equations where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Agda.Primitive renaming ( Set to Type )  using ()
open import Data.Fin.Base                            using ( Fin )
open import Data.Fin.Patterns                        using ( 0F ; 1F )
open import Data.Product                             using ( _×_ ; _,_ )
open import Level                                    using ( Level ; 0ℓ)
open import Relation.Binary.PropositionalEquality    using ( _≡_ ; refl ; sym ; subst )

-- Imports from agda-algebras -----------------------------------------------------
open import Classical.Operations  using ( pair )
open import Overture.Signatures   using ( Signature ; OperationSymbolsOf ; ArityOf )

private variable
  𝓞 χ : Level
```

The equation-builder API is parameterized over a fixed signature `𝑆`.  Each builder
takes operation symbols from `𝑆` together with evidence that the symbols' arities
match the equation's shape; given that, the builder returns a function from
however-many-variables-the-equation-needs to a pair of terms over the signature.

<!--
```agda
module _ {𝑆 : Signature 𝓞 0ℓ} {X : Type χ} where
  open import Overture.Terms {𝑆 = 𝑆} using ( Term ; ℊ ; node )
  -- Apply an operation symbol of known arity to its term arguments.  Each helper
  -- takes the symbol and the arity-conformance evidence; `subst` is what bridges
  -- the abstract `ArityOf 𝑆 f` (an opaque type that depends on the abstract
  -- signature) to the concrete `Fin n` the term-building code wants to use.  At
  -- a call site with concrete signature, `ArityOf 𝑆 f` reduces to `Fin n`,
  -- the arity-conformance becomes `refl`, and `subst P refl` is definitionally
  -- the identity — so the helpers carry no runtime overhead at use sites.


  -- The following helpers are public in case users want to defining custom equation
  -- builders downstream; use of standard identities defined below is preferred.
  app₀ : {e : OperationSymbolsOf 𝑆} → ArityOf 𝑆 e ≡ Fin 0 → Term X
  app₀ {e} e-nul = node e (subst (λ I → I → Term X) (sym e-nul) λ ())

  app₁ : {i : OperationSymbolsOf 𝑆} → ArityOf 𝑆 i ≡ Fin 1 → Term X → Term X
  app₁ {i} i-un s = node i (subst (λ I → I → Term X) (sym i-un) (λ _ → s))

  app₂ : {f : OperationSymbolsOf 𝑆} → ArityOf 𝑆 f ≡ Fin 2 → Term X → Term X → Term X
  app₂ {f} f-bin s t = node f (subst (λ I → I → Term X) (sym f-bin) (pair s t))
```
-->

#### Associative, Commutative, and Idempotent Laws

```agda
  -- f (f x y) z ≈ f x (f y z)
  Associative : (f : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 f ≡ Fin 2 → X → X → X → Term X × Term X
  Associative _ f-bin x y z =
    app₂ f-bin (app₂ f-bin (ℊ x) (ℊ y)) (ℊ z)
    , app₂ f-bin (ℊ x) (app₂ f-bin (ℊ y) (ℊ z))

  -- f x y ≈ f y x
  Commutative : (f : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 f ≡ Fin 2 → X → X → Term X × Term X

  Commutative _ f-bin x y = app₂ f-bin (ℊ x) (ℊ y) , app₂ f-bin (ℊ y) (ℊ x)

  -- f x x ≈ x
  Idempotent : (f : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 f ≡ Fin 2 → X → Term X × Term X
  Idempotent _ f-bin x = app₂ f-bin (ℊ x) (ℊ x) , ℊ x
```

#### <a id="identity-laws">Identity laws</a>

These take a binary operation `f` together with a nullary "identity element" symbol
`e`.  The arity-conformance evidence for `e` is `ArityOf e ≡ Fin 0`, consistent with
the `Op (Fin 0) A` representation of nullary operations in
[`Classical.Operations`][Classical.Operations].

```agda
  -- f e x ≈ x
  LeftIdentity :  (f e : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 f ≡ Fin 2 → ArityOf 𝑆 e ≡ Fin 0
    → X → Term X × Term X
  LeftIdentity _ _ f-bin e-nul x = app₂ f-bin (app₀ e-nul) (ℊ x) , ℊ x

  -- f x e ≈ x
  RightIdentity : (f e : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 f ≡ Fin 2 → ArityOf 𝑆 e ≡ Fin 0
    → X → Term X × Term X
  RightIdentity _ _ f-bin e-nul x = app₂ f-bin (ℊ x) (app₀ e-nul) , ℊ x
```

#### <a id="inverse-laws">Inverse laws</a>

These take a binary `f`, a nullary identity `e`, and a unary inverse `i`.  The arity
evidence for `i` is `ArityOf i ≡ Fin 1`.

```agda
  -- f (i x) x ≈ e
  LeftInverse : (f i e : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 f ≡ Fin 2 → ArityOf 𝑆 i ≡ Fin 1 → ArityOf 𝑆 e ≡ Fin 0
    → X → Term X × Term X
  LeftInverse _ _ _ f-bin i-un e-nul x =
    app₂ f-bin (app₁ i-un (ℊ x)) (ℊ x) , app₀ e-nul

  -- f x (i x) ≈ e
  RightInverse : (f i e : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 f ≡ Fin 2 → ArityOf 𝑆 i ≡ Fin 1 → ArityOf 𝑆 e ≡ Fin 0
    → X → Term X × Term X
  RightInverse _ _ _ f-bin i-un e-nul x =
    app₂ f-bin (ℊ x) (app₁ i-un (ℊ x)) , app₀ e-nul
```

#### <a id="distributive-laws">Distributive laws</a>

```agda
  -- x · (y + z) ≈ (x · y) + (x · z)
  DistributesOverˡ : (· + : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 · ≡ Fin 2 → ArityOf 𝑆 + ≡ Fin 2
    → X → X → X → Term X × Term X
  DistributesOverˡ _ _ ·-bin +-bin x y z =
      app₂ ·-bin (ℊ x) (app₂ +-bin (ℊ y) (ℊ z))
    , app₂ +-bin (app₂ ·-bin (ℊ x) (ℊ y)) (app₂ ·-bin (ℊ x) (ℊ z))

  -- (y + z) · x ≈ (y · x) + (z · x)
  DistributesOverʳ : (· + : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 · ≡ Fin 2 → ArityOf 𝑆 + ≡ Fin 2
    → X → X → X → Term X × Term X
  DistributesOverʳ _ _ ·-bin +-bin x y z =
      app₂ ·-bin (app₂ +-bin (ℊ y) (ℊ z)) (ℊ x)
    , app₂ +-bin (app₂ ·-bin (ℊ y) (ℊ x)) (app₂ ·-bin (ℊ z) (ℊ x))

```

#### <a id="absorption-laws">Absorption laws</a>

These take two binary operations `f` and `g`; each builder expresses one
direction of the absorption between them.  In a lattice, `f` and `g` are
typically `∧` and `∨`, and both directions appear in the theory.

```agda
  -- x ∨ (x ∧ y) ≈ x
  AbsorbsLeft : (∨ ∧ : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 ∨ ≡ Fin 2 → ArityOf 𝑆 ∧ ≡ Fin 2
    → X → X → Term X × Term X
  AbsorbsLeft _ _ ∨-bin ∧-bin x y =
    app₂ ∨-bin (ℊ x) (app₂ ∧-bin (ℊ x) (ℊ y)) , ℊ x

  -- (x ∨ y) ∧ x ≈ x
  AbsorbsRight : (∨ ∧ : OperationSymbolsOf 𝑆)
    → ArityOf 𝑆 ∨ ≡ Fin 2 → ArityOf 𝑆 ∧ ≡ Fin 2
    → X → X → Term X × Term X
  AbsorbsRight _ _ ∨-bin ∧-bin x y =
    app₂ ∧-bin (app₂ ∨-bin (ℊ x) (ℊ y)) (ℊ x) , ℊ x
```

In `Th-Lattice`, both `AbsorbsLeft ∧-Op ∨-Op refl refl` and `AbsorbsRight
...` appear as separate entries in `Eq-Lattice`.

This inventory covers every equation in `Th-Magma` (none), `Th-Semigroup`
(associativity), `Th-Monoid` (associativity, left/right identity), `Th-Group` (the
monoid equations + left/right inverse), `Th-CommutativeMonoid` (monoid +
commutativity), `Th-Semilattice` (associativity + commutativity + idempotency),
`Th-Lattice` (two associative + two commutative + two idempotent + two absorption),
`Th-Semiring` and `Th-Ring` (the additive and multiplicative components + the two
distributivity laws + ring-specific identities).  Builders for less-uniform equations
(the medial law, semigroup-with-identity-element-of-arity-two, etc.) are added
per-need.

--------------------------------------

<span style="float:left;">[← Classical.Operations](Classical.Operations.html)</span>
<span style="float:right;">[Classical.Signatures →](Classical.Signatures.html)</span>

{% include UALib.Links.md %}
```
