---
layout: default
title : "Setoid.Algebras.Basic module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---

#### Basic definitions

This is the [Setoid.Algebras.Basic][] module of the [Agda Universal Algebra Library][].

An **algebra over a signature** `𝑆`{.AgdaGeneralizable} is a setoid (i.e., a carrier
type together with an equivalence relation on it) equipped with an interpretation
of every operation symbol of `𝑆`{.AgdaGeneralizable} as a function on that carrier
which *respects* the equivalence.

That last clause is the entire difference from the type-based development: on a
setoid an operation is not a bare function but a `Func`{.AgdaRecord}, that is, a
function bundled with a proof that it sends related arguments to related results.
Carrying the proof inside the structure yields quotients: a quotient algebra is
the *same* carrier under a coarser equivalence, so forming one needs neither
quotient types nor an axiom.  That matters here, because the library is
`--safe --cubical-compatible`, where function extensionality is unavailable; see
the discussion at `mkAlgebra`{.AgdaFunction} below for where the cost reappears.

This module is the canonical entry point for the `Setoid/` tree.  It defines the
`Algebra`{.AgdaRecord} record, two smart constructors for building one from an
ordinary interpretation function, the operation-interpretation operator
`_^_`{.AgdaFunction}, and the universe-lifting operations that let algebras at
different levels be compared and related.

Modules most closely related to this one are the following:

+  [Setoid.Algebras.Products][]: indexed products;
+  [Setoid.Algebras.Finite][]: finite algebras;
+  [Setoid.Algebras.Reduct][]: reducts (to a smaller signature);
+  [Setoid.Congruences.Basic][]: congruences and the quotients they generate;
+  [Setoid.Homomorphisms.Basic][]: structure-preserving maps between algebras.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Algebras.Basic where

-- Imports from the Agda and the Agda Standard Library --------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ) public
open import Function         using ( _∘_ ; _∘₂_ ; Func ; _$_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------
open import Overture             using ( OperationSymbolsOf ; ArityOf ; 𝓞 ; 𝓥 ; Signature ; 𝑆 )
open import Overture.Operations  using ( Op )
open import Setoid.Signatures    using ( ⟨_⟩ )

private variable α ρ ι : Level
```
-->

`ov`{.AgdaFunction} abbreviates the recurring level join `ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α`;
it combines the levels of operation symbols and arities with the successor of a
caller-supplied level.  Abbreviating this join keeps many common level expressions
readable.

```agda
ov : {𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Level → Level
ov {𝓞 = 𝓞}{𝓥 = 𝓥} α = 𝓞 ⊔ 𝓥 ⊔ lsuc α
```

Other modules combine this shorthand with whatever carrier, equality, class, and
index levels their definitions quantify over.  For example,
[Setoid.Algebras.Products][] accepts `𝒦 : Pred (Algebra α ρ) (ov α)` and places
the type of pairs `(𝑨 , 𝑨 ∈ 𝒦)` at `ov (α ⊔ ρ)`, which is also the carrier level
of `class-product`{.AgdaFunction}; the signatures of `H`, `S`, and `P` in
[Setoid.Varieties.Closure][] add the corresponding equality, class, and index
levels explicitly.

The `Term`{.AgdaDatatype} type over `X : Type χ` is defined at `Type (ov χ)`
because the term construction needs the levels of the operation symbols and
arities, plus one more level for the carrier of the term itself.[^1]


#### Setoid Algebras

Here we define algebras over a setoid, instead of a mere type with no equivalence on it.

```agda
open Func renaming ( to to _⟨$⟩_ ; cong to ≈cong )
```

The `Algebra`{.AgdaRecord} defines a **setoid algebra**, which is just like an
ordinary algebra but we require that all of its basic operations respect the
underlying setoid equality.  The `Func` record packs a function (`f`, aka apply,
aka `_⟨$⟩_`) with a proof (cong) that the function respects equality.

```agda
record Algebra {𝑆 : Signature 𝓞 𝓥} α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
  field
    Domain : Setoid α ρ
    Interp : Func (⟨ 𝑆 ⟩ Domain) Domain
    --      ^^^^^^^^^^^^^^^^^^^^^^^ is a record type with two fields:
    --       1. a function  f : Carrier (⟨ 𝑆 ⟩ Domain)  → Carrier Domain
    --       2. a proof cong : f Preserves _≈₁_ ⟶ _≈₂_ (that f preserves the setoid equalities)

  open Setoid Domain using ( _≈_ )
  -- Actually, we already have the following: (it's called "reflexive"; see Structures.IsEquivalence)
  ≡→≈ : ∀{x}{y} → x ≡ y → x ≈ y
  ≡→≈ refl = Setoid.refl Domain

open Algebra
```

The operator `⟨_⟩`{.AgdaFunction} translates an ordinary signature into a
signature over a setoid domain, together with its companion
`EqArgs`{.AgdaFunction}; it is defined in the signature-generic module
[Setoid.Signatures][].[^2]

`𝔻[_]`{.AgdaFunction} is the **domain of an algebra**, which is the setoid
underlying it.  In other words, the domain is the carrier and equivalence of the
algebra, taken together.  It is the projection to reach for whenever the equality
matters.

```agda
𝔻[_] : Algebra {𝑆 = 𝑆} α ρ →  Setoid α ρ
𝔻[ 𝑨 ] = Domain 𝑨
```

`𝕌[_]`{.AgdaFunction} forgets one step further, to the bare carrier type.
Mathematically it is the underlying-set functor from algebras to sets, minus the
equality: `𝕌[ 𝑨 ]` is inhabited by the elements of `𝑨`{.AgdaGeneralizable} and
carries no notion of equality of its elements.

```agda
-- Forgetful functor: returns the carrier of (the domain of) 𝑨, forgetting its structure.
𝕌[_] : Algebra {𝑆 = 𝑆} α ρ →  Type α
𝕌[ 𝑨 ] = Setoid.Carrier 𝔻[ 𝑨 ]
```

We use the ascii symbol `^` to define an infix function for operation-symbol
interpretation in an algebra.[^3]

```agda
-- Interpretation of an operation symbol in an algebra.
_^_ : (f : OperationSymbolsOf 𝑆)(𝑨 : Algebra {𝑆 = 𝑆} α ρ) → Op (ArityOf 𝑆 f) 𝕌[ 𝑨 ]
f ^ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
```

We previously used a unicode symbol for this purpose; the definition is preserved for
backward compatibility, but its use is deprecated in favor of the ascii version
above.  See [ADR-002][] §7 for the rationale.

```agda
_̂_ : (f : OperationSymbolsOf 𝑆)(𝑨 : Algebra {𝑆 = 𝑆} α ρ) → Op (ArityOf 𝑆 f) 𝕌[ 𝑨 ]
f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
{-# WARNING_ON_USAGE _̂_
"The combining-caret notation `_̂_` is deprecated as of v3.0 and will be removed
in v3.1.  Use the ASCII `_^_` defined immediately above.  See ADR-002 §7."
#-}
```

#### Smart constructors for concrete algebras

Authoring a concrete `Algebra`{.AgdaRecord} by hand means supplying the
`Interp`{.AgdaField} field as a `Func`{.AgdaRecord} `(⟨ 𝑆 ⟩ Domain) Domain`, whose
congruence proof must take apart the `Σ`/`EqArgs`{.AgdaFunction} encoding of `⟨ 𝑆 ⟩`:
the clause `≈cong {o , _} {.o , _} (refl , args≈) = …` recurs verbatim in every such
algebra (it appears across `Examples.Setoid.*` and `Classical.Bundles.*`).  The two
builders below package that destructuring once.

A *fully automatic* congruence is not derivable at this layer, and deliberately so.
Passing from the pointwise hypothesis `∀ i → u i ≈ v i` to `f o u ≈ f o v` is exactly an
application of function extensionality, which the Setoid development avoids on principle
and which is in any case unavailable under `--safe --cubical-compatible`.

So each constructor still requires a per-operation, pointwise congruence `cong-f`;
it removes only the `(refl , args≈)` boilerplate, never the mathematical content.

`mkAlgebra`{.AgdaFunction} is the general builder.  Given a carrier setoid `𝐃`, an
interpretation `f` of each operation symbol, and a proof `cong-f` that every `f o`
respects pointwise setoid equality of its argument tuple, `mkAlgebra`{.AgdaFunction}
assembles the `Algebra`{.AgdaRecord}, discharging the `{o , _} {.o , _} (refl , args≈)`
match internally.

```agda
module _ (𝐷 : Setoid α ρ) where
  open Setoid 𝐷 using (_≈_) renaming (Carrier to D)
  mkAlgebra :
    (f : (o : OperationSymbolsOf 𝑆) → Op (ArityOf 𝑆 o) D)
    → (∀ o  → {u v : ArityOf 𝑆 o → D} → (∀ i → u i ≈ v i) → f o u ≈ f o v)
    → Algebra {𝑆 = 𝑆} α ρ
  mkAlgebra f cong-f .Domain = 𝐷
  mkAlgebra f cong-f .Interp ⟨$⟩ (o , args) = f o args
  mkAlgebra f cong-f .Interp .≈cong {o , _} {.o , _} (refl , args≈) = cong-f o args≈
```

`mkAlgebraₚ`{.AgdaFunction} specialises `mkAlgebra`{.AgdaFunction} to a carrier whose
equality is propositional `_≡_`.  It takes a bare type `A`, builds `Domain = ≡.setoid A`
(a `Setoid α α`, so the result is `Algebra α α`), and asks for `cong-f` in pointwise `_≡_`
form; e.g., `≡.cong₂` for a binary operation, as in the `ℕ∸`-magma of
`Examples.Setoid.FreeMagma`.

```agda
mkAlgebraₚ : (A : Type α)
  (f : (o : OperationSymbolsOf 𝑆) → Op (ArityOf 𝑆 o) A)
  → (∀ o → {u v : ArityOf 𝑆 o → A} → (∀ i → u i ≡ v i) → f o u ≡ f o v)
  → Algebra {𝑆 = 𝑆} α α
mkAlgebraₚ A f cong-f = mkAlgebra (≡.setoid A) f cong-f
```

Sometimes a level has to be named that is only implicit in an algebra's type.
Because Agda's universes are non-cumulative, an algebra cannot be silently reused
at a larger level; the two projections below recover the levels so that a caller
can state the lifting it needs.

`Level-of-Alg`{.AgdaFunction} is the **level of the algebra type**,
`𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)`, which is one universe above both the carrier and the
equality, since `Algebra α ρ` is a record containing a `Setoid α ρ`.

```agda
-- The universe level of an algebra
Level-of-Alg : {α ρ 𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra {𝑆 = 𝑆} α ρ → Level
Level-of-Alg {α = α}{ρ}{𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)
```

`Level-of-Carrier`{.AgdaFunction} is the **universe level of the carrier of an algebra**.

```agda
-- The universe level of the carrier of an algebra
Level-of-Carrier : {α ρ 𝓞 𝓥  : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra {𝑆 = 𝑆} α ρ → Level
Level-of-Carrier {α = α} _ = α
```


#### Level lifting setoid algebra types

Agda's universes are *non-cumulative*: an inhabitant of `Type α` is not an
inhabitant of `Type (α ⊔ ℓ)`, so two algebras built at different levels cannot
simply be compared, and a theorem proved about `Algebra α ρ` does not
automatically apply to `Algebra (α ⊔ ℓ) ρ`.

This bites constantly in universal algebra, where the closure operators of
[Setoid.Varieties.Closure][] move between levels at every step.  The remedy is to
*lift* an algebra explicitly, and the reason the remedy costs nothing
mathematically is that a lifted algebra is isomorphic to the original:
[Setoid.Homomorphisms.Isomorphisms][] proves `Lift-≅ : 𝑨 ≅ Lift-Alg 𝑨 ℓ ρ`, so
isomorphism classes are closed under lifting and every isomorphism-invariant
property survives it.

An algebra carries two independent levels: the carrier's `α` and the equality's
`ρ`; so there are two liftings, and they are kept separate.

`Lift-Algˡ`{.AgdaFunction} raises the *carrier* level, from `α` to `α ⊔ ℓ`,
leaving the equality where it is.  The carrier becomes `Lift ℓ 𝕌[ 𝑨 ]` and two
lifted elements are related exactly when the elements underneath them were, so the
equivalence is transported unchanged.

```agda
module _ {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra {𝑆 = 𝑆} α ρ)(ℓ : Level) where
  open Algebra 𝑨  using ()     renaming ( Domain to A )
  open Setoid A   using (sym ; trans )  renaming ( Carrier to ∣A∣ ; _≈_ to _≈₁_ ; refl to refl₁ )
  open Level


  Lift-Algˡ : Algebra {𝑆 = 𝑆} (α ⊔ ℓ) ρ
  Lift-Algˡ .Domain =
    record  { Carrier = Lift ℓ ∣A∣
            ; _≈_ = λ x y → lower x ≈₁ lower y
            ; isEquivalence = record  { refl = refl₁ ; sym = sym ; trans = trans }
            }
  Lift-Algˡ .Interp ⟨$⟩ (f , la) = lift $ (f ^ 𝑨) (lower ∘ la)
  Lift-Algˡ .Interp .≈cong (refl , la=lb) = ≈cong (Interp 𝑨) (refl , la=lb)
```

`Lift-Algʳ`{.AgdaFunction} raises the level of the *equality*, from `ρ` to `ρ ⊔
ℓ`, and leaves the carrier alone.  The relation becomes `Lift ℓ ∘₂ _≈₁_`, a
proposition-level lift of the original, and the equivalence proofs are re-wrapped
accordingly.

```agda
  Lift-Algʳ : Algebra {𝑆 = 𝑆} α (ρ ⊔ ℓ)
  Lift-Algʳ .Domain =
    record  { Carrier = ∣A∣
            ; _≈_ = (Lift ℓ) ∘₂ _≈₁_
            ; isEquivalence = record  { refl = lift refl₁
                                      ; sym = lift ∘ sym ∘ lower
                                      ; trans = λ x y → lift $ trans (lower x) (lower y)
                                      }
            }
  Lift-Algʳ .Interp ⟨$⟩ (f , la) = (f ^ 𝑨) la
  Lift-Algʳ .Interp .≈cong (refl , la≡lb) = lift $ ≈cong (Interp 𝑨) (≡.refl , (lower ∘ la≡lb))
```

`Lift-Alg`{.AgdaFunction} composes the two, raising both levels at once: given
target increments `ℓ₀` and `ℓ₁` it produces an algebra at `(α ⊔ ℓ₀, ρ ⊔ ℓ₁)`.
It is the operation the closure operators use to bring a class and a candidate
algebra to a common level; `Lift-≅`{.AgdaFunction} of
[Setoid.Homomorphisms.Isomorphisms][] is the isomorphism that makes the move
harmless.

```agda
Lift-Alg : (𝑨 : Algebra {𝑆 = 𝑆} α ρ)(ℓ₀ ℓ₁ : Level) → Algebra {𝑆 = 𝑆} (α ⊔ ℓ₀) (ρ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀)
```

--------------------------------

[^1]: This is why the term construction is a *relative* monad rather than a monad;
      see [Setoid.Terms.Monad][].

[^2]: Because the carrier of `⟨ 𝑆 ⟩ Domain` is a `Σ`-type, an `Interp`{.AgdaField}
      clause matches it as `(o , args)`, which needs the pair constructor `_,_` in scope.
      We therefore re-export `_,_` and `Σ-syntax`{.AgdaFunction} from this module (and
      hence from the `Setoid.Algebras` barrel), so that pattern-matching such a carrier
      needs no separate `Data.Product` import, and no longer trips the misleading
      "`∙-Op` is not a constructor of the datatype … `Σ`" error, which points at the
      operation symbol rather than at the missing `_,_`.

[^3]: The `_^_` symbol is definitionally identical to `_̂_` and was introduced for
      grep-friendliness and to survive shell-pipeline tooling.  New `Classical/` code
      uses `_^_` exclusively; existing `Setoid/` code may continue to use `_̂_` until
      v3.1.  See ADR-002 §7 for the rationale and per-tree policy.
