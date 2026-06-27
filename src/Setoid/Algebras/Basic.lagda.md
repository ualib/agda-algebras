---
layout: default
title : "Setoid.Algebras.Basic module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---

#### Basic definitions

This is the [Setoid.Algebras.Basic][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature )

module Setoid.Algebras.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda and the Agda Standard Library --------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ) public
open import Function         using ( _∘_ ; _∘₂_ ; Func ; _$_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------
open import Overture             using ( OperationSymbolsOf ; ArityOf )
open import Overture.Operations  using ( Op )
open import Setoid.Signatures    using ( ⟨_⟩ )

private variable α ρ ι : Level

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α
```


#### Setoid Algebras

Here we define algebras over a setoid, instead of a mere type with no equivalence on it.

The operator `⟨_⟩`{.AgdaFunction} that translates an ordinary signature into a
signature over a setoid domain — together with its companion `EqArgs`{.AgdaFunction}
— is defined in the signature-generic module [Setoid.Signatures][] and imported
here (see the import above).  Each takes its own signature argument rather than
reading this module's `{𝑆}`, so housing them in a non-parameterized module means
the unused `{𝑆 : Signature 𝓞 𝓥}` parameter of this module does not ride along as
an unsolvable metavariable at use sites.  The `Interp`{.AgdaField} field of
`Algebra`{.AgdaRecord} applies the imported `⟨ 𝑆 ⟩` to this module's signature `𝑆`.

Because the carrier of `⟨ 𝑆 ⟩ Domain` is a `Σ`-type — an operation symbol paired with
its argument tuple — an `Interp`{.AgdaField} clause matches it as `(o , args)`, which
needs the pair constructor `_,_` in scope.  We therefore re-export `_,_` and
`Σ-syntax`{.AgdaFunction} from this module (and hence from the `Setoid.Algebras` barrel),
so that pattern-matching such a carrier needs no separate `Data.Product` import — and no
longer trips the misleading "`∙-Op` is not a constructor of the datatype … `Σ`" error,
which points at the operation symbol rather than at the missing `_,_`.

```agda
open Func renaming ( to to _⟨$⟩_ ; cong to ≈cong )
```

A setoid algebra is just like an algebra but we require that all basic operations
of the algebra respect the underlying setoid equality. The `Func` record packs a
function (`f`, aka apply, aka `_⟨$⟩_`) with a proof (cong) that the function respects
equality.

```agda
record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
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

The next three definitions are merely syntactic sugar that we sometimes use to make
the code more readable.

```agda
𝔻[_] : Algebra α ρ →  Setoid α ρ
𝔻[ 𝑨 ] = Domain 𝑨

-- Forgetful functor: returns the carrier of (the domain of) 𝑨, forgetting its structure.
𝕌[_] : Algebra α ρ →  Type α
𝕌[ 𝑨 ] = Setoid.Carrier 𝔻[ 𝑨 ]
```

We use the ascii symbol `^` to define an infix function for operation-symbol
interpretation in an algebra.[^1]

```agda
-- Interpretation of an operation symbol in an algebra.
_^_ : (f : OperationSymbolsOf 𝑆)(𝑨 : Algebra α ρ) → Op (ArityOf 𝑆 f) 𝕌[ 𝑨 ]
f ^ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
```

We previously used a unicode symbol for this purpose; the definition is preserved for
backward compatibility, but its use is deprecated in favor of the ascii version
above.  See [ADR-002][] §7 for the rationale.

```agda
_̂_ : (f : OperationSymbolsOf 𝑆)(𝑨 : Algebra α ρ) → Op (ArityOf 𝑆 f) 𝕌[ 𝑨 ]
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
assembles the `Algebra`{.AgdaRecord}, discharging the
`{o , _} {.o , _} (refl , args≈)` match internally.

```agda
module _ (𝐷 : Setoid α ρ) where
  open Setoid 𝐷 using (_≈_) renaming (Carrier to D)
  mkAlgebra :
    (f : (o : OperationSymbolsOf 𝑆) → Op (ArityOf 𝑆 o) D)
    → (∀ o  → {u v : ArityOf 𝑆 o → D} → (∀ i → u i ≈ v i) → f o u ≈ f o v)
    → Algebra α ρ
  mkAlgebra f cong-f .Domain = 𝐷
  mkAlgebra f cong-f .Interp ⟨$⟩ (o , args) = f o args
  mkAlgebra f cong-f .Interp .≈cong {o , _} {.o , _} (refl , args≈) = cong-f o args≈
```

`mkAlgebraₚ`{.AgdaFunction} specialises `mkAlgebra`{.AgdaFunction} to a carrier whose
equality is propositional `_≡_`.  It takes a bare type `A`, builds `Domain = ≡.setoid A`
(a `Setoid α α`, so the result is `Algebra α α`), and asks for `cong-f` in pointwise `_≡_`
form — e.g. `≡.cong₂` for a binary operation, as in the `ℕ∸`-magma of
`Examples.Setoid.FreeMagma`.

```agda
mkAlgebraₚ : (A : Type α)
  (f : (o : OperationSymbolsOf 𝑆) → Op (ArityOf 𝑆 o) A)
  → (∀ o → {u v : ArityOf 𝑆 o → A} → (∀ i → u i ≡ v i) → f o u ≡ f o v)
  → Algebra α α
mkAlgebraₚ A f cong-f = mkAlgebra (≡.setoid A) f cong-f
```

Sometimes we want to extract the universe level of a given algebra or its carrier.
The following functions provide that information.

```agda
-- The universe level of an algebra
Level-of-Alg : {α ρ 𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α ρ → Level
Level-of-Alg {α = α}{ρ}{𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)

-- The universe level of the carrier of an algebra
Level-of-Carrier : {α ρ 𝓞 𝓥  : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α ρ → Level
Level-of-Carrier {α = α} _ = α
```


#### Level lifting setoid algebra types

```agda
module _ (𝑨 : Algebra α ρ)(ℓ : Level) where
  open Algebra 𝑨  using ()     renaming ( Domain to A )
  open Setoid A   using (sym ; trans )  renaming ( Carrier to ∣A∣ ; _≈_ to _≈₁_ ; refl to refl₁ )
  open Level


  Lift-Algˡ : Algebra (α ⊔ ℓ) ρ
  Lift-Algˡ .Domain =
    record  { Carrier = Lift ℓ ∣A∣
            ; _≈_ = λ x y → lower x ≈₁ lower y
            ; isEquivalence = record  { refl = refl₁ ; sym = sym ; trans = trans }
            }
  Lift-Algˡ .Interp ⟨$⟩ (f , la) = lift $ (f ^ 𝑨) (lower ∘ la)
  Lift-Algˡ .Interp .≈cong (refl , la=lb) = ≈cong (Interp 𝑨) (refl , la=lb)


  Lift-Algʳ : Algebra α (ρ ⊔ ℓ)
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

Lift-Alg : (𝑨 : Algebra α ρ)(ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀)
```

--------------------------------

[^1]: The `_^_` symbol is definitionally identical to `_̂_` and was introduced for grep-friendliness and to survive shell-pipeline tooling.  New `Classical/` code uses `_^_` exclusively; existing `Setoid/` code may continue to use `_̂_` until v3.1.  See ADR-002 §7 for the rationale and per-tree policy.


<span style="float:left;">[↑ Setoid.Algebras](Setoid.Algebras.html)</span>
<span style="float:right;">[Setoid.Algebras.Products →](Setoid.Algebras.Products.html)</span>

{% include UALib.Links.md %}
