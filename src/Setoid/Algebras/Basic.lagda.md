---
layout: default
title : "Setoid.Algebras.Basic module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---

#### Basic definitions

This is the [Setoid.Algebras.Basic][] module of the [Agda Universal Algebra Library][].

An **algebra over a signature** `𝑆`{.AgdaGeneralizable} is a setoid — a carrier type together with an equivalence relation on it — equipped with an interpretation of every operation symbol of `𝑆`{.AgdaGeneralizable} as a function on that carrier which *respects* the equivalence.  That last clause is the entire difference from the type-based development: on a setoid an operation is not a bare function but a `Func`{.AgdaRecord}, a function bundled with a proof that it sends related arguments to related results.  Carrying the proof inside the structure is what makes quotients cheap: a quotient algebra is the *same* carrier under a coarser equivalence, so forming one needs neither quotient types nor an axiom.  That matters here, because the library is `--safe --cubical-compatible`, where function extensionality is unavailable — see the discussion at `mkAlgebra`{.AgdaFunction} below for where the cost reappears.

This module is the canonical entry point for the `Setoid/` tree.  It defines the `Algebra`{.AgdaRecord} record, two smart constructors for building one from an ordinary interpretation function, the operation-interpretation operator `_^_`{.AgdaFunction}, and the universe-lifting operations that let algebras at different levels be compared.  For indexed products see [Setoid.Algebras.Products][]; for finite algebras, [Setoid.Algebras.Finite][]; for reducts to a smaller signature, [Setoid.Algebras.Reduct][].  Congruences and the quotients they generate are in [Setoid.Congruences.Basic][], and structure-preserving maps between algebras in [Setoid.Homomorphisms.Basic][].

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

`ov`{.AgdaFunction} names the level arithmetic that classes of algebras keep needing: `ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α`.  A membership condition on algebras is seldom a statement about one carrier; it quantifies over algebras themselves — `H`, `S` and `P` of [Setoid.Varieties.Closure][] each say "there is an algebra in `𝒦` such that …" — and `Algebra α ρ`{.AgdaRecord} is a type one universe above its carrier, which is precisely what `Level-of-Alg`{.AgdaFunction} below computes.  Such a condition therefore lands at `lsuc α`, and since it also mentions operation symbols and arities it joins `𝓞`{.AgdaGeneralizable} and `𝓥`{.AgdaGeneralizable}.  Abbreviating that join keeps the closure operators' level expressions readable: `Pred (Algebra α ρ) (ov α)` is the recurring shape of a class, and `class-product`{.AgdaFunction} of [Setoid.Algebras.Products][] builds an algebra at `ov (α ⊔ ρ)`.

The same `lsuc` is what forces `Term`{.AgdaDatatype} to raise levels, `Term X : Type (ov χ)` for `X : Type χ`, and so what makes the term construction a *relative* monad rather than a monad; see [Setoid.Terms.Monad][].

```agda
ov : {𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Level → Level
ov {𝓞 = 𝓞}{𝓥 = 𝓥} α = 𝓞 ⊔ 𝓥 ⊔ lsuc α
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

`𝔻[_]`{.AgdaFunction} is the *domain* of an algebra: the setoid `⟨A, ≈⟩` underlying it, carrier and equivalence together.  It is the projection to reach for whenever the equality matters — stating that a map is a `Func`{.AgdaRecord} between two algebras, or opening a `Setoid`{.AgdaRecord} to name its `_≈_`.

```agda
𝔻[_] : Algebra {𝑆 = 𝑆} α ρ →  Setoid α ρ
𝔻[ 𝑨 ] = Domain 𝑨
```

`𝕌[_]`{.AgdaFunction} forgets one step further, to the bare carrier type.  Mathematically it is the underlying-set functor from algebras to sets, minus the equality: `𝕌[ 𝑨 ]` is what an element of `𝑨`{.AgdaGeneralizable} *is*, with no record of when two such elements count as equal.  Use it where a plain type is wanted — the codomain of an operation, as in `_^_`{.AgdaFunction} just below — and `𝔻[_]`{.AgdaFunction} everywhere the equality is needed.

```agda
-- Forgetful functor: returns the carrier of (the domain of) 𝑨, forgetting its structure.
𝕌[_] : Algebra {𝑆 = 𝑆} α ρ →  Type α
𝕌[ 𝑨 ] = Setoid.Carrier 𝔻[ 𝑨 ]
```

We use the ascii symbol `^` to define an infix function for operation-symbol
interpretation in an algebra.[^1]

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
assembles the `Algebra`{.AgdaRecord}, discharging the
`{o , _} {.o , _} (refl , args≈)` match internally.

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
form — e.g. `≡.cong₂` for a binary operation, as in the `ℕ∸`-magma of
`Examples.Setoid.FreeMagma`.

```agda
mkAlgebraₚ : (A : Type α)
  (f : (o : OperationSymbolsOf 𝑆) → Op (ArityOf 𝑆 o) A)
  → (∀ o → {u v : ArityOf 𝑆 o → A} → (∀ i → u i ≡ v i) → f o u ≡ f o v)
  → Algebra {𝑆 = 𝑆} α α
mkAlgebraₚ A f cong-f = mkAlgebra (≡.setoid A) f cong-f
```

Sometimes a level has to be named that is only implicit in an algebra's type.  Because Agda's universes are non-cumulative, an algebra cannot be silently reused at a larger level; the two projections below recover the levels so that a caller can state the lifting it needs.

`Level-of-Alg`{.AgdaFunction} returns the level of the *algebra type* itself, `𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)` — one universe above both the carrier and the equality, since `Algebra α ρ`{.AgdaRecord} is a record containing a `Setoid α ρ`{.AgdaRecord}.

```agda
-- The universe level of an algebra
Level-of-Alg : {α ρ 𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra {𝑆 = 𝑆} α ρ → Level
Level-of-Alg {α = α}{ρ}{𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)
```

`Level-of-Carrier`{.AgdaFunction} returns just `α`, the level of the carrier — the argument to give `Lift-Alg`{.AgdaFunction} when only the elements, and not the equality, need to move up.

```agda
-- The universe level of the carrier of an algebra
Level-of-Carrier : {α ρ 𝓞 𝓥  : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra {𝑆 = 𝑆} α ρ → Level
Level-of-Carrier {α = α} _ = α
```


#### Level lifting setoid algebra types

Agda's universes are *non-cumulative*: an inhabitant of `Type α` is not thereby an inhabitant of `Type (α ⊔ ℓ)`, so two algebras built at different levels cannot simply be compared, and a theorem proved about `Algebra α ρ`{.AgdaRecord} does not automatically apply to `Algebra (α ⊔ ℓ) ρ`{.AgdaRecord}.  This bites constantly in universal algebra, where the closure operators of [Setoid.Varieties.Closure][] move between levels at every step.  The remedy is to *lift* an algebra explicitly, and the reason the remedy costs nothing mathematically is that a lifted algebra is isomorphic to the original: [Setoid.Homomorphisms.Isomorphisms][] proves `Lift-≅ : 𝑨 ≅ Lift-Alg 𝑨 ℓ ρ`, so isomorphism classes are closed under lifting and every isomorphism-invariant property survives it.

An algebra carries two independent levels — the carrier's `α` and the equality's `ρ` — so there are two liftings, and they are kept separate.

`Lift-Algˡ`{.AgdaFunction} raises the *carrier* level, from `α` to `α ⊔ ℓ`, leaving the equality where it is.  The carrier becomes `Lift ℓ ∣A∣` and two lifted elements are related exactly when the elements underneath them were, so the equivalence is transported unchanged.

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

`Lift-Algʳ`{.AgdaFunction} is the mirror image: it raises the level of the *equality*, from `ρ` to `ρ ⊔ ℓ`, and leaves the carrier alone.  The relation becomes `Lift ℓ ∘₂ _≈₁_`, a proposition-level lift of the original, and the equivalence proofs are re-wrapped accordingly.

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

`Lift-Alg`{.AgdaFunction} composes the two, raising both levels at once, and is the form almost every caller wants: given target increments `ℓ₀` and `ℓ₁` it produces an algebra at `(α ⊔ ℓ₀, ρ ⊔ ℓ₁)`.  It is the operation the closure operators use to bring a class and a candidate algebra to a common level; `Lift-≅`{.AgdaFunction} of [Setoid.Homomorphisms.Isomorphisms][] is the isomorphism that makes the move harmless.

```agda
Lift-Alg : (𝑨 : Algebra {𝑆 = 𝑆} α ρ)(ℓ₀ ℓ₁ : Level) → Algebra {𝑆 = 𝑆} (α ⊔ ℓ₀) (ρ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀)
```

--------------------------------

[^1]: The `_^_` symbol is definitionally identical to `_̂_` and was introduced for grep-friendliness and to survive shell-pipeline tooling.  New `Classical/` code uses `_^_` exclusively; existing `Setoid/` code may continue to use `_̂_` until v3.1.  See ADR-002 §7 for the rationale and per-tree policy.
