---
layout: default
title : "Overture.Basic module"
date : "2021-01-13"
author: "the agda-algebras development team"
---

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Basic][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

(See also the Equality module of the [agda-algebras][] library.)

An Agda program typically begins by setting some options and by importing types
from existing Agda libraries. Options are specified with the `OPTIONS` *pragma*
and control the way Agda behaves by, for example, specifying the logical axioms
and deduction rules we wish to assume when the program is type-checked to verify
its correctness.

Each module in the library begins with a pragma line of the form


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}
```


+  The `--cubical-compatible` flag asks Agda to rule out reasoning principles incompatible with univalent type theory — in particular, Streicher's axiom K and uniqueness of identity proofs — and to generate the internal support code that lets Cubical Agda import this module. It implies `--without-K` (which forbids K outright) and strengthens it by additionally preparing each definition for interaction with Cubical's path-based notion of equality.

   Earlier versions of the library used `--without-K` directly, which disables
   [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29);
   see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html)
   in the [Agda Language Reference Manual](https://agda.readthedocs.io/en/v2.6.1.3/language).

   However, `--cubical-compatible` superseded `--without-K` in Agda 2.6.3 (see [Agda issue #5843](https://github.com/agda/agda/issues/5843) for the rationale). The practical difference is that a module with only `--without-K` cannot be imported from a `--cubical` module, but one with `--cubical-compatible` can. Since we intend to port this library to Cubical Agda (see the project roadmap), `--cubical-compatible` is the correct choice.

+  The `--exact-split` flag requires every case in a definition by pattern matching to hold *definitionally*, not merely propositionally. This keeps the operational behavior of our definitions in lockstep with their intended mathematical meaning and catches accidental reliance on with-abstractions.

+  Finally, `--safe` forbids postulates, `trustMe`, and unsafe FFI — everything in agda-algebras is a genuine proof.

(Readers familiar with the standard library will notice occasional `-W[no]UnsupportedIndexedMatch` warnings on our pattern-matching definitions. These warnings come from `--cubical-compatible` and indicate that the flagged definition will not compute when applied to a `--cubical` transport. They are suppressed at the library level via the `flags:` field in `agda-algebras.agda-lib`. Every such site is a candidate for cleanup when we eventually port to Cubical; see the project's Milestone 5.)


#### <a id="agda-modules">Agda modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example,
the [Base.Functions.Basic][] module begins with the following line, and then a
list of imports of things used in the module.

```agda


module Overture.Basic where

-- Imports from Agda and the Agda Standard Library -----------------------------------------------
open import Agda.Primitive    using () renaming ( Set to  Type ; lzero to  ℓ₀ )
open import Data.Product      using ( _,_ ; ∃ ; Σ-syntax ; _×_ )
                              renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base     using ( _∘_ ; id )
open import Level             using ( Level ; suc ; _⊔_ ; lift ; lower ; Lift )
open import Relation.Binary   using ( Decidable )
open import Relation.Binary   using ( IsEquivalence ; IsPartialOrder )
open import Relation.Nullary  using ( Dec ; yes ; no ; Irrelevant )

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans )

private variable a b : Level

ℓ₁ : Level
ℓ₁ = suc ℓ₀

-- the two element type
data 𝟚 : Type ℓ₀ where 𝟎 : 𝟚 ;  𝟏 : 𝟚

-- the three element type
data 𝟛 : Type ℓ₀ where 𝟎 : 𝟛 ;  𝟏 : 𝟛 ;  𝟐 : 𝟛
```


#### <a id="projection-notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂`
representing the first and second projections out of the product.  However, we
prefer the shorter names `fst` and `snd`.  Sometimes we prefer to denote these
projections by `∣_∣` and `∥_∥`, respectively. We define these alternative
notations for projections out of pairs as follows.


```agda


module _ {A : Type a}{B : A → Type b} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd

 infix  40 ∣_∣
```


Here we put the definitions inside an *anonymous module*, which starts with the
 `module` keyword followed by an underscore (instead of a module name). The
purpose is simply to move the postulated typing judgments---the "parameters"
of the module (e.g., `A : Type a`)---out of the way so they don't obfuscate
the definitions inside the module.

Let's define some useful syntactic sugar that will make it easier to apply
symmetry and transitivity of `≡` in proofs.


```agda


_⁻¹ : {A : Type a} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p

infix  40 _⁻¹
```


If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of
`sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic
sugar makes abundant appeals to transitivity easier to stomach.


```agda


_∙_ : {A : Type a}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

𝑖𝑑 : (A : Type a) → A → A
𝑖𝑑 A = λ x → x

infixl 30 _∙_
```


#### <a id="sigma-types">Sigma types</a>


```agda


infix 2 ∃-syntax

∃-syntax : ∀ {A : Type a} → (A → Type b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ∈ A ] B
```


#### <a id="pi-types">Pi types</a>

The dependent function type is traditionally denoted with an uppercase pi symbol
and typically expressed as `Π(x : A) B x`, or something similar.  In Agda syntax,
one writes `(x : A) → B x` for this dependent function type, but we can define
syntax that is closer to standard notation as follows.


```agda


Π : {A : Type a } (B : A → Type b ) → Type (a ⊔ b)
Π {A = A} B = (x : A) → B x

Π-syntax : (A : Type a)(B : A → Type b) → Type (a ⊔ b)
Π-syntax A B = Π B

syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
infix 6 Π-syntax
```

In the modules that follow, we will see many examples of this syntax in action.


#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:

`Type a : Type (lsuc a)`, `Type (lsuc a) : Type (lsuc (lsuc a))` , etc.

and so on. This means that the universe `Type a` has type `Type(lsuc a)`, and
`Type(lsuc a)` has type `Type(lsuc (lsuc a))`, and so on.  It is important to
note, however, this does *not* imply that  `Type a : Type(lsuc(lsuc a))`. In other
words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to
treat universe levels more precisely, which is nice. On the other hand, a
non-cumulative hierarchy can sometimes make for a non-fun proof assistant.
Specifically, in certain situations, the non-cumulativity makes it unduly
difficult to convince Agda that a program or proof is correct.


#### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue
described in the previous subsection.  In the [Lifts of algebras
section](Base.Algebras.Basic.html#lifts-of-algebras) of the
[Base.Algebras.Basic][] module we will define a couple domain-specific lifting
types which have certain properties that make them useful for resolving universe
level problems when working with algebra types.

Let us be more concrete about what is at issue here by considering a typical
example. Agda will often complain with errors like the following:

    Birkhoff.lagda:498,20-23
    a != 𝓞 ⊔ 𝓥 ⊔ (lsuc a) when checking that the expression... has type...

This error message means that Agda encountered the universe level `lsuc a`, on
line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type
at level `𝓞 ⊔ 𝓥 ⊔ lsuc a` instead.

The general `Lift` record type that we now describe makes such problems easier to
deal with. It takes a type inhabiting some universe and embeds it into a higher
universe and, apart from syntax and notation, it is equivalent to the `Lift` type
one finds in the `Level` module of the [Agda Standard Library][].

    record Lift {𝓦 a : Level} (A : Set a) : Set (a ⊔ 𝓦) where
      constructor lift
      field lower : A

The point of having a ramified hierarchy of universes is to avoid Russell's
paradox, and this would be subverted if we were to lower the universe of a type
that wasn't previously lifted.  However, we can prove that if an application of
`lower` is immediately followed by an application of `lift`, then the result is
the identity transformation. Similarly, `lift` followed by `lower` is the
identity.

```agda


lift∼lower : {A : Type a} → lift ∘ lower ≡ 𝑖𝑑 (Lift b A)
lift∼lower = refl

lower∼lift : {A : Type a} → (lower {a}{b}) ∘ lift ≡ 𝑖𝑑 A
lower∼lift = refl
```

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion
that two functions are (extensionally) the same in the sense that they produce
the same output when given the same input.  (We will have more to say about
this notion of equality in the [Base.Equality.Extensionality][] module.)

```agda


module _ {a : Level}{A : Type a}{b : Level}{B : A → Type b } where

 _≈_ :  (f g : (a : A) → B a) → Type (a ⊔ b)
 f ≈ g = ∀ x → f x ≡ g x

 infix 8 _≈_

 ≈IsEquivalence : IsEquivalence _≈_
 IsEquivalence.refl   ≈IsEquivalence          = λ _ → refl
 IsEquivalence.sym    ≈IsEquivalence f≈g      = λ x → sym (f≈g x)
 IsEquivalence.trans  ≈IsEquivalence f≈g g≈h  = λ x → trans (f≈g x) (g≈h x)
```

The following is convenient for proving two pairs of a product type are equal
using the fact that their respective components are equal.

```agda


≡-by-parts :  {A : Type a}{B : Type b}{u v : A × B}
 →            fst u ≡ fst v → snd u ≡ snd v → u ≡ v

≡-by-parts refl refl = refl
```

Lastly, we will use the following type (instead of `subst`) to transport equality
proofs.


```agda


transport : {A : Type a } (B : A → Type b) {x y : A} → x ≡ y → B x → B y
transport B refl = id
```


------------------------------

<span style="float:left;">[← Overture.Preface](Overture.Preface.html)</span>
<span style="float:right;">[Overture.Signatures →](Overture.Signatures.html)</span>

{% include UALib.Links.md %}


