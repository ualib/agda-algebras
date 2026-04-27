---
layout: default
title : "Demos.HSP module"
date : "2022-04-27"
author: "the agda-algebras development team"
---

### <a id="introduction">Introduction</a>

The Agda Universal Algebra Library ([agda-algebras][]) formalizes the foundations of universal 
algebra in intensional Martin-Löf type theory ([MLTT][]) using [Agda][] ()  [@Norell:2007; @agdaref].
The library includes a collection of definitions and verified theorems originated in classical 
(set-theory based) universal algebra and equational logic, but adapted to [MLTT][].

The first major milestone of the project is a complete formalization of *Birkhoff's variety
theorem* (also known as the *HSP theorem*) [@Birkhoff:1935]. To the best of our knowledge, this
is the first time Birkhoff's celebrated 1935 result has been formalized in [MLTT][].[^1]

Our first attempt to formalize Birkhoff's theorem suffered from two flaws.[^2] First, we 
assumed function extensionality in [MLTT][]; consequently, it was unclear whether the
formalization was fully constructive. Second, an inconsistency could be contrived by taking the
type `X`, representing an arbitrary collection of variable symbols, to be the two element type
(see §[7](#sec:discuss){reference-type="ref" reference="sec:discuss"} for details). To resolve
these issues, we developed a new formalization of the HSP theorem based on *setoids* and
rewrote much of the [agda-algebras][] library to support this approach. This enabled us to
avoid function extensionality altogether. Moreover, the type `X` of variable symbols was
treated with more care using the *context* and *environment* types that Andreas Abel uses
in [@Abel:2021] to formalize Birkhoff's completeness theorem. These design choices are
discussed further in §[2.2](#setoids){reference-type="ref"
reference="setoids"}--[2.3](#setoid-functions){reference-type="ref"
reference="setoid-functions"}.

What follows is a self-contained formal proof of the HSP theorem in [Agda][]. This is achieved
by extracting a subset of the library, including only the pieces needed for the proof, into a
single literate file.[^3] For spaces reasons, we elide some inessential parts, but strive to
preserve the essential content and character of the development. Specifically, routine or
overly technical components, as well as anything that does not seem to offer insight into the
central ideas of the proof are omitted. (The file [[src/Demos/HSP.lagda]{.sans-serif}](https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda) mentioned above includes the full proof.)

<!-- We include here every line of code of our new proof of Birkhoff's theorem in a single module, -->
<!-- presented as a literate document,[^4]. Apart from a few dozen imports from the , the module is self-contained. -->

In this paper, we highlight some of the more challenging aspects of formalizing universal algebra in type theory. To some extent, this is a sobering glimpse of the significant technical hurdles that must be overcome to do mathematics in dependent type theory. Nonetheless, we hope to demonstrate that [MLTT][] is a relatively natural language for formalizing universal algebra. Indeed, we believe that researchers with sufficient patience and resolve can reap the substantial rewards of deeper insight and greater confidence in their results by using type
theory and a proof assistant like [Agda][]. On the other hand, this paper is probably not the best place to learn about the latter, since we assume the reader is already familiar with [MLTT][] and [Agda][]. In summary, our main contribution is to show that a straightforward but very general representation of algebraic structures in dependent type theory is quite practical, as we demonstrate by formalizing a major seminal result of universal algebra.

### <a id="preliminaries">Preliminaries</a>

#### <a id="logical-foundations">Logical foundations</a>

To best emulate [MLTT][], we use

```agda

{-# OPTIONS --cubical-compatible --exact-split --safe #-}
```

 disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29); 
directs [Agda][] to accept only definitions behaving like *judgmental* equalities;
**safe** ensures that nothing is postulated outright.
(See [@agdaref-axiomk; @agdaref-safeagda; @agdatools-patternmatching].)

Here are brief descriptions of these options, accompanied by links to
related documentation.

*  **without-K** disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29). See
   the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference Manual](https://agda.readthedocs.io/en/v2.6.1.3/language) [@agdaref-axiomk].

*  **exact-split** directs [Agda][] to accept only definitions behaving like *judgmental* equalities. See the [Pattern matching and equality](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) section of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1.3/tools/) documentation [@agdatools-patternmatching].

*  **safe** ensures that nothing is postulated outright---every non-axiom has to be an explicit assumption (e.g., an argument to a function or module). See the [cmdoption-safe](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) section of [@agdaref-safeagda].

We also make use of the following definitions from [Agda][]'s standard library (ver. 1.7).


```agda

-- Import universe levels and Signature type (described below) from the agda-algebras library.
open import Overture using ( 𝓞 ; 𝓥 ; Signature )
module Demos.HSP {𝑆 : Signature 𝓞 𝓥} where

-- Import 16 definitions from the Agda Standard Library.
open import Data.Unit.Polymorphic  using  ( ⊤ ; tt )
open import Function               using  ( id ; _∘_ ; flip )
open import Level                  using  ( Level ;  _⊔_ ; suc )
open import Relation.Binary        using  ( Rel ; Setoid ; IsEquivalence
                                          ; Reflexive ; Symmetric ; Transitive
                                          ; Sym ; Trans )
open import Relation.Unary         using  ( Pred ; _⊆_ ; _∈_ )

open import Relation.Binary.PropositionalEquality using ( _≡_ )

-- Import 23 definitions from the Agda Standard Library and rename 12 of them.
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _×_ ; _,_ ; Σ ; Σ-syntax )
                            renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using () renaming ( Func to _⟶_ )

open  _⟶_           using ( cong ) renaming ( to to _⟨$⟩_ )
open IsEquivalence  using ()
                    renaming ( refl to reflᵉ ; sym to symᵉ ; trans to transᵉ )
open Setoid         using ( Carrier ; isEquivalence ) renaming ( _≈_ to _≈ˢ_ )
                    renaming ( refl to reflˢ ; sym to symˢ ; trans to transˢ )

-- Assign handles to 3 modules of the Agda Standard Library.
import Function.Definitions                   as FD
import Relation.Binary.PropositionalEquality  as ≡
import Relation.Binary.Reasoning.Setoid       as SetoidReasoning

private variable
 α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ : Level
 Γ Δ : Type χ
```


The above imports include some adjustments to "standard" [Agda][] syntax; in particular, we use `Type` in place of `Set`, the infix long arrow symbol, `_⟶_`, in place of `Func` (the type of "setoid functions," discussed in
§[2.3](#setoid-functions){reference-type="ref"
reference="setoid-functions"} below), and the symbol `_⟨$⟩_` in place of `f` (application of the map of a setoid function); we use `fst` and `snd`, and sometimes `∣_∣` and `∥_∥`, to denote the first and second projections out of the product type `_×_`.


```agda

module _ {A : Type α }{B : A → Type β} where
 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst
 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd
```



#### <a id="setoids">Setoids</a>

A *setoid* is a pair consisting of a type and an equivalence relation on that type. Setoids are useful for representing a set with an explicit, "local" notion of equivalence, instead of relying on an implicit, "global" one as is more common in set theory. In reality, informal mathematical practice relies on equivalence relations quite pervasively, taking great care to define only functions that preserve equivalences, while eliding the details. To be properly formal, such details must be made explicit. While there are many different workable approaches, the one that requires no additional meta-theory is based on setoids, which is why we adopt it here. While in some settings setoids are found by others to be burdensome, we have not found them to be so for universal algebra.

The [agda-algebras][] library was first developed without setoids, relying on propositional equality instead, along with some experimental, domain-specific types for equivalence classes, quotients, etc. This
required postulating function extensionality,[^4] which is known to be independent from [MLTT][] [@MHE; @MHE:2019]; this was unsatisfactory as we aimed to show that the theorems hold directly in [MLTT][] without extra axioms. The present work makes no appeal to functional extensionality or classical axioms like Choice or Excluded Middle.[^5]

##### <a id="setoid-functions">Setoid functions</a>

A *setoid function* is a function from one setoid to another that respects the underlying equivalences. If [𝑨]{.ab} and [𝑩]{.ab} are setoids, we use [𝑨]{.ab}_[⟶]{.aor}_[𝑩]{.ab} to denote the type of setoid functions from [𝑨]{.ab} to [𝑩]{.ab}.

An example of a setoid function is the identity function from a setoid to itself. We define it, along with a binary composition operation for setoid functions, `_⟨∘⟩_`, as follows.


```agda


𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { to = id ; cong = id }

_⟨∘⟩_ :  {A : Setoid α ρᵃ} {B : Setoid β ρᵇ} {C : Setoid γ ρᶜ}
 →       B ⟶ C  →  A ⟶ B  →  A ⟶ C

f ⟨∘⟩ g = record  { to = (_⟨$⟩_ f) ∘ (_⟨$⟩_ g)
                  ; cong = (cong f) ∘ (cong g) }
```



#### <a id="inverses">Inverses</a>
<!-- {#inverses .unnumbered} -->

We define the *inverse* of a setoid function in terms of the image of the function's domain, as follows.


```agda


module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑩 using ( _≈_ ; sym ) renaming ( Carrier to B )

 data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → ∀ a → b ≈ f ⟨$⟩ a → Image f ∋ b
```


An inhabitant of the `Image f ∋ b` type is a point `a : Carrier 𝑨`, along with a proof `p : b ≈ f a`, that `f` maps `a` to `b`. Since a proof of `Image f ∋ b` must include a concrete witness `a : Carrier 𝑨`, we can actually *compute* a range-restricted right-inverse of `f`. Here is the definition of `Inv` which, for extra
certainty, is accompanied by a proof that it gives such a right-inverse.


```agda


 Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b → Carrier 𝑨
 Inv _ (eq a _) = a

 InvIsInverseʳ : {f : 𝑨 ⟶ 𝑩}{b : B}(q : Image f ∋ b) → f ⟨$⟩ (Inv f q) ≈ b
 InvIsInverseʳ (eq _ p) = sym p
```



#### <a id="injective-and-surjective-setoid-functions">Injective and surjective setoid functions</a>
<!-- {#injective-and-surjective-setoid-functions .unnumbered} -->

If `f : 𝑨 ⟶ 𝑩` then we call `f` *injective* provided `∀(a₀ a₁ : A)`, `f ⟨$⟩ a₀ ≈ᴮ f ⟨$⟩ a₁` implies `a₀ ≈ᴬ a₁`; we call `f` *surjective* provided `∀(b : B) ∃(a : A)` such that `f ⟨$⟩ a ≈ᴮ b`.

We represent injective functions on bare types by the type `Injective`, and use this to define the `IsInjective` type representing the property of being an injective setoid function. Similarly, the type `IsSurjective`
represents the property of being a surjective setoid function and `SurjInv` represents the *right-inverse* of a surjective function.

We reproduce the definitions and prove some of their properties inside the next submodule where we first set the stage by declaring two setoids `𝑨` and `𝑩` and naming their equality relations.


```agda


module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑨 using () renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝑩 using () renaming ( _≈_ to _≈ᴮ_ )
 open FD

 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective _≈ᴬ_ _≈ᴮ_ (_⟨$⟩_ f)

 IsSurjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ β ⊔ ρᵇ)
 IsSurjective F = ∀ {y} → Image F ∋ y

 SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → Carrier 𝑩 → Carrier 𝑨
 SurjInv f fonto b = Inv f (fonto {b})
```


Proving that the composition of injective setoid functions is again injective is simply a matter of composing the two assumed witnesses to injectivity. Proving that surjectivity is preserved under composition is only slightly more involved.


```agda


module _  {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ}
          (f : 𝑨 ⟶ 𝑩)(g : 𝑩 ⟶ 𝑪) where

 ∘-IsInjective : IsInjective f → IsInjective g → IsInjective (g ⟨∘⟩ f)
 ∘-IsInjective finj ginj = finj ∘ ginj

 ∘-IsSurjective : IsSurjective f → IsSurjective g → IsSurjective (g ⟨∘⟩ f)
 ∘-IsSurjective fonto gonto {y} = Goal where
  mp : Image g ∋ y → Image g ⟨∘⟩ f ∋ y
  mp (eq c p) = η fonto where
   open Setoid 𝑪 using ( trans )
   η : Image f ∋ c → Image g ⟨∘⟩ f ∋ y
   η (eq a q) = eq a (trans p (cong g q))

  Goal : Image g ⟨∘⟩ f ∋ y
  Goal = mp gonto
```




#### <a id="factorization-of-setoid-functions">Factorization of setoid functions[^6]</a>
<!-- {#factorization-of-setoid-functions .unnumbered} -->

Every (setoid) function `f : A ⟶ B` factors as a surjective map `toIm : A ⟶ Im f` followed
by an injective map `fromIm : Im f ⟶ B`.


```agda


module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 Im : (f : 𝑨 ⟶ 𝑩) → Setoid _ _
 Carrier (Im f) = Carrier 𝑨
 _≈ˢ_ (Im f) b1 b2 = f ⟨$⟩ b1 ≈ f ⟨$⟩ b2 where open Setoid 𝑩

 isEquivalence (Im f) = record { refl = refl ; sym = sym; trans = trans }
  where open Setoid 𝑩

 toIm : (f : 𝑨 ⟶ 𝑩) → 𝑨 ⟶ Im f
 toIm f = record { to = id ; cong = cong f }

 fromIm : (f : 𝑨 ⟶ 𝑩) → Im f ⟶ 𝑩
 fromIm f = record { to = λ x → f ⟨$⟩ x ; cong = id }

 fromIm-inj : (f : 𝑨 ⟶ 𝑩) → IsInjective (fromIm f)
 fromIm-inj _ = id

 toIm-surj : (f : 𝑨 ⟶ 𝑩) → IsSurjective (toIm f)
 toIm-surj _ = eq _ (reflˢ 𝑩)
```



### <a id="basic-universal-algebra">Basic Universal Algebra</a>

We now develop a working vocabulary in [MLTT][] corresponding to classical, single-sorted, set-based universal algebra. We cover a number of important concepts, but limit ourselves to those required to prove Birkhoff's HSP theorem. In each case, we give a type-theoretic version of the informal definition, followed by its implementation in [Agda][].

This section is organized into the following subsections:
§[3.1](#signatures){reference-type="ref" reference="signatures"} defines
a general type of *signatures* of algebraic structures;
§[3.2](#algebras){reference-type="ref" reference="algebras"} does the
same for structures and their products;
§[3.3](#homomorphisms){reference-type="ref" reference="homomorphisms"}
defines *homomorphisms*, *monomorphisms*, and *epimorphisms*, presents
types that codify these concepts, and formally verifies some of their
basic properties; §[3.5](#subalgebras){reference-type="ref"
reference="subalgebras"}--[3.6](#terms){reference-type="ref"
reference="terms"} do the same for *subalgebras* and *terms*,
respectively.

#### <a id="signatures">Signatures</a>

An (algebraic) *signature* is a pair `𝑆 = (F, ρ)` where `F` is a collection of *operation symbols* and `ρ : F → N` is an *arity function* which maps each operation symbol to its arity. Here, `N` denotes the *arity type*. Heuristically, the arity of an operation symbol may be thought of as the number of arguments that takes as
"input."  We represent signatures as inhabitants of the following dependent pair type.

    Signature : (𝒪 𝒱 : Level) → Type (lsuc (𝒪 ⊔ 𝒱))
    Signature 𝒪 𝒱 = Σ[ F ∈ Type 𝒪 ] (F → Type 𝒱)

Recalling our syntax for the first and second projections, if `𝑆` is a signature, then `∣ 𝑆 ∣` denotes the set of operation symbols and `∥ 𝑆 ∥` denotes the arity function. Thus, if `f : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, then `∥ 𝑆 ∥ f` is the arity of `f`.

We need to augment our `Signature` type so that it supports algebras over setoid domains. To do so, following Abel [@Abel:2021], we define an operator that translates an ordinary signature into a *setoid signature*, that is, a signature over a setoid domain. This raises a minor technical issue: given operations `f` and `g`, with arguments `u : ∥ 𝑆 ∥ f → A` and `v : ∥ 𝑆 ∥ g → A`, respectively, and a proof of `f ≡ g` (*intensional* equality), we ought to be able to check whether `u` and `v` are *pointwise* equal. Technically, `u` and `v` appear to inhabit different types; of course, this is reconciled by the hypothesis `f ≡ g`, as we see in the next definition (borrowed from [@Abel:2021]).


```agda


EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρᵃ}
 →        ∀ {f g} → f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type (𝓥 ⊔ ρᵃ)
EqArgs {ξ = ξ} ≡.refl u v = ∀ i → u i ≈ v i where open Setoid ξ using ( _≈_ )
```


This makes it possible to define an operator which translates a signature for algebras over bare types into a signature for algebras over setoids. We denote this operator by `⟨_⟩` and define it as follows.


```agda


⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρᵃ → Setoid _ _

Carrier  (⟨ 𝑆 ⟩ ξ)                = Σ[ f ∈ ∣ 𝑆 ∣ ] (∥ 𝑆 ∥ f → ξ .Carrier)
_≈ˢ_     (⟨ 𝑆 ⟩ ξ)(f , u)(g , v)  = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

reflᵉ   (isEquivalence (⟨ 𝑆 ⟩ ξ))                           = ≡.refl , λ i → reflˢ   ξ
symᵉ    (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)              = ≡.refl , λ i → symˢ    ξ (g i)
transᵉ  (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)(≡.refl , h)  = ≡.refl , λ i → transˢ  ξ (g i) (h i)
```



#### <a id="algebras">Algebras</a>

An *algebraic structure* `𝑨 = (A, Fᴬ)` *in the signature* `𝑆 = (F, ρ)`, or `𝑆`-*algebra*, consists of
*  a type `A`, called the *domain* of the algebra;
*  a collection `Fᴬ := {fᴬ ∣ f ∈ F, fᴬ : (ρ f → A) → A}` of *operations* on `A`;
*  a (potentially empty) collection of *identities* satisfied by elements and operations of `𝑨`.
Our [Agda][] implementation represents algebras as inhabitants of a record type with two fields---a `Domain` setoid denoting the domain of the algebra, and an `Interp` function denoting the interpretation in the algebra of each operation symbol in `𝑆`. We postpone introducing identities until §[4](#equational-logic){reference-type="ref" reference="equational-logic"}.


```agda


record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ suc (α ⊔ ρ)) where
 field  Domain  : Setoid α ρ
        Interp  : ⟨ 𝑆 ⟩ Domain ⟶ Domain
```


Thus, for each operation symbol in `𝑆` we have a setoid function `f` whose domain is a power of `Domain` and whose codomain is `Domain`. Further, we define some syntactic sugar to make our formalizations easier to read and reason about. Specifically, if `𝑨` is an algebra, then
*  `𝔻[ 𝑨 ]` denotes the `Domain` setoid of `𝑨`,
*  `𝕌[ 𝑨 ]` is the underlying carrier of (the `Domain` setoid of) `𝑨`, and
*  `f ̂ 𝑨` denotes the interpretation of the operation symbol `f` in the algebra `𝑨`.


```agda


open Algebra
𝔻[_] : Algebra α ρᵃ →  Setoid α ρᵃ
𝔻[ 𝑨 ] = Domain 𝑨

𝕌[_] : Algebra α ρᵃ →  Type α
𝕌[ 𝑨 ] = Carrier (Domain 𝑨)

_̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra α ρᵃ) → (∥ 𝑆 ∥ f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]
f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
```


#### <a id="universe-levels-of-algebra-types">Universe levels of algebra types</a>
<!-- {#universe-levels-of-algebra-types .unnumbered} -->

Types belong to *universes*, which are structured in [Agda][] as follows: 
`Type ℓ : Type (suc ℓ)`, `Type (suc ℓ) : Type (suc (suc ℓ))`.[^7] 
While this means that `Type ℓ` has type `Type (suc ℓ)`, it does *not* imply that `Type ℓ` 
has type `Type (suc (suc ℓ))`. In other words, [Agda][]'s universes are *non-cumulative*. 
This can be advantageous as it becomes possible to treat size issues more generally and precisely. 
However, dealing with explicit universe levels can be daunting, and the standard literature
(in which uniform smallness is typically assumed) offers little guidance. While in some settings, 
such as category theory, formalizing in [Agda][] works smoothly with respect to universe levels 
(see [@agda-categories]), in universal algebra the terrain is bumpier. Thus, it seems worthwhile to 
explain how we make use of universe lifting and lowering functions, available in the 
[Agda Standard Library][], to develop domain-specific tools for dealing with [Agda][]'s non-cumulative 
universe hierarchy.

<!-- Let us be more concrete about what is at issue by considering a typical example. frequently encounters problems during the type-checking process and responds by printing a message like the following. Here informs us that it encountered universe level on line 498 of the HSP module, where it was expecting level     ( ). In this case, we tried to use an algebra inhabiting the type whereas expected an inhabitant of the type ( ( )) . The operation of the standard library embeds a type into a higher universe. Specializing to our situation, we define a function  with the following interface. -2mm . -->

The `Lift` operation of the standard library embeds a type into a higher universe. Specializing `Lift` to our situation, we define a function `Lift-Alg`.


```agda


module _ (𝑨 : Algebra α ρᵃ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans ) ; open Level
 Lift-Algˡ : (ℓ : Level) → Algebra (α ⊔ ℓ) ρᵃ
 Domain (Lift-Algˡ ℓ) =
  record  { Carrier        = Lift ℓ 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → lower x ≈ lower y
          ; isEquivalence  = record { refl = refl ; sym = sym ; trans = trans }
          }
 Interp (Lift-Algˡ ℓ) ⟨$⟩ (f , la) = lift ((f ̂ 𝑨) (lower ∘ la))
 cong (Interp (Lift-Algˡ ℓ)) (≡.refl , lab) = cong (Interp 𝑨) ((≡.refl , lab))

 Lift-Algʳ : (ℓ : Level) → Algebra α (ρᵃ ⊔ ℓ)
 Domain (Lift-Algʳ ℓ) =
  record  { Carrier        = 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → Lift ℓ (x ≈ y)
          ; isEquivalence  = record  { refl  = lift refl
                                     ; sym   = lift ∘ sym ∘ lower
                                     ; trans = λ x y → lift (trans (lower x)(lower y))
                                     }
          }
 Interp (Lift-Algʳ ℓ ) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (Lift-Algʳ ℓ))(≡.refl , lab) =
  lift ( cong (Interp 𝑨) ( ≡.refl , λ i → lower (lab i) ) )

Lift-Alg : Algebra α ρᵃ → (ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρᵃ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ ℓ₁ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀) ℓ₁
```


Recall that our `Algebra` type has two universe level parameters corresponding to
those of the domain setoid. Concretely, an algebra of type `Algebra α ρᵃ` has a
`Domain` of type `Setoid α ρᵃ`. This packages a  "carrier set" (`Carrier`),
inhabiting `Type α`, with an equality on `Carrier` of type `Rel Carrier ρᵃ`.
`Lift-Alg` takes an algebra parametrized by levels `α` and `ρᵃ` and constructs a
new algebra whose carrier  inhabits `Type (α ⊔ ℓ₀)` and whose equivalence inhabits
`Rel Carrier (ρᵃ ⊔ ℓ₁)`. To be useful, this lifting operation should result in an
algebra with the same semantic properties as the one we started with. We will see
in §[3.4](#sec:lift-alg){reference-type="ref" reference="sec:lift-alg"} that this
is indeed the case.


#### <a id="product-algebras">Product Algebras</a>
 <!-- {#product-algebras .unnumbered} -->

We define the *product* of a family of algebras as follows. Let `ι` be a universe
and `I : Type ι` a type (the "indexing type"). Then `𝒜 : I → Algebra α ρᵃ`
represents an *indexed family of algebras*. Denote by `⨅ 𝒜` the *product of
algebras* in `𝒜` (or *product algebra*), by which we mean the algebra whose domain
is the Cartesian product `∏[i ∈ I] 𝔻[ 𝒜 i ]` of the domains of the algebras in
`𝒜`, and whose operations are those arising from the point-wise interpretation of
the operation symbols in the obvious way: if `f` is a `J`-ary operation symbol and
if `a : Π[ i ∈ I ] J → 𝔻[ 𝒜 i ]` is, for each `i : I`, a `J`-tuple of elements of
the domain `𝔻[ 𝒜 i ]`, then we define the interpretation of `f` in `⨅ 𝒜` by

`(f ̂ ⨅ 𝒜) a := λ (i : I) → (f ̂ 𝒜 i)(a i)`.

Here is the formal definition of the product algebra type in [Agda][].


```agda


module _ {ι : Level}{I : Type ι } where

 ⨅ : (𝒜 : I → Algebra α ρᵃ) → Algebra (α ⊔ ι) (ρᵃ ⊔ ι)
 Domain (⨅ 𝒜) =
  record  { Carrier = ∀ i → 𝕌[ 𝒜 i ]
          ; _≈_ = λ a b → ∀ i → (_≈ˢ_ 𝔻[ 𝒜 i ]) (a i)(b i)
          ; isEquivalence =
             record  { refl = λ i → reflᵉ (isEquivalence 𝔻[ 𝒜 i ])
                     ; sym = λ x i → symᵉ (isEquivalence 𝔻[ 𝒜 i ])(x i)
                     ; trans = λ x y i → transᵉ (isEquivalence 𝔻[ 𝒜 i ])(x i)(y i)
                     }
          }

 Interp (⨅ 𝒜) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
 cong (Interp (⨅ 𝒜)) (≡.refl , f=g ) = λ i → cong  ( Interp (𝒜 i) )
                                                   ( ≡.refl , flip f=g i )
```


Evidently, the carrier of the product algebra type is indeed the (dependent)
product of the carriers in the indexed family. The rest of the definitions are the
point-wise versions of the underlying ones.

#### <a id="structure-preserving-maps-and-isomorphism">Structure preserving maps and isomorphism</a>

Throughout the rest of the paper, unless stated otherwise, `𝑨` and `𝑩` will denote
`𝑆`-algebras inhabiting the types `Algebra α ρᵃ` and `Algebra β ρᵇ`, respectively.

A *homomorphism* (or "hom") from `𝑨` to `𝑩` is a setoid function
`h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]` that is *compatible* with all basic operations; that is, for
every operation symbol `f : ∣ 𝑆 ∣` and all tuples `a : ∥ 𝑆 ∥ f → 𝕌[ 𝑨 ]`, we have
`h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)`.

It is convenient to first formalize "compatible" (`compatible-map-op`),
representing the assertion that a given setoid function `h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]`
commutes with a given operation symbol `f`, and then generalize over operation
symbols to yield the type (`compatible-map`) of compatible maps from (the domain
of) `𝑨` to (the domain of) `𝑩`.


```agda


module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where

 compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → ∣ 𝑆 ∣ → Type _
 compatible-map-op h f = ∀ {a} → h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)
  where open Setoid 𝔻[ 𝑩 ] using ( _≈_ )

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type _
 compatible-map h = ∀ {f} → compatible-map-op h f
```


Using these we define the property (`IsHom`) of being a homomorphism, and
finally the type (`hom`) of homomorphisms from `𝑨` to `𝑩`.


```agda


 record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ) where
  constructor  mkhom
  field        compatible : compatible-map h

 hom : Type _
 hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom
```


Thus, an inhabitant of `hom 𝑨 𝑩` is a pair `(h , p)` consisting of a setoid
function `h`, from the domain of `𝑨` to that of `𝑩`, along with a proof `p` that
`h` is a homomorphism.

A *monomorphism* (resp. *epimorphism*) is an injective (resp. surjective)
homomorphism. The [agda-algebras][] library defines predicates and for these, as
well as and for the corresponding types.


```agda


 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field  isHom : IsHom h
         isInjective : IsInjective h
  HomReduct : hom
  HomReduct = h , isHom

 mon : Type _
 mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon
```


As with `hom`, the type `mon` is a dependent product type; each inhabitant is a
pair consisting of a setoid function, say, `h`, along with a proof that `h` is a
monomorphism.


```agda


 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
  field  isHom : IsHom h
         isSurjective : IsSurjective h
  HomReduct : hom
  HomReduct = h , isHom

 epi : Type _
 epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi
```


Here are two utilities that are useful for translating between types.


```agda


open IsHom ; open IsMon ; open IsEpi
module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
 mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
 mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

 epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
 epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
```


##### <a id="composition-of-homomorphisms">Composition of homomorphisms</a>
 <!-- {#composition-of-homomorphisms .unnumbered} -->

The composition of homomorphisms is again a homomorphism, and similarly
for epimorphisms and monomorphisms. The proofs of these facts are
straightforward.


```agda


module _  {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ}
          {g : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]}{h : 𝔻[ 𝑩 ] ⟶ 𝔻[ 𝑪 ]} where
  open Setoid 𝔻[ 𝑪 ] using ( trans )
  ∘-is-hom : IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h → IsHom 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-hom ghom hhom = mkhom c where
   c : compatible-map 𝑨 𝑪 (h ⟨∘⟩ g)
   c = trans (cong h (compatible ghom)) (compatible hhom)

  ∘-is-epi : IsEpi 𝑨 𝑩 g → IsEpi 𝑩 𝑪 h → IsEpi 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-epi gE hE =
    record  { isHom = ∘-is-hom (isHom gE) (isHom hE)
            ; isSurjective = ∘-IsSurjective g h (isSurjective gE) (isSurjective hE)
            }

module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ} where
  ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
  ∘-hom (h , hhom) (g , ghom) = (g ⟨∘⟩ h) , ∘-is-hom hhom ghom

  ∘-epi : epi 𝑨 𝑩 → epi 𝑩 𝑪  → epi 𝑨 𝑪
  ∘-epi (h , hepi) (g , gepi) = (g ⟨∘⟩ h) , ∘-is-epi hepi gepi
```


##### <a id="universe-lifting-of-homomorphisms">Universe lifting of homomorphisms</a>
 <!-- {#universe-lifting-of-homomorphisms .unnumbered} -->

Here we define the identity homomorphism for setoid algebras. Then we prove that
the operations of lifting and lowering of a setoid algebra are homomorphisms.


```agda


𝒾𝒹 : {𝑨 : Algebra α ρᵃ} → hom 𝑨 𝑨
𝒾𝒹 {𝑨 = 𝑨} =  𝑖𝑑 , mkhom (reflexive ≡.refl)
              where open Setoid ( Domain 𝑨 ) using ( reflexive )

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 open Setoid 𝔻[ 𝑨 ] using ( reflexive ) renaming ( _≈_ to _≈₁_ ; refl to refl₁ )
 open Setoid 𝔻[ Lift-Algˡ 𝑨 ℓ ]  using () renaming ( _≈_ to _≈ˡ_ ; refl to reflˡ)
 open Setoid 𝔻[ Lift-Algʳ 𝑨 ℓ ]  using () renaming ( _≈_ to _≈ʳ_ ; refl to reflʳ)
 open Level

 ToLiftˡ : hom 𝑨 (Lift-Algˡ 𝑨 ℓ)
 ToLiftˡ = record { to = lift ; cong = id } , mkhom (reflexive ≡.refl)

 FromLiftˡ : hom (Lift-Algˡ 𝑨 ℓ) 𝑨
 FromLiftˡ = record { to = lower ; cong = id } , mkhom reflˡ

 ToFromLiftˡ : ∀ b →  ∣ ToLiftˡ ∣ ⟨$⟩ (∣ FromLiftˡ ∣ ⟨$⟩ b) ≈ˡ b
 ToFromLiftˡ b = refl₁

 FromToLiftˡ : ∀ a → ∣ FromLiftˡ ∣ ⟨$⟩ (∣ ToLiftˡ ∣ ⟨$⟩ a) ≈₁ a
 FromToLiftˡ a = refl₁

 ToLiftʳ : hom 𝑨 (Lift-Algʳ 𝑨 ℓ)
 ToLiftʳ = record { to = id ; cong = lift } , mkhom (lift (reflexive ≡.refl))

 FromLiftʳ : hom (Lift-Algʳ 𝑨 ℓ) 𝑨
 FromLiftʳ = record { to = id ; cong = lower } , mkhom reflˡ

 ToFromLiftʳ : ∀ b → ∣ ToLiftʳ ∣ ⟨$⟩ (∣ FromLiftʳ ∣ ⟨$⟩ b) ≈ʳ b
 ToFromLiftʳ b = lift refl₁

 FromToLiftʳ : ∀ a → ∣ FromLiftʳ ∣ ⟨$⟩ (∣ ToLiftʳ ∣ ⟨$⟩ a) ≈₁ a
 FromToLiftʳ a = refl₁


module _ {𝑨 : Algebra α ρᵃ}{ℓ r : Level} where
 open  Setoid 𝔻[ 𝑨 ]               using ( refl )
 open  Setoid 𝔻[ Lift-Alg 𝑨 ℓ r ]  using ( _≈_ )
 open  Level
 ToLift : hom 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift = ∘-hom ToLiftˡ ToLiftʳ

 FromLift : hom (Lift-Alg 𝑨 ℓ r) 𝑨
 FromLift = ∘-hom FromLiftʳ FromLiftˡ

 ToFromLift : ∀ b → ∣ ToLift ∣ ⟨$⟩ (∣ FromLift ∣ ⟨$⟩ b) ≈ b
 ToFromLift b = lift refl

 ToLift-epi : epi 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift-epi =
  ∣ ToLift ∣ , record  { isHom = ∥ ToLift ∥
                       ; isSurjective = λ{y} → eq(∣ FromLift ∣ ⟨$⟩ y)(ToFromLift y)
                       }
```



##### <a id="homomorphisms-of-product-algebras">Homomorphisms of product algebras</a>
 <!-- {#homomorphisms-of-product-algebras .unnumbered} -->

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family
`ℬ : I → Algebra β ρᵇ` of algebras. We sometimes refer to the inhabitants of `I`
as *indices*, and call `ℬ` an *indexed family of algebras*. If in addition we have
a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a
homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.  We codify the
latter in dependent type theory as follows.


```agda


module _ {ι : Level}{I : Type ι}{𝑨 : Algebra α ρᵃ}(ℬ : I → Algebra β ρᵇ) where
 ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = h , hhom where  h : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ ℬ ]
                              h ⟨$⟩ a = λ i → ∣ 𝒽 i ∣ ⟨$⟩ a
                              cong h xy i = cong ∣ 𝒽 i ∣ xy
                              hhom : IsHom 𝑨 (⨅ ℬ) h
                              compatible hhom = λ i → compatible ∥ 𝒽 i ∥
```


Two structures are *isomorphic* provided there are homomorphisms from each to the
other that compose to the identity. We define the following record type to
represent this concept. Note that the definition, shown below, includes a proof of
the fact that the maps `to` and `from` are bijective, which makes this fact more
accessible.


```agda


module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
 open Setoid 𝔻[ 𝑨 ]  using ()  renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝔻[ 𝑩 ]  using ()  renaming ( _≈_ to _≈ᴮ_ )

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ ) where
  constructor  mkiso
  field        to    : hom 𝑨 𝑩
               from  : hom 𝑩 𝑨
               to∼from : ∀ b → ∣ to ∣    ⟨$⟩ (∣ from ∣  ⟨$⟩ b)  ≈ᴮ b
               from∼to : ∀ a → ∣ from ∣  ⟨$⟩ (∣ to ∣    ⟨$⟩ a)  ≈ᴬ a

  toIsInjective : IsInjective ∣ to ∣
  toIsInjective {x}{y} xy = trans (sym (from∼to x)) (trans ξ (from∼to y))
   where  open Setoid 𝔻[ 𝑨 ] using ( sym ; trans )
          ξ : ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ x) ≈ᴬ ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ y)
          ξ = cong ∣ from ∣ xy

  fromIsSurjective : IsSurjective ∣ from ∣
  fromIsSurjective {x} = eq (∣ to ∣ ⟨$⟩ x) (sym (from∼to x))
   where open Setoid 𝔻[ 𝑨 ] using ( sym )

open _≅_
```


It is easy to prove that `\au{`{.AgdaRecord}≅``{.AgdaArgument}} is an equivalence relation, as follows.


```agda


≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} =
 mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl) λ a → refl where open Setoid 𝔻[ 𝑨 ] using ( refl )

≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ}) (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν where
  f : hom 𝑨 𝑪                ;  g : hom 𝑪 𝑨
  f = ∘-hom (to ab) (to bc)  ;  g = ∘-hom (from bc) (from ab)

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; trans )
  open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈ᶜ_ ; trans to transᶜ )
  τ : ∀ b → ∣ f ∣ ⟨$⟩ (∣ g ∣ ⟨$⟩ b) ≈ᶜ b
  τ b = transᶜ (cong ∣ to bc ∣ (to∼from ab (∣ from bc ∣ ⟨$⟩ b))) (to∼from bc b)

  ν : ∀ a → ∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ a) ≈ a
  ν a = trans (cong ∣ from ab ∣ (from∼to bc (∣ to ab ∣ ⟨$⟩ a))) (from∼to ab a)
```


##### <a id="homomorphic-images">Homomorphic images</a>
 <!-- {#homomorphic-images .unnumbered} -->

We have found that a useful way to encode the concept of *homomorphic image* is to
produce a witness, that is, a surjective hom. Thus we define the type of
surjective homs and also record the fact that an algebra is its own homomorphic
image via the identity hom.


```agda


ov : Level → Level         -- shorthand for a common level transformation
ov α = 𝓞 ⊔ 𝓥 ⊔ suc α

_IsHomImageOf_ : (𝑩 : Algebra β ρᵇ)(𝑨 : Algebra α ρᵃ) → Type _
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

IdHomImage : {𝑨 : Algebra α ρᵃ} → 𝑨 IsHomImageOf 𝑨
IdHomImage {α = α}{𝑨 = 𝑨} = 𝒾𝒹 , λ {y} → Image_∋_.eq y refl
 where open Setoid 𝔻[ 𝑨 ] using ( refl )
```



##### <a id="factorization-of-homomorphisms">Factorization of homomorphisms</a>
 <!-- {#factorization-of-homomorphisms .unnumbered} -->

Another theorem in the [agda-algebras][] library, called `HomFactor`, formalizes
the following factorization result: if `g : hom 𝑨 𝑩`, `h : hom 𝑨 𝑪`, `h` is
surjective, and `ker h ⊆ ker g`, then there exists `φ : hom 𝑪 𝑩` such that `g = φ
∘ h`. A special case of this result that we use below is the fact that the setoid
function factorization we saw above lifts to factorization of homomorphisms.
Moreover, we associate a homomorphism `h` with its image---which is (the domain
of) a subalgebra of the codomain of `h`---using the function `HomIm` defined
below.[^8]


```agda


module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

 HomIm : (h : hom 𝑨 𝑩) → Algebra _ _
 Domain (HomIm h) = Im ∣ h ∣
 Interp (HomIm h) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (HomIm h)) {x1 , x2} {.x1 , y2} (≡.refl , e) =
  begin
      ∣ h ∣  ⟨$⟩         (Interp 𝑨  ⟨$⟩ (x1 , x2))  ≈⟨ h-compatible                  ⟩
   Interp 𝑩  ⟨$⟩ (x1 , λ x → ∣ h ∣  ⟨$⟩ x2 x)       ≈⟨ cong (Interp 𝑩) (≡.refl , e)  ⟩
   Interp 𝑩  ⟨$⟩ (x1 , λ x → ∣ h ∣  ⟨$⟩ y2 x)       ≈˘⟨ h-compatible                 ⟩
      ∣ h ∣  ⟨$⟩         (Interp 𝑨  ⟨$⟩ (x1 , y2))  ∎
   where  open Setoid 𝔻[ 𝑩 ] ; open SetoidReasoning 𝔻[ 𝑩 ]
          open IsHom ∥ h ∥ renaming (compatible to h-compatible)

 toHomIm : (h : hom 𝑨 𝑩) → hom 𝑨 (HomIm h)
 toHomIm h = toIm ∣ h ∣ , mkhom (reflˢ 𝔻[ 𝑩 ])

 fromHomIm : (h : hom 𝑨 𝑩) → hom (HomIm h) 𝑩
 fromHomIm h = fromIm ∣ h ∣ , mkhom (IsHom.compatible ∥ h ∥)
```



##### <a id="sec:lift-al">Lift-Alg is an algebraic invariant</a>
 <!-- {#sec:lift-alg} -->

The `Lift-Alg` operation neatly resolves the technical problem of universe
non-cumulativity because isomorphism classes of algebras are closed under
`Lift-Alg`. 


```agda


module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})
 Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ
```


#### <a id="subalgebras">Subalgebras</a>

We say that `𝑨` is a *subalgebra* of `𝑩` and write `𝑨 ≤ 𝑩` just in case `𝑨` can be *homomorphically
embedded* in `𝑩`; in other terms, `𝑨 ≤ 𝑩` iff there exists an injective hom from `𝑨` to `𝑩`.


```agda


_≤_ : Algebra α ρᵃ → Algebra β ρᵇ → Type _
𝑨 ≤ 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
```

The subalgebra relation is reflexive, by the identity monomorphism (and transitive by composition of monomorphisms, hence, a *preorder*, though we won't need this fact here).


```agda


≤-reflexive   :  {𝑨 : Algebra α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive = 𝒾𝒹 , id
```


<!-- If `𝒜 : I → Algebra α ρᵃ`, `ℬ : I → Algebra β ρᵇ` (families of -algebras) and if `ℬ i ≤ 𝒜 i` for all `i : I`, then `⨅ ℬ` is a subalgebra of `⨅ 𝒜`. Below we will use to denote this fact. -->

We conclude this section with a definition that will be useful later; it simply converts a monomorphism into a proof of a subalgebra relationship.


```agda


mon→≤ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x
```


#### <a id="terms">Terms</a>

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable symbols. Such a collection is called a *context*. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`, that is `X ∩ ∣ 𝑆 ∣ = ∅`. A *word* in the language of `𝑆` is a finite sequence of members of `X ∪ ∣ 𝑆 ∣`. We denote the
concatenation of such sequences by simple juxtaposition. Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n` the sets `Tₙ` of *words* over `X ∪ ∣ 𝑆 ∣` as follows: `T₀ := X ∪ S₀` and 
`Tₙ₊₁ := Tₙ ∪ 𝒯ₙ`, where `𝒯ₙ` is the collection of all `f t` such that `f : ∣ 𝑆 ∣` and `t : ∥ 𝑆 ∥ f → 𝑇ₙ`.
(Recall, `∥ 𝑆 ∥ f` is the arity of the operation symbol `f`.)
An `𝑆`-*term* is a term in the language of `𝑆` and the collection of all `𝑆`-terms in the context `X` is `Term X := ⋃ₙ Tₙ`.

In type theory, this translates to two cases: variable injection and applying an operation symbol to a tuple of terms. This represents each term as a tree with an operation symbol at each `node` and a variable symbol at
each leaf `ℊ`; hence the constructor names (`ℊ` for "generator" and `node` for "node") in the following inductively defined type.


```agda


data Term (X : Type χ) : Type (ov χ)  where
 ℊ : X → Term X
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X
```


##### <a id="the-term-algebra">The term algebra</a>
 <!-- {#the-term-algebra .unnumbered} -->

We enrich the `Term` type to a setoid of `𝑆`-terms, which will ultimately be the domain of an algebra, called the *term algebra in the signature* `𝑆`. For this we need an equivalence relation on terms.


```agda


module _ {X : Type χ } where

 data _≃_ : Term X → Term X → Type (ov χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≃ (ℊ y)
  gnl : ∀ {f}{s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → (s i) ≃ (t i)) → (node f s) ≃ (node f t)
```


It is easy to show that `_≃_` is an equivalence relation as follows.


```agda


 ≃-isRefl   : Reflexive      _≃_
 ≃-isRefl {ℊ _} = rfl ≡.refl
 ≃-isRefl {node _ _} = gnl λ _ → ≃-isRefl

 ≃-isSym    : Symmetric      _≃_
 ≃-isSym (rfl x) = rfl (≡.sym x)
 ≃-isSym (gnl x) = gnl λ i → ≃-isSym (x i)

 ≃-isTrans  : Transitive     _≃_
 ≃-isTrans (rfl x) (rfl y) = rfl (≡.trans x y)
 ≃-isTrans (gnl x) (gnl y) = gnl λ i → ≃-isTrans (x i) (y i)

 ≃-isEquiv  : IsEquivalence  _≃_
 ≃-isEquiv = record { refl = ≃-isRefl ; sym = ≃-isSym ; trans = ≃-isTrans }
```


For a given signature `𝑆` and context `X`, we define the algebra `𝑻 X`, known as the *term algebra in* 
`𝑆` *over* `X`. The domain of `𝑻 X` is `Term X` and, for each operation symbol `f : ∣ 𝑆 ∣`, we define 
`f ̂ 𝑻 X` to be the operation which maps each tuple `t : ∥ 𝑆 ∥ f → Term X` of terms to the formal
term `f t`.


```agda


TermSetoid : (X : Type χ) → Setoid _ _
TermSetoid X = record { Carrier = Term X ; _≈_ = _≃_ ; isEquivalence = ≃-isEquiv }

𝑻 : (X : Type χ) → Algebra (ov χ) (ov χ)
Algebra.Domain (𝑻 X) = TermSetoid X
Algebra.Interp (𝑻 X) ⟨$⟩ (f , ts) = node f ts
cong (Algebra.Interp (𝑻 X)) (≡.refl , ss≃ts) = gnl ss≃ts
```


##### <a id="environments-and-interpretation-of-terms">Environments and interpretation of terms</a>
 <!-- {#environments-and-interpretation-of-terms .unnumbered} -->

Fix a signature `𝑆` and a context `X`. An *environment* for `𝑨` and `X` is a setoid whose carrier
is a mapping from the variable symbols `X` to the domain `𝕌[ 𝐴 ]` and whose equivalence relation is 
point-wise equality. Our formalization of this concept is the same as that of [@Abel:2021], which 
Abel uses to formalize Birkhoff's completeness theorem.


```agda


module Environment (𝑨 : Algebra α ℓ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )

 Env : Type χ → Setoid _ _
 Env X = record  { Carrier = X → 𝕌[ 𝑨 ]
                 ; _≈_ = λ ρ τ → (x : X) → ρ x ≈ τ x
                 ; isEquivalence = record  { refl   = λ _      → refl
                                           ; sym    = λ h x    → sym (h x)
                                           ; trans  = λ g h x  → trans (g x)(h x) }}
```

The *interpretation* of a term *evaluated* in a particular environment is defined as follows.


```agda


 ⟦_⟧ : {X : Type χ}(t : Term X) → (Env X) ⟶ 𝔻[ 𝑨 ]
 ⟦ ℊ x ⟧          ⟨$⟩ ρ    = ρ x
 ⟦ node f args ⟧  ⟨$⟩ ρ    = (Interp 𝑨) ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧ u≈v          = u≈v x
 cong ⟦ node f args ⟧ x≈y  = cong (Interp 𝑨)(≡.refl , λ i → cong ⟦ args i ⟧ x≈y )
```

Two terms are proclaimed *equal* if they are equal for all environments.


```agda


 Equal : {X : Type χ}(s t : Term X) → Type _
 Equal {X = X} s t = ∀ (ρ : Carrier (Env X)) → ⟦ s ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ρ
```

Proof that `Equal` is an equivalence relation, and that the implication `s ≃ t → Equal s t` holds for all terms `s` and `t`, are also found in [@Abel:2021]. We reproduce them here to keep the presentation self-contained.


```agda


 ≃→Equal : {X : Type χ}(s t : Term X) → s ≃ t → Equal s t
 ≃→Equal .(ℊ _) .(ℊ _) (rfl ≡.refl) = λ _ → refl
 ≃→Equal (node _ s)(node _ t)(gnl x) =
  λ ρ → cong (Interp 𝑨)(≡.refl , λ i → ≃→Equal(s i)(t i)(x i)ρ )

 EqualIsEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
 reflᵉ   EqualIsEquiv = λ _        → refl
 symᵉ    EqualIsEquiv = λ x=y ρ    → sym (x=y ρ)
 transᵉ  EqualIsEquiv = λ ij jk ρ  → trans (ij ρ) (jk ρ)
```




##### <a id="compatibility-of-terms">Compatibility of terms</a>
 <!-- {#compatibility-of-terms .unnumbered} -->

We need to formalize two more concepts involving terms.
The first (`comm-hom-term`) is the assertion that every term commutes with every homomorphism, and
the second (`interp-prod`) is the interpretation of a term in a product algebra.


```agda


module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Environment 𝑨  using ( ⟦_⟧ )
 open Environment 𝑩  using () renaming ( ⟦_⟧ to ⟦_⟧ᴮ )
 open Setoid 𝔻[ 𝑩 ]  using ( _≈_ ; refl  )
 private hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 comm-hom-term : (t : Term X) (a : X → 𝕌[ 𝑨 ]) → h (⟦ t ⟧ ⟨$⟩ a) ≈ ⟦ t ⟧ᴮ ⟨$⟩ (h ∘ a)
 comm-hom-term (ℊ x) a = refl
 comm-hom-term (node f t) a =  begin
   h(⟦ node f t ⟧ ⟨$⟩ a)            ≈⟨ compatible ∥ hh ∥ ⟩
   (f ̂ 𝑩)(λ i → h(⟦ t i ⟧ ⟨$⟩ a))  ≈⟨ cong(Interp 𝑩)(≡.refl , λ i → comm-hom-term(t i) a) ⟩
   ⟦ node f t ⟧ᴮ ⟨$⟩ (h ∘ a)   ∎ where open SetoidReasoning 𝔻[ 𝑩 ]

module _ {X : Type χ}{ι : Level} {I : Type ι} (𝒜 : I → Algebra α ρᵃ) where
 open Setoid 𝔻[ ⨅ 𝒜 ]  using ( _≈_ )
 open Environment      using ( ⟦_⟧ ; ≃→Equal )

 interp-prod : (p : Term X) → ∀ ρ →  (⟦ ⨅ 𝒜 ⟧ p) ⟨$⟩ ρ   ≈   λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ λ x → (ρ x) i
 interp-prod (ℊ x)       = λ ρ i  → ≃→Equal (𝒜 i) (ℊ x) (ℊ x) ≃-isRefl λ _ → (ρ x) i
 interp-prod (node f t)  = λ ρ    → cong (Interp (⨅ 𝒜)) ( ≡.refl , λ j k → interp-prod (t j) ρ k )
```


### <a id="equational-logic">Equational Logic</a>

#### <a id="term-identities-equational-theories-and-the-relation">Term identities, equational theories, and the ⊧ relation</a>
 <!-- {#term-identities-equational-theories-and-the-relation .unnumbered} -->

An `𝑆`-*term equation* (or `𝑆`-*term identity*) is an ordered pair `(p , q)` of `𝑆`-terms, also denoted by `p ≈ q`. They are often simply called *equations* or *identities*, especially when the signature `𝑆` is evident.
We define an *equational theory* (or *algebraic theory*) to be a pair `T = (𝑆 , ℰ)` consisting of a signature `𝑆` and a collection `ℰ` of `𝑆`-term equations.[^9]

We say that the algebra `𝑨` *models* the identity `p ≈ q` and we write `𝑨 ⊧ p ≈ q`
if for all `ρ : X → 𝔻[ 𝑨 ]` we have `⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ`.
In other words, when interpreted in the algebra `𝑨`, the terms `p` and `q` are equal no matter what values are assigned to variable symbols occurring in `p` and `q`.

If `𝒦` is a class of algebras of a given signature, then we write `𝒦 ⊫ p ≈ q` and say that `𝒦` *models* the identity `p ≈ q` provided `𝑨 ⊧ p ≈ q` for every `𝑨 ∈ 𝒦`.


```agda


module _ {X : Type χ} where
 _⊧_≈_ : Algebra α ρᵃ → Term X → Term X → Type _
 𝑨 ⊧ p ≈ q = Equal p q where open Environment 𝑨

 _⊫_≈_ : Pred (Algebra α ρᵃ) ℓ → Term X → Term X → Type _
 𝒦 ⊫ p ≈ q = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q
```

We represent a set of term identities as a predicate over pairs of terms, say, `ℰ :  Pred(Term X × Term X)`, and we denote by `𝑨 ⊨ ℰ` the assertion that `𝑨` models `p ≈ q` for all `(p, q) ∈ ℰ`.


```agda


 _⊨_ : (𝑨 : Algebra α ρᵃ) → Pred(Term X × Term X)(ov χ) → Type _
 𝑨 ⊨ ℰ = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨
```

(The symbol `⊨` is a stretched version of the models symbol `⊧`,
so [Agda][] can distinguish between the two and parse expressions involving the types
`_⊨_` and `_⊧_≈_`. In Emacs `agda2-mode`, the symbol `⊨` is produced by typing
`\|=`, while `⊧` is produced with `\models`.)

An important property of the binary relation `⊧` is *algebraic invariance* (i.e.,
invariance under isomorphism).  We formalize this property as follows.


```agda


module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ)(p q : Term X) where
 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ = begin
  ⟦ p ⟧     ⟨$⟩             ρ    ≈˘⟨  cong ⟦ p ⟧ (f∼g ∘ ρ)        ⟩
  ⟦ p ⟧     ⟨$⟩ (f ∘  (g ∘  ρ))  ≈˘⟨  comm-hom-term fh p (g ∘ ρ)  ⟩
  f(⟦ p ⟧ᴬ  ⟨$⟩       (g ∘  ρ))  ≈⟨   cong ∣ fh ∣ (Apq (g ∘ ρ))   ⟩
  f(⟦ q ⟧ᴬ  ⟨$⟩       (g ∘  ρ))  ≈⟨   comm-hom-term fh q (g ∘ ρ)  ⟩
  ⟦ q ⟧     ⟨$⟩ (f ∘  (g ∘  ρ))  ≈⟨   cong ⟦ q ⟧ (f∼g ∘ ρ)        ⟩
  ⟦ q ⟧     ⟨$⟩             ρ    ∎
  where  f = _⟨$⟩_ ∣ fh ∣ ; g = _⟨$⟩_ ∣ gh ∣
         open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
         open Environment 𝑩  using ( ⟦_⟧ ) ; open SetoidReasoning 𝔻[ 𝑩 ]
```

If `𝒦` is a class of `𝑆`-algebras, the set of identities modeled by `𝒦`, denoted `Th 𝒦`, is called the *equational theory* of `𝒦`. If `ℰ` is a set of `𝑆`-term identities,
the class of algebras modeling `ℰ`, denoted `Mod ℰ`, is called the *equational class axiomatized* by `ℰ`. We codify these notions in the next two definitions.


```agda


Th : {X : Type χ} → Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

Mod : {X : Type χ} → Pred(Term X × Term X) ℓ → Pred (Algebra α ρᵃ) _
Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨
```


#### <a id="the-closure-operators-h-s-p-and-v">The Closure Operators H, S, P and V</a>
 <!-- {#the-closure-operators-h-s-p-and-v .unnumbered} -->

Fix a signature `𝑆`, let `𝒦` be a class of `𝑆`-algebras, and define
* `H 𝒦` := the class of all homomorphic images of members of `𝒦`;
* `S 𝒦` := the class of all subalgebras of members of `𝒦`;
* `P 𝒦` := the class of all products of members of `𝒦`.

`H`, `S`, and `P` are *closure operators* (expansive, monotone, and idempotent).  
A class `𝒦` of `𝑆`-algebras is said to be *closed under the taking of homomorphic images* 
provided `H 𝒦 ⊆ 𝒦`. Similarly, `𝒦` is *closed under the taking of subalgebras* (resp., *arbitrary products*) provided `S 𝒦 ⊆ 𝒦` (resp., `P 𝒦 ⊆ 𝒦`). The operators `H`, `S`, and `P` can be composed with one another repeatedly, forming yet more closure operators. We represent these three closure operators in type theory as follows.


```agda


module _ {α ρᵃ β ρᵇ : Level} where
 private a = α ⊔ ρᵃ
 H : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 H _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 IsHomImageOf 𝑨

 S : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 S _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 ≤ 𝑨

 P : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 P _ ι 𝒦 𝑩 = Σ[ I ∈ Type ι ] (Σ[ 𝒜 ∈ (I → Algebra α ρᵃ) ] (∀ i → 𝒜 i ∈ 𝒦) × (𝑩 ≅ ⨅ 𝒜))
```

Identities modeled by an algebra `𝑨` are also modeled by every homomorphic image of
`𝑨` and by every subalgebra of `𝑨`. These facts are formalized in [Agda][] as follows.


```agda


module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{p q : Term X} where
 ⊧-H-invar : 𝑨 ⊧ p ≈ q → 𝑩 IsHomImageOf 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-H-invar Apq (φh , φE) ρ = begin
       ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ p ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)        ⟩
   φ(  ⟦ p ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   cong ∣ φh ∣ (Apq (φ⁻¹ ∘ ρ))         ⟩
   φ(  ⟦ q ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)        ⟩
       ⟦ q ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈⟨   cong ⟦ q ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ q ⟧   ⟨$⟩               ρ    ∎ where
   φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
   φ⁻¹ = SurjInv ∣ φh ∣ φE
   φ = (_⟨$⟩_ ∣ φh ∣)
   open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
   open Environment 𝑩  using ( ⟦_⟧ ) ; open SetoidReasoning 𝔻[ 𝑩 ]

 ⊧-S-invar : 𝑨 ⊧ p ≈ q → 𝑩 ≤ 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-S-invar Apq B≤A b = ∥ B≤A ∥
  ( begin
    h (  ⟦ p ⟧   ⟨$⟩       b)  ≈⟨   comm-hom-term hh p b  ⟩
         ⟦ p ⟧ᴬ  ⟨$⟩ (h ∘  b)  ≈⟨   Apq (h ∘ b)           ⟩
         ⟦ q ⟧ᴬ  ⟨$⟩ (h ∘  b)  ≈˘⟨  comm-hom-term hh q b  ⟩
    h (  ⟦ q ⟧   ⟨$⟩       b)  ∎ )
  where
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩  using ( ⟦_⟧ )
  hh = ∣ B≤A ∣ ; h = _⟨$⟩_ ∣ hh ∣
```

An identity satisfied by all algebras in an indexed collection is also satisfied by the product of algebras in the collection.


```agda


module _ {X : Type χ}{I : Type ℓ}(𝒜 : I → Algebra α ρᵃ){p q : Term X} where
 ⊧-P-invar : (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-invar 𝒜pq a = begin
   ⟦ p ⟧₁               ⟨$⟩  a                ≈⟨   interp-prod 𝒜 p a            ⟩
   ( λ i → (⟦ 𝒜 i ⟧ p)  ⟨$⟩  λ x → (a x) i )  ≈⟨ (λ i → 𝒜pq i (λ x → (a x) i))  ⟩
   ( λ i → (⟦ 𝒜 i ⟧ q)  ⟨$⟩  λ x → (a x) i )  ≈˘⟨  interp-prod 𝒜 q a            ⟩
   ⟦ q ⟧₁               ⟨$⟩  a                ∎ where
  open Environment (⨅ 𝒜)  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment        using ( ⟦_⟧ )
  open Setoid 𝔻[ ⨅ 𝒜 ]    using ( _≈_ )
  open SetoidReasoning 𝔻[ ⨅ 𝒜 ]
```


A *variety* is a class of `𝑆`-algebras that is closed under the taking of homomorphic images, subalgebras, and arbitrary products. If we define `V 𝒦 := H (S (P 𝒦))`, then `𝒦` is a variety iff `V 𝒦  ⊆ 𝒦`.
(The converse inclusion holds by virtue of the fact that `V` is a composition of closure operators.)
The class `V 𝒦` is called the *varietal closure* of `𝒦`. Here is how we define `V` in type theory.
(The explicit universe level declarations that appear in the definition are needed for disambiguation.)


```agda


module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ
 V : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) →  Pred(Algebra δ ρᵈ) _
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (a ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))
```


The classes `H 𝒦`, `S 𝒦`, `P 𝒦`, and `V 𝒦` all satisfy the
same term identities.  We will only use a subset of the inclusions needed to prove this
assertion. (The others are included in the `Setoid.Varieties.Preservation` module of the [agda-algebras][] library.) First, the closure operator `H` preserves the identities modeled by the given class; this follows almost immediately from the invariance lemma `⊧-H-invar`.


```agda


module _  {X : Type χ}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 H-id1 : 𝒦 ⊫ p ≈ q → H{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 H-id1 σ 𝑩 (𝑨 , kA , BimgA) = ⊧-H-invar{p = p}{q} (σ 𝑨 kA) BimgA
```

The analogous preservation result for `S` is a consequence of the invariance lemma `⊧-S-invar`; the converse, which we call `S-id2`, has an equally straightforward proof.


```agda


 S-id1 : 𝒦 ⊫ p ≈ q → S{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

 S-id2 : S ℓ 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))
```

The [agda-algebras][] library includes analogous pairs of implications for `P`, `H`, and `V`, called `P-id1`, `P-id2`, `H-id1`, etc. Here we only need the first implication in each case, so we omit the others.


```agda


 P-id1 : ∀{ι} → 𝒦 ⊫ p ≈ q → P{β = α}{ρᵃ}ℓ ι 𝒦 ⊫ p ≈ q
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A) where
  IH : ⨅ 𝒜 ⊧ p ≈ q
  IH = ⊧-P-invar 𝒜 {p}{q} λ i → σ (𝒜 i) (kA i)

module _ {X : Type χ}{ι : Level}(ℓ : Level){𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 private aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι
 V-id1 : 𝒦 ⊫ p ≈ q → V ℓ ι 𝒦 ⊫ p ≈ q
 V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
  H-id1{ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)}{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgA)) where
   spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)
   spA = ⨅A , (p⨅A , A≤⨅A)
   spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ p ≈ q
   spK⊧pq = S-id1{ℓ = aℓι}{p = p}{q} (P-id1{ℓ = ℓ} {𝒦 = 𝒦}{p = p}{q} σ)
```



### <a id="free-algebras">Free Algebras</a>

#### <a id="the-absolutely-free-algebra">The absolutely free algebra</a>
 <!-- {#the-absolutely-free-algebra .unnumbered} -->

The term algebra `𝑻 X` is the *absolutely free* `𝑆`-algebra over `X`.
That is, for every `𝑆`-algebra `𝑨`, the following hold.
* Every function from `X` to `𝕌[ 𝑨 ]` lifts to a homomorphism from `𝑻 X` to `𝑨`.
* That homomorphism is unique.
Here we formalize the first of these properties by defining the lifting function `free-lift`
and its setoid analog `free-lift-func`, and then proving the latter is a homomorphism.
(For the proof of uniqueness, see the `Setoid.Terms.Properties` module of the [agda-algebras][] library.)


```agda


module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(h : X → 𝕌[ 𝑨 ]) where
 free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x)       = h x
 free-lift (node f t)  = (f ̂ 𝑨) λ i → free-lift (t i)

 free-lift-func : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( reflexive to reflexiveᴬ )
  flcong : ∀ {s t} → s ≃ t → free-lift s ≈ free-lift t
  flcong (_≃_.rfl x) = reflexiveᴬ (≡.cong h x)
  flcong (_≃_.gnl x) = cong (Interp 𝑨) (≡.refl , λ i → flcong (x i))

 lift-hom : hom (𝑻 X) 𝑨
 lift-hom = free-lift-func ,
   mkhom λ{_}{a} → cong (Interp 𝑨) (≡.refl , λ i → (cong free-lift-func){a i} ≃-isRefl)
```


It turns out that the interpretation of a term `p` in an environment `η` is the same
as the free lift of `η` evaluated at `p`. We apply this fact a number of times in the sequel.


```agda


module _  {X : Type χ} {𝑨 : Algebra α ρᵃ}   where
 open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; refl )
 open Environment 𝑨  using ( ⟦_⟧ )

 free-lift-interp : (η : X → 𝕌[ 𝑨 ])(p : Term X) → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p
 free-lift-interp η (ℊ x)       = refl
 free-lift-interp η (node f t)  = cong (Interp 𝑨) (≡.refl , (free-lift-interp η) ∘ t)
```


#### <a id="the-relatively-free-algebra">The relatively free algebra</a>
 <!-- {#the-relatively-free-algebra .unnumbered} -->

Given an arbitrary class `𝒦` of `𝑆`-algebras, we cannot expect that `𝑻 X` belongs to `𝒦`.
Indeed, there may be no free algebra in `𝒦`.
Nonetheless, it is always possible to construct an algebra that is free for `𝒦` and belongs to the class `S (P 𝒦`).
Such an algebra is called a *relatively free algebra over* `X` (relative to `𝒦`).
There are several informal approaches to defining this algebra.
We now describe the approach on which our formal construction is based and then we present the formalization.

Let `𝔽[ X ]` denote the relatively free algebra over `X`.  We represent `𝔽[ X ]` as the quotient `𝑻 X / ≈` where `x ≈ y` if and only if `h x = h y` for every homomorphism `h` from `𝑻 X` into a member of `𝒦`.
More precisely, if `𝑨 ∈ 𝒦` and `h : hom (𝑻 X) 𝑨`, then `h` factors as `𝑻 X → HomIm h  → 𝑨` and `𝑻 X / ker h ≅ HomIm h ≤ 𝑨`; that is, `𝑻 X / ker h` is (isomorphic to) an algebra in `S 𝒦`. Letting

`≈ := ⋂ \{θ ∈ Con(𝑻 X) ∣ 𝑻 X / θ ∈ S 𝒦\}`,

observe that `𝔽[ X ] := 𝑻 X / ≈` is a subdirect product of the algebras `𝑻 X / ker h`
as `h` ranges over all homomorphisms from `𝑻 X` to algebras in `𝒦`.  Thus, `𝔽[ X ] ∈ P (S 𝒦) ⊆ S (P 𝒦)`.
As we have seen, every map `ρ : X → 𝕌[ 𝑨 ]` extends uniquely to a homomorphism `h : hom (𝑻 X) 𝑨` and `h`
factors through the natural projection `𝑻 X → 𝔽[ X ]` (since `≈ ⊆ ker h`) yielding a unique homomorphism from `𝔽[ X ]` to `𝑨` extending `ρ`.

In [Agda][] we construct `𝔽[ X ]` as a homomorphic image of `𝑻 X` in the following way.
First, given `X` we define `𝑪` as the product of pairs `(𝑨, ρ)` of
algebras `𝑨 ∈ 𝒦` along with environments `ρ : X → 𝕌[ 𝑨 ]`.
To do so, we contrive an index type for the product; each index is a triple `(𝑨, p, ρ)` where `𝑨` is an algebra, `p` is proof of `𝑨 ∈ 𝒦`, and `ρ : X → 𝕌[ 𝑨 ]` is an arbitrary environment.


```agda


module FreeAlgebra (𝒦 : Pred (Algebra α ρᵃ) ℓ) where
 private c = α ⊔ ρᵃ ; ι = ov c ⊔ ℓ
 ℑ : {χ : Level} → Type χ → Type (ι ⊔ χ)
 ℑ X = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × (X → 𝕌[ 𝑨 ])

 𝑪 : {χ : Level} → Type χ → Algebra (ι ⊔ χ)(ι ⊔ χ)
 𝑪 X = ⨅ {I = ℑ X} ∣_∣
```

We then define `𝔽[ X ]` to be the image of a homomorphism from `𝑻 X` to `𝑪` as follows.


```agda


 homC : (X : Type χ) → hom (𝑻 X) (𝑪 X)
 homC X = ⨅-hom-co _ (λ i → lift-hom (snd ∥ i ∥))

 𝔽[_] : {χ : Level} → Type χ → Algebra (ov χ) (ι ⊔ χ)
 𝔽[ X ] = HomIm (homC X)
```

Observe that if the identity `p ≈ q` holds in all `𝑨 ∈ 𝒦` (for all environments), then `p ≈ q` holds in `𝔽[ X ]`; equivalently, the pair `(p , q)` belongs to the kernel of the natural homomorphism from `𝑻 X` onto `𝔽[ X ]`. This natural epimorphism from `𝑻 X` onto `𝔽[ X ]`
is defined as follows.


```agda


module FreeHom {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ; ι = ov c ⊔ ℓ
 open FreeAlgebra 𝒦 using ( 𝔽[_] ; homC )

 epiF[_] : (X : Type c) → epi (𝑻 X) 𝔽[ X ]
 epiF[ X ] = ∣ toHomIm (homC X) ∣ , record  { isHom = ∥ toHomIm (homC X) ∥
                                            ; isSurjective = toIm-surj ∣ homC X ∣ }

 homF[_] : (X : Type c) → hom (𝑻 X) 𝔽[ X ]
 homF[ X ] = IsEpi.HomReduct ∥ epiF[ X ] ∥
```


Before formalizing the HSP theorem in the next section, we need to prove the following important property of the relatively free algebra: For every algebra `𝑨`, if `𝑨 ⊨ Th (V 𝒦)`,
then there exists an epimorphism from `𝔽[ A ]` onto `𝑨`, where `A` denotes the carrier of `𝑨`.


```agda


module _ {𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ)(α ⊔ ρᵃ ⊔ ℓ)}{𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c
 open FreeAlgebra 𝒦 using ( 𝔽[_] ; 𝑪 )
 open Setoid 𝔻[ 𝑨 ] using ( refl ; sym ; trans ) renaming ( Carrier to A ; _≈_ to _≈ᴬ_ )

 F-ModTh-epi : 𝑨 ∈ Mod (Th 𝒦) → epi 𝔽[ A ]  𝑨
 F-ModTh-epi A∈ModThK = φ , isEpi where

  φ : 𝔻[ 𝔽[ A ] ] ⟶ 𝔻[ 𝑨 ]
  _⟨$⟩_ φ            = free-lift{𝑨 = 𝑨} id
  cong φ {p} {q} pq  = Goal
   where
   lift-pq : (p , q) ∈ Th 𝒦
   lift-pq 𝑩 x ρ = begin
    ⟦ p ⟧ ⟨$⟩ ρ    ≈⟨ free-lift-interp {𝑨 = 𝑩} ρ p  ⟩
    free-lift ρ p  ≈⟨ pq (𝑩 , x , ρ)                ⟩
    free-lift ρ q  ≈˘⟨ free-lift-interp{𝑨 = 𝑩} ρ q  ⟩
    ⟦ q ⟧ ⟨$⟩ ρ    ∎
     where open SetoidReasoning 𝔻[ 𝑩 ] ; open Environment 𝑩 using ( ⟦_⟧ )

   Goal : free-lift id p ≈ᴬ free-lift id q
   Goal = begin
    free-lift id p  ≈˘⟨ free-lift-interp {𝑨 = 𝑨} id p   ⟩
    ⟦ p ⟧ ⟨$⟩ id    ≈⟨ A∈ModThK {p = p} {q} lift-pq id  ⟩
    ⟦ q ⟧ ⟨$⟩ id    ≈⟨ free-lift-interp {𝑨 = 𝑨} id q    ⟩
    free-lift id q  ∎
     where open SetoidReasoning 𝔻[ 𝑨 ] ; open Environment 𝑨 using ( ⟦_⟧ )

  isEpi : IsEpi 𝔽[ A ] 𝑨 φ
  isEpi = record { isHom = mkhom refl ; isSurjective = eq (ℊ _) refl }

 F-ModThV-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ]  𝑨
 F-ModThV-epi A∈ModThVK = F-ModTh-epi λ {p}{q} → Goal {p}{q}
  where
  Goal : 𝑨 ∈ Mod (Th 𝒦)
  Goal {p}{q} x ρ = A∈ModThVK{p}{q} (V-id1 ℓ {p = p}{q} x) ρ
```

Actually, we will need the following lifted version of this result.


```agda


 F-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
 F-ModTh-epi-lift A∈ModThK = ∘-epi (F-ModThV-epi λ {p q} → A∈ModThK{p = p}{q} ) ToLift-epi
```



### <a id="birkhoffs-variety-theorem">Birkhoff's Variety Theorem</a>

Let `𝒦` be a class of algebras and recall that `𝒦` is a *variety* provided
it is closed under homomorphisms, subalgebras and products; equivalently,
`V 𝒦 ⊆ 𝒦`.
(Observe that `𝒦 ⊆ V 𝒦` holds for all `𝒦` since `V` is a closure operator.)
We call `𝒦` an *equational class* if it is the class of all models of some set of identities.

Birkhoff's variety theorem, also known as the HSP theorem, asserts that `𝒦` is an equational class if and only if it is a variety.  In this section, we present the statement and proof of this theorem---first in a style similar to what one finds in textbooks (e.g., [@Bergman:2012 Theorem 4.41]), and then formally in the language of [MLTT][].


#### <a id="informal-proof">Informal proof</a>
 <!-- {#informal-proof .unnumbered} -->

(⇒) *Every equational class is a variety*. Indeed, suppose `𝒦` is an equational class axiomatized by term identities `ℰ`; that is, `𝑨 ∈ 𝒦` iff `𝑨 ⊨ ℰ`. Since the classes `H 𝒦`, `S 𝒦`, `P 𝒦` and `𝒦` all satisfy the same set of equations, we have `V 𝒦 ⊫ p ≈ q` for all `(p , q) ∈ ℰ`, so `V 𝒦 ⊆ 𝒦`.

(⇐) *Every variety is an equational class*.[^10] Let `𝒦` be an arbitrary variety.  We will describe a set of equations that axiomatizes `𝒦`.  A natural choice is to take `Th 𝒦` and try to prove that `𝒦 = Mod (Th 𝒦)`. Clearly, `𝒦 ⊆ Mod (Th 𝒦)`.  To prove the converse inclusion, let `𝑨 ∈ Mod (Th 𝒦)`. It suffices to find an algebra `𝑭 ∈ S (P 𝒦)` such that `𝑨` is a homomorphic image of `𝑭`, as this will show that `𝑨 ∈ H (S (P 𝒦)) = 𝒦`.

Let `X` be such that there exists a surjective environment `ρ : X → 𝕌[ 𝑨 ]`.[^11]
By the `lift-hom` lemma, there is an epimorphism `h : 𝑻 X → 𝕌[ 𝑨 ]` that extends `ρ`. Put  `𝔽[ X ] := 𝑻 X / ≈` and let `g : 𝑻 X  → 𝔽[ X ]` be the natural epimorphism with kernel `≈`. We claim `ker g ⊆ ker h`. 
If the claim is true, then there is a map `f : 𝔽[ X ] → 𝑨` such that `f ∘ g = h`, and since `h`
is surjective so is `f`. Therefore, `𝑨 ∈ 𝖧 (𝔽[ X ]) ⊆ Mod (Th 𝒦)` completing the proof.

It remains to prove the claim `ker g ⊆ ker h`. Let `u`, `v` be terms and assume `g u = g v`. Since `𝑻 X` is generated by `X`, there are terms `p`, `q` such that `u = ⟦ 𝑻 X ⟧ p` and `v = ⟦ 𝑻 X ⟧ q`.[^12]
Therefore, `⟦ 𝔽[ X ] ⟧ p = g (⟦ 𝑻 X ⟧ p) = g u = g v = g (⟦ 𝑻 X ⟧ q) = ⟦ 𝔽[ X ]⟧ q`,
so `𝒦 ⊫ p ≈ q`; thus, `(p , q) ∈ Th 𝒦`. Since `𝑨 ∈ Mod (Th 𝒦)`, we obtain `𝑨 ⊧ p ≈ q`, which implies
that `h u = (⟦ 𝑨 ⟧ p) ⟨$⟩ ρ = (⟦ 𝑨 ⟧ q) ⟨$⟩ ρ = h v`, as desired.

#### <a id="formal-proof">Formal proof</a>
 <!-- {#formal-proof .unnumbered} -->

(⇒) *Every equational class is a variety*.
We need an arbitrary equational class, which we obtain by starting with an arbitrary collection `ℰ` of equations and then defining `𝒦 = Mod ℰ`, the class axiomatized by `ℰ`. We prove that `𝒦` is a variety by showing that `𝒦 = V 𝒦`. The inclusion `𝒦 ⊆ V 𝒦`, which holds for all classes `𝒦`, is called the *expansive* property of `V`.


```agda


module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)) where
 V-expa : 𝒦 ⊆ V ℓ (ov (α ⊔ ρᵃ ⊔ ℓ)) 𝒦
 V-expa {x = 𝑨}kA = 𝑨 , (𝑨 , (⊤ , (λ _ → 𝑨), (λ _ → kA), Goal), ≤-reflexive), IdHomImage
  where
  open Setoid 𝔻[ 𝑨 ]            using ( refl )
  open Setoid 𝔻[ ⨅ (λ _ → 𝑨) ]  using () renaming ( refl to refl⨅ )
  to⨅    : 𝔻[ 𝑨 ]            ⟶ 𝔻[ ⨅ (λ _ → 𝑨) ]
  to⨅    = record { to = λ x _ → x   ; cong = λ xy _ → xy }
  from⨅  : 𝔻[ ⨅ (λ _ → 𝑨) ]  ⟶ 𝔻[ 𝑨 ]
  from⨅  = record { to = λ x → x tt  ; cong = λ xy → xy tt }
  Goal   : 𝑨 ≅ ⨅ (λ x → 𝑨)
  Goal   = mkiso (to⨅ , mkhom refl⨅) (from⨅ , mkhom refl) (λ _ _ → refl) (λ _ → refl)
```

Observe how `𝑨` is expressed as (isomorphic to) a product with just one factor (itself), that is, the product
`⨅ (λ x → 𝑨)` indexed over the one-element type `⊤`.

For the inclusion `V 𝒦 ⊆ 𝒦`, recall lemma `V-id1` which asserts that `𝒦 ⊫ p ≈ q` implies
`V ℓ ι 𝒦 ⊫ p ≈ q`; whence, if `𝒦` is an equational class, then `V 𝒦 ⊆ 𝒦`, as we now confirm.


```agda


module _ {ℓ : Level}{X : Type ℓ}{ℰ : {Y : Type ℓ} → Pred (Term Y × Term Y) (ov ℓ)} where
 private 𝒦 = Mod{α = ℓ}{ℓ}{X} ℰ     -- an arbitrary equational class

 EqCl⇒Var : V ℓ (ov ℓ) 𝒦 ⊆ 𝒦
 EqCl⇒Var {𝑨} vA {p} {q} pℰq ρ = V-id1 ℓ {𝒦} {p} {q} (λ _ x τ → x pℰq τ) 𝑨 vA ρ
```

By `V-expa` and `Eqcl⇒Var`, every equational class is a variety.

(⇐) *Every variety is an equational class*.
To fix an arbitrary variety, start with an arbitrary class `𝒦` of `𝑆`-algebras and take the *varietal closure*, `V 𝒦`. We prove that `V 𝒦` is precisely the collection of algebras that model `Th (V 𝒦)`; that is, `V 𝒦 = Mod (Th (V 𝒦))`.  The inclusion `V 𝒦 ⊆ Mod (Th (V 𝒦))` is a consequence of the fact that `Mod Th` is a closure operator.


```agda


module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 ModTh-closure : V{β = β}{ρᵇ}{γ}{ρᶜ}{δ}{ρᵈ} ℓ ι 𝒦 ⊆ Mod{X = X} (Th (V ℓ ι 𝒦))
 ModTh-closure {x = 𝑨} vA {p} {q} x ρ = x 𝑨 vA ρ
```


Our proof of the inclusion `Mod( Th( V 𝒦)) ⊆ V 𝒦` is carried out in two steps.

* Prove  `𝔽[ X ] ≤ 𝑪 X`.
* Prove that every algebra in `Mod (Th (V 𝒦))` is a homomorphic image of `𝔽[ X ]`.

From the first item we have `𝔽[ X ] ∈ S( P 𝒦))`, since `𝑪 X` is a product of algebras in `𝒦`. From this and the second item will follow `Mod (Th (V 𝒦)) ⊆ H (S (P 𝒦))` (= `V 𝒦`), as desired.

To prove `𝔽[ X ] ≤ 𝑪 X`, we construct a homomorphism from `𝔽[ X ]` to `𝑪 X` and then show it is injective,
so `𝔽[ X ]` is (isomorphic to) a subalgebra of `𝑪 X`.


```agda


 open FreeHom {ℓ = ℓ}{𝒦}
 open FreeAlgebra 𝒦 using (homC ;  𝔽[_] ; 𝑪 )
 homFC : hom 𝔽[ X ] (𝑪 X)
 homFC = fromHomIm (homC X)

 monFC : mon 𝔽[ X ] (𝑪 X)
 monFC = ∣ homFC ∣ , record { isHom = ∥ homFC ∥
                            ; isInjective =  λ {x}{y}→ fromIm-inj ∣ homC X ∣ {x}{y}   }
 F≤C : 𝔽[ X ] ≤ 𝑪 X
 F≤C = mon→≤ monFC

 open FreeAlgebra 𝒦 using ( ℑ )

 SPF : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SPF = 𝑪 X , ((ℑ X) , (∣_∣ , ((λ i → fst ∥ i ∥) , ≅-refl))) ,  F≤C
```


Next we prove that every algebra in `Mod (Th (V 𝒦))` is a homomorphic image of `𝔽[ X ]`. Indeed,


```agda


module _ {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 Var⇒EqCl : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Var⇒EqCl 𝑨 ModThA = 𝔽[ 𝕌[ 𝑨 ] ] , (SPF{ℓ = ℓ} 𝒦 , Aim)
  where
  open FreeAlgebra 𝒦 using ( 𝔽[_] )
  epiFlA : epi 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 ι ι)
  epiFlA = F-ModTh-epi-lift{ℓ = ℓ} λ {p q} → ModThA{p = p}{q}

  φ : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  φ = epi→ontohom 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 ι ι) epiFlA

  Aim : 𝑨 IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  Aim = ∘-hom ∣ φ ∣(from Lift-≅), ∘-IsSurjective _ _ ∥ φ ∥(fromIsSurjective(Lift-≅{𝑨 = 𝑨}))
```

By `ModTh-closure` and `Var⇒EqCl`, we have `V 𝒦 = Mod (Th (V 𝒦))` for every class `𝒦` of `𝑆`-algebras.
Thus, every variety is an equational class.

This completes the formal proof of Birkhoff's variety theorem. ∎

### <a id="discussion">Discussion</a>
 <!-- {#sec:discussion} -->


How do we differ from the classical, set-theoretic approach? Most noticeable is our avoidance of all *size* issues. By using universe levels and level polymorphism, we always make sure we are in a *large enough* universe. So we can easily talk about "all algebras such that..." because these are always taken from a bounded (but arbitrary) universe.

Our use of setoids introduces nothing new: all the equivalence relations we use were already present in the classical proofs. The only "new" material is that we have to prove that functions respect those equivalences.

Our first attempt to formalize Birkhoff's theorem was not sufficiently careful in its handling of variable symbols `X`. Specifically, this type was unconstrained; it is meant to represent the informal notion of a "sufficiently large" collection of variable symbols. Consequently, we postulated surjections from `X` onto the domains of all algebras in the class under consideration. But then, given a signature `𝑺` and a one-element `𝑆`-algebra `𝑨`, by choosing `X` to be the empty type `⊥`, our surjectivity postulate gives a map from `⊥` onto the singleton domain of `𝑨`. (For details, see the [Demos.ContraX](https://github.com/ualib/agda-algebras/blob/master/src/Demos/ContraX.lagda) module which constructs the counterexample in [Agda][].)

### <a id="related-work">Related work</a>

There have been a number of efforts to formalize parts of universal algebra in type theory besides ours. The Coq proof assistant, based on the Calculus of Inductive Constructions, was used by Capretta, in [@Capretta:1999], and Spitters and Van der Weegen, in [@Spitters:2011], to formalized the basics of universal algebra and some classical algebraic structures. In [@Gunther:2018] Gunther et al developed what seemed (prior to the library) the most extensive libraryof formalized universal algebra to date. Like , [@Gunther:2018] is based on dependent type theory, is programmed in , and goes beyond the basic isomorphism theorems to include some equational logic. Although their coverage is less extensive than that of , Gunther et al do treat *multi-sorted* algebras, whereas is currently limited to single-sorted structures.

As noted by Abel [@Abel:2021], Amato et al, in [@Amato:2021], have formalized multi-sorted algebras with finitary operators in UniMath. The restriction to finitary operations was due to limitations of the UniMath type theory, which does not have W-types nor user-defined inductive types. Abel also notes that Lynge and Spitters, in [@Lynge:2019], formalize multi-sorted algebras with finitary operators in *Homotopy type theory* ([@HoTT]) using Coq. HoTT's higher inductive types enable them to define quotients as types, without the need for setoids. Lynge and Spitters prove three isomorphism theorems concerning subalgebras and quotient algebras, but do not formalize universal algebras nor varieties. Finally, in [@Abel:2021], Abel gives a new formal proof of the soundness and completeness theorem for multi-sorted algebraic structures.

-----------------------------------

### <a id="footnotes">Footnotes</a>

[^1]: An alternative formalization based on classical set-theory was achieved in [@birkhoff-in-mizar:1999].

[^2]: See the [[Birkhoff.lagda]{.sans-serif}](https://github.com/ualib/ualib.github.io/blob/71f173858701398d56224dd79d152c380c0c2b5e/src/lagda/UALib/Birkhoff.lagda) file in the [[ualib/ualib.gitlab.io]{.sans-serif}](https://github.com/ualib/ualib.github.io) repository ([15 Jan 2021 commit 71f1738](https://github.com/ualib/ualib.github.io/commit/71f173858701398d56224dd79d152c380c0c2b5e)) [@ualib_v1.0.0].

[^3]: [[src/Demos/HSP.lagda]{.sans-serif}](https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda) in the [agda-algebras][] repository: [[github.com/ualib/agda-algebras]{.sans-serif}](https://github.com/ualib/agda-algebras).

[^4]: the axiom asserting that two point-wise equal functions are equal

[^5]: All submodules of the module in the library are also fully constructive in this sense.

[^6]: The code in this paragraph was suggested by an anonymous referee.

[^7]: `suc ℓ` denotes the successor of `ℓ` in the universe hierarchy.

[^8]: The definition of was provided by an anonymous referee; it is indeed simpler than trying to apply the general `HomFactor` theorem found in the [agda-algebras][] library.

[^9]: Some authors reserve the term for a *deductively closed* set of equations, that is, a set of equations that is closed under entailment.

[^10]: The proof we present here is based on [@Bergman:2012 Theorem 4.41].

[^11]: Informally, this is done by assuming `X` has cardinality at least `max(| 𝕌[ 𝑨 ] |, ω)`. Later we will see how to construct an `X` with the required property in type theory.

[^12]: `⟦ 𝑨 ⟧ t` denotes the interpretation of the term `t` in the algebra `𝑨`.


{% include UALib.Links.md %}

