---
layout: default
title : Relations.Discrete module (The Agda Universal Algebra Library)
date : 2021-02-28
author: [the ualib/agda-algebras development team][]
---

### <a id="unary-relations">Discrete Relations</a>

This is the [Relations.Discrete][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- open import Agda.Builtin.Equality using (_≡_)
-- open import Agda.Primitive using (_⊔_; lzero; lsuc; Level)
-- open import Data.Empty using (⊥)
-- open import Data.Sum.Base using (_⊎_)

-- open import Overture.Preliminaries using (Type)

module Relations.Discrete where

open import Agda.Builtin.Equality using    ( _≡_ ; refl     )
open import Agda.Primitive        using    ( _⊔_            )
                                  renaming ( Set  to Type
                                           ; Setω to Typeω  )
open import Level                 using    ( Level          )
                                  renaming ( suc  to lsuc
                                           ; zero to ℓ₀     )
open import Relation.Binary.Core  using    ( _⇒_ ; _=[_]⇒_  )
                                  renaming ( REL  to BinREL ;
                                             Rel  to BinRel )
open import Relation.Unary        using    ( ∅; _∈_; Pred   )
open import Data.Product          using    ( _,_ ; _×_      )

private variable α β ρ 𝓥 : Level

\end{code}

We define convenient notation for asserting that the image of a function (the first argument) is contained in a predicate (the second argument).

\begin{code}

Im_⊆_ : {A : Type α}{B : Type β} → (A → B) → Pred B ρ → Type (α ⊔ ρ)
Im f ⊆ S = ∀ x → f x ∈ S

\end{code}

#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be represented in type theory and Agda in a number of ways, each of which may be useful in a particular context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, or a (unary) predicate type.


\begin{code}

module _ {A : Type α}{B : Type β} where

 ker : (A → B) → BinRel A β
 ker g x y = g x ≡ g y

 kernel : (A → B) → Pred (A × A) β
 kernel g (x , y) = g x ≡ g y

\end{code}

Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be represented as follows.<sup>[2](Relations.Discrete#fn2)</sup>

\begin{code}

module _ {A : Type α } where

 𝟎 : BinRel A α
 𝟎 x y = x ≡ y

\end{code}


#### <a id="operation-type">Operation type and compatibility</a>

**Notation**. For consistency and readability, throughout the [UniversalAlgebra][] library we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

In the next subsection, we will define types that are useful for asserting and proving facts about *compatibility* of *operations* with relations, but first we need a general type with which to represent operations.  Here is the definition, which we justify below.

\begin{code}

--The type of operations
Op : Type 𝓥 → Type α → Type(α ⊔ 𝓥)
Op I A = (I → A) → A

\end{code}

The type `Op` encodes the arity of an operation as an arbitrary type `I : Type 𝓥`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

\begin{code}

π : {I : Type 𝓥 } {A : Type α } → I → Op I A
π i x = x i

\end{code}

Now suppose `A` and `I` are types and let `𝑓 : Op I` and `R : Rel A β` be an `I`-ary operation and a binary relation on `A`, respectively. We say `𝑓` and `R` are *compatible* and we write `𝑓 |: R` just in case `∀ u v : I → A`,

&nbsp;&nbsp; `Π i ꞉ I , R (u i) (v i)` &nbsp; `→` &nbsp; `R (f u) (f v)`.<sup>[6](Relations.Discrete#fn6)</sup>

Here is how we implement this in the [UniversalAlgebra][] library.

\begin{code}

eval-rel : {A : Type α}{I : Type 𝓥} → BinRel A ρ → BinRel (I → A)(𝓥 ⊔ ρ)
eval-rel R u v = ∀ i → R (u i) (v i)

_|:_ : {A : Type α}{I : Type 𝓥} → Op I A → BinRel A ρ → Type(α ⊔ 𝓥 ⊔ ρ)
f |: R  = (eval-rel R) =[ f ]⇒ R

\end{code}

The function `eval-rel` "lifts" a binary relation to the corresponding `I`-ary relation.<sup>[5](Relations.Discrete#fn5)</sup>

In case it helps the reader, we note that instead of using the slick implication notation, we could have defined the `|:` relation more explicitly, like so.

\begin{code}

compatible-op : {A : Type α}{I : Type 𝓥} → (f : Op I A)(R : BinRel A ρ) → Type(α ⊔ 𝓥 ⊔ ρ)
compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

\end{code}

However, this is a rare case in which the more elegant syntax used to define `|:` sometimes results in simpler proofs when applying the definition. (See, for example, `compatible-term` in the [Terms.Operations][] module.)



--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> cf. `Relation/Unary.agda` in the [Agda Standard Library][].</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints** ([agda2-mode][]) `\.=` ↝ `≐`, `\u+` ↝ `⊎`, `\b0` ↝ `𝟘`, `\B0` ↝ `𝟎`.</span>

<sup>3</sup><span class="footnote" id="fn3">Agda also has a `postulate` mechanism that we could use, but this would require omitting the `--safe` pragma from the `OPTIONS` directive at the start of the module.</span>

<sup>4</sup><span class="footnote" id="fn4">The empty type is defined in the `Empty-Type` module of [Type Topology][] as an inductive type with no constructors: `data 𝟘 {α} : Type α where -- (empty body)`</span>

<sup>5</sup><span class="footnote" id="fn5">Initially we called the first function `lift-rel` because it "lifts" a binary relation on `A` to a binary relation on tuples of type `I → A`.  However, we renamed it `eval-rel` to avoid confusion with the universe level `Lift` type defined in the [Overture.Lifts][] module, or with `free-lift` ([Terms.Basic][]) which "lifts" a map defined on generators to a map on the thing being generated.</span>

<sup>6</sup><span class="footnote" id="fn6"> The symbol `|:` we use to denote the compatibility relation comes from Cliff Bergman's universal algebra textbook [Bergman (2012)][].

<br>
<br>

[↑ Relations](Relations.html)
<span style="float:right;">[Relations.Continuous →](Relations.Continuous.html)</span>

{% include UALib.Links.md %}


------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
