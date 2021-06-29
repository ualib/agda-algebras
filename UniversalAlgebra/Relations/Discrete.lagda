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

module Relations.Discrete where

open import Agda.Builtin.Equality using    ( _≡_ ; refl     )
open import Agda.Primitive        using    ( _⊔_            )
                                  renaming ( Set  to Type
                                           ; Setω to Typeω  )
open import Data.Product          using    ( _,_ ; _×_      )
open import Function.Base         using    ( _∘_            )
open import Level                 using    ( Level ; Lift   )
                                  renaming ( suc  to lsuc
                                           ; zero to ℓ₀     )
open import Relation.Binary.Definitions using (Reflexive ; Symmetric ; Transitive )
open import Relation.Binary.Core  using    ( _⇒_ ; _=[_]⇒_  )
                                  renaming ( REL  to BinREL
                                           ; Rel  to BinRel )
open import Relation.Unary        using    ( ∅; _∈_; Pred   )

private variable α β ρ 𝓥 : Level

\end{code}

We define convenient notation for asserting that the image of a function (the first argument) is contained in a predicate (i.e., a "subset" of the codomain---the second argument).

\begin{code}

Im_⊆_ : {A : Type α}{B : Type β} → (A → B) → Pred B ρ → Type (α ⊔ ρ)
Im f ⊆ S = ∀ x → f x ∈ S

\end{code}

#### Operation symbols, unary relations, binary relations

We now define the type of operation symbols of arity `I : Type lzero` over the type `A : Type α`.

We make a type alias called `Arity` so to make it easy to specialize the library later, e.g., by restricting `Arity` to be `Type lzero` (which would relieve us of having to carry the 𝓥 arity universe parameter around).

\begin{code}

Arity : (𝓥 : Level) → Type (lsuc 𝓥)
Arity 𝓥 = Type 𝓥

\end{code}

This is merely for notational convenience, and it's not clear whether it's a real restriction.

(Question: Are there use-cases requiring arities inhabiting higher types?)


The unary relation (or "predicate") type is imported from Relation.Unary of the std lib.

  ```
  Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
  Pred A ℓ = A → Set ℓ
  ```

The binary relation types are called `Rel` and `REL` in the standard library, but we
will call them `BinRel` and `BinREL` and reserve the names `Rel` and `REL` for the more
general types of relations we define below and in the Relations.Continuous module.

The heterogeneous binary relation type is imported from the standard library and renamed BinREL.

  ```
  BinREL : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  BinREL A B ℓ' = A → B → Type ℓ'
  ```

The homogeneous binary relation type is imported from the standard library and renamed BinRel.

  ```
  BinRel : ∀{ℓ} → Type ℓ → (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
  BinRel A ℓ' = REL A A ℓ'
  ```


#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be represented in type theory and Agda in a number of ways, each of which may be useful in a particular context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, or a (unary) predicate type.

\begin{code}

module _ {A : Type α}{B : Type β} where

 ker : (A → B) → BinRel A β
 ker g x y = g x ≡ g y

 kerlift : (A → B) → (ρ : Level) → BinRel A (β ⊔ ρ)
 kerlift g ρ x y = Lift ρ (g x ≡ g y)

 ker' : (A → B) → (I : Arity 𝓥) → BinRel (I → A) (β ⊔ 𝓥)
 ker' g I x y = g ∘ x ≡ g ∘ y

 kernel : (A → B) → Pred (A × A) β
 kernel g (x , y) = g x ≡ g y

\end{code}

The *identity relation* (which is equivalent to the kernel of an injective function) can be represented as follows.<sup>[2](Relations.Discrete#fn2)</sup>

\begin{code}

0[_] : (A : Type α) → {ρ : Level} → BinRel A (α ⊔ ρ)
0[ A ] {ρ} = λ x y → Lift ρ (x ≡ y)

\end{code}

#### Subset containment relation for binary realtions

\begin{code}

module _ {α ρ : Level}{A : Type (α ⊔ ρ)} where

 _⊑_ : BinRel A ρ → BinRel A ρ → Type (α ⊔ ρ)
 P ⊑ Q = ∀ x y → P x y → Q x y

 ⊑-refl : Reflexive _⊑_
 ⊑-refl = λ _ _ z → z

 ⊑-trans : Transitive _⊑_
 ⊑-trans P⊑Q Q⊑R x y Pxy = Q⊑R x y (P⊑Q x y Pxy)

\end{code}


#### <a id="operation-type">Operation type and compatibility</a>

**Notation**. For consistency and readability, throughout the [UniversalAlgebra][] library we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

In the next subsection, we will define types that are useful for asserting and proving facts about *compatibility* of *operations* with relations, but first we need a general type with which to represent operations.  Here is the definition, which we justify below.

The type `Op` encodes the arity of an operation as an arbitrary type `I : Type 𝓥`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

\begin{code}

-- OLD implementation of the type of operations
-- Op : Type 𝓥 → Type α → Type(α ⊔ 𝓥)
-- Op I A = (I → A) → A

-- π : {I : Type 𝓥 } {A : Type α } → I → Op I A
-- π i x = x i

-- New notation for operations on A of arity I
Op : Type α → Arity 𝓥 → Type (α ⊔ 𝓥)
Op A I = (I → A) → A

-- Example (projections)
π : {I : Arity 𝓥} {A : Type α } → I → Op A I
π i x = x i

\end{code}

Now suppose `A` and `I` are types and let `𝑓 : Op I` and `R : Rel A β` be an `I`-ary operation and a binary relation on `A`, respectively. We say `𝑓` and `R` are *compatible* and we write `𝑓 |: R` just in case `∀ u v : I → A`,

`Π i ꞉ I , R (u i) (v i)  →  R (f u) (f v)`.<sup>[6](Relations.Discrete#fn6)</sup>

Here is how we implement this in the [UniversalAlgebra][] library.

\begin{code}

-- OLD implementation:
--    eval-rel : {A : Type α}{I : Type 𝓥} → BinRel A ρ → BinRel (I → A)(𝓥 ⊔ ρ)
--    eval-rel R u v = ∀ i → R (u i) (v i)

-- NEW implementation:

{-Compatibility of binary relations.
  We now define the function `compatible` so that, if `𝑩` denotes a structure and `r` a binary
  relation, then `compatible 𝑩 r` will represent the assertion that `r` is *compatible* with all
  basic operations of `𝑩`. in the following sense:
  `∀ 𝑓 : ∣ 𝐹 ∣ → ∀(x y : ∥ 𝐹 ∥ 𝑓 → ∣ 𝑩 ∣) → (∀ i → r (x i)(y i)) → r (f x)(f y)` -}

eval-rel : {A : Type α}{I : Arity 𝓥} → BinRel A ρ → BinRel (I → A) (𝓥 ⊔ ρ)
eval-rel R u v = ∀ i → R (u i) (v i)

eval-pred : {A : Type α}{I : Arity 𝓥} → Pred (A × A) ρ → BinRel (I → A) (𝓥 ⊔ ρ)
eval-pred P u v = ∀ i → (u i , v i) ∈ P


\end{code}

The function `eval-rel` "lifts" a binary relation to the corresponding `I`-ary relation.<sup>[5](Relations.Discrete#fn5)</sup>

\begin{code}

-- OLD implementation:
--
--    compatible-op : {A : Type α}{I : Type 𝓥} → (f : Op I A)(R : BinRel A ρ) → Type(α ⊔ 𝓥 ⊔ ρ)
--    compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)
--
--    -- Fancy notation for compatible-op.
--    _|:_ : {A : Type α}{I : Type 𝓥} → Op I A → BinRel A ρ → Type(α ⊔ 𝓥 ⊔ ρ)
--    f |: R  = (eval-rel R) =[ f ]⇒ R
--
-- NEW implementation:

_preserves_ : {A : Type α}{I : Arity 𝓥} → Op A I → BinRel A ρ → Type (α ⊔ 𝓥 ⊔ ρ)
f preserves R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

_preserves-pred_ : {A : Type α}{I : Arity 𝓥} → Op A I → Pred ( A × A ) ρ → Type (α ⊔ 𝓥 ⊔ ρ)
f preserves-pred P  = ∀ u v → (eval-pred P) u v → (f u , f v) ∈ P

--shorthand notation for preserves, defined using the fancy implication notation from the std lib.
_|:_ : {A : Type α}{I : Arity 𝓥} → Op A I → BinRel A ρ → Type (α ⊔ 𝓥 ⊔ ρ)
f |: R  = (eval-rel R) =[ f ]⇒ R

--shorthand notation for preserves, defined using the fancy implication notation from the std lib.
_|:pred_ : {A : Type α}{I : Arity 𝓥} → Op A I → Pred (A × A) ρ → Type (α ⊔ 𝓥 ⊔ ρ)
f |:pred P  = (eval-pred P) =[ f ]⇒ λ x y → (x , y) ∈ P

\end{code}

These two types just defined are logically equivalent, as we now prove.

\begin{code}

compatibility-agreement : {A : Type α}{I : Arity 𝓥}{f : Op A I}{R : BinRel A ρ}
 →            f preserves R → f |: R
compatibility-agreement {f = f}{R} c {x}{y} Rxy = c x y Rxy

compatibility-agreement' : {A : Type α}{I : Arity 𝓥}{f : Op A I}{R : BinRel A ρ}
 →             f |: R → f preserves R
compatibility-agreement' {f = f}{R} c = λ u v x → c x

\end{code}

However, in this case the more elegant syntax used to define `|:` can result in simpler proofs. (See, for example, `compatible-term` in the [Terms.Operations][] module.)

The following function returns the arity of a given operation symbol, which is sometimes useful.

\begin{code}

arity[_] : {I : Arity 𝓥} {A : Type α } → Op A I → Arity 𝓥
arity[_] {I = I} f = I

\end{code}












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
