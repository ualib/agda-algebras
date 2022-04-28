---
layout: default
title : "Base.Algebras.Basic module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---

### <a id="basic-definitions">Basic definitions</a>

This is the [Base.Algebras.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Algebras.Basic where

-- Imports from the Agda (Builtin) and the Agda Standard Library -----------------------
open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to  Type ; lzero to ℓ₀ )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax )
open import Level           using ( Level )
open import Relation.Binary using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Unary  using ( _∈_ ; Pred )


-- Imports from the Agda Universal Algebra Library -------------------------------------
open import Base.Overture.Preliminaries using ( ∣_∣ ; ∥_∥ )
open import Base.Relations.Discrete     using ( Op ; _|:_ ; _|:pred_ )
open import Base.Relations.Continuous   using ( Rel ; compatible-Rel ; REL ; compatible-REL )

private variable α β ρ : Level

variable 𝓞 𝓥 : Level

\end{code}

The variables `𝓞` and `𝓥` are not private since, as mentioned earlier, throughout the [agda-algebras](https://github.com/ualib/agda-algebras) library `𝓞` denotes the universe level of *operation symbol* types, while `𝓥` denotes the universe level of *arity* types.


#### <a id="signatures-of-an-algebra">Signatures of an algebra</a>

In [model theory](https://en.wikipedia.org/wiki/Model_theory), the *signature* `𝑆 = (𝐶, 𝐹, 𝑅, ρ)` of a structure consists of three (possibly empty) sets `𝐶`, `𝐹`, and `𝑅`---called *constant symbols*, *function symbols*, and *relation symbols*, respectively---along with a function `ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁` that assigns an *arity* to each symbol. Often (but not always) `𝑁 = ℕ`, the natural numbers.

As our focus here is universal algebra, we are more concerned with the restricted notion of an *algebraic signature* (or *signature* for algebraic structures), by which we mean a pair `𝑆 = (𝐹, ρ)` consisting of a collection `𝐹` of *operation symbols* and an *arity function* `ρ : 𝐹 → 𝑁` that maps each operation symbol to its arity; here, 𝑁 denotes the *arity type*. Heuristically, the arity `ρ 𝑓` of an operation symbol `𝑓 ∈ 𝐹` may be thought of as the "number of arguments" that `𝑓` takes as "input".

If the arity of `𝑓` is `n`, then we call `𝑓` an `n`-*ary* operation symbol.  In case `n` is 0 (or 1 or 2 or 3, respectively) we call the function *nullary* (or *unary* or *binary* or *ternary*, respectively).

If `A` is a set and `𝑓` is a (`ρ 𝑓`)-ary operation on `A`, we often indicate this by writing `𝑓 : A`<sup>ρ 𝑓</sup> `→ A`. On the other hand, the arguments of such an operation form a (`ρ 𝑓`)-tuple, say, `(a 0, a 1, …, a (ρf-1))`, which may be viewed as the graph of the function `a : ρ𝑓 → A`. When the codomain of `ρ` is `ℕ`, we may view `ρ 𝑓` as the finite set `{0, 1, …, ρ𝑓 - 1}`. Thus, by identifying the `ρ𝑓`-th power `A`<sup>ρ 𝑓</sup> with the type `ρ 𝑓 → A` of functions from `{0, 1, …, ρ𝑓 - 1}` to `A`, we identify the function type `A`<sup>ρ f</sup> `→ A` with the function (or "functional") type `(ρ𝑓 → A) → A`.

**Example**. Suppose `𝑔 : (m → A) → A` is an `m`-ary operation on `A`, and `a : m → A` is an `m`-tuple on `A`. Then `𝑔 a` may be viewed as `𝑔 (a 0, a 1, …, a (m-1))`, which has type `A`. Suppose further that `𝑓 : (ρ𝑓 → B) → B` is a `ρ𝑓`-ary operation on `B`, let `a : ρ𝑓 → A` be a `ρ𝑓`-tuple on `A`, and let `h : A → B` be a function.  Then the following typing judgments obtain: `h ∘ a : ρ𝑓 → B` and we `𝑓 (h ∘ a) : B`.

#### <a id="signature-type">Signature type</a>

In the [agda-algebras](https://github.com/ualib/agda-algebras) library we represent the *signature* of an algebraic structure using the following type.

\begin{code}

Signature : (𝓞 𝓥 : Level) → Type (lsuc (𝓞 ⊔ 𝓥))
Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)


Level-of-Signature : {𝓞 𝓥 : Level} → Signature 𝓞 𝓥 → Level
Level-of-Signature {𝓞}{𝓥} _ = lsuc (𝓞 ⊔ 𝓥)

\end{code}


In the
[Overture](https://ualib.github.io/agda-algebras/Overture.html)
module of the [agda-algebras](https://github.com/ualib/agda-algebras) library, special syntax is defined for the first and second projections---namely, `∣_∣` and `∥_∥`, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then

* `∣ 𝑆 ∣` denotes the set of operation symbols, and
* `∥ 𝑆 ∥` denotes the arity function.

If `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, then `∥ 𝑆 ∥ 𝑓` is the arity of `𝑓`.



#### <a id="algebras">Algebras</a>

Our first goal is to develop a working vocabulary and formal library for classical (single-sorted, set-based) universal algebra.  In this section we define the main objects of study.  An *algebraic structure* (or *algebra*) in the signature `𝑆 = (𝐹, ρ)` is denoted by `𝑨 = (A, F`<sup>`𝑨`</sup>`)` and consists of

* `A` := a *nonempty* set (or type), called the *domain* (or *carrier* or *universe*) of the algebra;
* `F`<sup>`𝑨`</sup> := `{ f`<sup>`𝑨`</sup>` ∣ f ∈ F, f`<sup>`𝑨`</sup>` : (ρ𝑓 → A) → A }`, a collection of *operations* on `𝐴`;
* a (potentially empty) collection of *identities* satisfied by elements and operations of `𝐴`.

Note that to each operation symbol `𝑓 ∈ 𝐹` corresponds an operation `𝑓`<sup>`𝑨`</sup> on `𝐴` of arity `ρ𝑓`; we call such `𝑓`<sup>`𝑨`</sup> the *interpretation* of the symbol `𝑓` in the algebra `𝑨`. We call an algebra in the signature `𝑆` an `𝑆`-*algebra*.  An algebra is called *finite* if it has a finite domain, and is called *trivial* if its universe is a singleton.  Given two algebras `𝑨` and `𝑩`, we say that `𝑩` is a *reduct* of `𝑨` if both algebras have the same domain and `𝑩` can be obtained from `𝑨` by simply removing some of the operations.

Recall, we defined the type `Signature 𝓞 𝓥` above as the dependent pair type `Σ F ꞉ Type 𝓞 , (F → Type 𝓥)`, and the type `Op` of operation symbols is the function type `Op I A = (I → A) → A` (see [Base.Relations.Discrete][]).

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe level `α`, we define the *type of algebras in the signature* `𝑆` (or *type of* `𝑆`-*algebras*) *with domain type* `Type α` as follows.

\begin{code}

Algebra : (α : Level)(𝑆 : Signature 𝓞 𝓥) → Type (𝓞 ⊔ 𝓥 ⊔ lsuc α)
Algebra α 𝑆 = Σ[ A ∈ Type α ]                   -- the domain
              ∀ (f : ∣ 𝑆 ∣) → Op A (∥ 𝑆 ∥ f)    -- the basic operations

\end{code}

It would be more precise to refer to inhabitants of this type as ∞-*algebras* because their domains can be of arbitrary type and need not be truncated at some level and, in particular, need to be a set. (See [Base.Equality.Truncation][].)

We might take this opportunity to define the type of 0-*algebras*, that is, algebras whose domains are sets, which is probably closer to what most of us think of when doing informal universal algebra.  However, in the [agda-algebras](https://github.com/ualib/agda-algebras) library we will only need to know that the domains of certain algebras are sets in a few places, so it seems preferable to work with general (∞-)algebras throughout and then explicitly postulate additional axioms (e.g., [uniquness of identity proofs](https://ualib.github.io/agda-algebras/Equality.Truncation.html#uniqueness-of-identity-proofs) if and only if necessary.


#### <a id="algebras-as-record-types">Algebras as record types</a>

A popular way to represent algebraic structures in type theory is with record types.  The Sigma type defined above provides an equivalent alternative that we happen to prefer and we use it throughout the library, both for consistency and because of its direct connection to the existential quantifier of logic. Recall that the type `Σ x ꞉ X , P x` represents the proposition, "there exists `x` in `X` such that `P x` holds;" in symbols, `∃ x ∈ X , P x`.  Indeed, an inhabitant of `Σ x ꞉ X , P x` is a pair `(x , p)` such that `x` inhabits `X` and `p` is a proof of `P x`. In other terms, the pair `(x , p)` is a witness and proof of the proposition `∃ x ∈ X , P x`.

Nonetheless, for those who prefer to represent algebraic structures in type theory using records, we offer the following definition (which is equivalent to the Sigma type formulation).

\begin{code}

record algebra (α : Level) (𝑆 : Signature 𝓞 𝓥) : Type(lsuc(𝓞 ⊔ 𝓥 ⊔ α)) where
 constructor mkalg
 field
  carrier : Type α
  opsymbol : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → carrier) → carrier

\end{code}

This representation of algebras as inhabitants of a record type is equivalent to the representation using Sigma types in the sense that a bi-implication between the two representations is obvious.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} where

 open algebra

 algebra→Algebra : algebra α 𝑆 → Algebra α 𝑆
 algebra→Algebra 𝑨 = (carrier 𝑨 , opsymbol 𝑨)

 Algebra→algebra : Algebra α 𝑆 → algebra α 𝑆
 Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥

\end{code}


#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with, so we will use this new notation almost exclusively in the remaining modules of the [agda-algebras][] library.

\begin{code}

 _̂_ : (𝑓 : ∣ 𝑆 ∣)(𝑨 : Algebra α 𝑆) → (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 𝑓 ̂ 𝑨 = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎

\end{code}

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.



#### <a id="the-universe-level-of-an-algebra">The universe level of an algebra</a>

Occasionally we will be given an algebra and we just need to know the universe level of its domain. The following utility function provides this.

\begin{code}

Level-of-Alg : {α 𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α 𝑆 → Level
Level-of-Alg {α = α}{𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥 ⊔ lsuc α

Level-of-Carrier : {α 𝓞 𝓥  : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α 𝑆 → Level
Level-of-Carrier {α = α} _ = α

\end{code}


#### <a id="lifts-of-algebras">Level lifting algebra types</a>

Recall, in the [section on level lifting and lowering](Overture.Lifts.html#level-lifting-and-lowering), we described the difficulties one may encounter when working with a noncumulative universe hierarchy. We made a promise to provide some domain-specific level lifting and level lowering methods. Here we fulfill this promise by supplying a couple of bespoke tools designed specifically for our operation and algebra types.

\begin{code}


open Level

Lift-alg-op : {I : Type 𝓥} {A : Type α} → Op A I → (β : Level) → Op (Lift β A) I
Lift-alg-op f β = λ x → lift (f (λ i → lower (x i)))

Lift-Alg : {𝑆 : Signature 𝓞 𝓥} → Algebra α 𝑆 → (β : Level) → Algebra (α ⊔ β) 𝑆
Lift-Alg {𝑆 = 𝑆} 𝑨 β = Lift β ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → Lift-alg-op (𝑓 ̂ 𝑨) β)


open algebra

Lift-algebra : {𝑆 : Signature 𝓞 𝓥} → algebra α 𝑆 → (β : Level) → algebra (α ⊔ β) 𝑆
Lift-algebra {𝑆 = 𝑆} 𝑨 β = mkalg (Lift β (carrier 𝑨)) (λ (f : ∣ 𝑆 ∣) → Lift-alg-op ((opsymbol 𝑨) f) β)

\end{code}

What makes the `Lift-Alg` type so useful for resolving type level errors involving algebras is the nice properties it possesses.  Indeed, the [agda-algebras][] library contains formal proofs of the following facts.

+ [`Lift-Alg` is a homomorphism](Base.Homomorphisms.Basic.html#exmples-of-homomorphisms) (see [Base.Homomorphisms.Basic][])
+ [`Lift-Alg` is an algebraic invariant](Base.Homomorphisms.Isomorphisms.html#lift-is-an-algebraic-invariant") (see [Base.Homomorphisms.Isomorphisms][])
+ [`Lift-Alg` of a subalgebra is a subalgebra](Base.Subalgebras.Subalgebras.html#lifts-of-subalgebras) (see [Base.Subalgebras.Subalgebras][])
+ [`Lift-Alg` preserves identities](Base.Varieties.EquationalLogic.html#lift-invariance)) (see [Base.Varieties.EquationalLogic][])


#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

We now define the function `compatible` so that, if `𝑨` denotes an algebra and `R` a binary relation, then `compatible 𝑨 R` will represent the assertion that `R` is *compatible* with all basic operations of `𝑨`. The formal definition is immediate since all the work is done by the relation `|:`, which we defined above (see [Base.Relations.Discrete][]).

\begin{code}

compatible : {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra α 𝑆) → BinRel ∣ 𝑨 ∣ ρ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
compatible  𝑨 R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R

compatible-pred : {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra α 𝑆) → Pred (∣ 𝑨 ∣ × ∣ 𝑨 ∣)ρ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
compatible-pred  𝑨 P = ∀ 𝑓 → (𝑓 ̂ 𝑨) |:pred P

\end{code}

Recall, the `|:` type was defined in [Base.Relations.Discrete][] module.


#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations</a>

In the [Base.Relations.Continuous][] module, we defined a function called `compatible-Rel` to represent the assertion that a given continuous relation is compatible with a given operation. With that, it is easy to define a function, which we call `compatible-Rel-alg`, representing compatibility of a continuous relation with all operations of an algebra.  Similarly, we define the analogous `compatible-REL-alg` function for the (even more general) type of *dependent relations*.

\begin{code}

module _ {I : Type 𝓥} {𝑆 : Signature 𝓞 𝓥} where

 compatible-Rel-alg : (𝑨 : Algebra α 𝑆) → Rel ∣ 𝑨 ∣ I{ρ} → Type(𝓞 ⊔ α ⊔ 𝓥 ⊔ ρ)
 compatible-Rel-alg 𝑨 R = ∀ (𝑓 : ∣ 𝑆 ∣ ) →  compatible-Rel (𝑓 ̂ 𝑨) R

 compatible-REL-alg : (𝒜 : I → Algebra α 𝑆) → REL I (λ i → ∣ 𝒜  i ∣) {ρ} → Type(𝓞 ⊔ α ⊔ 𝓥 ⊔ ρ)
 compatible-REL-alg 𝒜 R = ∀ ( 𝑓 : ∣ 𝑆 ∣ ) →  compatible-REL (λ i → 𝑓 ̂ (𝒜 i)) R

\end{code}

-------------------------------------

<span style="float:left;">[↑ Base.Algebras](Base.Algebras.html)</span>
<span style="float:right;">[Base.Algebras.Products →](Base.Algebras.Products.html)</span>

{% include UALib.Links.md %}
