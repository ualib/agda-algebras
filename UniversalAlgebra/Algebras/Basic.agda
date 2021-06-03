{-
layout: default
title : Algebras.Basic module (Agda Universal Algebra Library)
date : 2021-04-23
author: [agda-algebras development team][]
-}

-- Basic Definitions
-- =================
--
-- This is the [Algebras.Basic][] module of the [Agda Universal Algebra Library][].

{-# OPTIONS --without-K --exact-split --safe #-}

module Algebras.Basic where

open import stdlib-imports

open import Overture.Preliminaries using (∣_∣; ∥_∥)
open import Relations.Continuous using (ContRel; DepRel; cont-compatible-op; dep-compatible-op)
open import Relations.Discrete using (Op; _|:_)


private variable 𝓞 𝓤 𝓥 𝓦 : Level

-- The signatures of an algebra
-- ----------------------------
-- In [model theory](https://en.wikipedia.org/wiki/Model_theory), the *signature* `𝑆 = (𝐶, 𝐹, 𝑅, ρ)` of a
-- structure consists of three (possibly empty) sets `𝐶`, `𝐹`, and `𝑅`---called *constant symbols*, *function
-- symbols*, and *relation symbols*, respectively---along with a function `ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁` that assigns an
-- *arity* to each symbol. Often (but not always) `𝑁 = ℕ`, the natural numbers.
--
-- As our focus here is universal algebra, we are more concerned with the restricted notion of an *algebraic
-- signature* (or *signature* for algebraic structures), by which we mean a pair `𝑆 = (𝐹, ρ)` consisting of a
-- collection `𝐹` of *operation symbols* and an *arity function* `ρ : 𝐹 → 𝑁` that maps each operation symbol
-- to its arity; here, 𝑁 denotes the *arity type*. Heuristically, the arity `ρ 𝑓` of an operation symbol `𝑓 ∈
-- 𝐹` may be thought of as the "number of arguments" that `𝑓` takes as "input".
--
-- If the arity of `𝑓` is `n`, then we call `𝑓` an `n`-*ary* operation symbol.  In case `n` is 0 (or 1 or 2 or
-- 3, respectively) we call the function *nullary* (or *unary* or *binary* or *ternary*, respectively).
--
-- If `A` is a set and `𝑓` is a (`ρ 𝑓`)-ary operation on `A`, we often indicate this by writing `𝑓 : A`<sup>ρ
-- 𝑓</sup> `→ A`. On the other hand, the arguments of such an operation form a (`ρ 𝑓`)-tuple, say, `(a 0, a 1,
-- …, a (ρf-1))`, which may be viewed as the graph of the function `a : ρ𝑓 → A`. When the codomain of `ρ` is
-- `ℕ`, we may view `ρ 𝑓` as the finite set `{0, 1, …, ρ𝑓 - 1}`. Thus, by identifying the `ρ𝑓`-th power
-- `A`<sup>ρ 𝑓</sup> with the type `ρ 𝑓 → A` of functions from `{0, 1, …, ρ𝑓 - 1}` to `A`, we identify the
-- function type `A`<sup>ρ f</sup> `→ A` with the function (or "functional") type `(ρ𝑓 → A) → A`.
--
-- **Example**. Suppose `𝑔 : (m → A) → A` is an `m`-ary operation on `A`, and `a : m → A` is an `m`-tuple on
-- `A`. Then `𝑔 a` may be viewed as `𝑔 (a 0, a 1, …, a (m-1))`, which has type `A`. Suppose further that `𝑓 :
-- (ρ𝑓 → B) → B` is a `ρ𝑓`-ary operation on `B`, let `a : ρ𝑓 → A` be a `ρ𝑓`-tuple on `A`, and let `h : A → B`
-- be a function.  Then the following typing judgments obtain: `h ∘ a : ρ𝑓 → B` and we `𝑓 (h ∘ a) : B`.

-- Signature type
-- --------------
-- In the [UniversalAlgebra][] library we represent the *signature* of an algebraic structure using the
-- following type.

Signature : (𝓞 𝓥 : Level) → Type (lsuc (𝓞 ⊔ 𝓥))
Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)

-- As mentioned earlier, throughout the [UniversalAlgebra][] library `𝓞` denote the universe level of
-- *operation symbol* types, while `𝓥` denotes the universe level of *arity* types.
--
-- In the [Overture][] module we defined special syntax for the first and second projections---namely, ∣\_∣
-- and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of
-- operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the
-- signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.
--
-- **Example (Monoid)**. Here is how we could define the signature for monoids as a member of the type
-- `Signature 𝓞 𝓥`.

data monoid-op {𝓞 : Level} : Type 𝓞 where
 e : monoid-op; · : monoid-op

monoid-sig : Signature 𝓞 lzero
monoid-sig = monoid-op , λ { e → ⊥; · → Bool }

-- Thus, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘;
-- · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two
-- element type 𝟚 (since `·` is binary).


-- Algebras
-- --------
-- Our first goal is to develop a working vocabulary and formal library for classical (single-sorted,
-- set-based) universal algebra.  In this section we define the main objects of study.  An *algebraic
-- structure* (or *algebra*) in the signature `𝑆 = (𝐹, ρ)` is denoted by `𝑨 = (A, F`<sup>`𝑨`</sup>`)` and
-- consists of
--
-- * `A` := a *nonempty* set (or type), called the *domain* (or *carrier* or *universe*) of the algebra;
--
-- * `F`<sup>`𝑨`</sup> := `{ f`<sup>`𝑨`</sup>` ∣ f ∈ F, f`<sup>`𝑨`</sup>` : (ρ𝑓 → A) → A }`, a collection of
-- *operations* on `𝐴`;
--
-- * a (potentially empty) collection of *identities* satisfied by elements and operations of `𝐴`.
--
-- Note that to each operation symbol `𝑓 ∈ 𝐹` corresponds an operation `𝑓`<sup>`𝑨`</sup> on `𝐴` of arity `ρ𝑓`;
-- we call such `𝑓`<sup>`𝑨`</sup> the *interpretation* of the symbol `𝑓` in the algebra `𝑨`. We call an
-- algebra in the signature `𝑆` an `𝑆`-*algebra*.  An algebra is called *finite* if it has a finite domain,
-- and is called *trivial* if its universe is a singleton.  Given two algebras `𝑨` and `𝑩`, we say that `𝑩` is
-- a *reduct* of `𝑨` if both algebras have the same domain and `𝑩` can be obtained from `𝑨` by simply removing
-- some of the operations.


-- Algebra types
-- -------------
-- Recall, we defined the type `Signature 𝓞 𝓥` above as the dependent pair type `Σ F ꞉ Type 𝓞 , (F → Type 𝓥)`,
-- and the type `Op` of operation symbols is the function type `Op I A = (I → A) → A` (see
-- [Relations.Discrete][]). For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe level `𝓤`, we define the
-- *type of algebras in the signature* `𝑆` (or *type of* `𝑆`-*algebras*) *with domain type* `Type 𝓤` as
-- follows.

Algebra : (𝓤 : Level)(𝑆 : Signature 𝓞 𝓥) → Type (𝓞 ⊔ 𝓥 ⊔ lsuc 𝓤)
Algebra 𝓤 𝑆 = Σ[ A ∈ Type 𝓤 ]                   -- the domain
              ∀ (f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A    -- the basic operations

-- It would be more precise to refer to inhabitants of this type as ∞-*algebras* because their domains can be
-- of arbitrary type and need not be truncated at some level and, in particular, need to be a set. (See the
-- [Relations.Truncation][] module.)
--
-- We might take this opportunity to define the type of 0-*algebras*, that is, algebras whose domains are
-- sets, which is probably closer to what most of us think of when doing informal universal algebra.  However,
-- below we will only need to know that the domains of certain algebras are sets in a few places in the
-- [UniversalAlgebra][] library, so it seems preferable to work with general (∞-)algebras throughout and then
-- explicitly postulate [uniquness of identity
-- proofs](Relations.Truncation.html#uniqueness-of-identity-proofs) when and only when necessary.


-- The universe level of an algebra
-- --------------------------------
-- Occasionally we will be given an algebra and we just need to know the universe level of its domain. The
-- following utility function provides this.

level-of-alg : {𝑆 : Signature 𝓞 𝓥} → Algebra 𝓤 𝑆 → Level
level-of-alg {𝓤 = 𝓤} _ = 𝓤


-- Algebras as record types
-- ------------------------
-- Some people prefer to represent algebraic structures in type theory using records, and for those folks we
-- offer the following (equivalent) definition.

record algebra (𝓤 : Level) (𝑆 : Signature 𝓞 𝓥) : Type(lsuc(𝓞 ⊔ 𝓥 ⊔ 𝓤)) where
 constructor mkalg
 field
  univ : Type 𝓤
  op : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → univ) → univ

-- This representation of algebras as inhabitants of a record type is equivalent to the representation using
-- Sigma types in the sense that a bi-implication between the two representations is obvious.


module _ {𝑆 : Signature 𝓞 𝓥} where

 open algebra

 algebra→Algebra : algebra 𝓤 𝑆 → Algebra 𝓤 𝑆
 algebra→Algebra 𝑨 = (univ 𝑨 , op 𝑨)

 Algebra→algebra : Algebra 𝓤 𝑆 → algebra 𝓤 𝑆
 Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥


-- Operation interpretation syntax
-- -------------------------------
-- We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar
-- to the standard notation one finds in the literature as compared to the double bar notation we started
-- with, so we will use this new notation almost exclusively in the remaining modules of the
-- [UniversalAlgebra][] library.

 _̂_ : (𝑓 : ∣ 𝑆 ∣)(𝑨 : Algebra 𝓤 𝑆) → (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 𝑓 ̂ 𝑨 = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎

-- So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of
-- the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.


-- Level lifting algebra types
-- ---------------------------
-- Recall, in the [section on level lifting and lowering](Overture.Lifts.html#level-lifting-and-lowering), we
-- described the difficulties one may encounter when working with a noncumulative universe hierarchy. We made
-- a promise to provide some domain-specific level lifting and level lowering methods. Here we fulfill this
-- promise by supplying a couple of bespoke tools designed specifically for our operation and algebra types.

open Lift

Lift-op : {𝓘 : Level}{I : Type 𝓘}{A : Type 𝓤} → Op I A → (𝓦 : Level) → Op I (Lift 𝓦 A)
Lift-op f 𝓦 = λ x → lift (f (λ i → lower (x i)))

Lift-alg : {𝑆 : Signature 𝓞 𝓥} → Algebra 𝓤 𝑆 → (𝓦 : Level) → Algebra (𝓤 ⊔ 𝓦) 𝑆
Lift-alg {𝑆 = 𝑆} 𝑨 𝓦 = Lift 𝓦 ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → Lift-op (𝑓 ̂ 𝑨) 𝓦)

open algebra

Lift-alg-record-type : {𝑆 : Signature 𝓞 𝓥} → algebra 𝓤 𝑆 → (𝓦 : Level) → algebra (𝓤 ⊔ 𝓦) 𝑆
Lift-alg-record-type {𝑆 = 𝑆} 𝑨 𝓦 = mkalg (Lift 𝓦 (univ 𝑨)) (λ (f : ∣ 𝑆 ∣) → Lift-op ((op 𝑨) f) 𝓦)

-- What makes the `Lift-alg` type so useful for resolving type level errors involving algebras is the nice
-- properties it possesses.  Indeed, the [UniversalAlgebra][] library contains formal proofs of the following
-- facts.
--
-- * [`Lift-alg` is a homomorphism](Homomorphisms.Basic.html#exmples-of-homomorphisms)
-- * [`Lift-alg` is an algebraic invariant](Homomorphisms.Isomorphisms.html#lift-is-an-algebraic-invariant")
-- * [`Lift-alg` of a subalgebra is a subalgebra](Subalgebras.Subalgebras.html#lifts-of-subalgebras)
-- * [`Lift-alg` preserves identities](Varieties.EquationalLogic.html#lift-invariance))

-- Compatibility of binary relations
-- ---------------------------------
-- We now define the function `compatible` so that, if `𝑨` denotes an algebra and `R` a binary relation, then
-- `compatible 𝑨 R` will represent the assertion that `R` is *compatible* with all basic operations of `𝑨`.
-- The formal definition is immediate since all the work is done by the relation `|:`, which we defined above
-- (see [Relations.Discrete][]).

compatible : {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra 𝓤 𝑆) → Rel ∣ 𝑨 ∣ 𝓦 → Type(𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦)
compatible  𝑨 R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R

-- Recall, the `|:` type was defined in [Relations.Discrete][] module.

-- Compatibility of continuous relations
-- -------------------------------------
-- In the [Relations.Continuous][] module, we defined a function called `cont-compatible-op` to represent the
-- assertion that a given continuous relation is compatible with a given operation. With that, it is easy to
-- define a function, which we call `cont-compatible`, representing compatibility of a continuous relation
-- with all operations of an algebra.  Similarly, we define the analogous `dep-compatible` function for the
-- (even more general) type of *dependent relations*.

module _ {I : Type 𝓥} {𝑆 : Signature 𝓞 𝓥} where

 cont-compatible : (𝑨 : Algebra 𝓤 𝑆) → ContRel I ∣ 𝑨 ∣ 𝓦 → Type(𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦)
 cont-compatible 𝑨 R = ∀ (𝑓 : ∣ 𝑆 ∣ ) →  cont-compatible-op (𝑓 ̂ 𝑨) R

 dep-compatible : (𝒜 : I → Algebra 𝓤 𝑆) → DepRel I (λ i → ∣ 𝒜  i ∣) 𝓦 → Type(𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦)
 dep-compatible 𝒜 R = ∀ ( 𝑓 : ∣ 𝑆 ∣ ) →  dep-compatible-op (λ i → 𝑓 ̂ (𝒜 i)) R


--------------------------------------

-- [agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
