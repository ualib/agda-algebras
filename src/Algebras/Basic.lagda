<h2>Algebras.Basic module</h2>

<h3>Basic Definitions</h3>

This is the [Algebras.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Algebras.Basic where

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality  using (_≡_ ; refl )
open import Agda.Primitive         using ( _⊔_ ; lsuc ) renaming ( Set to  Type ; lzero to ℓ₀ )
open import Data.Empty             using ( ⊥ )
open import Data.Product           using ( _,_ ; _×_ ; Σ ; Σ-syntax )
open import Level                  using ( Level )
open import Relation.Binary        using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Unary         using ( _∈_ ; Pred )


-- Imports from the Agda Universal Algebra Library
open import Overture.Preliminaries using (∣_∣; ∥_∥)
open import Relations.Discrete     using ( Op ; _|:_ ; _|:pred_ )
open import Relations.Continuous   using ( Rel; ΠΡ ; compatible-Rel ; compatible-ΠΡ )

private variable α β ρ : Level
variable 𝓞 𝓥 : Level

\end{code}

<h4>The signatures of an algebra</h4>

In <a href="https://en.wikipedia.org/wiki/Model_theory">model theory</a>, the <i>signature</i> `𝑆 = (𝐶, 𝐹, 𝑅, ρ)` of a structure consists of three (possibly empty) sets `𝐶`, `𝐹`, and `𝑅`---called <i>constant symbols</i>, <i>function symbols</i>, and <i>relation symbols</i>, respectively---along with a function `ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁` that assigns an <i>arity</i> to each symbol. Often (but not always) `𝑁 = ℕ`, the natural numbers.

As our focus here is universal algebra, we are more concerned with the restricted notion of an <i>algebraic signature</i> (or <i>signature</i> for algebraic structures), by which we mean a pair `𝑆 = (𝐹, ρ)` consisting of a collection `𝐹` of <i>operation symbols</i> and an <i>arity function</i> `ρ : 𝐹 → 𝑁` that maps each operation symbol to its arity; here, 𝑁 denotes the <i>arity type</i>. Heuristically, the arity `ρ 𝑓` of an operation symbol `𝑓 ∈ 𝐹` may be thought of as the "number of arguments" that `𝑓` takes as "input".

If the arity of `𝑓` is `n`, then we call `𝑓` an `n`-<i>ary</i> operation symbol.  In case `n` is 0 (or 1 or 2 or 3, respectively) we call the function <i>nullary</i> (or <i>unary</i> or <i>binary</i> or <i>ternary</i>, respectively).

If `A` is a set and `𝑓` is a (`ρ 𝑓`)-ary operation on `A`, we often indicate this by writing `𝑓 : A`<sup>ρ 𝑓</sup> `→ A`. On the other hand, the arguments of such an operation form a (`ρ 𝑓`)-tuple, say, `(a 0, a 1, …, a (ρf-1))`, which may be viewed as the graph of the function `a : ρ𝑓 → A`. When the codomain of `ρ` is `ℕ`, we may view `ρ 𝑓` as the finite set `{0, 1, …, ρ𝑓 - 1}`. Thus, by identifying the `ρ𝑓`-th power `A`<sup>ρ 𝑓</sup> with the type `ρ 𝑓 → A` of functions from `{0, 1, …, ρ𝑓 - 1}` to `A`, we identify the function type `A`<sup>ρ f</sup> `→ A` with the function (or "functional") type `(ρ𝑓 → A) → A`.

<b>Example</b>. Suppose `𝑔 : (m → A) → A` is an `m`-ary operation on `A`, and `a : m → A` is an `m`-tuple on `A`. Then `𝑔 a` may be viewed as `𝑔 (a 0, a 1, …, a (m-1))`, which has type `A`. Suppose further that `𝑓 : (ρ𝑓 → B) → B` is a `ρ𝑓`-ary operation on `B`, let `a : ρ𝑓 → A` be a `ρ𝑓`-tuple on `A`, and let `h : A → B` be a function.  Then the following typing judgments obtain: `h ∘ a : ρ𝑓 → B` and we `𝑓 (h ∘ a) : B`.

<h4>Signature type</h4>

In the <a href="https://github.com/ualib/agda-algebras">agda-algebras library</a> we represent the <i>signature</i> of an algebraic structure using the following type.

\begin{code}

Signature : (𝓞 𝓥 : Level) → Type (lsuc (𝓞 ⊔ 𝓥))
Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)


Level-of-Signature : {𝓞 𝓥 : Level} → Signature 𝓞 𝓥 → Level
Level-of-Signature {𝓞}{𝓥} _ = lsuc (𝓞 ⊔ 𝓥)

-- Let's also introduce a signature type for the (not so) special case where
-- arity types can be assumed to live at universe level zero.
signature : (𝓞 : Level) → Type (lsuc 𝓞)
signature 𝓞 = Σ[ F ∈ Type 𝓞 ] (F → Type)
-- (It turns out that everything in the library up to the Birkhoff HSP
-- theorem can be done with these "little" arities.)

\end{code}

As mentioned earlier, throughout the <a href="https://github.com/ualib/agda-algebras">agda-algebras library</a> `𝓞` denote the universe level of <i>operation symbol</i> types, while `𝓥` denotes the universe level of <i>arity</i> types.

In the [Overture][] module we defined special syntax for the first and second projections---namely, ∣\_∣ and ∥\_∥, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then ∣ 𝑆 ∣ denotes the set of operation symbols, and ∥ 𝑆 ∥ denotes the arity function. If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.



<h4>Algebras</h4>

Our first goal is to develop a working vocabulary and formal library for classical (single-sorted, set-based) universal algebra.  In this section we define the main objects of study.  An <i>algebraic structure</i> (or <i>algebra</i>) in the signature `𝑆 = (𝐹, ρ)` is denoted by `𝑨 = (A, F`<sup>`𝑨`</sup>`)` and consists of

<ul>
<li>`A` := a <i>nonempty</i> set (or type), called the <i>domain</i> (or <i>carrier</i> or <i>universe</i>) of the algebra;</li>
<li> `F`<sup>`𝑨`</sup> := `{ f`<sup>`𝑨`</sup>` ∣ f ∈ F, f`<sup>`𝑨`</sup>` : (ρ𝑓 → A) → A }`, a collection of <i>operations</i> on `𝐴`;</li>
<li> a (potentially empty) collection of <i>identities</i> satisfied by elements and operations of `𝐴`.</li>
</ul>

Note that to each operation symbol `𝑓 ∈ 𝐹` corresponds an operation `𝑓`<sup>`𝑨`</sup> on `𝐴` of arity `ρ𝑓`; we call such `𝑓`<sup>`𝑨`</sup> the <i>interpretation</i> of the symbol `𝑓` in the algebra `𝑨`. We call an algebra in the signature `𝑆` an `𝑆`-<i>algebra</i>.  An algebra is called <i>finite</i> if it has a finite domain, and is called <i>trivial</i> if its universe is a singleton.  Given two algebras `𝑨` and `𝑩`, we say that `𝑩` is a <i>reduct</i> of `𝑨` if both algebras have the same domain and `𝑩` can be obtained from `𝑨` by simply removing some of the operations.



<h4>Algebra types</h4>

Recall, we defined the type `Signature 𝓞 𝓥` above as the dependent pair type `Σ F ꞉ Type 𝓞 , (F → Type 𝓥)`, and the type `Op` of operation symbols is the function type `Op I A = (I → A) → A` (see [Relations.Discrete][]). For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe level `α`, we define the <i>type of algebras in the signature</i> `𝑆` (or <i>type of</i> `𝑆`-<i>algebras</i>) <i>with domain type</i> `Type α` as follows.

\begin{code}

Algebra : (α : Level)(𝑆 : Signature 𝓞 𝓥) → Type (𝓞 ⊔ 𝓥 ⊔ lsuc α)
Algebra α 𝑆 = Σ[ A ∈ Type α ]                   -- the domain
              ∀ (f : ∣ 𝑆 ∣) → Op A (∥ 𝑆 ∥ f)    -- the basic operations

\end{code}

It would be more precise to refer to inhabitants of this type as ∞-<i>algebras</i> because their domains can be of arbitrary type and need not be truncated at some level and, in particular, need to be a set. (See the [Relations.Truncation][] module.)

We might take this opportunity to define the type of 0-<i>algebras</i>, that is, algebras whose domains are sets, which is probably closer to what most of us think of when doing informal universal algebra.  However, below we will only need to know that the domains of certain algebras are sets in a few places in the [UniversalAlgebra][] library, so it seems preferable to work with general (∞-)algebras throughout and then explicitly postulate [uniquness of identity proofs](Relations.Truncation.html#uniqueness-of-identity-proofs) when and only when necessary.



<h5>The universe level of an algebra</h5>

Occasionally we will be given an algebra and we just need to know the universe level of its domain. The following utility function provides this.

\begin{code}

Level-of-Alg : {α 𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α 𝑆 → Level
Level-of-Alg {α = α}{𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥 ⊔ (lsuc α)

Level-of-Carrier : {α : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α 𝑆 → Level
Level-of-Carrier {α = α} _ = α

\end{code}



<h5>Algebras as record types</h5>

Some people prefer to represent algebraic structures in type theory using records, and for those folks we offer the following (equivalent) definition.

\begin{code}

record algebra (α : Level) (𝑆 : Signature 𝓞 𝓥) : Type(lsuc(𝓞 ⊔ 𝓥 ⊔ α)) where
 constructor mkalg
 field
  carrier : Type α
  opsymbol : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → carrier) → carrier

record lilalgebra (α : Level) (𝑆 : signature 𝓞) : Type(lsuc(𝓞 ⊔ α)) where
 constructor mklilalg
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


<h4>Operation interpretation syntax</h4>

We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with, so we will use this new notation almost exclusively in the remaining modules of the [UniversalAlgebra][] library.

\begin{code}

 _̂_ : (𝑓 : ∣ 𝑆 ∣)(𝑨 : Algebra α 𝑆) → (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 𝑓 ̂ 𝑨 = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎

\end{code}

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.


<h4>Level lifting algebra types</h4>

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

What makes the `Lift-Alg` type so useful for resolving type level errors involving algebras is the nice properties it possesses.  Indeed, the [UniversalAlgebra][] library contains formal proofs of the following facts.

<ul>
<li> <a href="Homomorphisms.Basic.html#exmples-of-homomorphisms">`Lift-Alg` is a homomorphism</a></li>
<li> <a href="Homomorphisms.Isomorphisms.html#lift-is-an-algebraic-invariant">`Lift-Alg` is an algebraic invariant</a></li>
<li> <a href="Subalgebras.Subalgebras.html#lifts-of-subalgebras">`Lift-Alg` of a subalgebra is a subalgebra</a></li>
<li> <a href="Varieties.EquationalLogic.html#lift-invariance">`Lift-Alg` preserves identities</a></li>
</ul>

<h4>Compatibility of binary relations</h4>

We now define the function `compatible` so that, if `𝑨` denotes an algebra and `R` a binary relation, then `compatible 𝑨 R` will represent the assertion that `R` is <i>compatible</i> with all basic operations of `𝑨`. The formal definition is immediate since all the work is done by the relation `|:`, which we defined above (see [Relations.Discrete][]).

\begin{code}

compatible : {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra α 𝑆) → BinRel ∣ 𝑨 ∣ ρ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
compatible  𝑨 R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R

compatible-pred : {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra α 𝑆) → Pred (∣ 𝑨 ∣ × ∣ 𝑨 ∣)ρ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
compatible-pred  𝑨 P = ∀ 𝑓 → (𝑓 ̂ 𝑨) |:pred P

\end{code}

Recall, the `|:` type was defined in [Relations.Discrete][] module.




<h4>Compatibility of continuous relations</h4>

In the [Relations.Continuous][] module, we defined a function called `cont-compatible-op` to represent the assertion that a given continuous relation is compatible with a given operation. With that, it is easy to define a function, which we call `cont-compatible`, representing compatibility of a continuous relation with all operations of an algebra.  Similarly, we define the analogous `dep-compatible` function for the (even more general) type of <i>dependent relations</i>.

\begin{code}

module _ {I : Type 𝓥} {𝑆 : Signature 𝓞 𝓥} where

 compatible-Rel-alg : (𝑨 : Algebra α 𝑆) → Rel ∣ 𝑨 ∣ I{ρ} → Type(𝓞 ⊔ α ⊔ 𝓥 ⊔ ρ)
 compatible-Rel-alg 𝑨 R = ∀ (𝑓 : ∣ 𝑆 ∣ ) →  compatible-Rel (𝑓 ̂ 𝑨) R

 compatible-ΠΡ-alg : (𝒜 : I → Algebra α 𝑆) → ΠΡ I (λ i → ∣ 𝒜  i ∣) {ρ} → Type(𝓞 ⊔ α ⊔ 𝓥 ⊔ ρ)
 compatible-ΠΡ-alg 𝒜 R = ∀ ( 𝑓 : ∣ 𝑆 ∣ ) →  compatible-ΠΡ (λ i → 𝑓 ̂ (𝒜 i)) R

\end{code}


{% include footer.html %}
