---
layout: default
title : Demos.TYPES2021-short module for talk introducing the Agda Universal Algebra Library
date : 2021-06-15
author: William DeMeo
---

























---



# THE AGDA UNIVERSAL ALGEBRA LIBRARY
## and Birkhoff's Theorem in Dependent Type Theory


*Conference* TYPES 2021
*Session*    Proof Assistant Applications

*Author*     William DeMeo

*Coauthors*  This is joint work with
             * Jacques Carette
             * Venanzio Capretta
             * Siva Somayyajula
             * Hyeyoung Shin


*References*

* Source: https://github.com/ualib/agda-algebras

* Docs: https://ualib.org






---

### INTRODUCTION

The Agda Universal Algebra Library (agda-algebras) is a collection of types
and programs (theorems and proofs) formalizing general (universal) algebra
in dependent type theory using Agda.

#### Current Scope of agda-algebras

* [Operations] of arbitrary arity over an arbitrary type (single-sorted)

* [Relations] of arbitrary arity over arbitrary type families (many-sorted)

* [Signatures] of operation and/or relation symbols and their arities

* [Algebras] and product algebras and quotient algebras (hom images)

* [Homomorphisms] and standard isomorphism and factoraization theorems

* [Terms] and the absolutely free term algebra

* [Subalgebras] and an inductive type for subalgebra generation

* [Varieties] and inductive types for closure operators H, S, and P.

* [Free Algebras] relative to a set of equations

* [Birkhoff's HSP Theorem]


---




#### FEATURES of agda-algebras

* [General]
  Algebraic/relational structures that are more general than those of
  "classical" algebra, and even more general than informal universal algebra.

* [Constructive]
  Classical axioms (Choice, Excluded Middle) are never used.

* [Computational] (to some degree)
  Occasionally we postulate extensionality of functions and propositions
  to prove theorems (but not globally, and we are working on removing these).

* [Specialized]
  Currently only single-sorted structures are covered (but we are developing a
  multi-sorted version).










---



#### LOGICAL FOUNDATIONS

We use the Agda OPTIONS pragma to specify the logical axioms
and deduction rules assumed throughout agda-algebras.

Every source file in agda-algebras begins with

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

* --without-K   →  no K axiom (essentially we have "proof relevance", not UIP).

* --exact-split →  allow only definitions that behave like judgmental equalities.

* --safe        →  nothing is postulated outright---non-MLTT axioms must be explicit









---

###### (skip)

\begin{code}
open import Demos.TYPES2021-shortimports
module Demos.TYPES2021-short  {𝓞 𝓥 : Level} where
variable α β γ ρ χ 𝓘 : Level
\end{code}






















---



### (SINGLE-SORTED) OPERATIONS OF ARBITRARY ARITY

The type Op encodes arity of an operation as a type  I : Type 𝓥,
so we can represent an operation as a function with

 domain:  I → A  (the type of "tuples" of A)  and  codomain: A.

\begin{code}

Op : Type α → {I : Type 𝓥 } → Type _
Op A {I} = (I → A) → A

\end{code}

Think of Op A {I} as Aᴵ → A, the collection of functions that map each tuple in
Aᴵ to an element of A. For example, the I-ary projection operations on A are

\begin{code}

π : {I : Type 𝓥 } {A : Type α } → I → Op A
π i x = x i

\end{code}




---


### (SINGLE-SORTED) RELATIONS OF ARBITRARY ARITY

In Set theory, an n-ary relation on a set A is a subset of

  A × A × ⋯ × A

Could model these as predicates over A × A × ⋯ × A or as

   A → A → ⋯ → A → Type      ...awkward.



Easier and more general to do...

\begin{code}

Arity : (𝓥 : Level) → Type _    -- (a type alias)
Arity 𝓥 = Type 𝓥

-- For an "arity type"  I : Arity 𝓥
-- define the type of I-ary relations on A as

Rel : Type α → {I : Arity 𝓥 } → {ρ : Level} → Type _
Rel A {I} {ρ} = (I → A) → Type ρ

\end{code}


---



### DEPENDENT RELATIONS  ("PiRho Types" ...?)

Remove the single-sorted restriction with dependent types!

For an arbitrary family, 𝒜 : I → Type α, imagine a relation

     from … to 𝒜 i  to  𝒜 j  to  𝒜 k  to  …               (*)

In set theory such relations are subsets of Π(i : I) 𝒜 i.

The "indexing" type I might not even be enumerable so (*) is misleading.

The ΠΡ (PiRho) type manifests this general notion of relation as follows.

\begin{code} -- arbitrary-sorted relations of arbitrary arity

ΠΡ : (I : Arity 𝓥 ) → (I → Type α) → {ρ : Level} → Type _
ΠΡ I 𝒜 {ρ} = ((i : I) → 𝒜 i) → Type ρ

\end{code}

These are just predicates over dependent functions!





---

### TYPES FOR ALGEBRAIC STRUCTURES

#### SIGNATURES

An *algebraic signature* is a pair 𝑆 = (F, ρ) where

* F is a (possibly empty) set

* ρ : F → N is an "arity function"

Heuristically, ρ 𝑓 is the "number of arguments" of 𝑓.

Often (but not always) N is the set of natural numbers.

Signature is represented in agda-algebras using dependent pair type.

\begin{code}

Signature : (𝓞 𝓥 : Level) → Type _

Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)

\end{code}

We define syntax for the first and second projections: ∣_∣ and ∥_∥.

If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is
the arity of 𝑓.

---



#### (Example: Monoid Signature)   (skip)

Here is how we could encode the signature for monoids as an inhabitant of
Signature 𝓞 ℓ₀.

\begin{code}


data monoid-op {𝓞 : Level} : Type 𝓞 where
 e : monoid-op; · : monoid-op

monoid-sig : {𝓞 : Level} → Signature 𝓞 ℓ₀
monoid-sig = monoid-op , λ { e → ⊥; · → Bool }

\end{code}

This signature consists of two operation symbols, e and ·, and a
function λ { e → 𝟘; · → 𝟚 } which maps

* e to the empty type 𝟘 (since e is the nullary identity) and
* · to the two element type 𝟚 (since · is binary).






---

#### (Special notation)  (skip)

Given a signature 𝑆 : Signature 𝓞 𝓥, the type Algebra α 𝑆 will have type
Type(𝓞 ⊔ 𝓥 ⊔ lsuc α) and such types occur so often in agda-algebras
that we define the following shorthand.

\begin{code}

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α

\end{code}

















---


#### ALGEBRAS

Informally, an *algebra* in the signature 𝑆 = (F , ρ) is denoted 𝑨 = (A , Fᴬ).

* A = a nonempty set called the *carrier* of the algebra;

* Fᴬ = { fᴬ ∣ f ∈ F, fᴬ : (ρ𝑓 → A) → A } = a collection of *operations* on A;

* a set (maybe empty) of identities satisfied by the elements and operations.


For signature 𝑆 and universe α the type of 𝑆-algebras with carrier in Type α is

\begin{code}

Algebra : (α : Level)(𝑆 : Signature 𝓞 𝓥) → Type (ov α)

Algebra α 𝑆 = Σ[ A ∈ Type α ]                   -- the domain

              ∀ (f : ∣ 𝑆 ∣) → Op A {∥ 𝑆 ∥ f}    -- the basic operations

\end{code}






---

#### (Truncation)   (skip)

It would be more precise to refer to inhabitants of Algebra α 𝑆 as
∞-algebras because their domains can be of arbitrary type and need not be
truncated at some particular universe level.

We might take this opportunity to define the type of 0-algebras, that is,
algebras whose domains are "sets" (where identity proofs are unique), which is
probably closer in spirit to classical universal algebra.

However, our experience has shown that much of the theory can be formalized more
generally, so it seems preferable to work with general (∞-)algebras throughout
and then explicitly require additional principles (e.g., unique identity proofs)
only when necessary.















---

#### OPERATION INTERPRETATION SYNTAX

A shorthand for the interpretation of an operation symbol which looks a bit
like the standard notation in the literature is defined as follows.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} where

 _̂_ : ∀ 𝑓 (𝑨 : Algebra α 𝑆) → (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 𝑓 ̂ 𝑨 = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎

\end{code}

If 𝑓 : ∣ 𝑆 ∣ is an operation symbol, and a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣ is a tuple of the
appropriate arity, then (𝑓 ̂ 𝑨) a denotes the operation 𝑓 interpreted in 𝑨 and
evaluated at a.











---

#### (Level lifting algebra types)   (skip)

One encounters difficulties when working with a noncumulative universe hierarchy like Agda's.

We provide some domain-specific level lifting and level lowering methods---bespoke tools
for our operation and algebra types.

\begin{code}

 open Lift

 Lift-Alg-op : {I : Arity 𝓥} {A : Type α} → Op A {I} → (β : Level) → Op (Lift β A) {I}

 Lift-Alg-op f β = λ x → lift (f (λ i → lower (x i)))


 Lift-Alg : Algebra α 𝑆 → (β : Level) → Algebra (α ⊔ β) 𝑆

 Lift-Alg 𝑨 β = Lift β ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → Lift-Alg-op (𝑓 ̂ 𝑨) β)

\end{code}

What makes Lift-Alg useful for resolving type level errors involving algebras is the
nice structure-preserving properties it possesses.  Indeed, we prove the following:

+ Lift-Alg is a homomorphism
+ Lift-Alg is an algebraic invariant (preserves isomorphism)
+ Lift-Alg is a "subalgebraic invariant" (lift of a subalgebra is a subalgebra)
+ Lift-Alg preserves identities
---


#### Product Algebras  (skip)


Recall the informal definition of a *product* of 𝑆-algebras.

Given a type I : Type 𝓘 and a family 𝒜 : I → Algebra α 𝑆, the *product* ⨅ 𝒜 is
the algebra with

* carrier: the Cartesian product Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣ of the domains of the algebras in 𝒜

* operations: if 𝑓 is a J-ary operation symbol and if 𝑎 : Π[ 𝑖 ∈ I ] J → 𝒜 𝑖 is an
 I-tuple of J-tuples such that 𝑎 𝑖 is a J-tuple of elements of 𝒜 𝑖, then

  (𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i).

\begin{code}
 module _ {𝓘 : Level}{I : Type 𝓘 } where

  ⨅ : (𝒜 : I → Algebra α 𝑆 ) → Algebra (𝓘 ⊔ α) 𝑆

  ⨅ 𝒜 = ( ∀ (i : I) → ∣ 𝒜 i ∣ ) ,           -- domain of the product algebra

         λ 𝑓 𝑎 i → (𝑓 ̂ 𝒜 i) λ x → 𝑎 x i   -- basic operations of the product algebra

\end{code}



---

#### PRODUCTS OF ARBITRARY CLASSES OF ALGEBRAS

We want to formally express and prove properties of *classes of algebras*.

Classes of 𝑆-algebras are represented as predicates over the type Algebra α 𝑆.

  𝒦 : Pred (Algebra α 𝑆) β

We want to prove theorems like

  PS(𝒦) ⊆ SP(𝒦 )

This is nontrivial, requiring a type of product over arbitrary
(nonindexed) families like 𝒦.

The solution: essentially take 𝒦 itself to be the indexing type.

\begin{code}

 module _ {𝒦 : Pred (Algebra α 𝑆)(ov α)} where
  -- The index for the product of algebras in 𝒦.
  ℑ : Type (ov α)
  ℑ = Σ[ 𝑨 ∈ Algebra α 𝑆 ] 𝑨 ∈ 𝒦

\end{code}

To take the product over the index type ℑ we just map each
index i = (𝑨ᵢ , pᵢ) to the corresponding algebra 𝑨ᵢ.

---



#### PRODUCTS OF ARBITRARY CLASSES OF ALGEBRAS

Each i : ℑ is a pair (𝑨 , p), where p is a proof that 𝑨 ∈ 𝒦, so the function
mapping an index to the corresponding algebra is simply the first projection.

\begin{code}

  𝔄 : ℑ → Algebra α 𝑆
  𝔄 i = ∣ i ∣

  class-product : Algebra (ov α) 𝑆      -- (the product of all members of 𝒦)
  class-product = ⨅ 𝔄

\end{code}

If p : 𝑨 ∈ 𝒦, then the pair (𝑨 , p) ∈ ℑ is an "index" over the class, and
𝔄 (𝑨 , p) is the projection of the product ⨅ 𝔄 onto the (𝑨 , p)-th component
algebra.









---


### CONGRUENCE RELATIONS

A *congruence relation* of an algebra 𝑨 is an equivalence relation that is
compatible with the basic operations of 𝑨.

\begin{code}

 record IsCongruence (𝑨 : Algebra α 𝑆)(θ : BinRel ∣ 𝑨 ∣ ρ) : Type(ov (ρ ⊔ α))  where
  constructor mkcon
  field       is-equivalence : IsEquivalence θ
              is-compatible  : compatible 𝑨 θ


 Con : (𝑨 : Algebra α 𝑆) → {ρ : Level} → Type _

 Con 𝑨 {ρ} = Σ[ θ ∈ ( BinRel ∣ 𝑨 ∣ ρ ) ] IsCongruence 𝑨 θ


 open IsCongruence

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in
the sense that each implies the other. One implication is the "uncurry" operation and the
other is the second projection.



---

#### QUOTIENT ALGEBRAS

If θ : Con 𝑨, the quotient algebra 𝑨 / θ is defined in agda-algebras as

\begin{code}

 _╱_ : (𝑨 : Algebra α 𝑆) → Con 𝑨 {ρ} → Algebra (α ⊔ lsuc ρ) 𝑆

 𝑨 ╱ θ = (∣ 𝑨 ∣ / ∣ θ ∣)  ,                                  -- domain of the quotient algebra

          λ 𝑓 𝑎 → ⟪ (𝑓 ̂ 𝑨)(λ i →  IsBlock.block-u ∥ 𝑎 i ∥) ⟫  -- operations of the quotient algebra

\end{code}


The following elimination rule is sometimes useful...

\begin{code}

 /-≡ : {𝑨 : Algebra α 𝑆}(θ : Con 𝑨 {ρ}){u v : ∣ 𝑨 ∣} → ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v

 /-≡ θ refl = IsEquivalence.refl (is-equivalence ∥ θ ∥)

\end{code}

...but it "cheats" by baking in a large amount of extensionality that is miraculously true.



---


#### HOMOMORPHISMS

If 𝑨 and 𝑩 are 𝑆-algebras, then a *homomorphism* from 𝑨 to 𝑩 is a function

  h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣

from the domain of 𝑨 to the domain of 𝑩 that is *compatible* (or *commutes*)
with all of the basic operations of the signature; that is,

∀ (𝑓 : ∣ 𝑆 ∣) (a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → h ((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑩) (h ∘ a).

To formalize this concept, we first define a type representing the assertion
that a function h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣ commutes with a single basic operation 𝑓.

\begin{code}

 module _ (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) where

  compatible-op-map : ∣ 𝑆 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type _

  compatible-op-map 𝑓 h = ∀ 𝑎 → h ((𝑓 ̂ 𝑨) 𝑎) ≡ (𝑓 ̂ 𝑩) (h ∘ 𝑎)

\end{code}





---



#### HOMOMORPHISMS

Type hom 𝑨 𝑩 of homomorphisms from 𝑨 to 𝑩 is defined using the type
is-homomorphism representing the property of being a homomorphism.

\begin{code}

  is-homomorphism : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type _
  is-homomorphism g = ∀ 𝑓  →  compatible-op-map 𝑓 g

  hom : Type _
  hom = Σ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) is-homomorphism

  -- Example. The identity hom.
 𝒾𝒹 : (𝑨 : Algebra α 𝑆) → hom 𝑨 𝑨
 𝒾𝒹 _ = id , λ 𝑓 𝑎 → refl

\end{code}









---


#### (Homomorphism theorems)  (skip)

1. The composition of homomorphisms is again a homomorphism.

\begin{code}

 module _ (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆) where


  ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪

  ∘-hom (g , ghom) (h , hhom) = h ∘ g , Goal

   where

   Goal : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)

   Goal 𝑓 a = (h ∘ g)((𝑓 ̂ 𝑨) a) ≡⟨ cong h ( ghom 𝑓 a ) ⟩
              h ((𝑓 ̂ 𝑩)(g ∘ a)) ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
              (𝑓 ̂ 𝑪)(h ∘ g ∘ a) ∎

\end{code}






---




#### (Homomorphism theorems)  (skip)

2. lift and lower are (the maps of) homomorphisms.

\begin{code}

 open Lift

 𝓁𝒾𝒻𝓉 : (𝑨 : Algebra α 𝑆) → hom 𝑨 (Lift-Alg 𝑨 β)
 𝓁𝒾𝒻𝓉 _ = lift , λ 𝑓 𝑎 → refl

 𝓁ℴ𝓌ℯ𝓇 : (𝑨 : Algebra α 𝑆) → hom (Lift-Alg 𝑨 β) 𝑨
 𝓁ℴ𝓌ℯ𝓇 _ = lower , λ 𝑓 𝑎 → refl

\end{code}











---

#### (Homomorphism factorization)  (skip)


If τ : hom 𝑨 𝑩, ν : hom 𝑨 𝑪, ν is surjective, and ker ν ⊆ ker τ, then there exists
φ : hom 𝑪 𝑩 such that τ = φ ∘ ν so the following diagram commutes:

   𝑨 --- ν ->> 𝑪
    \         .
     \       .
      τ     φ
       \   .
        \ .
         V
         𝑩

\begin{code}

 module _ {𝑨 : Algebra α 𝑆}{𝑪 : Algebra γ 𝑆} where

  HomFactor : funext α β → swelldef 𝓥 γ
   →          (𝑩 : Algebra β 𝑆)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
   →          kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣ → IsSurjective ∣ ν ∣
              --------------------------------------------------
   →          Σ[ φ ∈ (hom 𝑪 𝑩)] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣





---

 -- Proof of factorization theorem

  HomFactor fxy wd 𝑩 τ ν Kντ νE = (φ , φIsHomCB) , τφν
   where
    νInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
    νInv = SurjInv ∣ ν ∣ νE

    η : ∀ c → ∣ ν ∣ (νInv c) ≡ c
    η c = SurjInvIsRightInv ∣ ν ∣ νE c

    φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
    φ = ∣ τ ∣ ∘ νInv

    ξ : ∀ a → kernel ∣ ν ∣ (a , νInv (∣ ν ∣ a))
    ξ a = (η (∣ ν ∣ a))⁻¹

    τφν : ∣ τ ∣ ≡ φ ∘ ∣ ν ∣
    τφν = fxy λ x → Kντ (ξ x)

    φIsHomCB : ∀ 𝑓 c → φ ((𝑓 ̂ 𝑪) c) ≡ ((𝑓 ̂ 𝑩)(φ ∘ c))
    φIsHomCB 𝑓 c = φ ((𝑓 ̂ 𝑪) c) ≡⟨ cong φ (wd (𝑓 ̂ 𝑪) c (∣ ν ∣ ∘ (νInv ∘ c)) (λ i → (η (c i))⁻¹)) ⟩
                   φ ((𝑓 ̂ 𝑪)(∣ ν ∣ ∘(νInv ∘ c)))   ≡⟨ cong φ (∥ ν ∥ 𝑓 (νInv ∘ c))⁻¹ ⟩
                   φ (∣ ν ∣((𝑓 ̂ 𝑨)(νInv ∘ c)))     ≡⟨ cong-app(τφν ⁻¹)((𝑓 ̂ 𝑨)(νInv ∘ c))⟩
                   ∣ τ ∣((𝑓 ̂ 𝑨)(νInv ∘ c))         ≡⟨ ∥ τ ∥ 𝑓 (νInv ∘ c) ⟩
                   (𝑓 ̂ 𝑩)(λ x → ∣ τ ∣(νInv (c x))) ∎

\end{code}


---



### ISOMORPHISMS


Two structures are *isomorphic* provided there are homomorphisms going back and forth
between them which compose to the identity map.


\begin{code}

 _≅_ : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → Type _

 𝑨 ≅ 𝑩 =  Σ[ f ∈ hom 𝑨 𝑩 ] Σ[ g ∈ hom 𝑩 𝑨 ]

           ( (∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣) )

\end{code}

Recall, f ≈ g means f and g are *extensionally* (or pointwise) equal.









---

#### (Isomorphism is an equivalence relation)  (skip)

\begin{code}

 ≅-refl : {𝑨 : Algebra α 𝑆} → 𝑨 ≅ 𝑨
 ≅-refl {𝑨 = 𝑨} = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , (λ a → refl) , (λ a → refl)

 ≅-sym : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆} →  𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
 ≅-sym h = fst ∥ h ∥ , fst h , ∥ snd ∥ h ∥ ∥ , ∣ snd ∥ h ∥ ∣

 ≅-trans : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆}
  →        𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪
 ≅-trans {𝑨 = 𝑨} {𝑩}{𝑪} ab bc = f , g , τ , ν
  where
  f1 = ∣ ab ∣
  f2 = ∣ bc ∣
  f = ∘-hom 𝑨 𝑪 f1 f2
  g1 = fst ∥ bc ∥
  g2 = fst ∥ ab ∥
  g = ∘-hom 𝑪 𝑨 g1 g2

  τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (cong ∣ f2 ∣(∣ snd ∥ ab ∥ ∣ (∣ g1 ∣ x)))∙(∣ snd ∥ bc ∥ ∣) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (cong ∣ g2 ∣(∥ snd ∥ bc ∥ ∥ (∣ f1 ∣ x)))∙(∥ snd ∥ ab ∥ ∥) x

\end{code}

---


#### (Lift is an algebraic invariant)   (skip)

The lift operation preserves isomorphism.

  𝑨 ≅ 𝑩   →   Lift-Alg 𝑨 𝓧   ≅  Lift-Alg 𝑩 𝓨

In fact, we even have 𝑨 ≅ Lift-Alg 𝑨 𝓧.

This is why the lift is a workable solution to the technical problems
arising from noncumulativity of Agda's universe hierarchy.

\begin{code}

 open Lift

 Lift-≅ : {𝑨 : Algebra α 𝑆} → 𝑨 ≅ (Lift-Alg 𝑨 β)

 Lift-≅ {β = β}{𝑨 = 𝑨} = 𝓁𝒾𝒻𝓉 𝑨 , 𝓁ℴ𝓌ℯ𝓇 𝑨 , cong-app lift∼lower , cong-app (lower∼lift{β = β})

 Lift-hom : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆} (ℓᵇ : Level)
  →         hom 𝑨 𝑩  →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)







---


 -- Proof.
 Lift-hom {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ (f , fhom) = lift ∘ f ∘ lower , Goal
  where
  lABh : is-homomorphism (Lift-Alg 𝑨 ℓᵃ) 𝑩 (f ∘ lower)
  lABh = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) 𝑩 {lower}{f} (λ _ _ → refl) fhom

  Goal : is-homomorphism(Lift-Alg 𝑨 ℓᵃ)(Lift-Alg 𝑩 ℓᵇ) (lift ∘ (f ∘ lower))
  Goal = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ){f ∘ lower}{lift} lABh λ _ _ → refl


 Lift-Alg-iso : {𝑨 : Algebra α 𝑆}{𝓧 : Level}
                {𝑩 : Algebra β 𝑆}{𝓨 : Level}
                -----------------------------------------
  →             𝑨 ≅ 𝑩 → (Lift-Alg 𝑨 𝓧) ≅ (Lift-Alg 𝑩 𝓨)

 Lift-Alg-iso A≅B = ≅-trans (≅-trans (≅-sym Lift-≅) A≅B) Lift-≅

\end{code}










---


#### TERMS

Let X an arbitrary nonempty collection of variable symbols.

A *word* in the language of 𝑆 is a nonempty finite sequence of members of X ⊎ ∣ 𝑆 ∣.

Let S₀ denote the nullary operation symbols of 𝑆.

Define the sets 𝑇ₙ of *words* over X ⊎ ∣ 𝑆 ∣ by

    𝑇₀ := X ∪ S₀

  𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ

where 𝒯ₙ is the collection of all 𝑓 𝑡 such that 𝑓 : ∣ 𝑆 ∣ and 𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑇ₙ.

The collection of *terms* in the signature 𝑆 over X is

  Term X := ⋃ₙ 𝑇ₙ.









---


#### THE INDUCTIVE TYPE OF TERMS

Terms are simply trees with an operation symbol at each node and a variable
symbol at each leaf (generator).

\begin{code}

 data Term (X : Type χ ) : Type (ov χ)  where

  ℊ : X → Term X       -- (ℊ for "generator")

  node : (f : ∣ 𝑆 ∣) (𝑡 : ∥ 𝑆 ∥ f → Term X) → Term X

\end{code}

Here

* X represents an arbitrary collection of variable symbols.

* ov χ is our shorthand for the universe level 𝓞 ⊔ 𝓥 ⊔ lsuc χ








---



#### THE TERM ALGEBRA

An algebraic structure 𝑻 X called the *term algebra* in 𝑆 over X is

\begin{code}

 𝑻 : (X : Type χ ) → Algebra (ov χ) 𝑆

 𝑻 X = Term X , node

\end{code}

Terms act on other terms---both domain and operations of the algebra are terms.

+ 𝑓 ̂ (𝑻 X) maps a tuple 𝑡 of terms to the formal term 𝑓 𝑡.

+ 𝑻 X is the algebra with universe ∣ 𝑻 X ∣ := Term X and operations 𝑓 ̂ (𝑻 X).










---


#### THE UNIVERSAL PROPERTY of 𝑻 X

The term algebra 𝑻 X is *absolutely free* for 𝑆-algebras:

For every 𝑆-algebra 𝑨,

1. Every function in 𝑋 → ∣ 𝑨 ∣ lifts to a homomorphism in hom (𝑻 X) 𝑨;

2. The homomorphism of item 1 is unique.

Starting with the fact that every map in X → ∣ 𝑨 ∣ lifts to a map in ∣ 𝑻 X ∣ → ∣ 𝑨 ∣
by induction on the structure of the given term.

\begin{code}

 private variable X : Type χ

 free-lift : (𝑨 : Algebra α 𝑆)(h : X → ∣ 𝑨 ∣) → ∣ 𝑻 X ∣ → ∣ 𝑨 ∣

 free-lift _ h (ℊ x)     = h x

 free-lift 𝑨 h (node f 𝑡) = (f ̂ 𝑨) (λ i → free-lift 𝑨 h (𝑡 i))

\end{code}




---

#### EXISTENCE

At the base step the term is ℊ x and the free lift of h agrees with h.

In the inductive step the term is node f 𝑡 and the free lift is defined as
follows:

Assuming we know the image of each subterm 𝑡 i, define the free lift at the full
term by applying f ̂ 𝑨 to the images of subterms.

The free lift so defined is a homomorphism by construction.

\begin{code}

 lift-hom : (𝑨 : Algebra α 𝑆) → (X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨

 lift-hom 𝑨 h = free-lift 𝑨 h , λ f a → cong (f ̂ 𝑨) refl

\end{code}










---


#### UNIQUENESS

Proof that the homomorphism is unique requires a weak form of function
extensionality which we postulate in the premise as swelldef 𝓥 α.

\begin{code}

 free-unique : swelldef 𝓥 α → (𝑨 : Algebra α 𝑆)(g h : hom (𝑻 X) 𝑨)
  →            (∀ x → ∣ g ∣ (ℊ x) ≡ ∣ h ∣ (ℊ x))
               ----------------------------------------
  →            ∀ (t : Term X) →  ∣ g ∣ t ≡ ∣ h ∣ t

 free-unique _ _ _ _ p (ℊ x) = p x

 free-unique wd 𝑨 g h p (node 𝑓 𝑡) =

  ∣ g ∣ (node 𝑓 𝑡)    ≡⟨ ∥ g ∥ 𝑓 𝑡 ⟩
  (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)  ≡⟨ wd (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)(∣ h ∣ ∘ 𝑡)(λ i → free-unique wd 𝑨 g h p (𝑡 i)) ⟩
  (𝑓 ̂ 𝑨)(∣ h ∣ ∘ 𝑡)  ≡⟨ (∥ h ∥ 𝑓 𝑡)⁻¹ ⟩
  ∣ h ∣ (node 𝑓 𝑡)    ∎

\end{code}

(See Overture.Extensionality for definition of swelldef.)




---




### (Term Operations)  (skip)

For a term p, the *term operation* 𝑨 ⟦ p ⟧ is the *interpretation* of p in 𝑨.

1. If p is ℊ x and a : X → ∣ 𝑨 ∣ is 𝑎 tuple in ∣ 𝑨 ∣, then  𝑨 ⟦ p ⟧ 𝑎 := 𝑎 x.

2. If p = 𝑓 𝑡, where 𝑡 is a tuple of terms, and if 𝑎 is a tuple from 𝑨, then

   𝑨 ⟦ p ⟧ 𝑎 = 𝑨 ⟦ 𝑓 𝑡 ⟧ 𝑎 := (𝑓 ̂ 𝑨) (λ i → 𝑨 ⟦ 𝑡 i ⟧ 𝑎)

Here is the agda-algebras implementation.

\begin{code}

 _⟦_⟧ : (𝑨 : Algebra α 𝑆){X : Type χ } → Term X → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
 𝑨 ⟦ ℊ x ⟧ = λ η → η x
 𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → (𝑓 ̂ 𝑨) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)

\end{code}







---


#### (Compatibility of Terms) (skip)

We now prove two important facts about term operations.  The first of these, which is used
very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

 comm-hom-term : swelldef 𝓥 β → {𝑨 : Algebra α 𝑆} (𝑩 : Algebra β 𝑆)
                 (h : hom 𝑨 𝑩){X : Type χ}(t : Term X) (a : X → ∣ 𝑨 ∣)
                 -----------------------------------------
   →             ∣ h ∣ ((𝑨 ⟦ t ⟧) a) ≡ (𝑩 ⟦ t ⟧) (∣ h ∣ ∘ a)

 comm-hom-term _ 𝑩 h (ℊ x) a = refl
 comm-hom-term wd {𝑨} 𝑩 h (node 𝑓 𝑡) a = ∣ h ∣((𝑓 ̂ 𝑨) λ i →  (𝑨 ⟦ 𝑡 i ⟧) a)    ≡⟨ i  ⟩
                                          (𝑓 ̂ 𝑩)(λ i →  ∣ h ∣ ((𝑨 ⟦ 𝑡 i ⟧) a))  ≡⟨ ii ⟩
                                          (𝑓 ̂ 𝑩)(λ r → (𝑩 ⟦ 𝑡 r ⟧) (∣ h ∣ ∘ a)) ∎
  where i  = ∥ h ∥ 𝑓 λ r → (𝑨 ⟦ 𝑡 r ⟧) a
        ii = wd (𝑓 ̂ 𝑩) (λ i₁ → ∣ h ∣ ((𝑨 ⟦ 𝑡 i₁ ⟧) a))
                        (λ r → (𝑩 ⟦ 𝑡 r ⟧) (λ x → ∣ h ∣ (a x)))
                        λ j → comm-hom-term wd 𝑩 h (𝑡 j) a

\end{code}






---



### (Subuniverses)  (skip)

Suppose 𝑨 is an algebra.  A subset B ⊆ ∣ 𝑨 ∣ is said to be **closed under the operations
of** 𝑨 if for each 𝑓 ∈ ∣ 𝑆 ∣ and all tuples 𝒃 : ∥ 𝑆 ∥ 𝑓 → 𝐵 the element (𝑓 ̂ 𝑨) 𝒃 belongs
to B.

If a subset B ⊆ 𝐴 is closed under the operations of 𝑨, then we call B a **subuniverse** of 𝑨.

We first show how to represent the collection of subuniverses of an algebra 𝑨.

Since a subuniverse is viewed as a subset of the domain of 𝑨, we define it as a
predicate on ∣ 𝑨 ∣.  Thus, the collection of subuniverses is a predicate on predicates
on ∣ 𝑨 ∣.

\begin{code}

 Subuniverses : (𝑨 : Algebra α 𝑆) → Pred (Pred ∣ 𝑨 ∣ β) _

 Subuniverses 𝑨 B = (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ B → (𝑓 ̂ 𝑨) 𝑎 ∈ B

\end{code}






---




#### (Subuniverse Generation) (skip)

If 𝑨 is an algebra and X ⊆ ∣ 𝑨 ∣ a subset of the domain of 𝑨, then the **subuniverse
of** 𝑨 **generated by** X is typically denoted by Sg<sup>𝑨</sup>(X) and defined
to be the smallest subuniverse of 𝑨 containing X.  Equivalently,

Sgᴬ (X)  =  ⋂ { U : U is a subuniverse of 𝑨 and B ⊆ U }.

We define an inductive type, denoted by Sg, that represents the subuniverse generated by
a given subset of the domain of a given algebra, as follows.

\begin{code}

 data Sg (𝑨 : Algebra α 𝑆)(X : Pred ∣ 𝑨 ∣ β) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
  where
  var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
  app : ∀ f a → Im a ⊆ Sg 𝑨 X → (f ̂ 𝑨) a ∈ Sg 𝑨 X

\end{code}







---




#### (Subuniverse Lemmas) (skip)

By structural induction we prove Sg X is the smallest subuniverse of 𝑨 containing X.

\begin{code}

 sgIsSmallest : {𝓡 : Level}(𝑨 : Algebra α 𝑆){X : Pred ∣ 𝑨 ∣ β}(Y : Pred ∣ 𝑨 ∣ 𝓡)
  →             Y ∈ Subuniverses 𝑨  →  X ⊆ Y  →  Sg 𝑨 X ⊆ Y

 sgIsSmallest _ _ _ XinY (var Xv) = XinY Xv
 sgIsSmallest 𝑨 Y YsubA XinY (app f a SgXa) = Yfa
  where
  IH : Im a ⊆ Y
  IH i = sgIsSmallest 𝑨 Y YsubA XinY (SgXa i)

  Yfa : (f ̂ 𝑨) a ∈ Y
  Yfa = YsubA f a IH

\end{code}

When the element of Sg X is constructed as app f a SgXa, we may assume (the induction
hypothesis) that the arguments in the tuple a belong to Y. Then the result of applying
f to a also belongs to Y since Y is a subuniverse.



---


#### (Subuniverse Lemmas) (skip)

Here we formalize a few basic properties of subuniverses. First, the intersection of
subuniverses is again a subuniverse.

\begin{code}

 sub-intersection : {𝓘 : Level}{𝑨 : Algebra α 𝑆}{I : Type 𝓘}{𝒜 : I → Pred ∣ 𝑨 ∣ β}
  →                 (( i : I ) → 𝒜 i ∈ Subuniverses 𝑨)
                    ----------------------------------
  →                 ⋂ I 𝒜 ∈ Subuniverses 𝑨

 sub-intersection σ f a ν = λ i → σ i f a (λ x → ν x i)

\end{code}

In the proof above, we assume the following typing judgments:


 σ : ∀ i → 𝒜 i ∈ Subuniverses 𝑨
 f : ∣ 𝑆 ∣
 a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣
 ν : Im 𝑎 ⊆ ⋂ I 𝒜

and we must prove (f ̂ 𝑨) a ∈ ⋂ I 𝒜. In this case, Agda will fill in the proof term
λ i → σ i f a (λ x → ν x i) automatically with the command C-c C-a.


---

#### (Subuniverse Lemmas)  (skip)

Next we prove the important fact that homomorphisms are uniquely determined by their
values on a generating set.

\begin{code}

 hom-unique : swelldef 𝓥 β → {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}
              (X : Pred ∣ 𝑨 ∣ α)  (g h : hom 𝑨 𝑩)
  →           ((x : ∣ 𝑨 ∣) → (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x))
              -------------------------------------------------
  →           (a : ∣ 𝑨 ∣) → (a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

 hom-unique _ _ _ _ σ a (var x) = σ a x

 hom-unique wd {𝑨}{𝑩} X g h σ fa (app 𝑓 a ν) = Goal
  where
  IH : ∀ x → ∣ g ∣ (a x) ≡ ∣ h ∣ (a x)
  IH x = hom-unique wd{𝑨}{𝑩} X g h σ (a x) (ν x)

  Goal : ∣ g ∣ ((𝑓 ̂ 𝑨) a) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) a)
  Goal = ∣ g ∣ ((𝑓 ̂ 𝑨) a)   ≡⟨ ∥ g ∥ 𝑓 a ⟩
         (𝑓 ̂ 𝑩)(∣ g ∣ ∘ a ) ≡⟨ wd (𝑓 ̂ 𝑩) (∣ g ∣ ∘ a) (∣ h ∣ ∘ a) IH ⟩
         (𝑓 ̂ 𝑩)(∣ h ∣ ∘ a)  ≡⟨ ( ∥ h ∥ 𝑓 a )⁻¹ ⟩
         ∣ h ∣ ((𝑓 ̂ 𝑨) a )  ∎

\end{code}


---

In the induction step, the following typing judgments are assumed:


wd  : swelldef 𝓥 β
𝑨   : Algebra α 𝑆
𝑩   : Algebra β 𝑆
X   : Pred ∣ 𝑨 ∣ α
g h  : hom 𝑨 𝑩
σ   : Π x ꞉ ∣ 𝑨 ∣ , (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x)
fa  : ∣ 𝑨 ∣
fa  = (𝑓 ̂ 𝑨) a
𝑓   : ∣ 𝑆 ∣
a   : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣
ν   : Im a ⊆ Sg 𝑨 X


and, under these assumptions, we proved ∣ g ∣ ((𝑓 ̂ 𝑨) a) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) a).












---

### (Subalgebras) (skip)

Given algebras 𝑨 : Algebra α 𝑆 and 𝑩 : Algebra𝓦β 𝑆, we say that 𝑩 is a
**subalgebra** of 𝑨 just in case 𝑩 can be *homomorphically embedded* in 𝑨.

That is, there exists a map h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣ that is a hom and embedding.

\begin{code}

 module _ {α β : Level} where

  _IsSubalgebraOf_ : (𝑩 : Algebra β 𝑆)(𝑨 : Algebra α 𝑆) → Type _
  𝑩 IsSubalgebraOf 𝑨 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

  Subalgebra : Algebra α 𝑆 → Type _
  Subalgebra 𝑨 = Σ[ 𝑩 ∈ (Algebra β 𝑆) ] 𝑩 IsSubalgebraOf 𝑨

\end{code}

An simpler alternative would be to proclaim 𝑩 is a subalgebra of 𝑨 iff there is an
injective homomorphism from 𝐵 into 𝑨.

In preparation for the next major release of the agda-algebras library, we will
investigate the consequences of taking that path instead of the stricter embedding
requirement we chose for the definition of the type IsSubalgebraOf.




---






#### (The Subalgebra Relation) (skip)

For convenience, we define the following shorthand for the subalgebra relation.

\begin{code}

 _≤_ : Algebra β 𝑆 → Algebra α 𝑆 → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 𝑩 ≤ 𝑨 = 𝑩 IsSubalgebraOf 𝑨

\end{code}

From now on we will use 𝑩 ≤ 𝑨 to express the assertion that 𝑩 is a subalgebra of 𝑨.












---



#### (Subalgebras of a Class) (skip)

Suppose 𝒦 : Pred (Algebra α 𝑆) γ denotes a class of 𝑆-algebras and 𝑩 : Algebra β 𝑆
denotes an arbitrary 𝑆-algebra. Then we might wish to consider the assertion that 𝑩 is
a subalgebra of an algebra in the class 𝒦.  The next type we define allows us to express
this assertion as 𝑩 IsSubalgebraOfClass 𝒦.

\begin{code}

 module _ {α β : Level} where

  _IsSubalgebraOfClass_ : Algebra β 𝑆 → Pred (Algebra α 𝑆) γ → Type _

  𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ Algebra α 𝑆 ] Σ[ sa ∈ Subalgebra {α}{β} 𝑨 ] ((𝑨 ∈ 𝒦) × (𝑩 ≅ ∣ sa ∣))

\end{code}

Using this type, we express the collection of all subalgebras of algebras in a class by the type SubalgebraOfClass, which we now define.

\begin{code}

  SubalgebraOfClass : Pred (Algebra α 𝑆)(ov α) → Type _
  SubalgebraOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra β 𝑆 ] 𝑩 IsSubalgebraOfClass 𝒦

\end{code}

---





### VARIETIES, MODEL THEORY, AND EQUATIONAL LOGIC

We define the binary "models" relation ⊧ relating algebras (or classes of
algebras) to the identities they satisfy.

We prove some closure and invariance properties of ⊧.

In particular,

* [Algebraic invariance]
  ⊧  is an *algebraic invariant* (stable under isomorphism).

* [Subalgebraic invariance]
  ⊧ is a *subalgebraic invariant*

* [Product invariance]
  ⊧ is preserved under the taking of products








---




#### THE MODELS RELATION ⊧

The "models" relation ⊧ is a binary relation from algebras to equations.

For a pair p q of terms, 𝑨 ⊧ p ≈ q means the identity ∀ x → p x ≡ q x holds in 𝑨.

For a class 𝒦, we write 𝒦 ⊧ p ≋ q when 𝑨 ⊧ p ≈ q holds for all 𝑨 ∈ 𝒦.

\begin{code}

 module _ {X : Type χ} where

  _⊧_≈_ : Algebra α 𝑆 → Term X → Term X → Type(α ⊔ χ)
  𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

  _⊧_≋_ : Pred(Algebra α 𝑆)(ov α) → Term X → Term X → Type(χ ⊔ ov α)
  𝒦 ⊧ p ≋ q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}







---



#### (Semantics of ⊧) (skip)

The expression 𝑨 ⊧ p ≈ q represents the assertion that the identity p ≈ q holds
when interpreted in the algebra 𝑨; syntactically, 𝑨 ⟦ p ⟧ ≡ 𝑨 ⟦ q ⟧.

It should be emphasized that the expression  𝑨 ⟦ p ⟧ ≡ 𝑨 ⟦ q ⟧ interpreted
computationally as an *extensional equality* in the following sense:

For each "environment" ρ :  X → ∣ 𝑨 ∣, we have  𝑨 ⟦ p ⟧ ρ  ≡ 𝑨 ⟦ q ⟧ ρ.


















---



#### EQUATIONAL THEORIES AND MODELS

For a class 𝒦 of algebras, Th 𝒦 is the set of ids modeled by all members of 𝒦.

\begin{code}

 Th : {X : Type χ} → Pred (Algebra α 𝑆)(ov α) → Pred(Term X × Term X)(χ ⊔ ov α)

 Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

\end{code}

For a set ℰ of identities, Mod ℰ is the class of algebras satisfying all ids in ℰ.

\begin{code}

 Mod : {X : Type χ} → Pred(Term X × Term X)(χ ⊔ ov α) → Pred(Algebra α 𝑆) (ov (χ ⊔ α))

 Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

\end{code}






---


#### (Identitied and Homs) (skip)

More generally, an identity is satisfied by all algebras in a class if and only if that
identity is invariant under all homomorphisms from the term algebra 𝑻 X into algebras of
the class. More precisely, if 𝒦 is a class of 𝑆-algebras and 𝑝, 𝑞 terms in the
language of 𝑆, then,


  𝒦 ⊧ p ≈ q  ⇔  ∀ 𝑨 ∈ 𝒦,  ∀ φ : hom (𝑻 X) 𝑨,  φ ∘ (𝑻 X)⟦ p ⟧ = φ ∘ (𝑻 X)⟦ q ⟧.


\begin{code}

 module _ (wd : SwellDef){X : Type χ}{𝒦 : Pred (Algebra α 𝑆)(ov α)}  where

  -- ⇒ (the "only if" direction)
  ⊧-H-class-invar : {p q : Term X}
   →                𝒦 ⊧ p ≋ q → ∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∀ a → ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)
  ⊧-H-class-invar {p = p}{q} σ 𝑨 φ ka a = ξ
   where
   ξ : ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)
   ξ = ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a)  ≡⟨ comm-hom-term (wd 𝓥 α) 𝑨 φ p a ⟩
         (𝑨 ⟦ p ⟧)(∣ φ ∣ ∘ a)   ≡⟨ (σ ka) (∣ φ ∣ ∘ a) ⟩
         (𝑨 ⟦ q ⟧)(∣ φ ∣ ∘ a)   ≡⟨ (comm-hom-term (wd 𝓥 α) 𝑨 φ q a)⁻¹ ⟩
         ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)  ∎



---

  -- ⇐ (the "if" direction)
  ⊧-H-class-coinvar : {p q : Term X}
   →  (∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∀ a → ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)) → 𝒦 ⊧ p ≋ q

  ⊧-H-class-coinvar {p}{q} β {𝑨} ka = goal
   where
   φ : (a : X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
   φ a = lift-hom 𝑨 a

   goal : 𝑨 ⊧ p ≈ q
   goal a = (𝑨 ⟦ p ⟧)(∣ φ a ∣ ∘ ℊ)     ≡⟨(comm-hom-term (wd 𝓥 α) 𝑨 (φ a) p ℊ)⁻¹ ⟩
               (∣ φ a ∣ ∘ (𝑻 X ⟦ p ⟧)) ℊ  ≡⟨ β 𝑨 (φ a) ka ℊ ⟩
               (∣ φ a ∣ ∘ (𝑻 X ⟦ q ⟧)) ℊ  ≡⟨ (comm-hom-term (wd 𝓥 α) 𝑨 (φ a) q ℊ) ⟩
               (𝑨 ⟦ q ⟧)(∣ φ a ∣ ∘ ℊ)     ∎


\end{code}












---


### EQUATIONAL LOGIC


Fix a signature 𝑆, let 𝒦 be a class of 𝑆-algebras, and define

* H 𝒦 = algebras isomorphic to a homomorphic image of a members of 𝒦;
* S 𝒦 = algebras isomorphic to a subalgebra of a member of 𝒦;
* P 𝒦 = algebras isomorphic to a product of members of 𝒦.

H, S, and P are **closure operators** (expansive, monotone, and idempotent).



A *variety* is a class of algebras, in the same signature, that is closed under
the taking of homomorphic images, subalgebras, and arbitrary products.

  𝒦 is a variety   iff    HSP 𝒦 ⊆ 𝒦


To represent varieties in Agda, we define inductive types for the closure
operators H, S, and P that are composable, and an inductive type V which
simultaneously represents closure under all three operators, H, S, and P.





---



#### (The inductive types H, S, P)  (skip)


We import these from sub-modules.

\begin{code}
 open import Varieties.Closure.H {𝑆 = 𝑆} as VC-H public
 open import Varieties.Closure.S {𝑆 = 𝑆} as VC-S public
 open import Varieties.Closure.P {𝑆 = 𝑆} as VC-P public
 open import Varieties.Closure.V {𝑆 = 𝑆} as VC-V public

 open VC-H using (H) public
 open VC-S public
 open VC-P public
 open VC-V public
\end{code}











---



### BIRKHOFF'S THEOREM



Theorem (Birkhoff, 1935).  A variety is an equational class.





That is, a class 𝒦 of algebras is a variety (HSP(𝒦) ⊆ 𝒦)

  iff

𝒦 is the class of algebras satisfying a particular set of identities.












---


#### BIRKHOFF'S THEOREM (the hard direction)


Goal:   Mod X (Th (V 𝒦))  ⊆  V 𝒦


(Any algebra modeling all equations in Th (V 𝒦) belongs to V 𝒦.)


This will prove that V 𝒦 is an "equational class."

Indeed, V 𝒦 is the class satsifying the identities in Th (V 𝒦)!


We prove Goal by constructing an algebra 𝔽 with the following properties:

1. 𝔽 ∈ V 𝒦  and

2. Every 𝑨 ∈ Mod X (Th (V 𝒦)) is a homomorphic image of 𝔽 and so belongs to V 𝒦.









---------


[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team



---

#### REFERENCES

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
[Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29)
[section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html)
[Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality)
[this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe)
[Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda)


----------------------------

--------------------------------------




---

#### COMPATIBILITY OF OPERATIONS WITH BINARY RELATIONS

For types A and I,  let  𝑓 : Op A {I}  and   R : BinRel A β.

We say  𝑓  and  R  are *compatible* just in case  ∀ u v : I → A,

  ∀ i  →  R (u i) (v i)  →  R (f u) (f v).

This is implemented in the agda-algebras library as follows:

-- First lift the relation from pairs in A × A to pairs in Aᴵ × Aᴵ.

eval-rel : {A : Type α}{I : Arity 𝓥 } → BinRel A ρ → BinRel (I → A) (𝓥 ⊔ ρ)
eval-rel R u v = ∀ i → R (u i) (v i)

_preserves_ : {A : Type α}{I : Arity 𝓥 } → Op A{I} → BinRel A ρ → Type _
f preserves R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

-- "f preserves R"  iff  ∀ (u , v) ∈ (eval-rel R)  →  (f u) (f v) ∈ R

-- Shorthand
_|:_ : {A : Type α}{I : Arity 𝓥 } → Op A{I} → BinRel A ρ → Type _
f |: R  = (eval-rel R) =[ f ]⇒ R


-- ---

-- #### COMPATIBILITY OF OPERATIONS AND GENERAL RELATIONS

-- The analogous type for dependent relations looks more complicated, but the idea
-- is equally simple.

eval-Ρ : {I J : Arity 𝓥 }{𝒜 : I → Type α}
  →      Ρ I 𝒜 {ρ}                -- "subsets" of Π[ i ∈ I ] 𝒜 i
                                   -- Π[ i ∈ I ] 𝒜 i is a type of (dependent) "tuples"
  →      ((i : I) → J → 𝒜 i)      -- an I-tuple of (𝒥 i)-tuples
  →      Type _

eval-Ρ{I = I}{J}{𝒜} R t = ∀ j → R λ i → (t i) j

compatible-Ρ : {I J : Arity 𝓥 }{𝒜 : I → Type α}
  →              (∀ i → Op (𝒜 i){J})  -- for each i, an operation of type  (J → 𝒜 i) → 𝒜 i
  →              Ρ I 𝒜 {ρ}            -- a subset of Π[ i ∈ I ] 𝒜 i
                                      -- where Π[ i ∈ I ] 𝒜 i is a "set" of (dependent) "tuples"
  →              Type _

compatible-Ρ {I = I}{J}{𝒜} 𝑓 R = Π[ t ∈ ((i : I) → J → 𝒜 i) ] eval-Ρ R t

* eval-Ρ  "lifts" an I-ary relation to an (I → J)-ary relation.
  The lifted relation will relate an I-tuple of J-tuples when the "I-slices"
  (or "rows") of the J-tuples belong to the original relation.

* compatible-Ρ denotes compatibility of an operation with a dependent relation.

---






#### COMPATIBILITY OF TERMS AND CONGRUENCES

To conclude this module, we prove that every term is compatible with every congruence
relation. That is, if t : Term X and θ : Con 𝑨, then a θ b → t(a) θ t(b).

 open IsCongruence
 _∣:_ : {𝑨 : Algebra α 𝑆}(t : Term X)(θ : Con 𝑨 {ρ}) → (𝑨 ⟦ t ⟧) |: ∣ θ ∣
 ((ℊ x) ∣: θ) p = p x
 ((node 𝑓 𝑡) ∣: θ) p = is-compatible ∥ θ ∥ 𝑓 _ _ λ i → (𝑡 i ∣: θ) p





Classically, a *signature*  𝑆 = (𝐶, 𝐹, 𝑅, ρ)  consists of three (possibly empty) sets
(constant, function, and relation symbols) and an arity function

    ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁

assigning an *arity* to each symbol.



#### (Compatibility of binary relations with algebras)

We now define the function compatible so that, if 𝑨 is an algebra and R a binary
relation, then compatible 𝑨 R is the assertion that R is *compatible* with
all basic operations of 𝑨.

The formal definition is immediate since all the work is already done by the "preserves" relation
defined earlier.

 compatible : (𝑨 : Algebra α 𝑆) → BinRel ∣ 𝑨 ∣ ρ → Type _
 compatible  𝑨 R = ∀ 𝑓 → (𝑓 ̂ 𝑨) preserves R














---





#### COMPATIBILITY OF ALGEBRAS WITH GENERAL (RHO) RELATIONS

We defined compatible-Ρ to represent the assertion that a given dependent
relation is compatible with a given operation.

The following represents compatibility of a dependent relation with all
operations of an algebra.

 -- compatible-Ρ-alg : {I : Arity 𝓥} (𝒜 : I → Algebra α 𝑆) → Ρ I (λ i → ∣ 𝒜  i ∣) {ρ} → Type _
 -- compatible-Ρ-alg 𝒜 R = ∀ 𝑓 →  compatible-Ρ (λ i → 𝑓 ̂ (𝒜 i)) R












---




#### PRODUCTS OF ARBITRARY CLASSES OF ALGEBRAS

Observe that Π 𝒦 is certainly not what we want.

(Recall Pred (Algebra α 𝑆) β is the function type Algebra α 𝑆 → Type β, and the
semantics of the latter takes 𝒦 𝑨 to mean 𝑨 ∈ 𝒦. Thus, by definition, 

 Π 𝒦   :=   Π[ 𝑨 ∈ (Algebra α 𝑆) ] 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α 𝑆) → 𝑨 ∈ 𝒦,

which simply asserts that every inhabitant of Algebra α 𝑆 belongs to 𝒦.

We need a type that indexes the class 𝒦, and a function 𝔄 that maps an index to the
inhabitant of 𝒦 at that index.

But 𝒦 is a predicate (of type (Algebra α 𝑆) → Type β) and the type Algebra α 𝑆 seems
rather nebulous in that there is no natural indexing class with which to "enumerate" all
inhabitants of Algebra α 𝑆 belonging to 𝒦.









---


---


#### (Homomorphism factorization)

If in addition we assume τ is epic, then so is φ.

  HomFactorEpi : funext α β → swelldef 𝓥 γ
   →             (𝑩 : Algebra β 𝑆)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
   →             kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣
   →             IsSurjective ∣ ν ∣ → IsSurjective ∣ τ ∣
                 ---------------------------------------------
   →             Σ[ φ ∈ epi 𝑪 𝑩 ] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣

  HomFactorEpi fxy wd 𝑩 τ ν kerincl νe τe = (fst ∣ φF ∣ ,(snd ∣ φF ∣ , φE)), ∥ φF ∥
   where
    φF : Σ[ φ ∈ hom 𝑪 𝑩 ] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣
    φF = HomFactor fxy wd 𝑩 τ ν kerincl νe

    φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
    φ = ∣ τ ∣ ∘ (SurjInv ∣ ν ∣ νe)

    φE : IsSurjective φ
    φE = epic-factor  ∣ τ ∣ ∣ ν ∣ φ ∥ φF ∥ τe



---

#### (Interpretation of a term is the free-lift)

It turns out that the intepretation of a term is the same as the free-lift (modulo
argument order and assuming function extensionality).


 free-lift-interp : swelldef 𝓥 α → (𝑨 : Algebra α 𝑆){X : Type χ }(η : X → ∣ 𝑨 ∣)(p : Term X)
  →                 (𝑨 ⟦ p ⟧) η ≡ (free-lift 𝑨 η) p

 free-lift-interp _ 𝑨 η (ℊ x) = refl
 free-lift-interp wd 𝑨 η (node 𝑓 𝑡) = wd (𝑓 ̂ 𝑨) (λ z → (𝑨 ⟦ 𝑡 z ⟧) η)
                                       ((free-lift 𝑨 η) ∘ 𝑡)((free-lift-interp wd 𝑨 η) ∘ 𝑡)


If the algebra 𝑨 happens to be 𝑻 X, then we expect that ∀ 𝑠 we have (𝑻 X)⟦ p ⟧ 𝑠 ≡ p
𝑠. But what is (𝑻 X)⟦ p ⟧ 𝑠 exactly? By definition, it depends on the form of p as
follows: 

* if p = ℊ x, then (𝑻 X)⟦ p ⟧ 𝑠 := (𝑻 X)⟦ ℊ x ⟧ 𝑠 ≡ 𝑠 x

* if p = node 𝑓 𝑡, then (𝑻 X)⟦ p ⟧ 𝑠 := (𝑻 X)⟦ node 𝑓 𝑡 ⟧ 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑻 X)⟦ 𝑡 i ⟧ 𝑠

Now, assume ϕ : hom 𝑻 𝑨. Then by comm-hom-term, we have ∣ ϕ ∣ (𝑻 X)⟦ p ⟧ 𝑠 = 𝑨 ⟦ p ⟧ ∣ ϕ ∣ ∘ 𝑠.

* if p = ℊ x (and 𝑡 : X → ∣ 𝑻 X ∣), then

  ∣ ϕ ∣ p ≡ ∣ ϕ ∣ (ℊ x) ≡ ∣ ϕ ∣ (λ 𝑡 → h 𝑡) ≡ λ 𝑡 → (∣ ϕ ∣ ∘ 𝑡) x

---

* if p = node 𝑓 𝑡, then

   ∣ ϕ ∣ p ≡ ∣ ϕ ∣ (𝑻 X)⟦ p ⟧ 𝑠 = (𝑻 X)⟦ node 𝑓 𝑡 ⟧ 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑻 X)⟦ 𝑡 i ⟧ 𝑠

We claim that for all p : Term X there exists q : Term X and
𝔱 : X → ∣ 𝑻 X ∣ such that p ≡ (𝑻 X)⟦ q ⟧ 𝔱. We prove this fact as follows.


 term-interp : {X : Type χ} (𝑓 : ∣ 𝑆 ∣){𝑠 𝑡 : ∥ 𝑆 ∥ 𝑓 → Term X} → 𝑠 ≡ 𝑡 → node 𝑓 𝑠 ≡ (𝑓 ̂ 𝑻 X) 𝑡
 term-interp 𝑓 {𝑠}{𝑡} st = cong (node 𝑓) st

 term-interp' : swelldef 𝓥 (ov χ) → {X : Type χ} (𝑓 : ∣ 𝑆 ∣){𝑠 𝑡 : ∥ 𝑆 ∥ 𝑓 → Term X}
  →             (∀ i → 𝑠 i ≡ 𝑡 i) → node 𝑓 𝑠 ≡ (𝑓 ̂ 𝑻 X) 𝑡
 term-interp' wd 𝑓 {𝑠}{𝑡} st = wd (node 𝑓) 𝑠 𝑡 st

 term-gen : swelldef 𝓥 (ov χ) → {X : Type χ}(p : ∣ 𝑻 X ∣) → Σ[ q ∈ ∣ 𝑻 X ∣ ] p ≡ (𝑻 X ⟦ q ⟧) ℊ
 term-gen _ (ℊ x) = (ℊ x) , refl
 term-gen wd (node 𝑓 t) = (node 𝑓 (λ i → ∣ term-gen wd (t i) ∣)) ,
                          term-interp' wd 𝑓 λ i → ∥ term-gen wd (t i) ∥

 term-gen-agreement : (wd : swelldef 𝓥 (ov χ)){X : Type χ}(p : ∣ 𝑻 X ∣) → (𝑻 X ⟦ p ⟧) ℊ ≡ (𝑻 X ⟦ ∣ term-gen wd p ∣ ⟧) ℊ
 term-gen-agreement _ (ℊ x) = refl
 term-gen-agreement wd {X} (node f t) = wd (f ̂ 𝑻 X) (λ x → (𝑻 X ⟦ t x ⟧) ℊ)
                                          (λ x → (𝑻 X ⟦ ∣ term-gen wd (t x) ∣ ⟧) ℊ) λ i → term-gen-agreement wd (t i)

 term-agreement : swelldef 𝓥 (ov χ) → {X : Type χ}(p : ∣ 𝑻 X ∣) → p ≡  (𝑻 X ⟦ p ⟧) ℊ
 term-agreement wd {X} p = ∥ term-gen wd p ∥ ∙ (term-gen-agreement wd p)⁻¹

---
---



#### HOMOMORPHIC INVARIANCE OF ⊧

If an algebra 𝑨 models an identity p ≈ q, then the pair (p , q) belongs to the kernel of
every homomorphism φ : hom (𝑻 X) 𝑨 from the term algebra to 𝑨; that is, every homomorphism
from 𝑻 X to 𝑨 maps p and q to the same element of 𝑨.


 module _ (wd : SwellDef){X : Type χ}{𝑨 : Algebra α 𝑆} where

  ⊧-H-invar : {p q : Term X}(φ : hom (𝑻 X) 𝑨) → 𝑨 ⊧ p ≈ q  →  ∣ φ ∣ p ≡ ∣ φ ∣ q

  ⊧-H-invar {p}{q}φ β = ∣ φ ∣ p               ≡⟨ cong ∣ φ ∣(term-agreement(wd 𝓥 (ov χ)) p)⟩
                       ∣ φ ∣((𝑻 X ⟦ p ⟧) ℊ)  ≡⟨ comm-hom-term (wd 𝓥 α) 𝑨 φ p ℊ ⟩
                       (𝑨 ⟦ p ⟧) (∣ φ ∣ ∘ ℊ) ≡⟨ β (∣ φ ∣ ∘ ℊ ) ⟩
                       (𝑨 ⟦ q ⟧) (∣ φ ∣ ∘ ℊ) ≡⟨ (comm-hom-term (wd 𝓥 α)  𝑨 φ q ℊ )⁻¹ ⟩
                       ∣ φ ∣ ((𝑻 X ⟦ q ⟧) ℊ) ≡⟨(cong ∣ φ ∣ (term-agreement (wd 𝓥 (ov χ)) q))⁻¹ ⟩
                       ∣ φ ∣ q               ∎



