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

###### (skip)

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}
open import Demos.TYPES2021-shortimports
module Demos.TYPES2021-extrashort  {𝓞 𝓥 : Level} where
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


### DEPENDENT RELATIONS  ("Pi-Rho" types...?)

Remove the single-sorted restriction using dependent types!

For an arbitrary family  𝒜 : I → Type α  consider a relation

     from 𝒜 i  to  𝒜 j  to  𝒜 k  to  …               (*)

In set theory such relations are subsets of Π(i : I) 𝒜 i.

The "indexing" type I might not even be enumerable so (*) is misleading.

The ΠΡ type manifests this completely general notion of relation.

\begin{code} -- arbitrary-sorted relations of arbitrary arity

ΠΡ : (I : Arity 𝓥 ) → (I → Type α) → {ρ : Level} → Type _

ΠΡ I 𝒜 {ρ} = ((i : I) → 𝒜 i) → Type ρ

\end{code}

These are just predicates over dependent function types!





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


#### THE INDUCTIVE TYPE OF TERMS

Terms are simply trees with an operation symbol at each node and a variable
symbol at each leaf (generator).

\begin{code}
module _ {𝑆 : Signature 𝓞 𝓥}  where
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



