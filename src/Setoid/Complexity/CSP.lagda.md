---
layout: default
title : "Setoid.Complexity.CSP module (The Agda Universal Algebra Library)"
date : "2026-05-09"
author: "the agda-algebras development team"
---

### <a id="constraint-satisfaction-problems">Constraint Satisfaction Problems</a>

This is the [Setoid.Complexity.CSP][] module of the [Agda Universal Algebra Library][].

This module is the canonical home for the content previously developed in `Legacy.Base.Complexity.CSP`, ported under #307 (M2-7c).  The relational formulation of CSP and the Galois connection to polymorphism clones (Jeavons) are stated below; substantive theorems — most importantly the Jeavons Galois connection itself for a fixed finite domain, and a statement of the Bulatov–Zhuk algebraic dichotomy — are scheduled under #274 (M7-1).  The infinite-template / ω-categorical extension is covered separately under #281 (M9-2), which depends on this canonical-path version.

#### <a id="the-relational-formulation-of-csp">The relational formulation of CSP</a>

Let 𝒜 = (𝐴 , 𝑅ᵃ) be a *relational structure* (or 𝑅-structure), that is, a pair consisting of a set 𝐴 along with a collection 𝑅ᵃ ⊆ ⋃ₙ 𝒫(𝐴ⁿ) of relations on 𝐴.

We associate with 𝒜 a *constraint satisfaction problem* denoted by CSP(𝒜), which is the decision problem that is solved by finding an algorithm or program that does the following:

Take as input
+ an *instance*, which is an 𝑅-structure ℬ = (𝐵 , 𝑅ᵇ) (in the same signature as 𝒜)

Output
+ "yes" or "no" according as there is, or is not, a *solution*, which is a 𝑅-structure homomorphism h : ℬ → 𝒜.

If there is such an algorithm that takes at most a power of 𝑛 operations to process an input structure ℬ of size 𝑛 (i.e., 𝑛 bits of memory are required to encode ℬ), then we say that CSP(𝒜) is *tractable*.  Otherwise, CSP(𝒜) is *intractable*.

Equivalently, if we define

  CSP(𝒜) := \{ ℬ ∣ ℬ an 𝑅-structure and ∃ hom ℬ → 𝒜 \}

then the CSP problem described above is simply the membership problem for the subset CSP(𝒜) of 𝑅 structures having homomorphisms into 𝒜.  That is, our algorithm must take as input an 𝑅-structure (a relational structure in the signature of 𝒜) and decide whether or not it belongs to the set CSP(𝒜).

#### <a id="connection-to-algebraic-csp">Connection to algebraic CSP</a>

Let A be a set, let Op(A) denote the set of all operations, Rel(A) the set of all relations, on A.

Given R ⊆ Rel(A), define the set of operations on A that preserve all relations in R as follows:

∣: ⃖ R  =  \{ f ∈ Op(𝐴) ∣ ∀ r ∈ R, f ∣: r \}.

Recall, f ∣: r is our notation for `f Preserves r ⟶ r`, which means that r is a subuniverse of a power of the algebra (A , {f}).  Equivalently, `f Preserves r ⟶ r` means the following: if f is 𝑚-ary and r is 𝑛-ary, then for every size-𝑚 collection 𝑎𝑠 of 𝑛-tuples from r (that is, ∣ 𝑎𝑠 ∣ = 𝑚 and ∀ a ∈ 𝑎𝑠, r a) we have r (f ∘ (zip 𝑎𝑠)).

If 𝒜 = (A , R) is a relational structure, then the set ∣: ⃖R of operations on A that preserve all relations in R is called the set of *polymorphisms* of 𝒜.

Conversely, starting with a collection F ⊆ Op(A) of operations on A, define the set of all relations preserved by the functions in F as follows:

F ⃗ ∣:  =  \{ r ∈ Rel(A) ∣ ∀ f ∈ F, f ∣: r \}.

It is easy to see that for all F ⊆ Op(A) and all R ⊆ Rel(A), we have

  F ⊆  ∣: ⃖ (F ⃗ ∣:)    and    R ⊆ (∣: ⃖ R) ⃗ ∣:.

Let 𝑨(R) denote the algebraic structure with domain A and operations ∣: ⃖ R.  Then every r ∈ R is a subalgebra of a power of 𝑨(R).  Clearly (∣: ⃖ R) ⃗ ∣: is the set 𝖲 (𝖯fin 𝑨(R)) of subalgebras of finite powers of 𝑨(R).

The reason this Galois connection is useful is due to the following fact (observed by Peter Jeavons in the late 1990's):

*Theorem*. Let 𝒜 = (A, R) be a finite relational structure.
           If R' ⊆ (∣: ⃖ R) ⃗ ∣: is finite, then CSP((A, R'))
           is reducible in poly-time to CSP(𝒜)

In particular, the tractability of CSP(𝒜) depends only on its associated polymorphism algebra, 𝑨(R) := (A , ∣: ⃖ R).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Complexity.CSP {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Function.Base    using ( _∘_ )
open import Relation.Binary  using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
-- NOTE: `Legacy.Base.Relations.Continuous` is imported here because
-- `Setoid.Relations.Continuous` does not yet exist; the port of `Continuous` is
-- tracked under #308 (M2-7d, scheduled with M9).  Per the Category-B contract
-- in `src/Legacy/Base/DEPRECATED.md`, importing from `Legacy.Base.*` is the
-- supported, non-deprecated path until that port lands.  When #308 lands this
-- import will be redirected to the canonical path and the note removed.
open import Legacy.Base.Relations.Continuous  using ( REL ; REL-syntax )
open import Setoid.Algebras.Basic  {𝑆 = 𝑆}    using ( Algebra )
```

#### <a id="constraints">Constraints</a>

A constraint c consists of

1. a scope function,  s : I → var, and
2. a constraint relation, i.e., a predicate over the function type I → D

        I ···> var
         .     .
          .   .
           ⌟ ⌞
            D

The *scope* of a constraint is an indexed subset of the set of variable symbols.  We could define a type for this, e.g.,

    Scope : Type ν → Type ι → _
    Scope V I = I → V

but we omit this definition because it's so simple; to reiterate, a scope of "arity" I on "variables" V is simply a map from I to V, where,

* I denotes the "number" of variables involved in the scope
* V denotes a collection (type) of "variable symbols"

```agda
module  _              -- levels for...
        {ι : Level}    -- ...arity (or argument index) types
        {ν : Level}    -- ...variable symbol types
        {α ρ : Level}  -- ...domain carrier and equivalence levels
        {ρʳ : Level}   -- ...constraint relation level
 where
 open Setoid

 record Constraint (var : Type ν) (dom : var → Setoid α ρ)
                   : Type (ν ⊔ α ⊔ lsuc ι ⊔ lsuc ρʳ) where
  field
   arity  : Type ι               -- The "number" of variables involved in the constraint.
   scope  : arity → var          -- Which variables are involved in the constraint.
   rel    : REL[ i ∈ arity ] (Carrier (dom (scope i))) -- The constraint relation.

  satisfies : ((v : var) → Carrier (dom v)) → Type ρʳ  -- An assignment, 𝑓 : var → dom, of values to variables
  satisfies f = rel (f ∘ scope)                        -- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided
                                                       -- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.
```

**Note on `ρʳ`**.  The constraint-relation level `ρʳ` is fixed at the module level rather than parameterizing each `Constraint` independently.  This matches the universal-algebraic CSP literature, where every constraint of an instance typically lives at the same relation level (in practice `lzero`).  Lifting `ρʳ` to a per-record parameter is a mechanical refactor that may become warranted when later content (e.g., the M7-1 polymorphism-clone development under #274 or the M9-2 infinitary CSP work under #281) needs to mix relation levels across constraints in a single instance.


#### <a id="csp-templates-and-instances">CSP templates and instances</a>

A CSP "template" restricts the relations that may occur in instances of the problem.  A convenient way to specify a template is to give an indexed family 𝒜 : var → Algebra α ρ of algebras (one for each variable symbol in var) and require that relations be subalgebras of the product ⨅ var 𝒜.

To construct a CSP instance, then, we just have to give a family 𝒜 of algebras, specify the number (ar) of constraints, and for each i : ar, define a constraint as a relation over (some of) the members of 𝒜.

An instance of a constraint satisfaction problem is a triple 𝑃 = (𝑉, 𝐷, 𝐶) where
* 𝑉 denotes a set of "variables"
* 𝐷 denotes a "domain",
* 𝐶 denotes an indexed collection of constraints.

```agda
 open Algebra

 record CSPInstance (var : Type ν)(𝒜 : var → Algebra α ρ)
                    : Type (ν ⊔ α ⊔ lsuc ι ⊔ lsuc ρʳ) where
  field
   ar : Type ι       -- ar indexes the constraints in the instance
   cs : (i : ar) → Constraint var (λ v → Domain (𝒜 v))

  isSolution : ((v : var) → Carrier (Domain (𝒜 v))) → Type (ι ⊔ ρʳ)  -- An assignment *solves* the instance
  isSolution f = ∀ i → (Constraint.satisfies (cs i)) f               -- if it satisfies all the constraints.
```

--------------------------------

<span style="float:left;">[← Setoid.Complexity.Basic](Setoid.Complexity.Basic.html)</span>
<span style="float:right;">[Top ↑](index.html)</span>

{% include UALib.Links.md %}
