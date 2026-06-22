---
layout: default
file: "src/Examples/PolynomialFunctors/Functors.lagda.md"
title: "Examples.PolynomialFunctors.Functors module (The Agda Universal Algebra Library)"
date: "2026-05-09"
author: "the agda-algebras development team"
---

### Polynomial Functors and W-types

This is the [Examples.PolynomialFunctors.Functors][] module of the [Agda Universal Algebra Library][].

This module is illustrative rather than load-bearing.  It develops a closed-universe
encoding of polynomial functors and their least fixed points (W-types), using the
polymorphic-list datatype as a worked example.  The content was relocated here from
`Legacy.Base.Categories.Functors`;[^1] nothing in the canonical `Setoid/`,
`Classical/`, or planned `Cubical/` development of the library depends on it.

The main reference is
[Schwaab and Siek, *Modular Type-Safety Proofs in Agda* (PLPV '07)](https://doi.org/10.1145/2428116.2428120).


#### Functors

Recall, a *functor* `F` is a function that maps the objects and morphisms of one
category 𝐂 to the objects and morphisms of a category 𝐃 in such a way that the
following *functor laws* are satisfied:

* `∀ f g, F(f ∘ g) = F(f) ∘ F(g)`
* `∀ A, F(id A) = id (F A)`  (where `id X` denotes the identity morphism on X)


#### Polynomial functors

An important class of functors for our domain is the class of so called
*polynomial functors*.  These are functors that are built up using the constant,
identity, sum, and product functors.  To be precise, the actions of the latter on
objects are as follows: `∀ A B` (objects), `∀ F G` (functors),

* `const B A = B`
* `Id A = A`
* `(F + G) A = F A + G A`
* `(F × G) A = F A × G A`

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.PolynomialFunctors.Functors where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library  ---------------------------------------
open import Data.Nat                               using ( ℕ ; zero ; suc ; _>_ )
open import Data.Product                           using ( _,_ ; _×_ )
open import Data.Sum.Base                          using ( _⊎_ )
                                                   renaming ( inj₁ to inl ; inj₂ to inr )
open import Data.Unit                              using () renaming ( tt to 𝟎 )
open import Data.Unit.Polymorphic                  using ( ⊤ )
open import Level                                  using ( Level )
                                                   renaming (suc to lsuc ; 0ℓ to ℓ₀ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; _≢_ )

private variable α β : Level

infixl 6 _⊕_
infixr 7 _⊗_

data Functor₀ : Type (lsuc ℓ₀) where
 Id : Functor₀
 Const : Type → Functor₀
 _⊕_ : Functor₀ → Functor₀ → Functor₀
 _⊗_ : Functor₀ → Functor₀ → Functor₀

[_]₀ : Functor₀ → Type → Type
[ Id ]₀ B = B
[ Const C ]₀ B = C
[ F ⊕ G ]₀ B = [ F ]₀ B ⊎ [ G ]₀ B
[ F ⊗ G ]₀ B = [ F ]₀ B × [ G ]₀ B

data Functor {ℓ : Level} : Type (lsuc ℓ) where
 Id : Functor
 Const : Type ℓ → Functor
 _⊕_ : Functor{ℓ} → Functor{ℓ} → Functor
 _⊗_ : Functor{ℓ} → Functor{ℓ} → Functor

[_]_ : Functor → Type α → Type α
[ Id ] B = B
[ Const C ] B = C
[ F ⊕ G ] B = [ F ] B ⊎ [ G ] B
[ F ⊗ G ] B = [ F ] B × [ G ] B
```

The least fixed point of a polynomial function can then be defined in Agda with the
following datatype declaration.

```agda
data μ_ (F : Functor) : Type where
 inn : [ F ] (μ F) → μ F
```

An important example is the polymorphic list datatype.  The standard way to define
this in Agda is as follows:

```agda
data list (A : Type) : Type ℓ₀ where
 [] : list A
 _∷_ : A → list A → list A
```

We could instead define a `List` datatype by applying `μ` to a polynomial functor `L`
as follows:

```agda
L : {ℓ : Level}(A : Type ℓ) → Functor{ℓ}
L A = Const ⊤ ⊕ (Const A ⊗ Id)

List : (A : Type) → Type ℓ₀
List A = μ (L A)
```

To verify that both formulations of the polymorphic list type give what we expect, we
use "getter" functions, which take a list `l` and a natural number `n` and return the
element of `l` at index `n`.  Since such an element doesn't always exist, we first
define the `Option` type.

```agda
data Option (A : Type) : Type where
 some : A → Option A
 none : Option A

_[_] : {A : Type} → List A → ℕ → Option A
inn (inl x) [ n ] = none
inn (inr (x , xs)) [ zero ] = some x
inn (inr (x , xs)) [ suc n ] = xs [ n ]

_⟦_⟧ : {A : Type} → list A → ℕ → Option A
[] ⟦ n ⟧ = none
(x ∷ l) ⟦ zero ⟧ = some x
(x ∷ l) ⟦ suc n ⟧ = l ⟦ n ⟧
```

### Worked examples

The following examples confirm that the W-type encoding `List A = μ (L A)` and the
standard inductive definition `list A` produce the same observable behavior on small
concrete cases.

```agda
-- 1. Empty list
L₀ : List ℕ
L₀ = inn (inl (Level.lift 𝟎))

l₀ : list ℕ
l₀ = []

-- 2. One-element list, (3)
L₁ : List ℕ
L₁ = inn (inr (3 , L₀))

l₁ : list ℕ
l₁ = 3 ∷ l₀

-- 3. Three-element list, (1, 2, 3)
L₃ : List ℕ
L₃ = inn (inr (1 , (inn (inr (2 , L₁)))))

l₃ : list ℕ
l₃ = 1 ∷ (2 ∷ l₁)

L₀≡none : ∀ {n} → (L₀ [ n ]) ≡ none
L₀≡none = refl

l₀≡none : ∀ {n} → (l₀ ⟦ n ⟧) ≡ none
l₀≡none = refl

L₁[0]≡some3 : L₁ [ 0 ] ≡ some 3
L₁[0]≡some3 = refl

l₁⟦0⟧≡some3 : l₁ ⟦ 0 ⟧ ≡ some 3
l₁⟦0⟧≡some3 = refl

L₁[n>0]≡none : ∀ n → n > 0 → L₁ [ n ] ≡ none
L₁[n>0]≡none (suc n) _ = refl

l₁⟦n>0⟧≡none : ∀ n → n > 0 → l₁ ⟦ n ⟧ ≡ none
l₁⟦n>0⟧≡none (suc n) _ = refl

L₃[0]≡some1 : L₃ [ 0 ] ≡ some 1
L₃[0]≡some1 = refl

l₃⟦0⟧≡some1 : l₃ ⟦ 0 ⟧ ≡ some 1
l₃⟦0⟧≡some1 = refl

L₃[0]≢some2 : L₃ [ 0 ] ≢ some 2
L₃[0]≢some2 = λ ()

l₃[0]≢some2 : l₃ ⟦ 0 ⟧ ≢ some 2
l₃[0]≢some2 = λ ()

L₃[1]≡some2 : L₃ [ 1 ] ≡ some 2
L₃[1]≡some2 = refl

l₃⟦1⟧≡some2 : l₃ ⟦ 1 ⟧ ≡ some 2
l₃⟦1⟧≡some2 = refl

L₃[2]≡some3 : L₃ [ 2 ] ≡ some 3
L₃[2]≡some3 = refl

l₃⟦2⟧≡some3 : l₃ ⟦ 2 ⟧ ≡ some 3
l₃⟦2⟧≡some3 = refl

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀
```

--------------------------------

[^1]: PR #306.

<span style="float:left;">[← Examples.PolynomialFunctors](Examples.PolynomialFunctors.html)</span>

{% include UALib.Links.md %}

<!-- Some helpful excerpts from
     [Modular Type-Safety Proofs in Agda](https://doi.org/10.1145/2428116.2428120)
     by Schwaab and Siek (PLPV '07).

"Our technique is drawn from a solution to the expression problem where languages are
defined as the disjoint sum of smaller languages defined using parameterized
recursion. We show that this idea can be recast from types and terms, to proofs."

2. Review of the Expression Problem

Extending both data structures and the functions that operate on them in a modular
fashion is challenging, this is sometimes referred to as the expression problem. In
most functional languages, it is easy to add functions that operate on existing data
structures but it is difficult to extend a data type with new constructors. On the
other hand, in object-oriented languages, it is easy to extend data structures by
subclassing, but it is difficult to add new functions to existing classes.

While many solutions to the expression problem have been proposed over the years,
here we make use of the method described by Malcom [9] which generalizes recursion
operators such as fold from lists to polynomial types. The expression problem in
functional languages arises as a result of algebraic data types being closed: once
the type has been declared, no new constructors for the type may be added without
amending the original declaration. Malcom's solution is to remove immediate recursion
and split a monolithic datatype into parameterized components that can later be
collected under the umbrella of a disjoint sum (i.e., a tagged union)."

"Users of Coq might wonder why the definition of µ is accepted by Agda; Coq would
reject the above definition of µ because it does not pass Coq's conservative check
for positivity. In this case, Agda's type-checker inspects the behavior of the second
argument to [_]_ building a usage graph and determines that µF will occur positively
in [_]_, − ⊎ −, and − × −."
-->
