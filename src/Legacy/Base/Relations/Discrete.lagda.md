---
layout: default
title : "Base.Relations.Discrete module (The Agda Universal Algebra Library)"
date : "2021-02-28"
author: "the agda-algebras development team"
---

### <a id="discrete-relations">Discrete Relations</a>

This is the [Base.Relations.Discrete][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Legacy.Base.Relations.Discrete where

-- Imports from Agda and the Agda Standard Library ----------------------------------------------
open import Agda.Primitive               using () renaming ( Set to Type )
open import Data.Product                 using ( _,_ ; _×_ )
open import Function.Base                using ( _∘_ )
open import Level                        using ( _⊔_ ; Level ; Lift )
open import Relation.Binary              using ( IsEquivalence ; _⇒_ ; _=[_]⇒_ )
                                      renaming ( REL to BinREL ; Rel to BinRel )
open import Relation.Binary.Definitions  using ( Reflexive ; Transitive )
open import Relation.Unary               using ( _∈_; Pred )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

-- Imports from agda-algebras -------------------------------------------------------------------
open import Overture using (_≈_ ; Π-syntax ; Op)

private variable a b ρ 𝓥 : Level
```


We begin with a definition that is useful for defining poitwise "equality" of functions
with respect to a given "equality" relation (see also the definition of `_≈̇_` in the [Base.Adjunction.Residuation][] module).


```agda


module _ {A : Type a} where

 PointWise : {B : Type b} (_≋_ : BinRel B ρ) → BinRel (A → B) _
 PointWise {B = B} _≋_ = λ (f g : A → B) → ∀ x → f x ≋ g x
```


Thus, given a binary relation `≋` on ‵B`, and a pair of functions `f, g : A → B`,
we have `f (Pointwise _≋_) g` provided `∀ x → f x ≋ g x`.

Here is the analogous definition for dependent functions.


```agda


 depPointWise :  {B : A → Type b }
                 (_≋_ : {γ : Level}{C : Type γ} → BinRel C ρ)
  →              BinRel ((a : A) → B a) _
 depPointWise {B = B} _≋_ = λ (f g : (a : A) → B a) → ∀ x → f x ≋ g x
```


Next we define a type that is useful for asserting that the image of a function
is contained in a particular "subset" (predicate) of the codomain.


```agda
 Im_⊆_ : {B : Type b} → (A → B) → Pred B ρ → Type (a ⊔ ρ)
 Im f ⊆ S = ∀ x → f x ∈ S

 {-# WARNING_ON_USAGE Im_⊆_ "Use Overture.Relations.Im_⊆_ instead. Deprecated under #303." #-}
```



#### <a id="operation-symbols-unary-relations-binary-relations">Operation symbols, unary relations, binary relations</a>

The unary relation (or "predicate") type is imported from Relation.Unary of the [Agda Standard Library][].

`Pred : ∀ {a} → Type a → (ℓ : Level) → Type (a ⊔ suc ℓ)`
`Pred A ℓ = A → Type ℓ`

We represent "sets" as inhabitants of such predicate types.

(In the definition of `Pred` above, we replaced `Set` with `Type` for consistency with our notation.)

Sometimes it is useful to obtain the underlying type (`A`) over which the predicates in `Pred A ℓ` (the "subsets" of `A`) are defined.


```agda


 PredType : Pred A ρ → Type a
 PredType _ = A
```


The binary relation types are called `Rel` and `REL` in the standard library, but we
will call them `BinRel` and `BinREL` and reserve the names `Rel` and `REL` for the relation
types we define below and in the [Base.Relations.Continuous][] module.

We import the "heterogeneous" binary relation type from the standard library and renamed `BinREL`.

`BinREL : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))`
`BinREL A B ℓ' = A → B → Type ℓ'`


A special case, the homogeneous binary relation type is also imported and renamed `BinRel`.

`BinRel : ∀{ℓ} → Type ℓ → (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')`
`BinRel A ℓ' = REL A A ℓ'`

Occasionally it is useful to extract the universe level over which a binary relation is defined.


```agda


 Level-of-Rel : {ℓ : Level} → BinRel A ℓ → Level
 Level-of-Rel {ℓ} _ = ℓ
```



#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`.
This can be represented in type theory and Agda in a number of ways, each of which
may be useful in a particular context. For example, we could define the kernel
to be an inhabitant of a (binary) relation type, or a (unary) predicate type.


```agda


module _ {A : Type a}{B : Type b} where

 ker : (A → B) → BinRel A b
 ker g x y = g x ≡ g y

 kerRel : {ρ : Level} → BinRel B ρ → (A → B) → BinRel A ρ
 kerRel _≈_ g x y = g x ≈ g y

 kernelRel : {ρ : Level} → BinRel B ρ → (A → B) → Pred (A × A) ρ
 kernelRel _≈_ g (x , y) = g x ≈ g y

 open IsEquivalence

 kerRelOfEquiv :  {ρ : Level}{R : BinRel B ρ}
  →               IsEquivalence R → (h : A → B) → IsEquivalence (kerRel R h)

 kerRelOfEquiv eqR h = record  { refl = refl eqR
                               ; sym = sym eqR
                               ; trans = trans eqR
                               }

 kerlift : (A → B) → (ρ : Level) → BinRel A (b ⊔ ρ)
 kerlift g ρ x y = Lift ρ (g x ≡ g y)

 ker' : (A → B) → (I : Type 𝓥) → BinRel (I → A) (b ⊔ 𝓥)
 ker' g I x y = g ∘ x ≡ g ∘ y

 kernel : (A → B) → Pred (A × A) b
 kernel g (x , y) = g x ≡ g y

{-# WARNING_ON_USAGE kerRel "Use Overture.Relations.kerRel instead. Deprecated under #303; removal planned one minor cycle after #303 lands." #-}
{-# WARNING_ON_USAGE kerRelOfEquiv "Use Overture.Relations.kerRelOfEquiv instead. Deprecated under #303; removal planned one minor cycle after #303 lands." #-}
{-# WARNING_ON_USAGE kernelRel "Use Overture.Relations.kernelRel instead. Deprecated under #303; removal planned one minor cycle after #303 lands." #-}

-- The *identity relation* (equivalently, the kernel of a 1-to-1 function)
0[_] : (A : Type a) → {ρ : Level} → BinRel A (a ⊔ ρ)
0[ A ] {ρ} = λ x y → Lift ρ (x ≡ y)

{-# WARNING_ON_USAGE 0[_] "Use Overture.Relations.0[_] instead. Deprecated under #303; removal planned one minor cycle after #303 lands." #-}

module _ {A : Type (a ⊔ ρ)} where

 -- Subset containment relation for binary realtions
 _⊑_ : BinRel A ρ → BinRel A ρ → Type (a ⊔ ρ)
 P ⊑ Q = ∀ x y → P x y → Q x y

 ⊑-refl : Reflexive _⊑_
 ⊑-refl = λ _ _ z → z

 ⊑-trans : Transitive _⊑_
 ⊑-trans P⊑Q Q⊑R x y Pxy = Q⊑R x y (P⊑Q x y Pxy)
```



### <a id="compatibility-of-operations-and-relations">Compatibility of operations and relations</a>

Recall, from the [Overture.Signatures][] and [Overture.Operations][] modules which established
our convention of reserving the sybmols `𝓞` and `𝓥` for types that
represent operation symbols and arities, respectively.

In the present subsection, we define types that are useful for asserting and proving
facts about *compatibility* of operations and relations


```agda


-- lift a binary relation to the corresponding `I`-ary relation.

eval-rel : {A : Type a}{I : Type 𝓥} → BinRel A ρ → BinRel (I → A) (𝓥 ⊔ ρ)
eval-rel R u v = ∀ i → R (u i) (v i)

eval-pred : {A : Type a}{I : Type 𝓥} → Pred (A × A) ρ → BinRel (I → A) (𝓥 ⊔ ρ)
eval-pred P u v = ∀ i → (u i , v i) ∈ P
```


If `f : Op I` and `R : Rel A b`, then we say `f` and `R` are *compatible* just in case `∀ u v : I → A`, `Π i ꞉ I , R (u i) (v i)  →  R (f u) (f v)`.


```agda


_preserves_ : {A : Type a}{I : Type 𝓥} → Op A I → BinRel A ρ → Type (a ⊔ 𝓥 ⊔ ρ)
f preserves R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

--shorthand notation for preserves
_|:_ : {A : Type a}{I : Type 𝓥} → Op A I → BinRel A ρ → Type (a ⊔ 𝓥 ⊔ ρ)
f |: R  = (eval-rel R) =[ f ]⇒ R

{-# WARNING_ON_USAGE eval-rel "Use Overture.Relations.eval-rel instead. Deprecated under #303." #-}
{-# WARNING_ON_USAGE eval-pred "Use Overture.Relations.eval-pred instead. Deprecated under #303." #-}
{-# WARNING_ON_USAGE _preserves_ "Use Overture.Relations._preserves_ instead. Deprecated under #303." #-}
{-# WARNING_ON_USAGE _|:_ "Use Overture.Relations._|:_ instead. Deprecated under #303." #-}

-- predicate version of the compatibility relation
_preserves-pred_ : {A : Type a}{I : Type 𝓥} → Op A I → Pred ( A × A ) ρ → Type (a ⊔ 𝓥 ⊔ ρ)
f preserves-pred P  = ∀ u v → (eval-pred P) u v → (f u , f v) ∈ P

_|:pred_ : {A : Type a}{I : Type 𝓥} → Op A I → Pred (A × A) ρ → Type (a ⊔ 𝓥 ⊔ ρ)
f |:pred P  = (eval-pred P) =[ f ]⇒ λ x y → (x , y) ∈ P


-- The two types just defined are logically equivalent.
module _ {A : Type a}{I : Type 𝓥}{f : Op A I}{R : BinRel A ρ} where
 compatibility-agreement : f preserves R → f |: R
 compatibility-agreement c {x}{y} Rxy = c x y Rxy
 compatibility-agreement' : f |: R → f preserves R
 compatibility-agreement' c = λ u v x → c x
```


--------------------------------------

<span style="float:left;">[↑ Base.Relations](Base.Relations.html)</span>
<span style="float:right;">[Base.Relations.Continuous →](Base.Relations.Continuous.html)</span>

{% include UALib.Links.md %}
