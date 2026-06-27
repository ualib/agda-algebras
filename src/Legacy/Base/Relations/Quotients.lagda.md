---
layout: default
title : "Legacy.Base.Relations.Quotients module (The Agda Universal Algebra Library)"
date : "2021-01-13"
author: "the agda-algebras development team"
---

### <a id="quotients">Quotients</a>

This is the [Legacy.Base.Relations.Quotients][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Legacy.Base.Relations.Quotients where

-- Imports from Agda and the Agda Standard Library  ----------------------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Level           using ( Level ; _⊔_ ; suc )
open import Relation.Binary using ( IsEquivalence ; IsPartialEquivalence) renaming ( Rel to BinRel )
open import Relation.Unary  using ( Pred ; _⊆_ )
open import Relation.Binary.PropositionalEquality as PE
                            using ( _≡_ )

-- Imports from agda-algebras ---------------------------------------------------------------------
open import Overture                   using ( ∣_∣ )
open import Legacy.Base.Relations.Discrete    using ( ker ; 0[_] ; kerlift )
open import Legacy.Base.Relations.Properties  using ( Reflexive ; Symmetric ; Transitive )

private variable a b ℓ : Level
```


#### <a id="equivalence-relations">Equivalence relations</a>

A binary relation is called a *preorder* if it is reflexive and transitive.
An *equivalence relation* is a symmetric preorder. The property of being
an equivalence relation is represented in the [Agda Standard Library][] by
a record type called `IsEquivalence`.  Here we define the `Equivalence` type
which is inhabited by pairs `(r , p)` where `r` is a binary relation and `p`
is a proof that `r` satisfies `IsEquivalence`.


```agda
Equivalence : Type a → {ρ : Level} → Type (a ⊔ suc ρ)
Equivalence A {ρ} = Σ[ r ∈ BinRel A ρ ] IsEquivalence r

{-# WARNING_ON_USAGE Equivalence "Use Overture.Relations.Equivalence instead. Deprecated under #303." #-}
```


Another way to represent binary relations is as the inhabitants of the
type `Pred(X × X) _`, and we here define the `IsPartialEquivPred`
and `IsEquivPred` types corresponding to such a representation.


```agda


module _ {X : Type ℓ}{ρ : Level} where

 record IsPartialEquivPred (R : Pred (X × X) ρ) : Type (ℓ ⊔ ρ) where
  field
   sym   : Symmetric R
   trans : Transitive R

 record IsEquivPred (R : Pred (X × X) ρ) : Type (ℓ ⊔ ρ) where
  field
   refl  : Reflexive R
   sym   : Symmetric R
   trans : Transitive R

  reflexive : ∀ x y → x ≡ y → R (x , y)
  reflexive x .x PE.refl = refl
```


Thus, if we have `(R ,  p) : Equivalence A`, then `R` denotes a binary
relation over `A` and `p` is of record type `IsEquivalence R` with fields
containing the three proofs showing that `R` is an equivalence relation.

#### <a id="kernels">Kernels</a>

A prominent example of an equivalence relation is the kernel of any function.


```agda


open Level
ker-IsEquivalence : {A : Type a}{B : Type b}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record  { refl = PE.refl
                              ; sym = λ x → PE.sym x
                              ; trans = λ x y → PE.trans x y
                              }

kerlift-IsEquivalence :  {A : Type a}{B : Type b}(f : A → B){ρ : Level}
 →                       IsEquivalence (kerlift f ρ)

kerlift-IsEquivalence f = record  { refl = lift PE.refl
                                  ; sym = λ x → lift (PE.sym (lower x))
                                  ; trans = λ x y → lift (PE.trans (lower x) (lower y))
                                  }
```



#### <a id="equivalence-classes"> Equivalence classes (blocks) </a>


If `R` is an equivalence relation on `A`, then for each `u : A` there is
an *equivalence class* (or *equivalence block*, or `R`-*block*) containing `u`,
which we denote and define by `[ u ] := {v : A | R u v}`.

Before defining the quotient type, we define a type representing inhabitants of quotients;
i.e., blocks of a partition (recall partitions correspond to equivalence relations) -}


```agda


[_] : {A : Type a} → A → {ρ : Level} → BinRel A ρ → Pred A ρ
[ u ]{ρ} R = R u      -- (the R-block containing u : A)

{-# WARNING_ON_USAGE [_] "Use Overture.Relations.[_] instead. Deprecated under #303." #-}

-- Alternative notation
[_/_] : {A : Type a} → A → {ρ : Level} → Equivalence A {ρ} → Pred A ρ
[ u / R ] = ∣ R ∣ u

-- Alternative notation
Block : {A : Type a} → A → {ρ : Level} → Equivalence A{ρ} → Pred A ρ
Block u {ρ} R = ∣ R ∣ u

infix 60 [_]
```


Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]`
as the `R`-*block containing* `u`.

A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.
We represent this characterization of an `R`-block as follows.


```agda


record IsBlock  {A : Type a}{ρ : Level}
                (P : Pred A ρ){R : BinRel A ρ} : Type(a ⊔ suc ρ) where
 constructor mkblk
 field
  blk : A
  P≡[blk] : P ≡ [ blk ]{ρ} R
```


If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is
denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all
`R`-blocks.


```agda


Quotient : (A : Type a){ρ : Level} → Equivalence A{ρ} → Type(a ⊔ suc ρ)
Quotient A R = Σ[ P ∈ Pred A _ ] IsBlock P {∣ R ∣}

_/_ : (A : Type a){ρ : Level} → BinRel A ρ → Type(a ⊔ suc ρ)
A / R = Σ[ P ∈ Pred A _ ] IsBlock P {R}

infix -1 _/_
```


We use the following type to represent an R-block with a designated representative.


```agda


⟪_⟫ : {a : Level}{A : Type a}{ρ : Level} → A → {R : BinRel A ρ} → A / R
⟪ a ⟫{R} = [ a ] R , mkblk a PE.refl
```


Dually, the next type provides an *elimination rule*.


```agda


⌞_⌟ : {a : Level}{A : Type a}{ρ : Level}{R : BinRel A ρ} → A / R  → A
⌞ _ , mkblk a _ ⌟ = a
```


Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.


```agda


module _  {A : Type a}
          {ρ : Level}    -- note: ρ is an implicit parameter
          {R : Equivalence A {ρ}} where

 open IsEquivalence
 []-⊆ : (x y : A) → ∣ R ∣ x y → [ x ]{ρ} ∣ R ∣ ⊆  [ y ] ∣ R ∣
 []-⊆ x y Rxy {z} Rxz = IsEquivalence.trans (snd R) (IsEquivalence.sym (snd R) Rxy) Rxz

 []-⊇ : (x y : A) → ∣ R ∣ x y → [ y ] ∣ R ∣ ⊆  [ x ] ∣ R ∣
 []-⊇ x y Rxy {z} Ryz = IsEquivalence.trans (snd R) Rxy Ryz

 ⊆-[] : (x y : A) → [ x ] ∣ R ∣ ⊆  [ y ] ∣ R ∣ → ∣ R ∣ x y
 ⊆-[] x y xy = IsEquivalence.sym (snd R) (xy (IsEquivalence.refl (snd R)))

 ⊇-[] : (x y : A) → [ y ] ∣ R ∣ ⊆  [ x ] ∣ R ∣ → ∣ R ∣ x y
 ⊇-[] x y yx = yx (IsEquivalence.refl (snd R))
```


An example application of these is the `block-ext` type in the [Legacy.Base.Relations.Extensionality] module.

Recall, from Base.Relations.Discrete, the zero (or "identity") relation is

    0[_] : (A : Type a) → {ρ : Level} → BinRel A (a ⊔ ρ)
    0[ A ] {ρ} = λ x y → Lift ρ (x ≡ y)

This is obviously an equivalence relation, as we now confirm.


```agda


0[_]IsEquivalence : (A : Type a){ρ : Level} → IsEquivalence (0[ A ] {ρ})
0[ A ]IsEquivalence {ρ} = record  { refl = lift PE.refl
                                  ; sym = λ p → lift (PE.sym (lower p))
                                  ; trans = λ p q → lift (PE.trans (lower p) (lower q))
                                  }

0[_]Equivalence : (A : Type a) {ρ : Level} → Equivalence A {a ⊔ ρ}
0[ A ]Equivalence {ρ} = 0[ A ] {ρ} , 0[ A ]IsEquivalence

{-# WARNING_ON_USAGE 0[_]IsEquivalence "Use Overture.Relations.0[_]IsEquivalence instead. Deprecated under #303." #-}
{-# WARNING_ON_USAGE 0[_]Equivalence "Use Overture.Relations.0[_]Equivalence instead. Deprecated under #303." #-}

⟪_∼_⟫-elim : {A : Type a} → (u v : A) → {ρ : Level}{R : Equivalence A{ρ} }
 →           ⟪ u ⟫{∣ R ∣} ≡ ⟪ v ⟫ → ∣ R ∣ u v

⟪ u ∼ .u ⟫-elim {ρ} {R} PE.refl = IsEquivalence.refl (snd R)

≡→⊆ : {A : Type a}{ρ : Level}(Q R : Pred A ρ) → Q ≡ R → Q ⊆ R
≡→⊆ Q .Q PE.refl {x} Qx = Qx
```
