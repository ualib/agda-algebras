---
layout: default
title : Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: [agda-algebras development team][]
---

### Quotients

This is the [Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Quotients where

open import Agda.Builtin.Equality as E using ( _≡_ )
open import Data.Product               using ( _,_ ; _×_ ; Σ-syntax )
                                    renaming ( proj₁ to fst ; proj₂ to snd )
open import Agda.Primitive             using ( _⊔_ ; Level ; lsuc )
                                    renaming ( Set to Type )
open import Level                      using ( )
open import Relation.Binary            using ( IsEquivalence ; IsPartialEquivalence)
                                    renaming ( Rel to BinRel )
open import Relation.Unary             using ( Pred ; _⊆_ )
import Relation.Binary.PropositionalEquality as PE

open import Overture.Preliminaries  using  ( ∣_∣ )
open import Relations.Discrete      using  ( ker ; 0[_] ; kerlift )
open import Relations.BinPred       using  ( Reflexive ; Symmetric ; Transitive )

private variable
 α β χ : Level

-- ---------------------
-- Equivalence relations
-- ---------------------
-- A binary relation is called a *preorder* if it is reflexive and transitive.
-- An *equivalence relation* is a symmetric preorder. The property of being
-- an equivalence relation is represented in the [Agda Standard Library][] by
-- a record type called `IsEquivalence`.

Equivalence : Type α → {ρ : Level} → Type (α ⊔ lsuc ρ)
Equivalence A {ρ} = Σ[ r ∈ BinRel A ρ ] IsEquivalence r

-- Similarly, for "binary relations" of type `Pred(X × X) _`, we have corresponding
-- IsEquivalence and Equivalence types.

module _ {X : Type χ}{ρ : Level} where

 record IsPartialEquivPred (R : Pred (X × X) ρ) : Type (χ ⊔ ρ) where
  field
   sym   : Symmetric R
   trans : Transitive R

 record IsEquivPred (R : Pred (X × X) ρ) : Type (χ ⊔ ρ) where
  field
   refl  : Reflexive R
   sym   : Symmetric R
   trans : Transitive R

  reflexive : ∀ x y → x ≡ y → R (x , y)
  reflexive x .x PE.refl = refl

-- Thus, if we have `(R ,  p) : Equivalence A`, then `R` denotes a binary
-- relation over `A` and `p` is of record type `IsEquivalence R` with fields
-- containing the three proofs showing that `R` is an equivalence relation.

-- A prominent example of an equivalence relation is the kernel of any function.

open Level
ker-IsEquivalence : {A : Type α}{B : Type β}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record { refl = PE.refl
                             ; sym = λ x → PE.sym x
                             ; trans = λ x y → PE.trans x y
                             }

kerlift-IsEquivalence : {A : Type α}{B : Type β}(f : A → B){ρ : Level} → IsEquivalence (kerlift f ρ)
kerlift-IsEquivalence f = record { refl = lift PE.refl
                                 ; sym = λ x → lift (PE.sym (lower x))
                                 ; trans = λ x y → lift (PE.trans (lower x) (lower y))
                                 }

-- ----------------------------
-- Equivalence classes (blocks)
-- ----------------------------
-- If `R` is an equivalence relation on `A`, then for each `u : A` there is
-- an *equivalence class* (or *equivalence block*, or `R`-*block*) containing `u`,
-- which we denote and define by `[ u ] := {v : A | R u v}`.

-- Before defining the quotient type, we define a type representing inhabitants of quotients;
-- i.e., blocks of a partition (recall partitions correspond to equivalence relations) -}

[_] : {A : Type α} → A → {ρ : Level} → BinRel A ρ → Pred A ρ
[ u ]{ρ} R = R u      -- (the R-block containing u : A)

-- Alternative notation
[_/_] : {A : Type α} → A → {ρ : Level} → Equivalence A {ρ} → Pred A ρ
[ u / R ] = ∣ R ∣ u

-- Alternative notation
Block : {A : Type α} → A → {ρ : Level} → Equivalence A{ρ} → Pred A ρ
Block u {ρ} R = ∣ R ∣ u

infix 60 [_]

-- Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]`
-- as the `R`-*block containing* `u`.

-- A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.
-- We represent this characterization of an `R`-block as follows.

record IsBlock {A : Type α}{ρ : Level}(P : Pred A ρ){R : BinRel A ρ} : Type(α ⊔ lsuc ρ) where
 constructor R-block
 field
  block-u : A
  P≡[u] : P ≡ [ block-u ]{ρ} R

-- If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is
-- denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all
-- `R`-blocks.

Quotient : (A : Type α){ρ : Level} → Equivalence A{ρ} → Type(α ⊔ lsuc ρ)
Quotient A R = Σ[ P ∈ Pred A _ ] IsBlock P {∣ R ∣}

_/_ : (A : Type α){ρ : Level} → BinRel A ρ → Type(α ⊔ lsuc ρ)
A / R = Σ[ P ∈ Pred A _ ] IsBlock P {R}

infix -1 _/_

-- We use the following type to represent an \ab R-block with a designated representative.

⟪_⟫ : {α : Level}{A : Type α}{ρ : Level} → A → {R : BinRel A ρ} → A / R
⟪ a ⟫{R} = [ a ] R , R-block a PE.refl

-- Dually, the next type provides an *elimination rule*.<sup>[2](Relations.Quotients.html#fn2)</sup>

⌞_⌟ : {α : Level}{A : Type α}{ρ : Level}{R : BinRel A ρ} → A / R  → A
⌞ _ , R-block a _ ⌟ = a

-- (Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.)


module _ {A : Type α}
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


\end{code}

An example application of these is the `block-ext` type in the [Relations.Extensionality] module.

Recall, from Relations.Discrete, the zero (or "identity") relation is

```agda
0[_] : (A : Type α) → {ρ : Level} → BinRel A (α ⊔ ρ)
0[ A ] {ρ} = λ x y → Lift ρ (x ≡ y)
```

This is obviously an equivalence relation, as we now confirm.

\begin{code}

0[_]IsEquivalence : (A : Type α){ρ : Level} → IsEquivalence (0[ A ] {ρ})
0[ A ]IsEquivalence {ρ} = record { refl = lift PE.refl
                                 ; sym = λ p → lift (PE.sym (lower p))
                                 ; trans = λ p q → lift (PE.trans (lower p) (lower q))
                                 }

0[_]Equivalence : (A : Type α) {ρ : Level} → Equivalence A {α ⊔ ρ}
0[ A ]Equivalence {ρ} = 0[ A ] {ρ} , 0[ A ]IsEquivalence


⟪_∼_⟫-elim : {A : Type α} → (u v : A) → {ρ : Level}{R : Equivalence A{ρ} }
 →           ⟪ u ⟫{∣ R ∣} ≡ ⟪ v ⟫ → ∣ R ∣ u v

⟪ u ∼ .u ⟫-elim {ρ} {R} PE.refl = IsEquivalence.refl (snd R)


≡→⊆ : {A : Type α}{ρ : Level}(Q R : Pred A ρ) → Q ≡ R → Q ⊆ R
≡→⊆ Q .Q PE.refl {x} Qx = Qx

\end{code}


--------------------------------------

{% include UALib.Links.md %}

-----------------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

