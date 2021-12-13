---
layout: default
title : "Base.Relations.Quotients module (The Agda Universal Algebra Library)"
date : "2021-01-13"
author: "the agda-algebras development team"
---

### <a id="quotients">Quotients</a>

This is the [Base.Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Relations.Quotients where

-- Imports from Agda and the Agda Standard Library  ----------------------------------------------
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Agda.Primitive  using ( _⊔_ ; Level ; lsuc ) renaming ( Set to Type )
open import Level           using ()
open import Relation.Binary using ( IsEquivalence ; IsPartialEquivalence) renaming ( Rel to BinRel )
open import Relation.Unary  using ( Pred ; _⊆_ )
open import Relation.Binary.PropositionalEquality as PE
                            using ( _≡_ )

-- Imports from agda-algebras ---------------------------------------------------------------------
open import Base.Overture.Preliminaries  using  ( ∣_∣ )
open import Base.Relations.Discrete      using  ( ker ; 0[_] ; kerlift )
open import Base.Relations.Properties       using  ( Reflexive ; Symmetric ; Transitive )

private variable
 α β χ : Level

\end{code}

#### <a id="equivalence-relations">Equivalence relations</a>

A binary relation is called a *preorder* if it is reflexive and transitive.
An *equivalence relation* is a symmetric preorder. The property of being
an equivalence relation is represented in the [Agda Standard Library][] by
a record type called `IsEquivalence`.  Here we define the `Equivalence` type
which is inhabited by pairs `(r , p)` where `r` is a binary relation and `p`
is a proof that `r` satisfies `IsEquivalence`.

\begin{code}

Equivalence : Type α → {ρ : Level} → Type (α ⊔ lsuc ρ)
Equivalence A {ρ} = Σ[ r ∈ BinRel A ρ ] IsEquivalence r

\end{code}

Another way to represent binary relations is as the inhabitants of the
type `Pred(X × X) _`, and we here define the `IsPartialEquivPred`
and `IsEquivPred` types corresponding to such a representation.

\begin{code}

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

\end{code}

Thus, if we have `(R ,  p) : Equivalence A`, then `R` denotes a binary
relation over `A` and `p` is of record type `IsEquivalence R` with fields
containing the three proofs showing that `R` is an equivalence relation.

#### <a id="kernels">Kernels</a>

A prominent example of an equivalence relation is the kernel of any function.

\begin{code}

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

\end{code}


#### <a id="equivalence-classes"> Equivalence classes (blocks) </a>


If `R` is an equivalence relation on `A`, then for each `u : A` there is
an *equivalence class* (or *equivalence block*, or `R`-*block*) containing `u`,
which we denote and define by `[ u ] := {v : A | R u v}`.

Before defining the quotient type, we define a type representing inhabitants of quotients;
i.e., blocks of a partition (recall partitions correspond to equivalence relations) -}

\begin{code}

[_] : {A : Type α} → A → {ρ : Level} → BinRel A ρ → Pred A ρ
[ u ]{ρ} R = R u      -- (the R-block containing u : A)

-- Alternative notation
[_/_] : {A : Type α} → A → {ρ : Level} → Equivalence A {ρ} → Pred A ρ
[ u / R ] = ∣ R ∣ u

-- Alternative notation
Block : {A : Type α} → A → {ρ : Level} → Equivalence A{ρ} → Pred A ρ
Block u {ρ} R = ∣ R ∣ u

infix 60 [_]

\end{code}

Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]`
as the `R`-*block containing* `u`.

A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.
We represent this characterization of an `R`-block as follows.

\begin{code}

record IsBlock {A : Type α}{ρ : Level}(P : Pred A ρ){R : BinRel A ρ} : Type(α ⊔ lsuc ρ) where
 constructor mkblk
 field
  blk : A
  P≡[blk] : P ≡ [ blk ]{ρ} R

\end{code}

If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is
denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all
`R`-blocks.

\begin{code}

Quotient : (A : Type α){ρ : Level} → Equivalence A{ρ} → Type(α ⊔ lsuc ρ)
Quotient A R = Σ[ P ∈ Pred A _ ] IsBlock P {∣ R ∣}

_/_ : (A : Type α){ρ : Level} → BinRel A ρ → Type(α ⊔ lsuc ρ)
A / R = Σ[ P ∈ Pred A _ ] IsBlock P {R}

infix -1 _/_

\end{code}

We use the following type to represent an R-block with a designated representative.

\begin{code}

⟪_⟫ : {α : Level}{A : Type α}{ρ : Level} → A → {R : BinRel A ρ} → A / R
⟪ a ⟫{R} = [ a ] R , mkblk a PE.refl

\end{code}

Dually, the next type provides an *elimination rule*.

\begin{code}

⌞_⌟ : {α : Level}{A : Type α}{ρ : Level}{R : BinRel A ρ} → A / R  → A
⌞ _ , mkblk a _ ⌟ = a

\end{code}

Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.

\begin{code}

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

An example application of these is the `block-ext` type in the [Base.Relations.Extensionality] module.

Recall, from Base.Relations.Discrete, the zero (or "identity") relation is

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


-------------------------------------

<span style="float:left;">[← Base.Relations.Properties](Base.Relations.Properties.html)</span>
<span style="float:right;">[Base.Equality →](Base.Equality.html)</span>

{% include UALib.Links.md %}

