---
layout: default
title : Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: [the ualib/agda-algebras development team][]
---

### <a id="equivalence-relations-and-quotients">Equivalence Relations and Quotients</a>

This section presents the [Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Quotients where

open import Agda.Builtin.Equality                 using    (_≡_  ; refl      )
open import Data.Product                          using    ( _,_ ; Σ
                                                           ; Σ-syntax        )
                                                  renaming ( proj₁ to fst
                                                           ; proj₂ to snd    )
open import Agda.Primitive                        using    ( _⊔_             )
                                                  renaming ( Set   to Type
                                                           ; Setω  to Typeω  )
open import Level                                 renaming ( suc   to lsuc
                                                           ; zero  to ℓ₀     )
open import Relation.Binary                       using    ( IsEquivalence   )
                                                  renaming ( Rel   to BinRel )
open import Relation.Binary.PropositionalEquality using    ( sym  ; trans    )
open import Relation.Unary                        using    ( Pred ; _⊆_      )


open import Overture.Preliminaries  using  ( ∣_∣ )
open import Relations.Discrete      using  ( ker ; 0[_] ; kerlift )



-- private variable α β ρ 𝓥 : Level


\end{code}


#### <a id="equivalence-classes">Equivalence relations</a>

A binary relation is called a *preorder* if it is reflexive and transitive. An *equivalence relation* is a symmetric preorder. The property of being an equivalence relation is represented in the [Agda Standard Library][] by a record type called `IsEquivalence`.

\begin{code}

Equivalence : {α : Level} → Type α → {ρ : Level} → Type (α ⊔ lsuc ρ)
Equivalence {α} A {ρ} = Σ[ r ∈ BinRel A ρ ] IsEquivalence r

\end{code}

Thus, if we have `(R ,  p) : Equivalence A`, then `R` denotes a binary relation over `A` and `p` is of record type `IsEquivalence R` with fields containing the three proofs showing that `R` is an equivalence relation.

A prominent example of an equivalence relation is the kernel of any function.

\begin{code}

ker-IsEquivalence : {α : Level}{A : Type α}{β : Level}{B : Type β}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record { refl = refl ; sym = λ x → sym x ; trans = λ x y → trans x y }

kerlift-IsEquivalence : {α : Level}{A : Type α}{β : Level}{B : Type β}(f : A → B){ρ : Level} → IsEquivalence (kerlift f ρ)
kerlift-IsEquivalence f = record { refl = lift refl ; sym = λ x → lift (sym (lower x)) ; trans = λ x y → lift (trans (lower x) (lower y)) }

\end{code}

#### <a id="equivalence-classes">Equivalence classes (blocks)</a>

If `R` is an equivalence relation on `A`, then for each `u : A` there is an *equivalence class* (or *equivalence block*, or `R`-*block*) containing `u`, which we denote and define by `[ u ] := {v : A | R u v}`.

Before defining the quotient type, we define a type representing inhabitants of quotients;
i.e., blocks of a partition (recall partitions correspond to equivalence relations) -}

\begin{code}

-- [_] : {A : Type α} → A → {R : BinRel A ρ} → Pred A ρ
-- [ u ]{R} = R u
[_] : {α : Level}{A : Type α} → A → {ρ : Level} → BinRel A ρ → Pred A ρ

[ u ]{ρ} R = R u      -- (the R-block containing u : A)

-- Alternative notation
[_/_] : {α : Level}{A : Type α} → A → {ρ : Level} → Equivalence A {ρ} → Pred A ρ
[ u / R ] = ∣ R ∣ u

-- Alternative notation

Block : {α : Level}{A : Type α} → A → {ρ : Level} → Equivalence A{ρ} → Pred A ρ
Block u {ρ} R = ∣ R ∣ u


infix 60 [_]

\end{code}


Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]` as the `R`-*block containing* `u`.

A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.  We represent this characterization of an `R`-block as follows.

\begin{code}

record IsBlock {α : Level}{A : Type α}{ρ : Level}(P : Pred A ρ){R : BinRel A ρ} : Type(α ⊔ lsuc ρ) where
  constructor R-block
  field
    block-u : A
    P≡[u] : P ≡ [ block-u ]{ρ} R

\end{code}

If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all `R`-blocks.<sup>[1](Relations.Quotients.html#fn1)</sup>

\begin{code}

Quotient : {α : Level}(A : Type α){ρ : Level} → Equivalence A{ρ} → Type(α ⊔ lsuc ρ)
Quotient A R = Σ[ P ∈ Pred A _ ] IsBlock P {∣ R ∣}

_/_ : {α : Level}(A : Type α){ρ : Level} → BinRel A ρ → Type(α ⊔ lsuc ρ)
A / R = Σ[ P ∈ Pred A _ ] IsBlock P {R}


infix -1 _/_

\end{code}

We use the following type to represent an \ab R-block with a designated representative.

\begin{code}

⟪_⟫ : {α : Level}{A : Type α}{ρ : Level} → A → {R : BinRel A ρ} → A / R
⟪ a ⟫{R} = [ a ] R , R-block a refl

\end{code}

Dually, the next type provides an *elimination rule*.<sup>[2](Relations.Quotients.html#fn2)</sup>

\begin{code}

⌞_⌟ : {α : Level}{A : Type α}{ρ : Level}{R : BinRel A ρ} → A / R  → A
⌞ _ , R-block a _ ⌟ = a

\end{code}

Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.

It will be convenient to have the following subset inclusion lemmas on hand when working with quotient types.

\begin{code}

-- private variable A : Type α ; x y : A ; R : BinRel A ρ
-- open IsEquivalence
-- /-subset : IsEquivalence R → R x y →  [ x ]{R} ⊆ [ y ]{R}
-- /-subset Req Rxy {z} Rxz = IsEquivalence.trans Req (IsEquivalence.sym Req Rxy) Rxz
-- /-supset : IsEquivalence R → R x y →  [ y ]{R} ⊆ [ x ]{R}
-- /-supset Req Rxy {z} Ryz = IsEquivalence.trans Req Rxy Ryz

module _ {α : Level}{A : Type α}
         {ρ : Level}                   -- note: ρ is an explicit parameter
         {R : Equivalence A {ρ}} where

 open IsEquivalence
 -- ([]-⊆ used to be called /-subset)
 []-⊆ : (x y : A) → ∣ R ∣ x y → [ x ]{ρ} ∣ R ∣ ⊆  [ y ] ∣ R ∣
 []-⊆ x y Rxy {z} Rxz = IsEquivalence.trans (snd R) (IsEquivalence.sym (snd R) Rxy) Rxz

 -- ([]-⊇ used to be called /-supset)
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

0[_]IsEquivalence : {α : Level}(A : Type α){ρ : Level} → IsEquivalence (0[ A ] {ρ})
0[ A ]IsEquivalence {ρ} = record { refl = lift refl
                              ; sym = λ p → lift (sym (lower p))
                              ; trans = λ p q → lift (trans (lower p) (lower q)) }

0[_]Equivalence : {α : Level}(A : Type α) {ρ : Level} → Equivalence A {α ⊔ ρ}
0[ A ]Equivalence {ρ} = 0[ A ] {ρ} , 0[ A ]IsEquivalence


\end{code}


The following are sometimes useful.

\begin{code}

-- ⟪⟫≡-elim : {α : Level}{A : Type α} → (u v : A) → {ρ : Level}{R : BinRel A ρ }
--  →         ⟪ u ⟫{R} ≡ ⟪ v ⟫ → R u v
-- ⟪⟫≡-elim u v refl = {!!} -- IsEquivalence.refl (snd R)


⟪_∼_⟫-elim : {α : Level}{A : Type α} → (u v : A) → {ρ : Level}{R : Equivalence A{ρ} }
 →         ⟪ u ⟫{∣ R ∣} ≡ ⟪ v ⟫ → ∣ R ∣ u v

⟪ u ∼ .u ⟫-elim {ρ} {R} refl = IsEquivalence.refl (snd R)


≡→⊆ : {α : Level}{A : Type α}{ρ : Level}(P Q : Pred A ρ) → P ≡ Q → P ⊆ Q
≡→⊆ P .P refl {x} Px = Px

\end{code}




--------------------------------------


<sup>1</sup><span class="footnote" id="fn1">**Unicode Hints** ([agda2-mode][]). `\cl ↝ ⌞`; `\clr ↝ ⌟`.</span>


<br>
<br>


[← Relations.Continuous](Relations.Continuous.html)
<span style="float:right;">[Relations.Truncation →](Relations.Truncation.html)</span>

{% include UALib.Links.md %}

-----------------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team

