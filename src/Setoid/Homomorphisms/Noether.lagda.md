---
layout: default
title : "Setoid.Homomorphisms.Noether module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

### Homomorphism Theorems for Setoid Algebras

This is the [Setoid.Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

Here we formalize a version of the *first isomorphism theorem*, sometimes called
*the first homomorphism theorem* or *Noether's first homomorphism theorem*.

The theorem presented here is a general version of the theorem first formulated by
Emmy Noether in her 1927 paper *Abstrakter Aufbau der Idealtheorie in algebraischen
Zahl- und Funktionenkörpern*.[^noether1927]

Noether's contribution was not merely a new proof, but the recognition that the
theorem belongs to a general abstract theory rather than to any particular class of
algebraic structures.

However, her level of abstraction is still not as general as universal algebra.
She worked with modules and ideals over rings (i.e., algebraic structures with
addition and scalar multiplication), whereas Birkhoff's 1935 paper *On the Structure of
Abstract Algebras* took the next conceptual step by showing that these kinds of
quotient constructions and homomorphism principles belong to the general theory of
arbitrary algebras defined by operations and equations.[^birkhoff1935]

The historical progression in very broad strokes:

+  Dedekind, Jordan, Hölder, etc. — special cases for groups and lattices;
+  Noether (1927) — unified abstract algebraic formulation for modules, ideals, and
   related structures;
+  Birkhoff (1935) — universal algebra, where homomorphisms, congruences, quotients,
   and the isomorphism theorems become structural facts about arbitrary equational
   classes.

The formal development here in the `agda-algebras` library goes beyond the classical
group-theoretic theorem, expressing Noether's abstraction at the even more general
level envisioned by Birkhoff.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Homomorphisms.Noether where

-- Imports from Agda and the Agda Standard Library ---------------------------
open import Data.Product     renaming ( _×_ to _∧_)    using (Σ-syntax ; _,_ )
open import Function         renaming ( Func to _⟶_ )  using ( id )
open import Level                                      using ( Level )
open import Relation.Binary                            using ( Setoid )
open import Relation.Binary.PropositionalEquality      using ( refl )

-- Imports from agda-algebras ------------------------------------------------
open import Overture                      using ( proj₁ ; proj₂ ; 𝓞 ; 𝓥 ; Signature)
open import Setoid.Algebras               using ( Algebra ; 𝔻[_] )
open import Setoid.Functions              using ( IsInjective )
open import Setoid.Homomorphisms.Basic    using ( hom ; IsHom )
open import Setoid.Homomorphisms.Kernels  using ( kerquo ; πker )

private variable α ρᵃ β ρᵇ γ ρᶜ ι : Level
```
-->


#### The first homomorphism theorem for setoid algebras

Informally, the theorem states that every homomorphism from `𝑨` to `𝑩` (`𝑆`-algebras)
factors through the quotient algebra `𝑨 ╱ ker h` (`𝑨` modulo the kernel of the given
homomorphism).  In other terms, given `h : hom 𝑨 𝑩` there exists `φ : hom (𝑨 ╱ ker h) 𝑩`
which, when composed with the canonical projection `πker : 𝑨 ↠ 𝑨 ╱ ker h`, is equal to
`h`; that is, `h = φ ∘ πker`.  Moreover, `φ` is a *monomorphism* (injective homomorphism)
and is unique.

```agda
open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

module _
  {𝑆 : Signature 𝓞 𝓥}
  {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} {𝑩 : Algebra β ρᵇ}
  (hh : hom 𝑨 𝑩)
  where
  open Algebra 𝑩 using ( Interp )
  open Setoid 𝔻[ 𝑩 ] using ( _≈_ ) renaming (refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Algebra (kerquo hh) using () renaming ( Domain to A/hKer )

  open IsHom
  private
    hfunc : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]
    hfunc = hh .proj₁
    h = _⟨$⟩_ hfunc

  FirstHomTheorem :
    Σ[ (φ , _) ∈ hom (kerquo hh) 𝑩  ] ( ∀ a → h a ≈ φ ⟨$⟩ (πker hh .proj₁ ⟨$⟩ a) ) ∧ IsInjective φ

  FirstHomTheorem = (φ , φhom) , (λ _ → ≈refl) , φmon
    where
    φ : A/hKer ⟶ 𝔻[ 𝑩 ]
    φ ⟨$⟩ x = h x
    φ .cong = id

    φhom : IsHom (kerquo hh) 𝑩 φ
    φhom .compatible = ≈trans (hh .proj₂ .compatible) (cong Interp (refl , (λ _ → ≈refl)))

    φmon : IsInjective φ
    φmon = id
```

Now we prove that the homomorphism whose existence is guaranteed by `FirstHomTheorem` is unique.

```agda
  FirstHomUnique : {(f , _) (g , _) : hom (kerquo hh) 𝑩}
    → ( ∀ a → h a ≈ f ⟨$⟩ (πker hh .proj₁ ⟨$⟩ a) )
    → ( ∀ a → h a ≈ g ⟨$⟩ (πker hh .proj₁ ⟨$⟩ a) )
    → ∀ [a] → f ⟨$⟩ [a] ≈ g ⟨$⟩ [a]

  FirstHomUnique hfk hgk a = ≈trans (≈sym (hfk a)) (hgk a)
```

---

[^noether1927]:
    Emmy Noether,
    *Abstrakter Aufbau der Idealtheorie in algebraischen Zahl- und Funktionenkörpern*,
    **Mathematische Annalen** **96** (1927), 26–61.
    This paper contains the general formulation of what are now known as the First,
    Second, and Third Isomorphism Theorems for modules.

[^birkhoff1935]:
    Garrett Birkhoff,
    *On the Structure of Abstract Algebras*,
    **Mathematical Proceedings of the Cambridge Philosophical Society**
    **31**(4) (1935), 433–454.
    https://doi.org/10.1017/S0305004100013463.
    This is a seminal paper in universal algebra that develops the theory of
    arbitrary algebraic structures in terms of homomorphisms, subalgebras,
    congruences, and direct products, culminating in what is now known as Birkhoff's
    HSP Theorem.
