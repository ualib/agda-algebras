---
layout: default
file: "src/Examples/Setoid/FiniteQuotient.lagda.md"
title: "Examples.Setoid.FiniteQuotient module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked example: a finite quotient of `(ℕ, +, 0)` {#examples-setoid-finitequotient}

This is the [Examples.Setoid.FiniteQuotient][] module of the [Agda Universal Algebra Library][].

The quotient of an algebra by a congruence is one of the central constructions of
universal algebra; in the Setoid development it is the operation `_╱_`{.AgdaFunction}
of [Setoid.Congruences][].  This module takes the quotient of the
commutative monoid `(ℕ, +, 0)` modulo the *parity* congruence
`a ∼ b ⟺ a % 2 ≡ b % 2`{.AgdaFunction}.  The result is a genuinely *finite*
quotient: it has exactly two congruence classes, even and odd, and its induced
operation is addition modulo `2` — i.e. the two-element group `ℤ/2ℤ`.

(Incidentally, the monoid `(ℕ, +, 0)` that we use here is the same one that appears in
[Examples.Classical.CommutativeMonoid][]; it is rebuilt here directly over
`Sig-Monoid`{.AgdaFunction}.)

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.FiniteQuotient where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Fin.Patterns using ( 0F ; 1F )
open import Data.Nat          using ( ℕ ; _+_ ; _%_ )
open import Data.Nat.DivMod   using ( %-distribˡ-+ )
open import Data.Product      using ( _,_ )
open import Function          using ( Func )
open import Level             using ( 0ℓ )
open import Relation.Binary   using ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality as ≡
                              using ( _≡_ ; refl ; cong₂ ; sym ; trans )
open import Relation.Nullary  using ( ¬_ )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Classical.Signatures.Monoid          using ( Sig-Monoid ; ∙-Op ; ε-Op )
open import Setoid.Algebras {𝑆 = Sig-Monoid}     using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Congruences {𝑆 = Sig-Monoid}  using ( Con ; IsCongruence ; _∣≈_ ; _╱_ )
open import Setoid.Signatures                    using  ( ⟨_⟩ )

open Func renaming ( to to _⟨$⟩_ )
```

#### The monoid `(ℕ, +, 0)` over `Sig-Monoid` {#the-monoid}

```agda
ℕ+-monoid : Algebra 0ℓ 0ℓ
ℕ+-monoid = record { Domain = ≡.setoid ℕ ; Interp = interp }
  where
  interp : Func (⟨ Sig-Monoid ⟩ (≡.setoid ℕ)) (≡.setoid ℕ)
  interp ⟨$⟩ (∙-Op , args) = args 0F + args 1F
  interp ⟨$⟩ (ε-Op , _) = 0
  cong interp {∙-Op , _} {.∙-Op , _} (refl , args≈) = cong₂ _+_ (args≈ 0F) (args≈ 1F)
  cong interp {ε-Op , _} {.ε-Op , _} (refl , _) = refl
```

#### The parity congruence

Two naturals are related when they have the same remainder modulo `2`.  This is the
kernel of `_% 2`, hence an equivalence; compatibility with `+` is the standard fact
that remainder distributes over addition (`%-distribˡ-+`{.AgdaFunction}), and
compatibility with the nullary `0` is immediate.

```agda
θ : ℕ → ℕ → Type
θ a b = a % 2 ≡ b % 2

θ-isEquiv : IsEquivalence θ
θ-isEquiv = record { refl = refl ; sym = sym ; trans = trans }

-- + preserves parity:  (u₀ + u₁) % 2 ≡ (v₀ + v₁) % 2  from  uᵢ % 2 ≡ vᵢ % 2.
θ-compatible : ℕ+-monoid ∣≈ θ
θ-compatible ∙-Op {u} {v} h =
  trans  (%-distribˡ-+ (u 0F) (u 1F) 2)
         (trans  (cong₂ (λ r s → (r + s) % 2) (h 0F) (h 1F))
                 (sym (%-distribˡ-+ (v 0F) (v 1F) 2)))
θ-compatible ε-Op _ = refl

parity : Con ℕ+-monoid 0ℓ
parity = θ , record  { reflexive       = ≡.cong (_% 2)
                     ; is-equivalence  = θ-isEquiv
                     ; is-compatible   = θ-compatible }
```

#### The quotient `(ℕ, +, 0) ╱ parity ≅ ℤ/2ℤ` {#the-quotient}

The carrier of the quotient is still `ℕ`{.AgdaDatatype}, but its equality is parity,
so distinct naturals of the same parity become equal.  We exhibit the two classes,
the failure of cross-class identification, and the modular addition `1 + 1 ≈ 0`.

```agda
ℤ/2 : Algebra 0ℓ 0ℓ
ℤ/2 = ℕ+-monoid ╱ parity

open Setoid 𝔻[ ℤ/2 ] using ( _≈_ )

-- every even number collapses to 0, every odd number to 1
2≈0 : 2 ≈ 0
2≈0 = refl

4≈0 : 4 ≈ 0
4≈0 = refl

3≈1 : 3 ≈ 1
3≈1 = refl

-- the two classes are genuinely distinct
0≉1 : ¬ (0 ≈ 1)
0≉1 ()

-- the induced operation is addition modulo 2:  1 + 1 ≈ 0
1+1≈0 : (1 + 1) ≈ 0
1+1≈0 = refl
```

--------------------------------------

{% include UALib.Links.md %}
