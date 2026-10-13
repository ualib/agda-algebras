---
layout: default
file: "src/Examples/Classical/Groups/CyclicGroup6.lagda.md"
title: "Examples.Classical.Groups.CyclicGroup6 module"
date: "2026-10-13"
author: "the agda-algebras development team"
---

### Worked example: `ℤ/6ℤ ≅ ℤ/2ℤ × ℤ/3ℤ` as a direct decomposition

This is the [Examples.Classical.Groups.CyclicGroup6][] module of the [Agda Universal Algebra Library][].

The cyclic group of order six is the direct product of the cyclic groups of
orders two and three, by the Chinese remainder theorem.  This module checks that
decomposition with the theory of [Setoid.Decompositions][], every finite fact
decided by evaluation.

+  The groups `ℤ/6ℤ` and `ℤ/2ℤ` are built from their addition tables, as in
   [Examples.Classical.Groups.CyclicGroup3][], which supplies `ℤ/3ℤ`.
+  Reduction modulo 2 and modulo 3 are homomorphisms `ℤ/6ℤ → ℤ/2ℤ` and
   `ℤ/6ℤ → ℤ/3ℤ`; the homomorphism equations are decided over the finite carriers.
   Their kernels `θ₂` (congruence mod 2) and `θ₃` (congruence mod 3) are decidable
   congruences of `ℤ/6ℤ`.
+  `θ₂` and `θ₃` form a factor pair (ALV Definition 4.28), decided by
   `isFactorPair?`{.AgdaFunction}: their meet is the diagonal and their composite
   is total.  By Theorem 4.29, `ℤ/6ℤ ≅ ℤ/6ℤ/θ₂ × ℤ/6ℤ/θ₃`, and by the first
   isomorphism theorem the two quotients are `ℤ/2ℤ` and `ℤ/3ℤ`.
+  `ℤ/2ℤ` and `ℤ/3ℤ` are directly indecomposable, by
   `small→indecomposable`{.AgdaFunction} (each has at most three elements, and
   their nontriviality is decided); so `θ₂` and `θ₃` are indecomposable
   congruences, and `0 = θ₂ × θ₃` is a factorization of `ℤ/6ℤ` into
   indecomposables.  `ℤ/6ℤ` itself is not directly indecomposable.

The congruence lattice of `ℤ/6ℤ` is the four-element Boolean lattice, which is
distributive, so `ℤ/6ℤ` has the strict refinement property (ALV Theorem 5.17,
Corollary 1) and its factorization is unique; that corollary is not formalized
here.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Examples.Classical.Groups.CyclicGroup6 where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin.Base                           using ( Fin )
open import Data.Fin.Patterns                       using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.Fin.Properties                     using ( _≟_ ; all? )
open import Data.Nat.Properties                     using () renaming ( _≤?_ to _≤ⁿ?_ )
open import Data.Product                            using ( _,_ ; proj₁ )
open import Data.Sum.Base                           using ( inj₁ ; inj₂ )
open import Data.Vec.Base                           using ( _∷_ ; [] )
open import Function                                using ( Func )
open import Level                                   using ( 0ℓ )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; refl ; cong )
open import Relation.Nullary                        using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Cayley                         using  ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties          using  ( Associative? ; LeftIdentity?
                                                           ; RightIdentity? ; LeftInverse?
                                                           ; RightInverse? )
open import Classical.Signatures.Group              using  ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Small.Structures.Group        using  ( Group ; eqsToGroup )
open import Examples.Classical.Groups.CyclicGroup3  using  ( z3-group )
                                                    renaming ( _·_ to _+₃_ ; z3-inv to z3-neg )
open import Setoid.Algebras                         using  ( Algebra ; 𝔻[_] ; _×ᴬ_ )
open import Setoid.Algebras.Finite                  using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic                using  ( Con ; _╱_ )
open import Setoid.Congruences.Finite               using  ( DecCon )
open import Setoid.Congruences.Monolith             using  ( Trivial )
open import Setoid.Decompositions                   using  ( IsFactorPair ; isFactorPair?
                                                           ; factorPair→≅ ; nontrivial?
                                                           ; IsDirectlyIndecomposable
                                                           ; factor-trivial ; small→indecomposable
                                                           ; IsIndecomposable
                                                           ; directly→indecomposable
                                                           ; ≅-indecomposable )
open import Setoid.Functions                        using  ( IsSurjective ; Image_∋_ )
open import Setoid.Homomorphisms                    using  ( hom ; mkhom ; compatible-map
                                                           ; kercon ; FirstIsoTheorem ; _≅_
                                                           ; ≅-sym ; ≅-trans ; ×ᴬ-≅ )

open Func using () renaming ( to to _⟨$⟩_ )
```
-->

#### The groups

The addition table of `ℤ/6ℤ` (entry `a , b` is `(a + b) mod 6`), its negation, and
the group, with the five group axioms decided over the carrier `Fin 6`.

```agda
-- The addition-mod-6 table.
z6-table : Table 6
z6-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ [])
         ∷ (1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 0F ∷ [])
         ∷ (2F ∷ 3F ∷ 4F ∷ 5F ∷ 0F ∷ 1F ∷ [])
         ∷ (3F ∷ 4F ∷ 5F ∷ 0F ∷ 1F ∷ 2F ∷ [])
         ∷ (4F ∷ 5F ∷ 0F ∷ 1F ∷ 2F ∷ 3F ∷ [])
         ∷ (5F ∷ 0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ [])
         ∷ []

-- Addition mod 6.
_+₆_ : Fin 6 → Fin 6 → Fin 6
_+₆_ = ⟦ z6-table ⟧

-- Negation mod 6.
neg₆ : Fin 6 → Fin 6
neg₆ 0F = 0F
neg₆ 1F = 5F
neg₆ 2F = 4F
neg₆ 3F = 3F
neg₆ 4F = 2F
neg₆ 5F = 1F

-- The group ℤ/6ℤ.
z6-group : Group
z6-group = eqsToGroup (Fin 6) _+₆_ 0F neg₆
  (from-yes (Associative?   _+₆_)) (from-yes (LeftIdentity?  _+₆_ 0F))
  (from-yes (RightIdentity? _+₆_ 0F)) (from-yes (LeftInverse?   _+₆_ 0F neg₆))
  (from-yes (RightInverse?  _+₆_ 0F neg₆))
```

The same for `ℤ/2ℤ`, whose negation is the identity.

```agda
-- The addition-mod-2 table.
z2-table : Table 2
z2-table = (0F ∷ 1F ∷ []) ∷ (1F ∷ 0F ∷ []) ∷ []

-- Addition mod 2.
_+₂_ : Fin 2 → Fin 2 → Fin 2
_+₂_ = ⟦ z2-table ⟧

-- Negation mod 2.
neg₂ : Fin 2 → Fin 2
neg₂ x = x

-- The group ℤ/2ℤ.
z2-group : Group
z2-group = eqsToGroup (Fin 2) _+₂_ 0F neg₂
  (from-yes (Associative?   _+₂_)) (from-yes (LeftIdentity?  _+₂_ 0F))
  (from-yes (RightIdentity? _+₂_ 0F)) (from-yes (LeftInverse?   _+₂_ 0F neg₂))
  (from-yes (RightInverse?  _+₂_ 0F neg₂))
```

The underlying `Sig-Group`{.AgdaFunction} algebras, and their finiteness
witnesses: each carrier `Fin n` enumerates itself.

```agda
-- The underlying algebras of ℤ/6ℤ, ℤ/2ℤ, and ℤ/3ℤ.
𝒁₆ 𝒁₂ 𝒁₃ : Algebra {𝑆 = Sig-Group} 0ℓ 0ℓ
𝒁₆ = proj₁ z6-group
𝒁₂ = proj₁ z2-group
𝒁₃ = proj₁ z3-group

-- They are finite algebras.
𝑭₆ : FiniteAlgebra 𝒁₆
𝑭₆ = record { _≟_ = _≟_ ; card = 6 ; enum = λ i → i ; enum-sur = λ x → x , refl }

𝑭₂ : FiniteAlgebra 𝒁₂
𝑭₂ = record { _≟_ = _≟_ ; card = 2 ; enum = λ i → i ; enum-sur = λ x → x , refl }

𝑭₃ : FiniteAlgebra 𝒁₃
𝑭₃ = record { _≟_ = _≟_ ; card = 3 ; enum = λ i → i ; enum-sur = λ x → x , refl }
```

#### Reduction mod 2 and mod 3

Reduction modulo 2 sends `x` to the parity of `x`, and reduction modulo 3 to its
residue; both respect addition and negation, which is decided over the carrier,
and they preserve the identity on the nose.

```agda
-- Reduction mod 2.
mod₂ : Fin 6 → Fin 2
mod₂ 0F = 0F
mod₂ 1F = 1F
mod₂ 2F = 0F
mod₂ 3F = 1F
mod₂ 4F = 0F
mod₂ 5F = 1F

-- Reduction mod 3.
mod₃ : Fin 6 → Fin 3
mod₃ 0F = 0F
mod₃ 1F = 1F
mod₃ 2F = 2F
mod₃ 3F = 0F
mod₃ 4F = 1F
mod₃ 5F = 2F

-- Reduction mod 2 respects addition and negation (decided).
mod₂-+ : ∀ x y → mod₂ (x +₆ y) ≡ mod₂ x +₂ mod₂ y
mod₂-+ = from-yes (all? λ x → all? λ y → mod₂ (x +₆ y) ≟ mod₂ x +₂ mod₂ y)

mod₂-neg : ∀ x → mod₂ (neg₆ x) ≡ neg₂ (mod₂ x)
mod₂-neg = from-yes (all? λ x → mod₂ (neg₆ x) ≟ neg₂ (mod₂ x))

-- Reduction mod 3 respects addition and negation (decided).
mod₃-+ : ∀ x y → mod₃ (x +₆ y) ≡ mod₃ x +₃ mod₃ y
mod₃-+ = from-yes (all? λ x → all? λ y → mod₃ (x +₆ y) ≟ mod₃ x +₃ mod₃ y)

mod₃-neg : ∀ x → mod₃ (neg₆ x) ≡ z3-neg (mod₃ x)
mod₃-neg = from-yes (all? λ x → mod₃ (neg₆ x) ≟ z3-neg (mod₃ x))
```

The two reductions are homomorphisms of `Sig-Group`{.AgdaFunction} algebras: the
interpretation of `∙-Op`{.AgdaInductiveConstructor} applies the table to the two
arguments, so compatibility with each operation symbol is one of the decided
equations.

```agda
-- Reduction mod 2 is a homomorphism ℤ/6ℤ → ℤ/2ℤ.
mod₂-hom : hom 𝒁₆ 𝒁₂
mod₂-hom = mkhom 𝒁₆ 𝒁₂ F λ {f} {a} → compatible {f} {a}
  where
  F : Func 𝔻[ 𝒁₆ ] 𝔻[ 𝒁₂ ]
  F ⟨$⟩ x = mod₂ x
  F .Func.cong = cong mod₂

  compatible : compatible-map 𝒁₆ 𝒁₂ F
  compatible {∙-Op}   {a} = mod₂-+ (a 0F) (a 1F)
  compatible {ε-Op}   {a} = refl
  compatible {⁻¹-Op}  {a} = mod₂-neg (a 0F)

-- Reduction mod 3 is a homomorphism ℤ/6ℤ → ℤ/3ℤ.
mod₃-hom : hom 𝒁₆ 𝒁₃
mod₃-hom = mkhom 𝒁₆ 𝒁₃ F λ {f} {a} → compatible {f} {a}
  where
  F : Func 𝔻[ 𝒁₆ ] 𝔻[ 𝒁₃ ]
  F ⟨$⟩ x = mod₃ x
  F .Func.cong = cong mod₃

  compatible : compatible-map 𝒁₆ 𝒁₃ F
  compatible {∙-Op}   {a} = mod₃-+ (a 0F) (a 1F)
  compatible {ε-Op}   {a} = refl
  compatible {⁻¹-Op}  {a} = mod₃-neg (a 0F)
```

#### The factor pair

The kernels of the reductions are congruence modulo 2 and congruence modulo 3.
They are decidable, by comparing residues, so they are decidable congruences
(`DecCon`{.AgdaFunction}), and `isFactorPair?`{.AgdaFunction} decides that they
form a factor pair: an element is determined by its residues mod 2 and mod 3, and
every pair of residues occurs.

```agda
-- Congruence mod 2 and congruence mod 3, the kernels of the reductions.
θ₂ θ₃ : Con 𝒁₆ 0ℓ
θ₂ = kercon mod₂-hom
θ₃ = kercon mod₃-hom

-- They are decidable.
θ₂ᵈ θ₃ᵈ : DecCon 𝒁₆ 0ℓ
θ₂ᵈ = θ₂ , λ x y → mod₂ x ≟ mod₂ y
θ₃ᵈ = θ₃ , λ x y → mod₃ x ≟ mod₃ y

-- ⟨θ₂ , θ₃⟩ is a factor pair of ℤ/6ℤ (decided).
θ₂θ₃-factorPair : IsFactorPair θ₂ θ₃
θ₂θ₃-factorPair = from-yes (isFactorPair? 𝑭₆ θ₂ᵈ θ₃ᵈ)
```

Neither member of the pair is the total congruence, so `ℤ/6ℤ` is not directly
indecomposable: `0` and `1` differ mod 2, and `0` and `1` differ mod 3.

```agda
-- Neither factor is trivial.
θ₂-proper : ¬ Trivial (𝒁₆ ╱ θ₂)
θ₂-proper t with t 0F 1F
... | ()

θ₃-proper : ¬ Trivial (𝒁₆ ╱ θ₃)
θ₃-proper t with t 0F 1F
... | ()

-- So ℤ/6ℤ is not directly indecomposable.
z6-decomposable : ¬ IsDirectlyIndecomposable 0ℓ 𝒁₆
z6-decomposable di with factor-trivial di θ₂ θ₃ θ₂θ₃-factorPair
... | inj₁ t = θ₂-proper t
... | inj₂ t = θ₃-proper t
```

#### The decomposition `ℤ/6ℤ ≅ ℤ/2ℤ × ℤ/3ℤ`

Theorem 4.29 turns the factor pair into the isomorphism
`ℤ/6ℤ ≅ ℤ/6ℤ/θ₂ × ℤ/6ℤ/θ₃`.  The reductions are onto, so by the first isomorphism
theorem the two quotients are `ℤ/2ℤ` and `ℤ/3ℤ`, and the product of the two
isomorphisms (`×ᴬ-≅`{.AgdaFunction}) gives the decomposition.

```agda
-- ALV Theorem 4.29: ℤ/6ℤ ≅ ℤ/6ℤ/θ₂ × ℤ/6ℤ/θ₃.
z6≅quotients : 𝒁₆ ≅ ((𝒁₆ ╱ θ₂) ×ᴬ (𝒁₆ ╱ θ₃))
z6≅quotients = factorPair→≅ θ₂ θ₃ θ₂θ₃-factorPair

-- The reductions are onto.
mod₂-onto : IsSurjective (proj₁ mod₂-hom)
mod₂-onto {0F} = Image_∋_.eq 0F refl
mod₂-onto {1F} = Image_∋_.eq 1F refl

mod₃-onto : IsSurjective (proj₁ mod₃-hom)
mod₃-onto {0F} = Image_∋_.eq 0F refl
mod₃-onto {1F} = Image_∋_.eq 1F refl
mod₃-onto {2F} = Image_∋_.eq 2F refl

-- The first isomorphism theorem identifies the quotients.
quotient₂≅z2 : (𝒁₆ ╱ θ₂) ≅ 𝒁₂
quotient₂≅z2 = FirstIsoTheorem mod₂-hom mod₂-onto

quotient₃≅z3 : (𝒁₆ ╱ θ₃) ≅ 𝒁₃
quotient₃≅z3 = FirstIsoTheorem mod₃-hom mod₃-onto

-- ℤ/6ℤ ≅ ℤ/2ℤ × ℤ/3ℤ.
z6≅z2×z3 : 𝒁₆ ≅ (𝒁₂ ×ᴬ 𝒁₃)
z6≅z2×z3 = ≅-trans z6≅quotients (×ᴬ-≅ quotient₂≅z2 quotient₃≅z3)
```

#### The factors are indecomposable

`ℤ/2ℤ` and `ℤ/3ℤ` have at most three elements and are nontrivial (decided), so
they are directly indecomposable by `small→indecomposable`{.AgdaFunction}.
Transporting along the first isomorphism theorem and applying Lemma 2 of ALV §5.2,
`θ₂` and `θ₃` are indecomposable congruences: `0 = θ₂ × θ₃` is a factorization of
`ℤ/6ℤ` into indecomposables.

```agda
-- ℤ/2ℤ and ℤ/3ℤ are directly indecomposable.
z2-indecomposable : IsDirectlyIndecomposable 0ℓ 𝒁₂
z2-indecomposable = small→indecomposable 𝑭₂ (from-yes (2 ≤ⁿ? 3)) (from-yes (nontrivial? 𝑭₂))

z3-indecomposable : IsDirectlyIndecomposable 0ℓ 𝒁₃
z3-indecomposable = small→indecomposable 𝑭₃ (from-yes (3 ≤ⁿ? 3)) (from-yes (nontrivial? 𝑭₃))

-- So congruence mod 2 and congruence mod 3 are indecomposable congruences of ℤ/6ℤ.
θ₂-indecomposable : IsIndecomposable θ₂
θ₂-indecomposable =
  directly→indecomposable θ₂ (≅-indecomposable (≅-sym quotient₂≅z2) z2-indecomposable)

θ₃-indecomposable : IsIndecomposable θ₃
θ₃-indecomposable =
  directly→indecomposable θ₃ (≅-indecomposable (≅-sym quotient₃≅z3) z3-indecomposable)
```
