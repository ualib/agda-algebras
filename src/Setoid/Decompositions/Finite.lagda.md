---
layout: default
file: "src/Setoid/Decompositions/Finite.lagda.md"
title: "Setoid.Decompositions.Finite module (The Agda Universal Algebra Library)"
date: "2026-10-13"
author: "the agda-algebras development team"
---

### Direct decompositions of finite algebras

This is the [Setoid.Decompositions.Finite][] module of the [Agda Universal Algebra Library][].

On a finite algebra the notions of [Setoid.Decompositions.FactorPairs][] and
[Setoid.Decompositions.Indecomposable][] become computable, and every algebra
factors into directly indecomposable ones:

> **Exercise 4.38 (2).**  Every finite algebra is isomorphic to a product of
> directly indecomposable algebras.  (McKenzie, McNulty, and Taylor, *Algebras,
> Lattices, Varieties* I, ALV below; Exercise 5.1 (10) repeats it.)

This module proves that theorem and supplies the decision procedures it runs on.
The finite algebra is given by its carrier data, a `FiniteAlgebra`{.AgdaRecord}
of [Setoid.Algebras.Finite][] (decidable equality and a surjective enumeration),
and, where the congruence lattice must be searched, by a complete list of its
decidable congruences, a `FiniteCongruencesᵈ`{.AgdaRecord} of
[Setoid.Congruences.Finite.Decidable][].

**No classical assumption.**  The conclusions are about *semantic* factor pairs,
those of `Con`{.AgdaFunction}, even though the list is complete only for the
*decidable* congruences.  ADR-008 explains why the two layers differ: an
arbitrary congruence of a finite algebra need not be decidable, and the semantic
completeness of `FiniteCongruences`{.AgdaRecord} is a classical assumption that no
concrete algebra with two distinct elements can discharge under `--safe`.  But a
factor of a decidable product is decidable (`product₂-decˡ`{.AgdaFunction} of
[Setoid.Decompositions.FactorPairs][]), so every semantic factor pair is one of
the listed pairs, up to `≑`; that is all the searches need.

The module provides the following:

+  decision procedures, for decidable congruences of a finite algebra, for the
   composite relation, triviality and nontriviality of a quotient, products of two
   congruences (`isProduct₂?`{.AgdaFunction}), and factor pairs
   (`isFactorPair?`{.AgdaFunction});
+  given a complete list of decidable congruences, the list
   `factorPairs`{.AgdaFunction} of all factor pairs, sound and complete for the
   semantic ones, and decisions of direct indecomposability
   (`isDirectlyIndecomposable?`{.AgdaFunction}) and of indecomposability of a
   congruence (`isIndecomposable?`{.AgdaFunction});
+  `small→indecomposable`{.AgdaFunction}: a nontrivial algebra with an enumeration
   of at most three elements is directly indecomposable, with no list at all
   (two nontrivial factors would make four distinct elements);
+  `finite-decomposition`{.AgdaFunction}, Exercise 4.38 (2): a finite algebra with
   a complete list of decidable congruences is isomorphic to a finite product of
   directly indecomposable quotients of itself; since such a list exists for every
   finite algebra over a finite signature, so does the factorization
   (`finitary-decomposition≅`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Decompositions.Finite where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Data.Empty                              using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                           using ( Fin ; _<_ ; splitAt )
open import Data.Fin.Patterns                       using ( 0F ; 1F ; 2F ; 3F )
open import Data.Fin.Properties                     using ( pigeonhole )
open import Data.List.Base                          using ( List ; [] ; _∷_ ; length
                                                          ; cartesianProduct ; filter )
open import Data.List.Membership.Propositional      using ( _∈_ )
open import Data.List.Membership.Propositional.Properties
                                                    using ( ∈-cartesianProduct⁺ ; ∈-filter⁺
                                                          ; ∈-filter⁻ )
open import Data.List.Relation.Unary.All            using ( All ; lookup ; tabulate )
                                                    renaming ( all? to All? )
open import Data.List.Relation.Unary.All.Properties using ( ¬All⇒Any¬ )
open import Data.List.Relation.Unary.Any            using ( satisfied ; here ; there )
open import Data.Nat.Base                           using ( ℕ ; zero ; suc ; s≤s ; z≤n ; _+_ )
                                                    renaming ( _≤_ to _≤ⁿ_ ; _<_ to _<ⁿ_ )
open import Data.Nat.Properties                     using ( m≤n⇒m≤1+n ; <-≤-trans ; ≤-pred
                                                          ; ≤-refl )
open import Data.Product                            using ( _×_ ; _,_ ; proj₁ ; proj₂
                                                          ; Σ-syntax ; ∃-syntax )
open import Data.Sum.Base                           using ( _⊎_ ; inj₁ ; inj₂ ; map ; [_,_]′ )
open import Level                                   using ( Level ; _⊔_ ; lift ; lower )
                                                    renaming ( suc to lsuc )
open import Relation.Binary                         using ( Setoid ; IsEquivalence )
                                                    renaming ( Rel to BinaryRel )
open import Relation.Binary.PropositionalEquality   using ( refl ) renaming ( cong to ≡-cong )
open import Relation.Nullary                        using ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable              using ( map′ ; _×-dec_ ; _⊎-dec_
                                                          ; _→-dec_ ; ¬? ; decidable-stable )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                            using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras                     using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra ; all²? ; exists? )
open import Setoid.Congruences.Basic            using ( Con ; _╱_ ; reflexive
                                                      ; is-equivalence ; 𝟘[_] )
open import Setoid.Congruences.Finite           using ( DecCon ; ConRel ; FiniteCongruencesᵈ
                                                      ; FiniteAlgebra→FiniteCongruencesᵈ )
open import Setoid.Congruences.Lattice          using ( _≑_ ; _⊆_ )
open import Setoid.Congruences.Monolith         using ( Nontrivial ; Trivial )
open import Setoid.Congruences.Permutability    using ( _∘_ )
open import Setoid.Decompositions.FactorPairs   using ( IsProduct₂ ; to-meet ; from-meet
                                                      ; composite ; IsFactorPair
                                                      ; factorPair→product₂
                                                      ; product₂→factorPair ; product₂-≑
                                                      ; product₂-decˡ ; product₂-decʳ
                                                      ; product₂-sym ; product₂-→trivialˡ )
open import Setoid.Decompositions.Products      using ( IsProduct ; product-≑ ; product-resp
                                                      ; total→product-empty ; product-singleton
                                                      ; product-++ ; product→≅ )
open import Setoid.Homomorphisms.Isomorphisms   using ( _≅_ )
open import Setoid.Subalgebras.Subdirect.Basic  using ( 𝑨╱ )
open import Setoid.Algebras.Products            using ( ⨅ )
open import Setoid.Signatures.Finite            using ( FiniteSignature )
open import Setoid.Decompositions.Indecomposable
  using ( IsDirectlyIndecomposable ; nontrivial ; factor-trivial
        ; IsIndecomposable ; quotient-nontrivial ; product-trivial
        ; indecomposable→directly )

private variable α ρ ℓ ℓ′ : Level
```
-->

#### Deciding products and factor pairs

Fix a finite algebra `𝑨`.  A relation `R` on its carrier **respects equality**
when it can be transported along `≈` in both arguments; every congruence does,
since it contains `≈` and is transitive (`con-resp`{.AgdaFunction}), and so does
`≈` itself.  The sweeps of [Setoid.Algebras.Finite][] decide properties of this
kind by checking the finitely many enumerated instances.

The composite `θ ∘ φ` of two decidable congruences is decidable by a search for
the middle element (`∘?`{.AgdaFunction}); triviality of `𝑨 ╱ θ` ("`θ = 1`") and
the separation of a pair ("`|A/θ| > 1`") by sweeps over pairs
(`trivial?`{.AgdaFunction}, `quotient-nontrivial?`{.AgdaFunction}).  A product
decomposition `R = θ × φ` is then a conjunction of three sweeps, one per field of
`IsProduct₂`{.AgdaRecord} (`isProduct₂?`{.AgdaFunction}), and a factor pair is
the case `R = ≈` (`isFactorPair?`{.AgdaFunction}), by the equivalence of the two
forms of a factor pair.  Note that the join `θ ∨ φ` of Definition 4.28, a
generated congruence, is never computed: the composite form replaces it.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( sym to ≈sym ; trans to ≈trans )

  -- R can be transported along ≈ in both arguments.
  RespectsEq : BinaryRel 𝕌[ 𝑨 ] ℓ′ → Type (α ⊔ ρ ⊔ ℓ′)
  RespectsEq R = ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → R a b → R a′ b′

  -- Setoid equality respects itself.
  ≈-resp : RespectsEq _≈_
  ≈-resp a≈a′ b≈b′ a≈b = ≈trans (≈sym a≈a′) (≈trans a≈b b≈b′)

  -- Every congruence respects setoid equality.
  con-resp : (θ : Con 𝑨 ℓ) → RespectsEq (proj₁ θ)
  con-resp (_ , θc) a≈a′ b≈b′ r =
    θtrans (reflexive θc (≈sym a≈a′)) (θtrans r (reflexive θc b≈b′))
    where θtrans = IsEquivalence.trans (is-equivalence θc)
```

Now fix the finiteness witness.  The composite `∘?`{.AgdaFunction} searches the
enumeration for a middle element; `trivial?`{.AgdaFunction} sweeps all pairs;
`quotient-nontrivial?`{.AgdaFunction} and `nontrivial?`{.AgdaFunction} search
for a pair that the congruence, or the setoid equality, does not relate.  Each
transports its answer from the enumerated elements to all elements by the
respect lemmas above.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (𝑭 : FiniteAlgebra 𝑨) where
  open FiniteAlgebra 𝑭 using ( _≟_ )
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( sym to ≈sym ; trans to ≈trans )

  -- The composite of two decidable congruences is decidable: search for the middle.
  ∘? : (d e : DecCon 𝑨 ℓ) → ∀ x y → Dec ((proj₁ d ∘ proj₁ e) x y)
  ∘? d e x y = exists? 𝑭 (λ z → ConRel d x z × ConRel e z y)
                       (λ z≈z′ (xz , zy) → con-resp (proj₁ d) (≈refl′ x) z≈z′ xz
                                         , con-resp (proj₁ e) z≈z′ (≈refl′ y) zy)
                       (λ z → proj₂ d x z ×-dec proj₂ e z y)
    where ≈refl′ = λ (a : 𝕌[ 𝑨 ]) → Setoid.refl 𝔻[ 𝑨 ] {a}

  -- "θ = 1": is the quotient 𝑨 ╱ θ trivial?
  trivial? : (d : DecCon 𝑨 ℓ) → Dec (Trivial (𝑨 ╱ proj₁ d))
  trivial? d = all²? 𝑭 (ConRel d) (con-resp (proj₁ d)) (proj₂ d)

  -- "|A/θ| > 1": does θ separate some pair?
  quotient-nontrivial? : (d : DecCon 𝑨 ℓ) → Dec (Nontrivial (𝑨 ╱ proj₁ d))
  quotient-nontrivial? d =
    exists? 𝑭 (λ a → ∃[ b ] ¬ ConRel d a b)
              (λ a≈a′ (b , ¬ab) → b , λ a′b → ¬ab (con-resp (proj₁ d) (≈sym a≈a′) (≈refl′ b) a′b))
              (λ a → exists? 𝑭 (λ b → ¬ ConRel d a b)
                               (λ b≈b′ ¬ab ab′ → ¬ab (con-resp (proj₁ d) (≈refl′ a) (≈sym b≈b′) ab′))
                               (λ b → ¬? (proj₂ d a b)))
    where ≈refl′ = λ (a : 𝕌[ 𝑨 ]) → Setoid.refl 𝔻[ 𝑨 ] {a}

  -- Is 𝑨 nontrivial?
  nontrivial? : Dec (Nontrivial 𝑨)
  nontrivial? =
    exists? 𝑭 (λ a → ∃[ b ] ¬ a ≈ b)
              (λ a≈a′ (b , ¬ab) → b , λ a′b → ¬ab (≈trans a≈a′ a′b))
              (λ a → exists? 𝑭 (λ b → ¬ a ≈ b)
                               (λ b≈b′ ¬ab ab′ → ¬ab (≈trans ab′ (≈sym b≈b′)))
                               (λ b → ¬? (a ≟ b)))
```

A congruence that is not total separates a pair, which a search finds: the
negative answer of `trivial?`{.AgdaFunction} becomes the positive witness of
`quotient-nontrivial?`{.AgdaFunction} (`¬trivial→nontrivial`{.AgdaFunction}).

```agda
  -- A decidable congruence that is not total separates some pair.
  ¬trivial→nontrivial : (d : DecCon 𝑨 ℓ) → ¬ Trivial (𝑨 ╱ proj₁ d) → Nontrivial (𝑨 ╱ proj₁ d)
  ¬trivial→nontrivial d ¬t with quotient-nontrivial? d
  ... | yes nt  = nt
  ... | no ¬nt  = ⊥-elim (¬t λ a b → decidable-stable (proj₂ d a b) λ ¬ab → ¬nt (a , b , ¬ab))
```

The three fields of a product decomposition `R = θ × φ` are universal statements
about pairs, each decided by a sweep, and the record is decided by deciding their
conjunction.

```agda
  -- Decide R = θ × φ, for decidable R respecting ≈ and decidable θ, φ.
  isProduct₂? : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′} → (∀ x y → Dec (R x y)) → RespectsEq {𝑨 = 𝑨} R
    → (d e : DecCon 𝑨 ℓ) → Dec (IsProduct₂ R (proj₁ d) (proj₁ e))
  isProduct₂? {R = R} R? R-resp d e =
    map′ assemble disassemble (to? ×-dec from? ×-dec composite?)
    where
    θ = proj₁ d ; φ = proj₁ e
    d-resp = con-resp θ ; e-resp = con-resp φ

    to? : Dec (∀ x y → R x y → ConRel d x y × ConRel e x y)
    to? = all²? 𝑭 _ (λ a≈a′ b≈b′ h r′ → let (r₀ , r₁) = h (R-resp (≈sym a≈a′) (≈sym b≈b′) r′)
                                         in  d-resp a≈a′ b≈b′ r₀ , e-resp a≈a′ b≈b′ r₁)
                    (λ x y → R? x y →-dec (proj₂ d x y ×-dec proj₂ e x y))

    from? : Dec (∀ x y → ConRel d x y × ConRel e x y → R x y)
    from? = all²? 𝑭 _ (λ a≈a′ b≈b′ h (r₀ , r₁) →
                         R-resp a≈a′ b≈b′ (h ( d-resp (≈sym a≈a′) (≈sym b≈b′) r₀
                                             , e-resp (≈sym a≈a′) (≈sym b≈b′) r₁)))
                      (λ x y → (proj₂ d x y ×-dec proj₂ e x y) →-dec R? x y)

    composite? : Dec (∀ x y → (θ ∘ φ) x y)
    composite? = all²? 𝑭 _ (λ a≈a′ b≈b′ (z , az , zb) → z , d-resp a≈a′ (≈refl′ z) az
                                                           , e-resp (≈refl′ z) b≈b′ zb)
                           (∘? d e)
      where ≈refl′ = λ (a : 𝕌[ 𝑨 ]) → Setoid.refl 𝔻[ 𝑨 ] {a}

    assemble : _ → IsProduct₂ R θ φ
    assemble (t , f , c) = record  { to-meet = λ {x} {y} → t x y
                                   ; from-meet = λ {x} {y} → f x y
                                   ; composite = c }

    disassemble : IsProduct₂ R θ φ → _
    disassemble p = (λ x y → to-meet p) , (λ x y → from-meet p) , composite p

  -- Decide whether two decidable congruences form a factor pair.
  isFactorPair? : (d e : DecCon 𝑨 ℓ) → Dec (IsFactorPair (proj₁ d) (proj₁ e))
  isFactorPair? d e = map′ product₂→factorPair factorPair→product₂ (isProduct₂? _≟_ (≈-resp {𝑨 = 𝑨}) d e)
```

#### Factor congruences are decidable congruences

A factor of a decidable product is decidable (`product₂-decˡ`{.AgdaFunction} of
[Setoid.Decompositions.FactorPairs][]); to decide whether `x` and `y` are related
it uses one auxiliary element, and `x` itself will do.  So the factors of a
decidable product package as decidable congruences, with no hypothesis on the
algebra (`factorˡ-DecCon`{.AgdaFunction}, `factorʳ-DecCon`{.AgdaFunction}).

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- The first factor of a decidable product R = θ × φ, as a decidable congruence.
  factorˡ-DecCon : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ φ : Con 𝑨 ℓ}
    → (∀ x y → Dec (R x y)) → IsProduct₂ R θ φ → DecCon 𝑨 ℓ
  factorˡ-DecCon {θ = θ} R? p = θ , λ x y → product₂-decˡ p x R? x y

  -- The second factor of a decidable product R = θ × φ, as a decidable congruence.
  factorʳ-DecCon : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′}{θ φ : Con 𝑨 ℓ}
    → (∀ x y → Dec (R x y)) → IsProduct₂ R θ φ → DecCon 𝑨 ℓ
  factorʳ-DecCon {φ = φ} R? p = φ , λ x y → product₂-decʳ p x R? x y
```

#### Searching a complete list of decidable congruences

Now fix, besides the finite algebra, a complete list of its decidable
congruences, at the working level `W = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ` of
[Setoid.Congruences.Finite.Basic][].  Every product decomposition
`R = θ₀ × θ₁` of a decidable relation, with `θ₀` and `θ₁` *semantic* congruences,
is then a listed pair up to `≑` (`listed-split`{.AgdaFunction}): its factors are
decidable, and so `≑` to listed congruences.

The question "does every decomposition of `R` have a total factor?"
(`NoProperSplit`{.AgdaFunction}) is therefore decided by checking the listed
pairs (`SplitTrivial`{.AgdaFunction} at each, `noProperSplit?`{.AgdaFunction}).
With `R = ≈` it is the second half of direct indecomposability, and with `R` a
listed congruence the second half of indecomposability of a congruence; adding the
decisions of nontriviality gives `isDirectlyIndecomposable?`{.AgdaFunction} and
`isIndecomposable?`{.AgdaFunction}.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ}
         (𝑭 : FiniteAlgebra 𝑨) (𝑪 : FiniteCongruencesᵈ 𝑨) where
  open FiniteAlgebra 𝑭 using ( _≟_ )
  open FiniteCongruencesᵈ 𝑪 using ( consᵈ ; witnessᵈ ; witnessᵈ∈ ; witnessᵈ≑ )

  private
    W : Level
    W = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ

  -- The listed pairs of decidable congruences.
  listedPairs : List (DecCon 𝑨 W × DecCon 𝑨 W)
  listedPairs = cartesianProduct consᵈ consᵈ

  -- At a listed pair: if it decomposes R, then one factor is total.
  SplitTrivial : BinaryRel 𝕌[ 𝑨 ] ℓ′ → DecCon 𝑨 W × DecCon 𝑨 W → Type (α ⊔ ℓ′ ⊔ W)
  SplitTrivial R (d , e) =
    IsProduct₂ R (proj₁ d) (proj₁ e) → Trivial (𝑨 ╱ proj₁ d) ⊎ Trivial (𝑨 ╱ proj₁ e)

  -- Every decomposition of R into two semantic congruences has a total factor.
  NoProperSplit : BinaryRel 𝕌[ 𝑨 ] ℓ′ → Type (α ⊔ ℓ′ ⊔ lsuc W)
  NoProperSplit R = (θ₀ θ₁ : Con 𝑨 W) → IsProduct₂ R θ₀ θ₁ → Trivial (𝑨 ╱ θ₀) ⊎ Trivial (𝑨 ╱ θ₁)

  -- Every decomposition of a decidable R is a listed pair, up to ≑.
  listed-split : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′} → (∀ x y → Dec (R x y))
    → {θ₀ θ₁ : Con 𝑨 W} → IsProduct₂ R θ₀ θ₁
    → Σ[ q ∈ DecCon 𝑨 W × DecCon 𝑨 W ]  q ∈ listedPairs
                                       × θ₀ ≑ proj₁ (proj₁ q) × θ₁ ≑ proj₁ (proj₂ q)
  listed-split R? p =  (witnessᵈ d₀ , witnessᵈ d₁)
                    ,  ∈-cartesianProduct⁺ (witnessᵈ∈ d₀) (witnessᵈ∈ d₁)
                    ,  witnessᵈ≑ d₀ , witnessᵈ≑ d₁
    where
    d₀ = factorˡ-DecCon R? p
    d₁ = factorʳ-DecCon R? p

  -- The check at the listed pairs gives the semantic statement ...
  all→noProperSplit : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′} → (∀ x y → Dec (R x y))
    → All (SplitTrivial R) listedPairs → NoProperSplit R
  all→noProperSplit R? h θ₀ θ₁ p =
    let (q , q∈ , θ₀≑ , θ₁≑) = listed-split R? p
    in  map (λ t a b → proj₂ θ₀≑ (t a b)) (λ t a b → proj₂ θ₁≑ (t a b))
            (lookup h q∈ (product₂-≑ θ₀≑ θ₁≑ p))

  -- ... and conversely.
  noProperSplit→all : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′} → NoProperSplit R → All (SplitTrivial R) listedPairs
  noProperSplit→all nps = tabulate λ {(d , e)} _ → nps (proj₁ d) (proj₁ e)

  -- Decide the check at one listed pair.
  splitTrivial? : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′} → (∀ x y → Dec (R x y)) → RespectsEq {𝑨 = 𝑨} R
    → (q : DecCon 𝑨 W × DecCon 𝑨 W) → Dec (SplitTrivial R q)
  splitTrivial? R? R-resp (d , e) =
    isProduct₂? 𝑭 R? R-resp d e →-dec (trivial? 𝑭 d ⊎-dec trivial? 𝑭 e)

  -- Decide whether every decomposition of R has a total factor.
  noProperSplit? : {R : BinaryRel 𝕌[ 𝑨 ] ℓ′} → (∀ x y → Dec (R x y)) → RespectsEq {𝑨 = 𝑨} R
    → Dec (NoProperSplit R)
  noProperSplit? R? R-resp =
    map′ (all→noProperSplit R?) noProperSplit→all (All? (splitTrivial? R? R-resp) listedPairs)

  -- Decide direct indecomposability (a semantic statement, decided constructively).
  isDirectlyIndecomposable? : Dec (IsDirectlyIndecomposable W 𝑨)
  isDirectlyIndecomposable? =
    map′  (λ (nt , nps) → record  { nontrivial = nt
                                  ; factor-trivial = λ θ φ fp → nps θ φ (factorPair→product₂ fp) })
          (λ di → nontrivial di , λ θ φ p → factor-trivial di θ φ (product₂→factorPair p))
          (nontrivial? 𝑭 ×-dec noProperSplit? _≟_ (≈-resp {𝑨 = 𝑨}))

  -- Decide indecomposability of a listed (or any decidable) congruence.
  isIndecomposable? : (d : DecCon 𝑨 W) → Dec (IsIndecomposable (proj₁ d))
  isIndecomposable? d =
    map′  (λ (nt , nps) → record { quotient-nontrivial = nt ; product-trivial = nps })
          (λ ind → quotient-nontrivial ind , product-trivial ind)
          (quotient-nontrivial? 𝑭 d ×-dec noProperSplit? (proj₂ d) (con-resp (proj₁ d)))
```

The existence theorem below needs more than a yes-or-no answer: when a
congruence `d` is not indecomposable, it needs the decomposition that shows it.
`indecomposable-or-split`{.AgdaFunction} supplies it: if the check fails at some
listed pair `(d₀ , d₁)`, then, all three conditions being decidable,
`d = d₀ × d₁` holds and neither factor is total (`ProperSplit`{.AgdaFunction}).

```agda
  -- A proper split of d: a listed decomposition d = d₀ × d₁ with neither factor total.
  ProperSplit : DecCon 𝑨 W → Type (α ⊔ lsuc W)
  ProperSplit d = Σ[ (d₀ , d₁) ∈ DecCon 𝑨 W × DecCon 𝑨 W ]
                     IsProduct₂ (ConRel d) (proj₁ d₀) (proj₁ d₁)
                   × ¬ Trivial (𝑨 ╱ proj₁ d₀) × ¬ Trivial (𝑨 ╱ proj₁ d₁)

  -- A congruence with a nontrivial quotient is indecomposable or splits properly.
  indecomposable-or-split : (d : DecCon 𝑨 W) → Nontrivial (𝑨 ╱ proj₁ d)
    → IsIndecomposable (proj₁ d) ⊎ ProperSplit d
  indecomposable-or-split d nt = decide (All? check listedPairs)
    where
    check = splitTrivial? (proj₂ d) (con-resp (proj₁ d))

    -- A failure of the check at a listed pair is a proper split.
    refute : (q : DecCon 𝑨 W × DecCon 𝑨 W) → ¬ SplitTrivial (ConRel d) q → ProperSplit d
    refute (d₀ , d₁) ¬st =  (d₀ , d₁)
                         ,  decidable-stable (isProduct₂? 𝑭 (proj₂ d) (con-resp (proj₁ d)) d₀ d₁)
                                             (λ ¬p → ¬st λ p → ⊥-elim (¬p p))
                         ,  (λ t₀ → ¬st λ _ → inj₁ t₀)
                         ,  (λ t₁ → ¬st λ _ → inj₂ t₁)

    decide : Dec (All (SplitTrivial (ConRel d)) listedPairs)
      → IsIndecomposable (proj₁ d) ⊎ ProperSplit d
    decide (yes h)  = inj₁ record  { quotient-nontrivial = nt
                                   ; product-trivial = all→noProperSplit (proj₂ d) h }
    decide (no ¬h)  = let (q , ¬st) = satisfied (¬All⇒Any¬ check listedPairs ¬h)
                      in  inj₂ (refute q ¬st)
```

Finally the list of all factor pairs, sound and complete: every listed pair it
contains is a factor pair, and every semantic factor pair is `≑` to one it
contains.

```agda
  -- The listed pair is a factor pair.
  FactorPairᵈ : DecCon 𝑨 W × DecCon 𝑨 W → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ W)
  FactorPairᵈ (d , e) = IsFactorPair (proj₁ d) (proj₁ e)

  -- Decide whether a pair of decidable congruences is a factor pair.
  factorPairᵈ? : (q : DecCon 𝑨 W × DecCon 𝑨 W) → Dec (FactorPairᵈ q)
  factorPairᵈ? (d , e) = isFactorPair? 𝑭 d e

  -- The factor pairs among the listed pairs.
  factorPairs : List (DecCon 𝑨 W × DecCon 𝑨 W)
  factorPairs = filter factorPairᵈ? listedPairs

  -- Every member of factorPairs is a factor pair ...
  factorPairs-sound : {q : DecCon 𝑨 W × DecCon 𝑨 W} → q ∈ factorPairs → FactorPairᵈ q
  factorPairs-sound q∈ = proj₂ (∈-filter⁻ factorPairᵈ? {xs = listedPairs} q∈)

  -- ... and every semantic factor pair is one of them, up to ≑.
  factorPairs-complete : {θ φ : Con 𝑨 W} → IsFactorPair θ φ
    → Σ[ q ∈ DecCon 𝑨 W × DecCon 𝑨 W ] q ∈ factorPairs × θ ≑ proj₁ (proj₁ q) × φ ≑ proj₁ (proj₂ q)
  factorPairs-complete fp =
    let p = factorPair→product₂ fp
        (q , q∈ , θ≑ , φ≑) = listed-split _≟_ p
    in  q , ∈-filter⁺ factorPairᵈ? q∈ (product₂→factorPair (product₂-≑ θ≑ φ≑ p))
          , θ≑ , φ≑
```

#### Algebras with at most three elements

ALV remarks after Definition 4.37 that every finite algebra of prime cardinality
is directly indecomposable, since the cardinality of `𝑨 ≅ 𝑩 × 𝑪` is the product of
the cardinalities of the factors.  For algebras of at most three elements the
counting needs only the pigeonhole principle, and no congruence list at all.

Let `0_A = θ × φ` with both factors nontrivial: `a` and `b` are not `θ`-related,
and `c` and `d` are not `φ`-related.  Write `w x y` for the element linking `x`
to `y`, with `x θ w x y φ y`, which is "the element with the `θ`-coordinate of
`x` and the `φ`-coordinate of `y`".  Then the four "corners"
`w a c`, `w a d`, `w b c`, `w b d` are pairwise distinct: two corners with
different first arguments are separated by `θ` (`θ-separates`{.AgdaFunction}),
and two with different second arguments by `φ` (`φ-separates`{.AgdaFunction}).
An enumeration of at most three elements cannot list four distinct elements, so
one of the factors is trivial.  The decisions of the first section turn this
contradiction into the disjunction the definition asks for: each factor
congruence is decidable, so each factor is decided trivial or nontrivial, with a
witness pair in the second case.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {θ φ : Con 𝑨 ℓ}
         (p : IsProduct₂ (Setoid._≈_ 𝔻[ 𝑨 ]) θ φ) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( sym to ≈sym )
  private
    θsym = IsEquivalence.sym (is-equivalence (proj₂ θ))
    θtrans = IsEquivalence.trans (is-equivalence (proj₂ θ))
    φsym = IsEquivalence.sym (is-equivalence (proj₂ φ))
    φtrans = IsEquivalence.trans (is-equivalence (proj₂ φ))

  -- The element with the θ-coordinate of x and the φ-coordinate of y.
  corner : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  corner x y = proj₁ (composite p x y)

  -- Corners with θ-unrelated first arguments are distinct.
  θ-separates : ∀ {x x′} → ¬ proj₁ θ x x′ → ∀ y y′ → ¬ (corner x y ≈ corner x′ y′)
  θ-separates {x} {x′} ¬xθx′ y y′ e =
    let (_ , xθw , _) = composite p x y
        (_ , x′θw′ , _) = composite p x′ y′
    in  ¬xθx′ (θtrans xθw (θtrans (reflexive (proj₂ θ) e) (θsym x′θw′)))

  -- Corners with φ-unrelated second arguments are distinct.
  φ-separates : ∀ {y y′} → ¬ proj₁ φ y y′ → ∀ x x′ → ¬ (corner x y ≈ corner x′ y′)
  φ-separates {y} {y′} ¬yφy′ x x′ e =
    let (_ , _ , wφy) = composite p x y
        (_ , _ , w′φy′) = composite p x′ y′
    in  ¬yφy′ (φtrans (φsym wφy) (φtrans (reflexive (proj₂ φ) e) w′φy′))

  -- Two nontrivial factors give four pairwise distinct corners.
  four-corners : Nontrivial (𝑨 ╱ θ) → Nontrivial (𝑨 ╱ φ)
    → Σ[ c ∈ (Fin 4 → 𝕌[ 𝑨 ]) ] (∀ i j → i < j → ¬ (c i ≈ c j))
  four-corners (a , b , ¬aθb) (c , d , ¬cφd) = cs , distinct
    where
    cs : Fin 4 → 𝕌[ 𝑨 ]
    cs 0F = corner a c
    cs 1F = corner a d
    cs 2F = corner b c
    cs 3F = corner b d

    distinct : ∀ i j → i < j → ¬ (cs i ≈ cs j)
    distinct 0F 0F ()
    distinct 0F 1F _ = φ-separates ¬cφd a a
    distinct 0F 2F _ = θ-separates ¬aθb c c
    distinct 0F 3F _ = θ-separates ¬aθb c d
    distinct 1F 0F ()
    distinct 1F 1F (s≤s ())
    distinct 1F 2F _ = θ-separates ¬aθb d c
    distinct 1F 3F _ = θ-separates ¬aθb d d
    distinct 2F 0F ()
    distinct 2F 1F (s≤s ())
    distinct 2F 2F (s≤s (s≤s ()))
    distinct 2F 3F _ = φ-separates ¬cφd b b
    distinct 3F 0F ()
    distinct 3F 1F (s≤s ())
    distinct 3F 2F (s≤s (s≤s ()))
    distinct 3F 3F (s≤s (s≤s (s≤s ())))
```

The pigeonhole principle of the standard library finds two of the four corners
with the same enumeration index, hence equal, and the theorem follows.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (𝑭 : FiniteAlgebra 𝑨) where
  open FiniteAlgebra 𝑭 using ( _≟_ ; card ; enum ; enum-sur )
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( sym to ≈sym ; trans to ≈trans
                                           ; reflexive to ≡→≈ )

  -- An enumeration of at most three elements lists no four distinct elements.
  no-four-distinct : card ≤ⁿ 3 → (c : Fin 4 → 𝕌[ 𝑨 ]) → (∀ i j → i < j → ¬ (c i ≈ c j)) → ⊥
  no-four-distinct card≤3 c distinct =
    let (i , j , i<j , same) = pigeonhole (s≤s card≤3) (λ k → proj₁ (enum-sur (c k)))
    in  distinct i j i<j (≈trans (≈sym (proj₂ (enum-sur (c i))))
                                 (≈trans (≡→≈ (≡-cong enum same)) (proj₂ (enum-sur (c j)))))

  -- A nontrivial algebra with an enumeration of at most three elements is directly
  -- indecomposable.
  small→indecomposable : card ≤ⁿ 3 → Nontrivial 𝑨 → IsDirectlyIndecomposable ℓ 𝑨
  small→indecomposable card≤3 nt = record
    { nontrivial      = nt
    ; factor-trivial  = λ θ φ fp → split (factorPair→product₂ fp)
    }
    where
    split : {θ φ : Con 𝑨 ℓ} → IsProduct₂ _≈_ θ φ → Trivial (𝑨 ╱ θ) ⊎ Trivial (𝑨 ╱ φ)
    split p = decide (trivial? 𝑭 θᵈ) (trivial? 𝑭 φᵈ)
      where
      θᵈ = factorˡ-DecCon _≟_ p
      φᵈ = factorʳ-DecCon _≟_ p

      decide : Dec (Trivial (𝑨 ╱ proj₁ θᵈ)) → Dec (Trivial (𝑨 ╱ proj₁ φᵈ)) → _
      decide (yes t) _        = inj₁ t
      decide (no _) (yes t)   = inj₂ t
      decide (no ¬t) (no ¬t′) =
        let (c , distinct) = four-corners p (¬trivial→nontrivial 𝑭 θᵈ ¬t) (¬trivial→nontrivial 𝑭 φᵈ ¬t′)
        in  ⊥-elim (no-four-distinct card≤3 c distinct)
```

#### Every finite algebra is a product of directly indecomposable algebras

The textbook proof of Exercise 4.38 (2) is an induction on the size of the
algebra: if `𝑨` is neither trivial nor directly indecomposable, then
`𝑨 ≅ 𝑩 × 𝑪` with both factors nontrivial, hence smaller than `𝑨`.  We run the same
induction inside the congruence lattice, which is ALV's "blanket assumption" of
§5.2 that the factors of `𝑨` are taken from its quotients `𝑨/θ`: starting from the
diagonal, a congruence `d` that is neither total nor indecomposable splits
properly as `d = d₀ × d₁` (`indecomposable-or-split`{.AgdaFunction}); both factors
are decomposed in turn, and the two decompositions are concatenated
(`product-++`{.AgdaFunction} of [Setoid.Decompositions.Products][], which is
ALV's Lemma 3 (ii)).

The measure is not the size of the quotient, which a surjective enumeration does
not compute (its `card` is an upper bound on the number of elements, not the
number), but the number `above d`{.AgdaFunction} of listed congruences
containing `d`.  It strictly decreases from `d` to each factor of a proper split:
`d ⊆ d₀`, so every listed congruence above `d₀` is above `d`; and the listed
representative of `d` is above `d` but not above `d₀`, since `d₀ ⊆ d` would make
`d₁` total.  The recursion is structural on a bound for the measure.

First, two facts about filtering a list by decidable predicates: a weaker
predicate keeps at least as many members, and strictly more if it keeps a member
the stronger one rejects.

```agda
module _ {a p q : Level} {A : Type a} {P : A → Type p} {Q : A → Type q}
         (P? : (x : A) → Dec (P x)) (Q? : (x : A) → Dec (Q x)) (P⇒Q : ∀ {x} → P x → Q x) where

  -- Filtering by a weaker predicate keeps at least as many members.
  filter-length-mono : (xs : List A) → length (filter P? xs) ≤ⁿ length (filter Q? xs)
  filter-length-mono []        = z≤n
  filter-length-mono (x ∷ xs) with P? x | Q? x
  ... | yes _   | yes _    = s≤s (filter-length-mono xs)
  ... | yes px  | no ¬qx   = ⊥-elim (¬qx (P⇒Q px))
  ... | no _    | yes _    = m≤n⇒m≤1+n (filter-length-mono xs)
  ... | no _    | no _     = filter-length-mono xs

  -- ... and strictly more if some member satisfies Q but not P.
  filter-length-strict : {x : A} {xs : List A} → x ∈ xs → Q x → ¬ P x
    → length (filter P? xs) <ⁿ length (filter Q? xs)
  filter-length-strict {xs = y ∷ ys} (here refl) qx ¬px with P? y | Q? y
  ... | yes py  | _        = ⊥-elim (¬px py)
  ... | no _    | yes _    = s≤s (filter-length-mono ys)
  ... | no _    | no ¬qy   = ⊥-elim (¬qy qx)
  filter-length-strict {xs = y ∷ ys} (there x∈) qx ¬px with P? y | Q? y
  ... | yes _   | yes _    = s≤s (filter-length-strict x∈ qx ¬px)
  ... | yes py  | no ¬qy   = ⊥-elim (¬qy (P⇒Q py))
  ... | no _    | yes _    = m≤n⇒m≤1+n (filter-length-strict x∈ qx ¬px)
  ... | no _    | no _     = filter-length-strict x∈ qx ¬px
```

Containment of decidable congruences is decidable by a sweep
(`⊆?`{.AgdaFunction}), which makes the measure computable, and the measure
decreases as claimed (`above-<`{.AgdaFunction}).

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (𝑭 : FiniteAlgebra 𝑨) where
  open Setoid 𝔻[ 𝑨 ] using () renaming ( sym to ≈sym )

  -- Containment of decidable congruences is decidable.
  ⊆? : (d e : DecCon 𝑨 ℓ) → Dec (proj₁ d ⊆ proj₁ e)
  ⊆? d e = map′ (λ h {x} {y} → h x y) (λ h x y → h)
                (all²? 𝑭 (λ x y → ConRel d x y → ConRel e x y) resp
                         (λ x y → proj₂ d x y →-dec proj₂ e x y))
    where
    resp : RespectsEq {𝑨 = 𝑨} (λ x y → ConRel d x y → ConRel e x y)
    resp a≈a′ b≈b′ h r = con-resp (proj₁ e) a≈a′ b≈b′ (h (con-resp (proj₁ d) (≈sym a≈a′) (≈sym b≈b′) r))

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ}
         (𝑭 : FiniteAlgebra 𝑨) (𝑪 : FiniteCongruencesᵈ 𝑨) where
  open FiniteCongruencesᵈ 𝑪 using ( consᵈ ; witnessᵈ ; witnessᵈ∈ ; witnessᵈ≑ )

  private
    W : Level
    W = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ

  -- The number of listed congruences containing d.
  above : DecCon 𝑨 W → ℕ
  above d = length (filter (⊆? 𝑭 d) consᵈ)

  -- A strictly larger congruence is contained in fewer listed congruences.
  above-< : (d d′ : DecCon 𝑨 W) → proj₁ d ⊆ proj₁ d′ → ¬ (proj₁ d′ ⊆ proj₁ d)
    → above d′ <ⁿ above d
  above-< d d′ d⊆d′ ¬d′⊆d =
    filter-length-strict (⊆? 𝑭 d′) (⊆? 𝑭 d) (λ d′⊆e r → d′⊆e (d⊆d′ r))
                         (witnessᵈ∈ d) (proj₁ (witnessᵈ≑ d))
                         (λ d′⊆wd → ¬d′⊆d λ r → proj₂ (witnessᵈ≑ d) (d′⊆wd r))
```

A **decomposition** of `d` is a list of indecomposable decidable congruences
whose product is `d`.  Two decompositions concatenate along a split
`d = d₀ × d₁`: the family `δ₀ ++ᵈ δ₁`{.AgdaFunction} is `δ₀` followed by `δ₁`,
and its congruences are those of `product-++`{.AgdaFunction}, up to `≑` (the two
families agree on every index once the index is split).

```agda
  -- d is the product of n indecomposable decidable congruences.
  Decomposition : DecCon 𝑨 W → Type (lsuc W)
  Decomposition d =  Σ[ n ∈ ℕ ] Σ[ δ ∈ (Fin n → DecCon 𝑨 W) ]
                     IsProduct (ConRel d) (λ i → proj₁ (δ i)) × (∀ i → IsIndecomposable (proj₁ (δ i)))

  -- The concatenation of two lists of decidable congruences.
  _++ᵈ_ : {m n : ℕ} → (Fin m → DecCon 𝑨 W) → (Fin n → DecCon 𝑨 W) → Fin (m + n) → DecCon 𝑨 W
  _++ᵈ_ {m = m} δ₀ δ₁ k = [ δ₀ , δ₁ ]′ (splitAt m k)

  -- Concatenating two decompositions along d = d₀ × d₁ decomposes d.
  concat : (d d₀ d₁ : DecCon 𝑨 W) → IsProduct₂ (ConRel d) (proj₁ d₀) (proj₁ d₁)
    → Decomposition d₀ → Decomposition d₁ → Decomposition d
  concat d d₀ d₁ p (m , δ₀ , p₀ , ind₀) (n , δ₁ , p₁ , ind₁) =
    m + n , δ₀ ++ᵈ δ₁ , product-≑ (λ k → agree (splitAt m k)) (product-++ p p₀ p₁)
          , λ k → indecomposable (splitAt m k)
    where
    -- The two descriptions of the concatenated family agree.
    agree : (s : Fin m ⊎ Fin n)
      → [ (λ i → proj₁ (δ₀ i)) , (λ j → proj₁ (δ₁ j)) ]′ s ≑ proj₁ ([ δ₀ , δ₁ ]′ s)
    agree (inj₁ i) = (λ r → r) , (λ r → r)
    agree (inj₂ j) = (λ r → r) , (λ r → r)

    -- Every member of the concatenated family is indecomposable.
    indecomposable : (s : Fin m ⊎ Fin n) → IsIndecomposable (proj₁ ([ δ₀ , δ₁ ]′ s))
    indecomposable (inj₁ i) = ind₀ i
    indecomposable (inj₂ j) = ind₁ j
```

The recursion: a total `d` is the empty product, an indecomposable `d` the
product of itself alone, and a properly split `d` the concatenation of the
decompositions of its factors, whose measures are smaller.  It needs one element
`u` of the carrier, for the empty product.

```agda
  module _ (u : 𝕌[ 𝑨 ]) where
    private
      -- The factors of a proper split lie strictly above d ...
      d⊆d₀ : (d d₀ d₁ : DecCon 𝑨 W) → IsProduct₂ (ConRel d) (proj₁ d₀) (proj₁ d₁)
        → proj₁ d ⊆ proj₁ d₀
      d⊆d₀ _ _ _ p r = proj₁ (to-meet p r)

      d⊆d₁ : (d d₀ d₁ : DecCon 𝑨 W) → IsProduct₂ (ConRel d) (proj₁ d₀) (proj₁ d₁)
        → proj₁ d ⊆ proj₁ d₁
      d⊆d₁ _ _ _ p r = proj₂ (to-meet p r)

      -- ... because the other factor is not total.
      d₀⊈d : (d d₀ d₁ : DecCon 𝑨 W) → IsProduct₂ (ConRel d) (proj₁ d₀) (proj₁ d₁)
        → ¬ Trivial (𝑨 ╱ proj₁ d₁) → ¬ (proj₁ d₀ ⊆ proj₁ d)
      d₀⊈d _ _ _ p ¬t₁ d₀⊆d = ¬t₁ (product₂-→trivialˡ (product₂-sym p) d₀⊆d)

      d₁⊈d : (d d₀ d₁ : DecCon 𝑨 W) → IsProduct₂ (ConRel d) (proj₁ d₀) (proj₁ d₁)
        → ¬ Trivial (𝑨 ╱ proj₁ d₀) → ¬ (proj₁ d₁ ⊆ proj₁ d)
      d₁⊈d _ _ _ p ¬t₀ d₁⊆d = ¬t₀ (product₂-→trivialˡ p d₁⊆d)

      -- No natural number is below zero.
      ≮0 : {n : ℕ} → ¬ (n <ⁿ 0)
      ≮0 ()

    -- Decompose d, given a bound k on its measure.
    decompose : (k : ℕ) (d : DecCon 𝑨 W) → above d ≤ⁿ k → Decomposition d
    decompose-step : (k : ℕ) (d : DecCon 𝑨 W) → above d ≤ⁿ k
      → Dec (Trivial (𝑨 ╱ proj₁ d)) → Decomposition d
    decompose-split : (k : ℕ) (d : DecCon 𝑨 W) → above d ≤ⁿ k
      → IsIndecomposable (proj₁ d) ⊎ ProperSplit 𝑭 𝑪 d → Decomposition d

    decompose k d bound = decompose-step k d bound (trivial? 𝑭 d)

    decompose-step _ _ _ (yes t) = 0 , (λ ()) , total→product-empty u t , λ ()
    decompose-step k d bound (no ¬t) =
      decompose-split k d bound (indecomposable-or-split 𝑭 𝑪 d (¬trivial→nontrivial 𝑭 d ¬t))

    decompose-split _ d _ (inj₁ ind) = 1 , (λ _ → d) , product-singleton (proj₁ d) , λ _ → ind
    decompose-split zero d bound (inj₂ ((d₀ , d₁) , p , _ , ¬t₁)) =
      ⊥-elim (≮0 (<-≤-trans (above-< d d₀ (d⊆d₀ d d₀ d₁ p) (d₀⊈d d d₀ d₁ p ¬t₁)) bound))
    decompose-split (suc k) d bound (inj₂ ((d₀ , d₁) , p , ¬t₀ , ¬t₁)) =
      concat d d₀ d₁ p
        (decompose k d₀ (≤-pred (<-≤-trans (above-< d d₀ (d⊆d₀ d d₀ d₁ p) (d₀⊈d d d₀ d₁ p ¬t₁)) bound)))
        (decompose k d₁ (≤-pred (<-≤-trans (above-< d d₁ (d⊆d₁ d d₀ d₁ p) (d₁⊈d d d₀ d₁ p ¬t₀)) bound)))
```

Starting the recursion at the diagonal (`diagonalᵈ`{.AgdaFunction}, the setoid
equality as a decidable congruence) proves the theorem: `0_A` is a product of
indecomposable congruences (`finite-decomposition`{.AgdaFunction}), so by
Theorem 4.31 and Lemma 2 of §5.2, `𝑨` is isomorphic to the product of the
corresponding quotients, each of them directly indecomposable
(`finite-decomposition≅`{.AgdaFunction}).

```agda
    -- The diagonal 0_A, as a decidable congruence at the working level.
    diagonalᵈ : DecCon 𝑨 W
    diagonalᵈ = 𝟘[ 𝑨 ] {𝓞 ⊔ 𝓥 ⊔ α} , λ x y → map′ lift lower (FiniteAlgebra._≟_ 𝑭 x y)

    -- 0_A is a product of finitely many indecomposable congruences.
    finite-decomposition :
      Σ[ n ∈ ℕ ] Σ[ θ ∈ (Fin n → Con 𝑨 W) ]
        IsProduct (Setoid._≈_ 𝔻[ 𝑨 ]) θ × (∀ i → IsIndecomposable (θ i))
    finite-decomposition =
      let (n , δ , p , ind) = decompose (above diagonalᵈ) diagonalᵈ ≤-refl
      in  n , (λ i → proj₁ (δ i)) , product-resp lower lift p , ind

    -- ALV Exercise 4.38 (2): 𝑨 is isomorphic to a finite product of directly
    -- indecomposable algebras, namely quotients of 𝑨.
    finite-decomposition≅ :
      Σ[ n ∈ ℕ ] Σ[ θ ∈ (Fin n → Con 𝑨 W) ]
        (𝑨 ≅ ⨅ (𝑨╱ θ)) × (∀ i → IsDirectlyIndecomposable W (𝑨 ╱ θ i))
    finite-decomposition≅ =
      let (n , θ , p , ind) = finite-decomposition
      in  n , θ , product→≅ θ p , λ i → indecomposable→directly (θ i) (ind i)
```

Such a list exists for every finite algebra over a finite signature: the list
`FiniteAlgebra→FiniteCongruencesᵈ`{.AgdaFunction} of
[Setoid.Congruences.Finite.Decidable][] enumerates all Boolean tables on the
carrier and is complete for the decidable congruences, constructively.  So
every nonempty finite finitary algebra is a product of directly indecomposable
algebras (`finitary-decomposition≅`{.AgdaFunction}), with no further hypothesis.
That list has exponentially many members and an abstract decision procedure, so
the decisions above do not evaluate on it during type checking; concrete
examples supply a short list, or use `small→indecomposable`{.AgdaFunction}.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- Every nonempty finite finitary algebra is isomorphic to a finite product of
  -- directly indecomposable algebras (ALV Exercise 4.38 (2)).
  finitary-decomposition≅ : FiniteAlgebra 𝑨 → FiniteSignature 𝑆 → 𝕌[ 𝑨 ]
    → Σ[ n ∈ ℕ ] Σ[ θ ∈ (Fin n → Con 𝑨 (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)) ]
        (𝑨 ≅ ⨅ (𝑨╱ θ)) × (∀ i → IsDirectlyIndecomposable (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) (𝑨 ╱ θ i))
  finitary-decomposition≅ 𝑭 𝑺 = finite-decomposition≅ 𝑭 (FiniteAlgebra→FiniteCongruencesᵈ 𝑭 𝑺)
```
