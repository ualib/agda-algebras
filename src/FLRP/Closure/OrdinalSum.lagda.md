---
layout: default
file: "src/FLRP/Closure/OrdinalSum.lagda.md"
title: "FLRP.Closure.OrdinalSum module (The Agda Universal Algebra Library)"
date: "2026-07-24"
author: "the agda-algebras development team"
---

### Ordinal-sum closure of decidable representability

This is the [FLRP.Closure.OrdinalSum][] module of the [Agda Universal Algebra Library][].

The class of representable lattices is closed under **ordinal sums**.[^1]

Here we formalize the *adjoined* (glued) ordinal sum of
[Classical.Structures.Lattice.OrdinalSum][] at Layer D of [ADR-008][].

Given decidable representations of the summands and chosen extrema — a
`TopOf 𝓛₁`{.AgdaFunction} and a `BotOf 𝓛₂`{.AgdaFunction} — we construct a
finite finitary algebra whose decidable-congruence poset is order-isomorphic to
the glued sum, yielding

    ordinalSum-Representableᵈ : (t : TopOf 𝓛₁) (b : BotOf 𝓛₂)
      → Representableᵈ 𝓛₁ → Representableᵈ 𝓛₂
      → Representableᵈ (ordinalSum 𝓛₁ t 𝓛₂ b)


#### The witness algebra

Given representing algebras `𝑨` and `𝑩` with basepoints `a*` and `b*`, the composite
`𝑪` lives on the amalgam setoid `A ⊎ B` glued at `(a* , b*)`
(`GlueSetoid`{.AgdaModule}) — the constructive counterpart of the manuscript's
universe `A ⊎ (B ∖ {b₀})` — over the signature

    𝑆₁  ⊎  𝑆₂  ⊎  (Fin (card 𝑩) × Fin (card 𝑨))

interpreted as follows:

+  a symbol of `𝑆₁` acts through the left retraction (collapse `B` to `a*`) and lands
   in the left summand;

+  a symbol of `𝑆₂` acts through the right retraction and lands in the right summand;

+  the `(i , k)`-indexed family interprets the manuscript's unary maps
   `ĥ`{.AgdaFunction}: identity on the left summand, and on the right summand the
   *single-point collapse* `h` sending (anything `≈` to) `enum₂ i` to `enum₁ k`, the
   basepoint to `a*`, and everything else to `a*`.


#### The boundary congruence and the dichotomy

The kernel `α` of the right retraction — all of `A` in one class, `B` split by `≈` —
is a decidable congruence, and the heart of the proof is that *every* decidable
congruence of `𝑪` is comparable to it.  Both containments are decidable
(`⊆ᵈ-dec`{.AgdaFunction} of [FLRP.Representable][]); if both fail, the two violating
pairs they surrender are contradictory: a `θ`-unrelated pair inside the lower summand
on the one hand, and a `θ`-related pair with distinct right-retraction images on the
other, which the `ĥ` family maps onto the unrelated pair — one application if the
related pair is mixed, two chained through `a*` if it is pure.

This dichotomy is exactly the step that is *non-constructive at Layer S*: for
semantic congruences, comparability with `α` decides arbitrary propositions, which is
why ordinal-sum closure is a Layer-D theorem only.

#### The splitting

A congruence below `α` is determined by its restriction to the lower summand together
with `α` itself, and one above `α` by its quotient along the right retraction
(`lower-split`{.AgdaFunction} / `upper-split`{.AgdaFunction}); composing with the
given isomorphisms sends the lower cone onto `inj₁`-elements, the upper cone onto
`inj₂`-elements, and `α` itself onto the glue.

As in the product case, basepoints are supplied by `inhabited-witness`{.AgdaFunction}
normalization, so the closure theorem has no side conditions beyond the extremum data
the sum itself needs.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Closure.OrdinalSum where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Empty                             using  ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using  ( Fin ; splitAt ; join
                                                          ; combine ; remQuot )
open import Data.Fin.Patterns                      using  ( 0F )
open import Data.Fin.Properties                    using  ( splitAt-join ; remQuot-combine )
open import Data.Nat.Base                          using  ( _+_ ; _*_ )
open import Data.Product                           using  ( _,_ ; _×_ ; proj₁ ; proj₂
                                                          ; Σ-syntax )
open import Data.Sum.Base                          using  ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Data.Unit.Base                         using  ( tt )
open import Function                               using  ( _∘_ ; id )
open import Function.Construct.Identity            using  ( ↔-id )
open import Level                                  using  ( 0ℓ ; lift ; lower )
open import Relation.Binary                        using  ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; refl ; cong ; trans ; sym )
open import Relation.Nullary                       using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable             using  ( _×-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice             using  ( module Lattice-Order
                                                            ; TopOf ; BotOf )
open import Classical.Signatures.Lattice             using  (Sig-Lattice)
open import Classical.Small.Structures.Lattice       using  ( Lattice )
open import Classical.Structures.Interpret           using  ( interp-cong )
open import Classical.Structures.Lattice.OrdinalSum  using  ( module GlueSetoid
                                                            ; module LatticeOrdinalSum
                                                            ; ordinalSum )
open import FLRP.Problem                             using  ( OrderIso )
open import FLRP.Representable                       using  ( Representableᵈ ; ConIsoᵈ
                                                            ; _⊆ᵈ_ ; _≑ᵈ_ ; ConRel-resp
                                                            ; 𝟘ᵈ ; 𝟙ᵈ ; ⊆ᵈ-dec ; ⊈ᵈ-witness
                                                            ; module ConIsoᵈ-Consequences
                                                            ; inhabited-witness )
open import Overture                                 using  ( Signature
                                                            ; OperationSymbolsOf ; ArityOf )
open import Overture.Operations                      using  ( Op )
open import Setoid.Algebras.Basic                    using  ( Algebra ; 𝔻[_] ; 𝕌[_] ; _^_
                                                            ; mkAlgebra )
open import Setoid.Algebras.Finite                   using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic                 using  ( mkcon ; reflexive ; _∣≈_
                                                            ; is-equivalence ; is-compatible )
open import Setoid.Congruences.Finite.Basic          using  ( DecCon ; ConRel )
open import Setoid.Signatures.Finite                 using  ( FiniteSignature )

open FiniteAlgebra
open FiniteSignature
```
-->

#### The composite witness algebra

`OrdinalSumWitness`{.AgdaModule} packages the construction for two fixed finite
finitary algebras with chosen basepoints, everything at level `0ℓ`.

```agda
module OrdinalSumWitness
  {𝑆₁ 𝑆₂ : Signature 0ℓ 0ℓ}
  (𝑨 : Algebra {𝑆 = 𝑆₁} 0ℓ 0ℓ) (𝑭₁ : FiniteAlgebra 𝑨) (S₁ : FiniteSignature 𝑆₁) (a* : 𝕌[ 𝑨 ])
  (𝑩 : Algebra {𝑆 = 𝑆₂} 0ℓ 0ℓ) (𝑭₂ : FiniteAlgebra 𝑩) (S₂ : FiniteSignature 𝑆₂) (b* : 𝕌[ 𝑩 ])
  where

  private
    m      = 𝑭₁ .card
    n      = 𝑭₂ .card
    enum₁  = 𝑭₁ .enum
    enum₂  = 𝑭₂ .enum

  open Setoid 𝔻[ 𝑨 ] using ()
    renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝔻[ 𝑩 ] using ()
    renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )
```

#### The carrier

The amalgam of the two carriers at the basepoints is accompanied by the retractions.[^2]

```agda
  open GlueSetoid 𝔻[ 𝑨 ] a* 𝔻[ 𝑩 ] b*

  private
    A⊎B : Type 0ℓ
    A⊎B = 𝕌[ 𝑨 ] ⊎ 𝕌[ 𝑩 ]

  open Setoid glueSetoid using ()
    renaming ( trans to transᵍ ; reflexive to ≡→≈ᵍ )
```

#### The signature

The two component signatures side-by-side with the single-point collapse family is
indexed by a source in `𝑩` and a target in `𝑨` (via the enumerations).  Family
members are unary.

```agda
  OpSymbols : Type 0ℓ
  OpSymbols = OperationSymbolsOf 𝑆₁ ⊎ (OperationSymbolsOf 𝑆₂ ⊎ (Fin n × Fin m))

  arity : OpSymbols → Type 0ℓ
  arity (inj₁ f)          = ArityOf 𝑆₁ f
  arity (inj₂ (inj₁ g))   = ArityOf 𝑆₂ g
  arity (inj₂ (inj₂ _))   = Fin 1

  𝑆ₒ : Signature 0ℓ 0ℓ
  𝑆ₒ = OpSymbols , arity
```

#### The collapse maps

`h i k` sends (anything `≈` to) the basepoint to `a*`, then (anything `≈` to)
`enum₂ i` to `enum₁ k`, and everything else to `a*`; the guard keeps the lift `ĥ`
congruent across the glue.

The three evaluation lemmas — at the basepoint, at the programmed point, away from it
— are the module's workhorses.

```agda
  private
    h : Fin n → Fin m → 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
    h i k b with 𝑭₂ ._≟_ b b*
    ... | yes _ = a*
    ... | no _ with 𝑭₂ ._≟_ b (enum₂ i)
    ...   | yes _ = enum₁ k
    ...   | no _  = a*

    -- h respects ≈₂: aligned decisions take the same branch, misaligned ones clash.
    h-cong : ∀ i k {x y} → x ≈₂ y → h i k x ≈₁ h i k y
    h-cong i k {x} {y} e with 𝑭₂ ._≟_ x b* | 𝑭₂ ._≟_ y b*
    ... | yes _  | yes _   = refl₁
    ... | yes p  | no ¬p'  = ⊥-elim (¬p' (trans₂ (sym₂ e) p))
    ... | no ¬p  | yes p'  = ⊥-elim (¬p (trans₂ e p'))
    ... | no _   | no _ with 𝑭₂ ._≟_ x (enum₂ i) | 𝑭₂ ._≟_ y (enum₂ i)
    ...   | yes _  | yes _   = refl₁
    ...   | yes q  | no ¬q'  = ⊥-elim (¬q' (trans₂ (sym₂ e) q))
    ...   | no ¬q  | yes q'  = ⊥-elim (¬q (trans₂ e q'))
    ...   | no _   | no _    = refl₁

    -- At the basepoint the collapse gives a*.
    h-at-b* : ∀ i k {x} → x ≈₂ b* → h i k x ≈₁ a*
    h-at-b* i k {x} e with 𝑭₂ ._≟_ x b*
    ... | yes _  = refl₁
    ... | no ¬p  = ⊥-elim (¬p e)

    -- Enumeration indices of designated elements, with their proofs.
    idx₁ : 𝕌[ 𝑨 ] → Fin m
    idx₁ x = proj₁ (𝑭₁ .enum-sur x)

    idx₁-≈ : ∀ x → enum₁ (idx₁ x) ≈₁ x
    idx₁-≈ x = proj₂ (𝑭₁ .enum-sur x)

    idx₂ : 𝕌[ 𝑩 ] → Fin n
    idx₂ x = proj₁ (𝑭₂ .enum-sur x)

    idx₂-≈ : ∀ x → enum₂ (idx₂ x) ≈₂ x
    idx₂-≈ x = proj₂ (𝑭₂ .enum-sur x)

    -- The concrete family member sending b to x.
    h[_↦_] : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
    h[ b ↦ x ] = h (idx₂ b) (idx₁ x)

    -- Away from the basepoint, the map hits its programmed value at its source ...
    h-at : ∀ b x → ¬ (b ≈₂ b*) → h[ b ↦ x ] b ≈₁ x
    h-at b x ¬b* with 𝑭₂ ._≟_ b b*
    ... | yes p = ⊥-elim (¬b* p)
    ... | no _ with 𝑭₂ ._≟_ b (enum₂ (idx₂ b))
    ...   | yes _  = idx₁-≈ x
    ...   | no ¬q  = ⊥-elim (¬q (sym₂ (idx₂-≈ b)))

    -- ... and collapses everything ≉ the source to a*.
    h-away : ∀ b x b' → ¬ (b' ≈₂ b) → h[ b ↦ x ] b' ≈₁ a*
    h-away b x b' ¬eq with 𝑭₂ ._≟_ b' b*
    ... | yes _ = refl₁
    ... | no _ with 𝑭₂ ._≟_ b' (enum₂ (idx₂ b))
    ...   | yes q  = ⊥-elim (¬eq (trans₂ q (idx₂-≈ b)))
    ...   | no _   = refl₁

    -- The lift of h to the amalgam: identity on the left, collapse on the right.
    ĥ : Fin n → Fin m → A⊎B → A⊎B
    ĥ i k (inj₁ a) = inj₁ a
    ĥ i k (inj₂ b) = inj₁ (h i k b)

    ĥ-cong : ∀ i k {x y} → x ≈ᵍ y → ĥ i k x ≈ᵍ ĥ i k y
    ĥ-cong i k {inj₁ a} {inj₁ a'} (ea , _)   = ≈ᵍ-inj₁ ea
    ĥ-cong i k {inj₁ a} {inj₂ b}  (ea , eb)  =
      ≈ᵍ-inj₁ (trans₁ ea (sym₁ (h-at-b* i k (sym₂ eb))))
    ĥ-cong i k {inj₂ b} {inj₁ a}  (ea , eb)  =
      ≈ᵍ-inj₁ (trans₁ (h-at-b* i k eb) ea)
    ĥ-cong i k {inj₂ b} {inj₂ b'} (_ , eb)   = ≈ᵍ-inj₁ (h-cong i k eb)

    -- The lift always lands in the left summand, so its right retraction is b*.
    ĥ-lands-left : ∀ i k x → retractʳ (ĥ i k x) ≡ b*
    ĥ-lands-left i k (inj₁ _) = refl
    ĥ-lands-left i k (inj₂ _) = refl
```

#### The algebra

`𝑆₁` acts through the left retraction, `𝑆₂` through the right one, and the family
symbols act by `ĥ`{.AgdaFunction}.

```agda
  𝑪 : Algebra {𝑆 = 𝑆ₒ} 0ℓ 0ℓ
  𝑪 = mkAlgebra glueSetoid interp interp-congruence
    where
    interp : (o : OpSymbols) → Op (arity o) A⊎B
    interp (inj₁ f) args = inj₁ ((f ^ 𝑨) (retractˡ ∘ args))
    interp (inj₂ (inj₁ g)) args = inj₂ ((g ^ 𝑩) (retractʳ ∘ args))
    interp (inj₂ (inj₂ (i , k))) args = ĥ i k (args 0F)

    interp-congruence : ∀ o {u v : arity o → A⊎B}
      → (∀ i → u i ≈ᵍ v i) → interp o u ≈ᵍ interp o v
    interp-congruence (inj₁ f) e = ≈ᵍ-inj₁ (interp-cong 𝑨 f (proj₁ ∘ e))
    interp-congruence (inj₂ (inj₁ g)) e = ≈ᵍ-inj₂ (interp-cong 𝑩 g (proj₂ ∘ e))
    interp-congruence (inj₂ (inj₂ (i , k))) {u} {v} e = ĥ-cong i k {u 0F} {v 0F} (e 0F)
```

#### Finiteness of the composite

The carrier is enumerated by `Fin (m + n)` through one `splitAt` layer, with
glued equality decided by cases; the signature adds the `n * m` family symbols
through a `combine`/`remQuot` layer.

```agda
  private
    enumC : Fin (m + n) → A⊎B
    enumC = [ inj₁ ∘ enum₁ , inj₂ ∘ enum₂ ]′ ∘ splitAt m

    enumC-join : (x : Fin m ⊎ Fin n) → enumC (join m n x) ≡ [ inj₁ ∘ enum₁ , inj₂ ∘ enum₂ ]′ x
    enumC-join x = cong [ inj₁ ∘ enum₁ , inj₂ ∘ enum₂ ]′ (splitAt-join m n x)

  𝑪-FiniteAlgebra : FiniteAlgebra 𝑪
  𝑪-FiniteAlgebra ._≟_ = decEq
    where
    open FiniteAlgebra 𝑭₁ using() renaming (_≟_ to _≟₁_ )
    open FiniteAlgebra 𝑭₂ using() renaming (_≟_ to _≟₂_ )

    decEq : (x y : A⊎B) → Dec (x ≈ᵍ y)

    decEq (inj₁ a) (inj₁ a') with a ≟₁ a'
    ... | yes p = yes (p , refl₂)
    ... | no ¬p = no λ e → ¬p (proj₁ e)

    decEq (inj₁ a) (inj₂ b) with a ≟₁ a* | b* ≟₂ b
    ... | yes p  | yes q  = yes (p , q)
    ... | yes _  | no ¬q  = no λ (_ , e) → ¬q e
    ... | no ¬p  | yes _  = no λ (e , _) → ¬p e
    ... | no ¬p  | no _   = no λ (e , _) → ¬p e

    decEq (inj₂ b) (inj₁ a) with a* ≟₁ a | b ≟₂ b*
    ... | yes p  | yes q  = yes (p , q)
    ... | yes _  | no ¬q  = no λ (_ , e) → ¬q e
    ... | no ¬p  | yes _  = no λ (e , _) → ¬p e
    ... | no ¬p  | no _   = no λ (e , _) → ¬p e
    decEq (inj₂ b) (inj₂ b') with b ≟₂ b'
    ... | yes p = yes (refl₁ , p)
    ... | no ¬p = no λ (_ , e) → ¬p e

  𝑪-FiniteAlgebra .card = m + n
  𝑪-FiniteAlgebra .enum = enumC
  𝑪-FiniteAlgebra .enum-sur = sur
    where
    sur : ∀ x → Σ[ i ∈ Fin (m + n) ] enumC i ≈ᵍ x
    sur (inj₁ a) with 𝑭₁ .enum-sur a
    ... | i , p =  join m n (inj₁ i)
                   ,  transᵍ
                      {enumC (join m n (inj₁ i))} {inj₁ (enum₁ i)} {inj₁ a}
                      (≡→≈ᵍ (enumC-join (inj₁ i))) (≈ᵍ-inj₁ p)
    sur (inj₂ b) with 𝑭₂ .enum-sur b
    ... | j , p =  join m n (inj₂ j)
                   ,  transᵍ
                      {enumC (join m n (inj₂ j))} {inj₂ (enum₂ j)} {inj₂ b}
                      (≡→≈ᵍ (enumC-join (inj₂ j))) (≈ᵍ-inj₂ p)
  private
    c₁ = S₁ .opCard
    c₂ = S₂ .opCard

    decode₂ : Fin (c₂ + n * m) → OperationSymbolsOf 𝑆₂ ⊎ (Fin n × Fin m)
    decode₂ = [ inj₁ ∘ S₂ .opEnum , inj₂ ∘ remQuot {n} m ]′ ∘ splitAt c₂

    decode : Fin (c₁ + (c₂ + n * m)) → OpSymbols
    decode = [ inj₁ ∘ S₁ .opEnum , inj₂ ∘ decode₂ ]′ ∘ splitAt c₁

    decode-join : (x : Fin c₁ ⊎ Fin (c₂ + n * m))
      → decode (join c₁ _ x) ≡ [ inj₁ ∘ S₁ .opEnum , inj₂ ∘ decode₂ ]′ x
    decode-join x = cong [ inj₁ ∘ S₁ .opEnum , inj₂ ∘ decode₂ ]′ (splitAt-join c₁ _ x)

    decode₂-join : (x : Fin c₂ ⊎ Fin (n * m))
      → decode₂ (join c₂ _ x) ≡ [ inj₁ ∘ S₂ .opEnum , inj₂ ∘ remQuot {n} m ]′ x
    decode₂-join x = cong [ inj₁ ∘ S₂ .opEnum , inj₂ ∘ remQuot {n} m ]′ (splitAt-join c₂ _ x)


    decode-sur : (o : OpSymbols) → Σ[ k ∈ Fin (c₁ + (c₂ + n * m)) ] decode k ≡ o

    decode-sur (inj₁ f) with S₁ .opEnum-sur f
    ... | i , p = join c₁ _ (inj₁ i) , trans (decode-join (inj₁ i)) (cong inj₁ p)

    decode-sur (inj₂ (inj₁ g)) with S₂ .opEnum-sur g
    ... | j , p =
      join c₁ _ (inj₂ (join c₂ _ (inj₁ j)))
      , trans  (decode-join (inj₂ (join c₂ _ (inj₁ j))))
               (trans  (cong inj₂ (decode₂-join (inj₁ j))) (cong (inj₂ ∘ inj₁) p))

    decode-sur (inj₂ (inj₂ (i , k))) =
      join c₁ _ (inj₂ (join c₂ _ (inj₂ (combine i k))))
      , trans  (decode-join (inj₂ (join c₂ _ (inj₂ (combine i k)))))
               (trans  (cong inj₂ (decode₂-join (inj₂ (combine i k))))
                       (cong (inj₂ ∘ inj₂) (remQuot-combine i k)))

  𝑆ₒ-FiniteSignature : FiniteSignature 𝑆ₒ
  𝑆ₒ-FiniteSignature .opCard                    = c₁ + (c₂ + n * m)
  𝑆ₒ-FiniteSignature .opEnum                    = decode
  𝑆ₒ-FiniteSignature .opEnum-sur                = decode-sur
  𝑆ₒ-FiniteSignature .finitary (inj₁ f)         = S₁ .finitary f
  𝑆ₒ-FiniteSignature .finitary (inj₂ (inj₁ g))  = S₂ .finitary g
  𝑆ₒ-FiniteSignature .finitary (inj₂ (inj₂ _))  = 1 , ↔-id _
```

#### The boundary congruence

`αᵈ`{.AgdaFunction} is the kernel of the right retraction: the whole lower
summand in one class, the upper summand split by its own equality.  Every
operation of `𝑪` descends along the retraction, so compatibility is uniform.

```agda
  αᵈ : DecCon 𝑪 0ℓ
  αᵈ = (rel , mkcon (λ {x} {y} e → rfl {x} {y} e) eqv cmp) , dec
    where
    rel : A⊎B → A⊎B → Type 0ℓ
    rel x y = retractʳ x ≈₂ retractʳ y

    rfl : ∀ {x y} → x ≈ᵍ y → rel x y
    rfl e = proj₂ e

    eqv : IsEquivalence rel
    eqv = record
      { refl   = λ {x} → refl₂ {retractʳ x}
      ; sym    = sym₂
      ; trans  = trans₂
      }

    cmp : 𝑪 ∣≈ rel
    cmp (inj₁ f) _ = refl₂
    cmp (inj₂ (inj₁ g)) {U} {V} uv = interp-cong 𝑩 g {retractʳ ∘ U} {retractʳ ∘ V} uv
    cmp (inj₂ (inj₂ (i , k))) {U} {V} _ = ≡→≈₂ (trans  (ĥ-lands-left i k (U 0F))
                                                       (sym (ĥ-lands-left i k (V 0F))))
      where ≡→≈₂ = Setoid.reflexive 𝔻[ 𝑩 ]

    dec : ∀ x y → Dec (rel x y)
    dec x y = retractʳ x ≟₂ retractʳ y
      where open FiniteAlgebra 𝑭₂ using () renaming ( _≟_ to _≟₂_ )
```

#### Restrictions and extensions of congruences

A congruence of the composite restricts to each summand; a congruence of a
summand extends to the composite — below `α` for the lower summand (paired
with the kernel condition) and above `α` for the upper one (pulled back along
the retraction).  All four constructions preserve decidability, and their
compatibility proofs ride on the same reductions as the interpretations.

```agda
  -- Restrict to the lower summand.
  restrictA : DecCon 𝑪 0ℓ → DecCon 𝑨 0ℓ
  restrictA d = (rel , mkcon rfl eqv cmp) , dec
    where
    θcon = proj₂ (proj₁ d)

    rel : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type 0ℓ
    rel a a' = ConRel d (inj₁ a) (inj₁ a')

    rfl : ∀ {x y} → x ≈₁ y → rel x y
    rfl e = reflexive θcon (≈ᵍ-inj₁ e)

    eqv : IsEquivalence rel
    eqv = record
      { refl   = IsEquivalence.refl (is-equivalence θcon)
      ; sym    = IsEquivalence.sym (is-equivalence θcon)
      ; trans  = IsEquivalence.trans (is-equivalence θcon)
      }

    cmp : 𝑨 ∣≈ rel
    cmp f uv = is-compatible θcon (inj₁ f) uv

    dec : ∀ x y → Dec (rel x y)
    dec x y = proj₂ d (inj₁ x) (inj₁ y)

  -- Restrict to the upper summand.
  restrictB : DecCon 𝑪 0ℓ → DecCon 𝑩 0ℓ
  restrictB d = (rel , mkcon rfl eqv cmp) , dec
    where
    θcon = proj₂ (proj₁ d)

    rel : 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → Type 0ℓ
    rel b b' = ConRel d (inj₂ b) (inj₂ b')

    rfl : ∀ {x y} → x ≈₂ y → rel x y
    rfl e = reflexive θcon (≈ᵍ-inj₂ e)

    eqv : IsEquivalence rel
    eqv = record
      { refl   = IsEquivalence.refl (is-equivalence θcon)
      ; sym    = IsEquivalence.sym (is-equivalence θcon)
      ; trans  = IsEquivalence.trans (is-equivalence θcon)
      }

    cmp : 𝑩 ∣≈ rel
    cmp g uv = is-compatible θcon (inj₂ (inj₁ g)) uv

    dec : ∀ x y → Dec (rel x y)
    dec x y = proj₂ d (inj₂ x) (inj₂ y)

  -- Extend a lower-summand congruence below the boundary.
  lowerExt : DecCon 𝑨 0ℓ → DecCon 𝑪 0ℓ
  lowerExt d₁@((θ , con₁) , dec₁) = (rel , mkcon (λ {x} {y} e → rfl {x} {y} e) eqv cmp) , dec
    where

    rel : A⊎B → A⊎B → Type 0ℓ
    rel x y = ConRel d₁ (retractˡ x) (retractˡ y) × (retractʳ x ≈₂ retractʳ y)

    rfl : ∀ {x y} → x ≈ᵍ y → rel x y
    rfl {x} {y} (l , r) = reflexive con₁ l , r

    eqv : IsEquivalence rel
    eqv = record
      { refl   = IsEquivalence.refl (is-equivalence con₁) , refl₂
      ; sym    = λ (l , r) → IsEquivalence.sym (is-equivalence con₁) l , sym₂ r
      ; trans  = λ (l , r) (l' , r') →
                   IsEquivalence.trans (is-equivalence con₁) l l' , trans₂ r r'
      }

    -- The family maps preserve the extension: pointwise, by shape.
    ĥ-pres : ∀ i k {x y} → rel x y → rel (ĥ i k x) (ĥ i k y)
    ĥ-pres i k {inj₁ a} {inj₁ a'} (l , _)  = l , refl₂
    ĥ-pres i k {inj₂ b} {inj₂ b'} (_ , r)  = reflexive con₁ (h-cong i k r) , refl₂
    ĥ-pres i k {inj₁ a} {inj₂ b}  (l , r)  =
      ConRel-resp d₁ {a} {a} {a*} {h i k b} refl₁ (sym₁ (h-at-b* i k (sym₂ r))) l , refl₂
    ĥ-pres i k {inj₂ b} {inj₁ a}  (l , r)  =
      ConRel-resp d₁ {a*} {h i k b} {a} {a} (sym₁ (h-at-b* i k r)) refl₁ l , refl₂

    cmp : 𝑪 ∣≈ rel
    cmp (inj₁ f) uv = is-compatible con₁ f (proj₁ ∘ uv) , refl₂
    cmp (inj₂ (inj₁ g)) {U} {V} uv =  reflexive con₁ refl₁ , interp-cong 𝑩 g (proj₂ ∘ uv)
    cmp (inj₂ (inj₂ (i , k))) {U} {V} uv = ĥ-pres i k {U 0F} {V 0F} (uv 0F)

    dec : ∀ x y → Dec (rel x y)
    dec x y = (dec₁ (retractˡ x) (retractˡ y)) ×-dec (𝑭₂ ._≟_ (retractʳ x) (retractʳ y))

  -- Extend an upper-summand congruence above the boundary.
  upperExt : DecCon 𝑩 0ℓ → DecCon 𝑪 0ℓ
  upperExt d₂@((_ , con₂) , dec₂) = (rel , mkcon (λ {x} {y} e → rfl {x} {y} e) eqv cmp) , dec
    where
    rel : A⊎B → A⊎B → Type 0ℓ
    rel x y = ConRel d₂ (retractʳ x) (retractʳ y)

    rfl : ∀ {x y} → x ≈ᵍ y → rel x y
    rfl {x} {y} (_ , r) = reflexive con₂ r

    eqv : IsEquivalence rel
    eqv = record
      { refl   = IsEquivalence.refl (is-equivalence con₂)
      ; sym    = IsEquivalence.sym (is-equivalence con₂)
      ; trans  = IsEquivalence.trans (is-equivalence con₂)
      }

    cmp : 𝑪 ∣≈ rel
    cmp (inj₁ f) _ = reflexive con₂ refl₂
    cmp (inj₂ (inj₁ g)) {U} {V} uv = is-compatible con₂ g {retractʳ ∘ U} {retractʳ ∘ V} uv
    cmp (inj₂ (inj₂ (i , k))) {U} {V} uv =
      reflexive con₂ (≡→≈₂ (trans (ĥ-lands-left i k (U 0F)) (sym (ĥ-lands-left i k (V 0F)))))
      where ≡→≈₂ = Setoid.reflexive 𝔻[ 𝑩 ]

    dec : ∀ x y → Dec (rel x y)
    dec x y = dec₂ (retractʳ x) (retractʳ y)
```

The bookkeeping lemmas the isomorphism consumes: monotonicity and
`≑ᵈ`-congruence of the four maps, the two round trips on the summand side, the
standing containments against the boundary, and the identification of the
boundary's restrictions with the extreme congruences.

```agda
  restrictA-mono : {d e : DecCon 𝑪 0ℓ} → d ⊆ᵈ e → restrictA d ⊆ᵈ restrictA e
  restrictA-mono s p = s p

  restrictB-mono : {d e : DecCon 𝑪 0ℓ} → d ⊆ᵈ e → restrictB d ⊆ᵈ restrictB e
  restrictB-mono s p = s p

  lowerExt-mono : {d e : DecCon 𝑨 0ℓ} → d ⊆ᵈ e → lowerExt d ⊆ᵈ lowerExt e
  lowerExt-mono s (l , r) = s l , r

  upperExt-mono : {d e : DecCon 𝑩 0ℓ} → d ⊆ᵈ e → upperExt d ⊆ᵈ upperExt e
  upperExt-mono s p = s p

  lowerExt-cong≑ : {d e : DecCon 𝑨 0ℓ} → d ≑ᵈ e → lowerExt d ≑ᵈ lowerExt e
  lowerExt-cong≑ (s₁ , s₂) = (λ (l , r) → s₁ l , r) , (λ (l , r) → s₂ l , r)

  upperExt-cong≑ : {d e : DecCon 𝑩 0ℓ} → d ≑ᵈ e → upperExt d ≑ᵈ upperExt e
  upperExt-cong≑ (s₁ , s₂) = s₁ , s₂

  -- Restricting an extension recovers the summand congruence.
  restrictA-lowerExt : (d₁ : DecCon 𝑨 0ℓ) → restrictA (lowerExt d₁) ≑ᵈ d₁
  restrictA-lowerExt d₁ = proj₁ , λ p → (p , refl₂)

  restrictB-upperExt : (d₂ : DecCon 𝑩 0ℓ) → restrictB (upperExt d₂) ≑ᵈ d₂
  restrictB-upperExt d₂ = id , id

  -- Lower extensions sit below the boundary; upper ones sit above it.
  lowerExt-⊆-α : (d₁ : DecCon 𝑨 0ℓ) → lowerExt d₁ ⊆ᵈ αᵈ
  lowerExt-⊆-α _ (_ , r) = r

  α-⊆-upperExt : (d₂ : DecCon 𝑩 0ℓ) → αᵈ ⊆ᵈ upperExt d₂
  α-⊆-upperExt ((_ , con₂) , _) e = reflexive con₂ e

  -- The boundary restricts to the total congruence below, the diagonal above.
  restrictA-α : restrictA αᵈ ≑ᵈ 𝟙ᵈ {ℓ = 0ℓ}
  restrictA-α = (λ _ → lift tt) , (λ _ → refl₂)

  restrictB-α : restrictB αᵈ ≑ᵈ 𝟘ᵈ (𝑭₂ ._≟_)
  restrictB-α = lift , lower
```

#### The comparability dichotomy

Every decidable congruence of `𝑪` is comparable to the boundary.  Decide both
containments; if both fail, `⊈ᵈ-witness`{.AgdaFunction} surrenders (i) a pair
related by `α` but not by `θ` — which normalizes to a `θ`-unrelated pair
*inside the lower summand*, since `α`-related pairs touching the upper summand
are glued — and (ii) a `θ`-related pair with distinct retraction images.  The
collapse family then maps pair (ii) onto pair (i): one application in the
mixed case (after checking which endpoint the unrelated pair misses), two
chained through `a*` in the pure case.

```agda
  private
    -- (i): a θ-unrelated pair in the lower summand.
    lower-gap : (θ : DecCon 𝑪 0ℓ) → ¬ (αᵈ ⊆ᵈ θ)
      → Σ[ x ∈ 𝕌[ 𝑨 ] ] Σ[ y ∈ 𝕌[ 𝑨 ] ] (¬ ConRel θ (inj₁ x) (inj₁ y))
    lower-gap θ ¬α⊆θ with ⊈ᵈ-witness 𝑪-FiniteAlgebra αᵈ θ ¬α⊆θ
    ... | inj₁ a , inj₁ a' , (_ , ¬θr)   = a , a' , ¬θr
    ... | inj₁ a , inj₂ b , (αr , ¬θr)   =
      a , a* , λ p → ¬θr (ConRel-resp θ (refl₁ , refl₂) (refl₁ , αr) p)

    ... | inj₂ b , inj₁ a , (αr , ¬θr)   =
      a* , a , λ p → ¬θr (ConRel-resp θ (refl₁ , sym₂ αr) (refl₁ , refl₂) p)
    ... | inj₂ b , inj₂ b' , (αr , ¬θr)  =
      ⊥-elim (¬θr (reflexive (proj₂ (proj₁ θ)) (refl₁ , αr)))

    -- The mixed engine: a θ-related pair (inj₁ a , inj₂ b) with b off the
    -- basepoint collapses onto any given lower pair, refuting its unrelatedness.
    mixed-absurd : (θ : DecCon 𝑪 0ℓ) (x y : 𝕌[ 𝑨 ]) → ¬ ConRel θ (inj₁ x) (inj₁ y)
      → (a : 𝕌[ 𝑨 ]) (b : 𝕌[ 𝑩 ]) → ¬ (b ≈₂ b*) → ConRel θ (inj₁ a) (inj₂ b) → ⊥
    mixed-absurd θ x y ¬θxy a b ¬b* θab = decide
      where
      θcon    = proj₂ (proj₁ θ)
      θsym    = IsEquivalence.sym (is-equivalence θcon)
      θtrans  = IsEquivalence.trans (is-equivalence θcon)

      -- Send b to any designated target, staying θ-related to a.
      punch : (z : 𝕌[ 𝑨 ]) → ConRel θ (inj₁ a) (inj₁ z)
      punch z = ConRel-resp θ  (refl₁ , refl₂) (≈ᵍ-inj₁ (h-at b z ¬b*))
                  (is-compatible θcon (inj₂ (inj₂ (idx₂ b , idx₁ z))) (λ _ → θab))

      decide : ⊥
      decide with proj₂ θ (inj₁ x) (inj₁ a) | proj₂ θ (inj₁ y) (inj₁ a)
      ... | yes θxa  | yes θya  = ¬θxy (θtrans θxa (θsym θya))
      ... | yes _    | no ¬θya  = ¬θya (θsym (punch y))
      ... | no ¬θxa  | yes _    = ¬θxa (θsym (punch x))
      ... | no ¬θxa  | no _     = ¬θxa (θsym (punch x))

    incomparable-absurd : (θ : DecCon 𝑪 0ℓ) → ¬ (θ ⊆ᵈ αᵈ) → ¬ (αᵈ ⊆ᵈ θ) → ⊥
    incomparable-absurd θ ¬θ⊆α ¬α⊆θ = final (⊈ᵈ-witness 𝑪-FiniteAlgebra θ αᵈ ¬θ⊆α)
      where
      θcon    = proj₂ (proj₁ θ)
      θsym    = IsEquivalence.sym (is-equivalence θcon)
      θtrans  = IsEquivalence.trans (is-equivalence θcon)

      gap  = lower-gap θ ¬α⊆θ
      x    = proj₁ gap
      y    = proj₁ (proj₂ gap)
      ¬θxy = proj₂ (proj₂ gap)

      final : Σ[ p ∈ A⊎B ] Σ[ q ∈ A⊎B ] (ConRel θ p q × ¬ (retractʳ p ≈₂ retractʳ q)) → ⊥
      final (inj₁ a , inj₁ a' , (_ , ¬ρ))   = ¬ρ refl₂
      final (inj₁ a , inj₂ b , (θr , ¬ρ))   = mixed-absurd θ x y ¬θxy a b (λ e → ¬ρ (sym₂ e)) θr
      final (inj₂ b , inj₁ a , (θr , ¬ρ))   = mixed-absurd θ x y ¬θxy a b ¬ρ (θsym θr)
      final (inj₂ b , inj₂ b' , (θr , ¬ρ))  = pure ¬ρ
        where
        -- Both endpoints upper: peel off basepoint-touching subcases, then
        -- collapse twice through a*.
        pure : ¬ (b ≈₂ b') → ⊥
        pure ¬bb' with 𝑭₂ ._≟_ b b* | 𝑭₂ ._≟_ b' b*
        ... | yes pb  | yes pb'  =  ¬bb' (trans₂ pb (sym₂ pb'))
        ... | yes pb  | no ¬pb'  =  mixed-absurd θ x y ¬θxy a* b' ¬pb'
                                    (ConRel-resp θ (refl₁ , pb) (refl₁ , refl₂) θr)
        ... | no ¬pb  | yes pb'  =  mixed-absurd θ x y ¬θxy a* b ¬pb
                                    (θsym (ConRel-resp θ (refl₁ , refl₂) (refl₁ , pb') θr))
        ... | no ¬pb  | no ¬pb'  =  ¬θxy (θtrans θx-a* θa*-y)
          where
          θx-a* : ConRel θ (inj₁ x) (inj₁ a*)
          θx-a* = ConRel-resp θ
                    (≈ᵍ-inj₁ (h-at b x ¬pb))
                    (≈ᵍ-inj₁ (h-away b x b' (λ e → ¬bb' (sym₂ e))))
                    (is-compatible θcon (inj₂ (inj₂ (idx₂ b , idx₁ x))) (λ _ → θr))

          θa*-y : ConRel θ (inj₁ a*) (inj₁ y)
          θa*-y = ConRel-resp θ
                    (≈ᵍ-inj₁ (h-away b' y b ¬bb'))
                    (≈ᵍ-inj₁ (h-at b' y ¬pb'))
                    (is-compatible θcon (inj₂ (inj₂ (idx₂ b' , idx₁ y))) (λ _ → θr))

  -- The dichotomy: every decidable congruence of 𝑪 is comparable to αᵈ.
  compare : (θ : DecCon 𝑪 0ℓ) → θ ⊆ᵈ αᵈ ⊎ αᵈ ⊆ᵈ θ
  compare θ with ⊆ᵈ-dec 𝑪-FiniteAlgebra θ αᵈ
  ... | yes s = inj₁ s
  ... | no ¬s with ⊆ᵈ-dec 𝑪-FiniteAlgebra αᵈ θ
  ...   | yes s' = inj₂ s'
  ...   | no ¬s' = ⊥-elim (incomparable-absurd θ ¬s ¬s')
```

#### The two splittings

A congruence below the boundary is its lower extension; one above it is its
upper extension.  These are the constructive readings of the manuscript's
"congruences comparable to `α` are determined on one side".

```agda
  lower-split : (θ : DecCon 𝑪 0ℓ) → θ ⊆ᵈ αᵈ → θ ≑ᵈ lowerExt (restrictA θ)
  lower-split θ θ⊆α = fwd , bwd
    where
    θcon = proj₂ (proj₁ θ)

    fwd : θ ⊆ᵈ lowerExt (restrictA θ)
    fwd {inj₁ _} {inj₁ _} p = p , θ⊆α p
    fwd {inj₁ _} {inj₂ _} p = ConRel-resp θ (refl₁ , refl₂) (refl₁ , sym₂ (θ⊆α p)) p , θ⊆α p
    fwd {inj₂ _} {inj₁ _} p = ConRel-resp θ (refl₁ , θ⊆α p) (refl₁ , refl₂) p , θ⊆α p
    fwd {inj₂ _} {inj₂ _} p = reflexive θcon (≈ᵍ-inj₁ refl₁) , θ⊆α p

    bwd : lowerExt (restrictA θ) ⊆ᵈ θ
    bwd {inj₁ _} {inj₁ _} (l , r) = l
    bwd {inj₁ _} {inj₂ _} (l , r) = ConRel-resp θ  (refl₁ , refl₂) (refl₁ , r) l
    bwd {inj₂ _} {inj₁ _} (l , r) = ConRel-resp θ (refl₁ , sym₂ r) (refl₁ , refl₂) l
    bwd {inj₂ _} {inj₂ _} (l , r) = reflexive θcon (refl₁ , r)

  upper-split : (θ : DecCon 𝑪 0ℓ) → αᵈ ⊆ᵈ θ → θ ≑ᵈ upperExt (restrictB θ)
  upper-split θ@((_ , θcon) , θdec) α⊆θ = fwd , bwd
    where
    θsym    = IsEquivalence.sym (is-equivalence θcon)
    θtrans  = IsEquivalence.trans (is-equivalence θcon)

    -- Every element is θ-related to the upper image of its right retraction:
    -- upper elements on the nose, lower ones through the boundary.
    bridge : ∀ z → ConRel θ z (inj₂ (retractʳ z))
    bridge (inj₁ a) = α⊆θ refl₂
    bridge (inj₂ b) = reflexive θcon (refl₁ , refl₂)

    fwd : θ ⊆ᵈ upperExt (restrictB θ)
    fwd {x} {y} p = θtrans (θsym (bridge x)) (θtrans p (bridge y))

    bwd : upperExt (restrictB θ) ⊆ᵈ θ
    bwd {x} {y} p = θtrans (bridge x) (θtrans p (θsym (bridge y)))
```

#### The order isomorphism onto the ordinal sum

Fix the target lattices, the extremum data the sum glues at, and the two
isomorphisms.  The map sends a congruence below the boundary into the lower
summand and one above it into the upper summand; the boundary itself lands on
the glue, and the coherence of that overlap is exactly the uniqueness of
extrema (`top-unique`{.AgdaFunction} / `bot-unique`{.AgdaFunction}) applied to
the images of the total and diagonal congruences.

```agda
  module _ {𝓛₁ 𝓛₂ : Lattice} (t : TopOf 𝓛₁) (b : BotOf 𝓛₂)
           (iso₁ : ConIsoᵈ 𝑨 𝓛₁) (iso₂ : ConIsoᵈ 𝑩 𝓛₂)
    where
    𝑳₁ 𝑳₂ : Algebra {𝑆 = Sig-Lattice} 0ℓ 0ℓ
    𝑳₁ = 𝓛₁ .proj₁
    𝑳₂ = 𝓛₂ .proj₁

    private
      ⊤₁ : 𝕌[ 𝑳₁ ]
      ⊤₁ = proj₁ t

      ⊥₂ : 𝕌[ 𝑳₂ ]
      ⊥₂ = proj₁ b

    open OrderIso iso₁
      renaming ( to to to₁ ; from to from₁ ; to-mono to to-mono₁
               ; from-mono to from-mono₁ ; to∘from to to∘from₁ ; from∘to to from∘to₁ )
    open OrderIso iso₂
      renaming ( to to to₂ ; from to from₂ ; to-mono to to-mono₂
               ; from-mono to from-mono₂ ; to∘from to to∘from₂ ; from∘to to from∘to₂ )
    open ConIsoᵈ-Consequences {𝑆 = 𝑆₁} {𝑨 = 𝑨} {𝑳 = 𝓛₁} iso₁ using ()
      renaming ( to-cong≑ to to-cong≑₁ ; from-cong≈ to from-cong≈₁ ; to-𝟙-top to to-𝟙-top₁ )
    open ConIsoᵈ-Consequences {𝑆 = 𝑆₂} {𝑨 = 𝑩} {𝑳 = 𝓛₂} iso₂ using ()
      renaming ( to-cong≑ to to-cong≑₂ ; from-cong≈ to from-cong≈₂ ; to-𝟘-bot to to-𝟘-bot₂ )
    open Setoid 𝔻[ 𝑳₁ ] using ()
      renaming ( _≈_ to _≈ᴸ¹_ ; refl to reflᴸ¹ ; sym to symᴸ¹ ; trans to transᴸ¹ )
    open Setoid 𝔻[ 𝑳₂ ] using ()
      renaming ( _≈_ to _≈ᴸ²_ ; refl to reflᴸ² ; sym to symᴸ² ; trans to transᴸ² )
    open LatticeOrdinalSum 𝓛₁ t 𝓛₂ b using
      ( ≤ᵒ-inj₁ ; ≤ᵒ-inj₁-elim ; ≤ᵒ-inj₂ ; ≤ᵒ-inj₂-elim ; ≤ᵒ-up ; ≤ᵒ-down ; ≤ᵒ-down-elim )

    private
      -- Boundary coherence: the extreme images agree with the chosen extrema.
      to₁𝟙≈⊤ : to₁ (𝟙ᵈ {ℓ = 0ℓ}) ≈ᴸ¹ ⊤₁
      to₁𝟙≈⊤ = Lattice-Order.top-unique 𝓛₁
                 {t = to₁ (𝟙ᵈ {ℓ = 0ℓ})} {t' = ⊤₁} to-𝟙-top₁ (proj₂ t)

      to₂𝟘≈⊥ : to₂ (𝟘ᵈ (𝑭₂ ._≟_)) ≈ᴸ² ⊥₂
      to₂𝟘≈⊥ =  Lattice-Order.bot-unique 𝓛₂
                {b = to₂ (𝟘ᵈ (𝑭₂ ._≟_))} {b' = ⊥₂} (to-𝟘-bot₂ (𝑭₂ ._≟_)) (proj₂ b)

      -- The images of a boundary-equal congruence sit at the glue.
      atGlue-⊤ : (θ : DecCon 𝑪 0ℓ) → θ ≑ᵈ αᵈ → to₁ (restrictA θ) ≈ᴸ¹ ⊤₁
      atGlue-⊤ θ (s₁ , s₂) =
        transᴸ¹  (to-cong≑₁ ((λ _ → lift tt) , (λ {a} {a'} _ → s₂ {inj₁ a} {inj₁ a'} refl₂)))
                 to₁𝟙≈⊤

      atGlue-⊥ : (θ : DecCon 𝑪 0ℓ) → θ ≑ᵈ αᵈ → to₂ (restrictB θ) ≈ᴸ² ⊥₂
      atGlue-⊥ θ (s₁ , s₂) =
        transᴸ² (to-cong≑₂ ((λ p → lift (s₁ p)) , (λ q → s₂ (lower q)))) to₂𝟘≈⊥
```

The map, its inverse, and the four obligations.  The map decides the side via
`compare`{.AgdaFunction}; each obligation re-runs that decision and reasons per
branch, with the mixed branches all funneling through the glue coherences.

```agda
    toᵒ : DecCon 𝑪 0ℓ → 𝕌[ 𝑳₁ ] ⊎ 𝕌[ 𝑳₂ ]
    toᵒ θ with compare θ
    ... | inj₁ _ = inj₁ (to₁ (restrictA θ))
    ... | inj₂ _ = inj₂ (to₂ (restrictB θ))

    fromᵒ : 𝕌[ 𝑳₁ ] ⊎ 𝕌[ 𝑳₂ ] → DecCon 𝑪 0ℓ
    fromᵒ (inj₁ u) = lowerExt (from₁ u)
    fromᵒ (inj₂ v) = upperExt (from₂ v)

    to-monoᵒ : {θ θ' : DecCon 𝑪 0ℓ} → θ ⊆ᵈ θ'
      → Lattice-Order._≤_ (ordinalSum 𝓛₁ t 𝓛₂ b) (toᵒ θ) (toᵒ θ')
    to-monoᵒ {θ} {θ'} s with compare θ | compare θ'
    ... | inj₁ _   | inj₁ _    = ≤ᵒ-inj₁ (to-mono₁ (restrictA-mono {θ} {θ'} s))
    ... | inj₁ _   | inj₂ _    = ≤ᵒ-up {to₁ (restrictA θ)} {to₂ (restrictB θ')}
    ... | inj₂ _   | inj₂ _    = ≤ᵒ-inj₂ (to-mono₂ (restrictB-mono {θ} {θ'} s))
    ... | inj₂ α⊆θ | inj₁ θ'⊆α = ≤ᵒ-down (atGlue-⊤ θ' (θ'⊆α , s ∘ α⊆θ)) (atGlue-⊥ θ (θ'⊆α ∘ s , α⊆θ))
    -- θ ⊆ θ' pins both to the boundary; both images land on the glue.

    from-monoᵒ : {u v : 𝕌[ 𝑳₁ ] ⊎ 𝕌[ 𝑳₂ ]}
      → Lattice-Order._≤_ (ordinalSum 𝓛₁ t 𝓛₂ b) u v → fromᵒ u ⊆ᵈ fromᵒ v
    from-monoᵒ {inj₁ _} {inj₂ v} le (l , r) = reflexive (proj₂ (proj₁ (from₂ v))) r

    from-monoᵒ {inj₁ u} {inj₁ v} le {x} {y} p =
      lowerExt-mono {from₁ u} {from₁ v} (from-mono₁ (≤ᵒ-inj₁-elim le)) {x} {y} p

    from-monoᵒ {inj₂ u} {inj₂ v} le {x} {y} p =
      upperExt-mono {from₂ u} {from₂ v} (from-mono₂ (≤ᵒ-inj₂-elim le)) {x} {y} p

    from-monoᵒ {inj₂ u} {inj₁ v} le {x} {y} p = down {x} {y} p
      where
      -- u at bottom, v at top: both preimages are extreme, and the extreme extensions nest.
      u≈⊥ : u ≈ᴸ² ⊥₂
      u≈⊥ = proj₂ (≤ᵒ-down-elim le)
      v≈⊤ : v ≈ᴸ¹ ⊤₁
      v≈⊤ = proj₁ (≤ᵒ-down-elim le)

      open FiniteAlgebra 𝑭₂ using () renaming ( _≟_ to _≟₂_ )

      from₂u≑𝟘 : from₂ u ≑ᵈ 𝟘ᵈ _≟₂_
      from₂u≑𝟘 = (proj₁ e₂) ∘ (proj₁ e₁) , (proj₂ e₁) ∘ (proj₂ e₂)
        where
        e₁ : from₂ u ≑ᵈ from₂ (to₂ (𝟘ᵈ _≟₂_))
        e₁ = from-cong≈₂ (transᴸ² u≈⊥ (symᴸ² to₂𝟘≈⊥))
        e₂ : from₂ (to₂ (𝟘ᵈ _≟₂_)) ≑ᵈ 𝟘ᵈ _≟₂_
        e₂ = from∘to₂ (𝟘ᵈ _≟₂_)

      from₁v≑𝟙 : from₁ v ≑ᵈ 𝟙ᵈ
      from₁v≑𝟙 = proj₁ e₂ ∘ proj₁ e₁ , proj₂ e₁ ∘ proj₂ e₂
        where
        e₁ : from₁ v ≑ᵈ from₁ (to₁ 𝟙ᵈ)
        e₁ = from-cong≈₁ (transᴸ¹ v≈⊤ (symᴸ¹ to₁𝟙≈⊤))
        e₂ : from₁ (to₁ 𝟙ᵈ) ≑ᵈ 𝟙ᵈ
        e₂ = from∘to₁ 𝟙ᵈ

      down : upperExt (from₂ u) ⊆ᵈ lowerExt (from₁ v)
      down p = proj₂ from₁v≑𝟙 (lift tt) , lower (proj₁ from₂u≑𝟘 p)


    to∘fromᵒ : ∀ u → Setoid._≈_ 𝔻[ proj₁ (ordinalSum 𝓛₁ t 𝓛₂ b) ] (toᵒ (fromᵒ u)) u
    to∘fromᵒ (inj₁ u) with compare (lowerExt (from₁ u))
    ... | inj₁ _ = transᴸ¹ (to-cong≑₁ (restrictA-lowerExt (from₁ u))) (to∘from₁ u) , reflᴸ²
    ... | inj₂ α⊆ = symᴸ¹ u≈⊤ , atGlue-⊥ (lowerExt (from₁ u)) ext≑α
      where
      -- the extension is squeezed onto the boundary, so u is the top
      ext≑α : lowerExt (from₁ u) ≑ᵈ αᵈ
      ext≑α = (λ {x y} p → lowerExt-⊆-α (from₁ u) {x}{y} p) , λ {x y} p → α⊆ {x}{y} p

      from₁u≑𝟙 : from₁ u ≑ᵈ 𝟙ᵈ {ℓ = 0ℓ}
      from₁u≑𝟙 = (λ _ → lift tt) , (λ {a} {a'} _ → proj₁ (α⊆ {inj₁ a} {inj₁ a'} refl₂))

      u≈⊤ : u ≈ᴸ¹ ⊤₁
      u≈⊤ = transᴸ¹ (symᴸ¹ (to∘from₁ u)) (transᴸ¹ (to-cong≑₁ from₁u≑𝟙) to₁𝟙≈⊤)
    to∘fromᵒ (inj₂ v) with compare (upperExt (from₂ v))
    ... | inj₂ _ = reflᴸ¹ , transᴸ² (to-cong≑₂ (restrictB-upperExt (from₂ v))) (to∘from₂ v)
    ... | inj₁ θ⊆α = atGlue-⊤ (upperExt (from₂ v)) ext≑α , symᴸ² v≈⊥
      where
      ext≑α : upperExt (from₂ v) ≑ᵈ αᵈ
      ext≑α = (λ {x y} p → θ⊆α {x}{y} p) , λ {x y} p → α-⊆-upperExt (from₂ v) {x}{y} p

      from₂v≑𝟘 : from₂ v ≑ᵈ 𝟘ᵈ (𝑭₂ ._≟_)
      from₂v≑𝟘 = (λ {x y} p → lift (θ⊆α {inj₂ x} {inj₂ y} p))
               , (λ q → reflexive (proj₂ (proj₁ (from₂ v))) (lower q))

      v≈⊥ : v ≈ᴸ² ⊥₂
      v≈⊥ = transᴸ² (symᴸ² (to∘from₂ v)) (transᴸ² (to-cong≑₂ from₂v≑𝟘) to₂𝟘≈⊥)

    from∘toᵒ : ∀ θ → fromᵒ (toᵒ θ) ≑ᵈ θ
    from∘toᵒ θ with compare θ
    ... | inj₁ θ⊆α =
      (λ {x} {y} p → proj₂ (lower-split θ θ⊆α) {x} {y} (proj₁ ext {x} {y} p))
      , (λ {x} {y} q → proj₂ ext {x} {y} (proj₁ (lower-split θ θ⊆α) {x} {y} q))
      where
      ext = lowerExt-cong≑ {from₁ (to₁ (restrictA θ))} {restrictA θ} (from∘to₁ (restrictA θ))
    ... | inj₂ α⊆θ =
      (λ {x} {y} p → proj₂ (upper-split θ α⊆θ) {x} {y} (proj₁ ext {x} {y} p))
      , (λ {x} {y} q → proj₂ ext {x} {y} (proj₁ (upper-split θ α⊆θ) {x} {y} q))
      where
      ext = upperExt-cong≑ {from₂ (to₂ (restrictB θ))} {restrictB θ} (from∘to₂ (restrictB θ))

    𝑪-ConIsoᵈ : ConIsoᵈ 𝑪 (ordinalSum 𝓛₁ t 𝓛₂ b)
    𝑪-ConIsoᵈ = record
      { to         = toᵒ
      ; from       = fromᵒ
      ; to-mono    = λ {θ} {θ'} → to-monoᵒ {θ} {θ'}
      ; from-mono  = λ {u} {v} → from-monoᵒ {u} {v}
      ; to∘from    = to∘fromᵒ
      ; from∘to    = from∘toᵒ
      }
```

**The closure theorem**.

Normalize both witnesses to inhabited carriers, instantiate the construction,
and package the result.

```agda
ordinalSum-Representableᵈ : {𝓛₁ 𝓛₂ : Lattice} (t : TopOf 𝓛₁) (b : BotOf 𝓛₂)
  → Representableᵈ 𝓛₁ → Representableᵈ 𝓛₂ → Representableᵈ (ordinalSum 𝓛₁ t 𝓛₂ b)
ordinalSum-Representableᵈ {𝓛₁} {𝓛₂} t b r₁ r₂ =
  assemble (inhabited-witness r₁) (inhabited-witness r₂)
  where
  open Representableᵈ

  assemble : Σ[ r ∈ Representableᵈ 𝓛₁ ] 𝕌[ r .algᵈ ]
           → Σ[ r ∈ Representableᵈ 𝓛₂ ] 𝕌[ r .algᵈ ]
           → Representableᵈ (ordinalSum 𝓛₁ t 𝓛₂ b)
  assemble (r₁' , a*) (r₂' , b*) = record
    { sigᵈ      = W.𝑆ₒ
    ; algᵈ      = W.𝑪
    ; finiteᵈ   = W.𝑪-FiniteAlgebra
    ; finsigᵈ   = W.𝑆ₒ-FiniteSignature
    ; con-isoᵈ  = W.𝑪-ConIsoᵈ {𝓛₁ = 𝓛₁} {𝓛₂ = 𝓛₂} t b (r₁' .con-isoᵈ) (r₂' .con-isoᵈ)
    }
    where
    module W = OrdinalSumWitness
      (r₁' .algᵈ) (r₁' .finiteᵈ) (r₁' .finsigᵈ) a*
      (r₂' .algᵈ) (r₂' .finiteᵈ) (r₂' .finsigᵈ) b*
```

--------------------------------------

[^1]: McKenzie 1984; Snow 2000; see
      [`docs/papers/fin-lat-rep/SmallLatticeReps.tex`](docs/papers/fin-lat-rep/SmallLatticeReps.tex),
      § Ordinal Sums, whose `m + n − 1`-element construction this module follows.

[^2]: The isolated-equality locus for the Cubical port lives in `GlueSetoid`{.AgdaModule}.
