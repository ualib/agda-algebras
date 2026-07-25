---
layout: default
file: "src/FLRP/Closure/Product.lagda.md"
title: "FLRP.Closure.Product module (The Agda Universal Algebra Library)"
date: "2026-07-24"
author: "the agda-algebras development team"
---

### Product closure of decidable representability

This is the [FLRP.Closure.Product][] module of the [Agda Universal Algebra Library][].

The class of representable lattices is closed under finite direct products.[^1]
This module formalizes the binary case at Layer D of the two-layer
discipline ([ADR-008][]): given decidable representations of `𝑳₁`{.AgdaBound} and
`𝑳₂`{.AgdaBound}, it constructs a finite finitary algebra whose
decidable-congruence poset is order-isomorphic to the product lattice
`𝑳₁ ×ˡ 𝑳₂`{.AgdaFunction} of [Classical.Structures.Lattice.Product][], yielding

    product-Representableᵈ : Representableᵈ 𝑳₁ → Representableᵈ 𝑳₂
                           → Representableᵈ (𝑳₁ ×ˡ 𝑳₂)

**The witness algebra**.

Given representing algebras `𝑨` and `𝑩` with chosen
basepoints `a*` and `b*`, the composite `𝑪` lives on the product setoid `A × B`
over the signature

    𝑆₁  ⊎  𝑆₂  ⊎  Fin (card 𝑨)  ⊎  Fin (card 𝑩)

interpreted as follows: a symbol of `𝑆₁` acts through the first coordinates with
the second pinned to `b*` (dually for `𝑆₂`), and the two `Fin`-indexed families
are the unary **coordinate setters** `(a , b) ↦ (enum i , b)` and
`(a , b) ↦ (a , enum j)` that overwrite one coordinate with an enumerated
element while carrying the other along.

**Why the congruences split**.

The setters force every congruence `θ` of `𝑪` to be a product: writing
`θˡ a a' := θ (a , b*) (a' , b*)` and symmetrically `θʳ`, setting the second
coordinate shows any `θ`-related pair is `θˡ`-related in the first coordinate (and
dually), while conversely a common overwrite lets `θˡ`-relatedness and
`θʳ`-relatedness be chained through the intermediate point `(a' , b)` — so `θ` is
exactly the conjunction `θˡ × θʳ` (`restrict-pair-⊆`{.AgdaFunction} /
`restrict-pair-⊇`{.AgdaFunction} below).

This is the constructive heart of the closure proof; everything else is the transport
of that splitting through the two given isomorphisms, componentwise.

Both coordinatewise restrictions and the pairing preserve decidability, so the
whole argument stays at Layer D with no classical assumption.  (At Layer S the
same splitting goes through verbatim, but its consumers would be the WLEM-hard
`Representable`{.AgdaRecord} witnesses of the no-go theorem, so the library states
product closure at Layer D only.)

Basepoints exist because representing algebras may be *normalized to inhabited
carriers*: `inhabited-witness`{.AgdaFunction} of [FLRP.Representable][] replaces
an empty-carrier witness (whose lattice is then trivial) by the one-element
algebra.  The closure theorem therefore has no side conditions.

This is problem-specific formal content; the lattice-level product it targets
lives in the `Classical/` tree.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Closure.Product where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Fin.Base                          using  ( Fin ; splitAt ; join
                                                          ; combine ; remQuot )
open import Data.Fin.Patterns                      using  ( 0F )
open import Data.Fin.Properties                    using  ( splitAt-join
                                                          ; remQuot-combine )
open import Data.Nat.Base                          using  ( _+_ ; _*_ ; ℕ)
open import Data.Product                           using  ( _,_ ; _×_ ; proj₁ ; proj₂
                                                          ; Σ-syntax )
open import Data.Sum.Base                          using  ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function                               using  ( _∘_ )
open import Function.Construct.Identity            using  ( ↔-id )
open import Level                                  using  ( 0ℓ )
open import Relation.Binary                        using  ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; cong ; trans )
open import Relation.Nullary                       using  ( Dec )
open import Relation.Nullary.Decidable             using  ( _×-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Small.Structures.Lattice    using  ( Lattice )
open import Classical.Structures.Interpret        using  ( interp-cong )
open import Classical.Structures.Lattice.Product  using  ( module LatticeProduct ; _×ˡ_ )
open import FLRP.Problem                          using  ( OrderIso )
open import FLRP.Representable                    using  ( Representableᵈ ; ConIsoᵈ
                                                         ; _⊆ᵈ_ ; _≑ᵈ_ ; ConRel-resp
                                                         ; module ConIsoᵈ-Consequences
                                                         ; inhabited-witness )
open import Overture                              using  ( Signature
                                                         ; OperationSymbolsOf ; ArityOf )
open import Overture.Operations                   using  ( Op )
open import Setoid.Algebras.Basic                 using  ( Algebra ; 𝔻[_] ; 𝕌[_] ; _^_
                                                         ; mkAlgebra )
open import Setoid.Algebras.Finite                using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic              using  ( mkcon ; is-equivalence ; _∣≈_
                                                         ; reflexive ; is-compatible )
open import Setoid.Congruences.Finite.Basic       using  ( DecCon ; ConRel )
open import Setoid.Signatures.Finite              using  ( FiniteSignature )

open FiniteAlgebra
open FiniteSignature
```
-->

#### The composite witness algebra

`ProductWitness`{.AgdaModule} packages the construction for a fixed pair of
finite finitary algebras with chosen basepoints.  Everything is at level `0ℓ`,
matching `Representableᵈ`{.AgdaRecord}.

```agda
module ProductWitness
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

**The signature**.

The two component signatures sit side-by-side with the two setter families.
Setters are unary; component symbols keep their arities.

```agda
  OpSymbols : Type 0ℓ
  OpSymbols = OperationSymbolsOf 𝑆₁ ⊎ (OperationSymbolsOf 𝑆₂ ⊎ (Fin m ⊎ Fin n))

  arity : OpSymbols → Type 0ℓ
  arity (inj₁ f)          = ArityOf 𝑆₁ f
  arity (inj₂ (inj₁ g))   = ArityOf 𝑆₂ g
  arity (inj₂ (inj₂ _))   = Fin 1

  𝑆ₓ : Signature 0ℓ 0ℓ
  𝑆ₓ = OpSymbols , arity
```

**The carrier**.

The product setoid is accompanied by the pointwise pair equivalence.[^2]

```agda
  A×B : Setoid 0ℓ 0ℓ
  A×B = record
    { Carrier        = 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]
    ; _≈_            = λ p q → (proj₁ p ≈₁ proj₁ q) × (proj₂ p ≈₂ proj₂ q)
    ; isEquivalence  = record
        { refl   = refl₁ , refl₂
        ; sym    = λ e → sym₁ (proj₁ e) , sym₂ (proj₂ e)
        ; trans  = λ d e → trans₁ (proj₁ d) (proj₁ e) , trans₂ (proj₂ d) (proj₂ e)
        }
    }

  open Setoid A×B using ()
    renaming ( _≈_ to _≈ₓ_ ; trans to transₓ ; reflexive to ≡→≈ₓ )
```

**The algebra**.

Component symbols act through their coordinate with the other pinned to the
basepoint; setters overwrite their coordinate with an enumerated element.

```agda
  𝑪 : Algebra {𝑆 = 𝑆ₓ} 0ℓ 0ℓ
  𝑪 = mkAlgebra A×B interp interp-congruence
    where
    interp : (o : OpSymbols) → Op (arity o) (𝕌[ 𝑨 ] × 𝕌[ 𝑩 ])
    interp (inj₁ f)               args = (f ^ 𝑨) (proj₁ ∘ args) , b*
    interp (inj₂ (inj₁ g))        args = a* , (g ^ 𝑩) (proj₂ ∘ args)
    interp (inj₂ (inj₂ (inj₁ i))) args = enum₁ i , proj₂ (args 0F)
    interp (inj₂ (inj₂ (inj₂ j))) args = proj₁ (args 0F) , enum₂ j

    interp-congruence : ∀ o {u v : arity o → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]}
      → (∀ i → u i ≈ₓ v i) → interp o u ≈ₓ interp o v
    interp-congruence (inj₁ f)               e = interp-cong 𝑨 f (proj₁ ∘ e) , refl₂
    interp-congruence (inj₂ (inj₁ g))        e = refl₁ , interp-cong 𝑩 g (proj₂ ∘ e)
    interp-congruence (inj₂ (inj₂ (inj₁ i))) e = refl₁ , proj₂ (e 0F)
    interp-congruence (inj₂ (inj₂ (inj₂ j))) e = proj₁ (e 0F) , refl₂
```

#### Finiteness of the composite

The carrier is enumerated by `Fin (m * n)` through `combine`/`remQuot`, with
decidable equality componentwise.

```agda
  private
    enumC : Fin (m * n) → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]
    enumC k = enum₁ (proj₁ (remQuot {m} n k)) , enum₂ (proj₂ (remQuot {m} n k))

    -- Enumerating at a combined index recovers the component enumerations.
    enumC-combine : (i : Fin m) (j : Fin n) → enumC (combine i j) ≈ₓ (enum₁ i , enum₂ j)
    enumC-combine i j =
      ≡→≈ₓ (cong (λ z → enum₁ (proj₁ z) , enum₂ (proj₂ z)) (remQuot-combine i j))

  𝑪-FiniteAlgebra : FiniteAlgebra 𝑪
  𝑪-FiniteAlgebra ._≟_ p q = 𝑭₁ ._≟_ (proj₁ p) (proj₁ q) ×-dec 𝑭₂ ._≟_ (proj₂ p) (proj₂ q)
  𝑪-FiniteAlgebra .card = m * n
  𝑪-FiniteAlgebra .enum = enumC
  𝑪-FiniteAlgebra .enum-sur = sur
    where
    sur : ∀ p → Σ[ k ∈ Fin (m * n) ] enumC k ≈ₓ p
    sur p with 𝑭₁ .enum-sur (proj₁ p) | 𝑭₂ .enum-sur (proj₂ p)
    ... | i , pi | j , pj = combine i j , transₓ (enumC-combine i j) (pi , pj)
```

The signature is finite finitary: symbols are enumerated by
`Fin (c₁ + (c₂ + (m + n)))` through a three-layer `splitAt` decoder, and the new
setter symbols are unary.

```agda
  private
    c₁ c₂ : ℕ
    c₁ = S₁ .opCard
    c₂ = S₂ .opCard

    -- Decode a flat index into a symbol, one ⊎-layer of splitAt at a time.
    decode₂ : Fin (c₂ + (m + n)) → OperationSymbolsOf 𝑆₂ ⊎ (Fin m ⊎ Fin n)
    decode₂ = [ inj₁ ∘ S₂ .opEnum , inj₂ ∘ splitAt m ]′ ∘ splitAt c₂

    decode : Fin (c₁ + (c₂ + (m + n))) → OpSymbols
    decode = [ inj₁ ∘ S₁ .opEnum , inj₂ ∘ decode₂ ]′ ∘ splitAt c₁

    -- One computation rule per ⊎-layer: decoding a joined index reduces to the branch.
    decode-join : (x : Fin c₁ ⊎ Fin (c₂ + (m + n)))
      → decode (join c₁ _ x) ≡ [ inj₁ ∘ S₁ .opEnum , inj₂ ∘ decode₂ ]′ x
    decode-join x = cong [ inj₁ ∘ S₁ .opEnum , inj₂ ∘ decode₂ ]′ (splitAt-join c₁ _ x)

    decode₂-join : (x : Fin c₂ ⊎ Fin (m + n))
      → decode₂ (join c₂ _ x) ≡ [ inj₁ ∘ S₂ .opEnum , inj₂ ∘ splitAt m ]′ x
    decode₂-join x = cong [ inj₁ ∘ S₂ .opEnum , inj₂ ∘ splitAt m ]′ (splitAt-join c₂ _ x)


    -- Encoding hits every symbol: chain the computation rules layer by layer.
    decode-sur : (o : OpSymbols) → Σ[ k ∈ Fin (c₁ + (c₂ + (m + n))) ] decode k ≡ o

    decode-sur (inj₁ f) with S₁ .opEnum-sur f
    ... | i , p = join c₁ _ (inj₁ i) , trans (decode-join (inj₁ i)) (cong inj₁ p)

    decode-sur (inj₂ (inj₁ g)) with S₂ .opEnum-sur g
    ... | j , p =  join c₁ _ (inj₂ (join c₂ _ (inj₁ j)))
                   , trans  (decode-join (inj₂ (join c₂ _ (inj₁ j))))
                            (trans  (cong inj₂ (decode₂-join (inj₁ j)))
                                    (cong (inj₂ ∘ inj₁) p))

    decode-sur (inj₂ (inj₂ (inj₁ i))) =
      join c₁ _ (inj₂ (join c₂ _ (inj₂ (join m n (inj₁ i)))))
      , trans  (decode-join (inj₂ (join c₂ _ (inj₂ (join m n (inj₁ i))))))
               (trans  (cong inj₂ (decode₂-join (inj₂ (join m n (inj₁ i)))))
                       (cong (inj₂ ∘ inj₂) (splitAt-join m n (inj₁ i))))

    decode-sur (inj₂ (inj₂ (inj₂ j))) =
      join c₁ _ (inj₂ (join c₂ _ (inj₂ (join m n (inj₂ j)))))
      , trans  (decode-join (inj₂ (join c₂ _ (inj₂ (join m n (inj₂ j))))))
               (trans  (cong inj₂ (decode₂-join (inj₂ (join m n (inj₂ j)))))
                       (cong (inj₂ ∘ inj₂) (splitAt-join m n (inj₂ j))))

  𝑆ₓ-FiniteSignature : FiniteSignature 𝑆ₓ
  𝑆ₓ-FiniteSignature .opCard      = c₁ + (c₂ + (m + n))
  𝑆ₓ-FiniteSignature .opEnum      = decode
  𝑆ₓ-FiniteSignature .opEnum-sur  = decode-sur
  𝑆ₓ-FiniteSignature .finitary (inj₁ f)         = S₁ .finitary f
  𝑆ₓ-FiniteSignature .finitary (inj₂ (inj₁ g))  = S₂ .finitary g
  𝑆ₓ-FiniteSignature .finitary (inj₂ (inj₂ _))  = 1 , ↔-id _
```

#### Restriction and pairing of congruences

A congruence of the composite restricts to each coordinate along the opposite
basepoint, and a pair of component congruences pairs into a composite one.

All three constructions preserve decidability.  Compatibility of a restriction with a
component symbol `f` is exactly compatibility of the original congruence with `inj₁ f`:
the composite interpretation pins the second coordinate to `b*`, which is precisely
the restriction's frame.

```agda
  -- Restrict to the first coordinate, along b*.
  restrictˡ : DecCon 𝑪 0ℓ → DecCon 𝑨 0ℓ
  restrictˡ d@((_ , θcon) , θdec) = (rel , mkcon rfl eqv cmp) , dec
    where
    rel : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type 0ℓ
    rel a a' = ConRel d (a , b*) (a' , b*)

    rfl : ∀ {x y} → x ≈₁ y → rel x y
    rfl e = reflexive θcon (e , refl₂)

    eqv : IsEquivalence rel
    eqv = record
      { refl   = IsEquivalence.refl (is-equivalence θcon)
      ; sym    = IsEquivalence.sym (is-equivalence θcon)
      ; trans  = IsEquivalence.trans (is-equivalence θcon)
      }

    cmp : 𝑨 ∣≈ rel
    cmp f uv = is-compatible θcon (inj₁ f) uv

    dec : ∀ x y → Dec (rel x y)
    dec x y = θdec (x , b*) (y , b*)

  -- Restrict to the second coordinate, along a*.
  restrictʳ : DecCon 𝑪 0ℓ → DecCon 𝑩 0ℓ
  restrictʳ d@((_ , θcon) , θdec) = (rel , mkcon rfl eqv cmp) , dec
    where
    rel : 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → Type 0ℓ
    rel b b' = ConRel d (a* , b) (a* , b')

    rfl : ∀ {x y} → x ≈₂ y → rel x y
    rfl e = reflexive θcon (refl₁ , e)

    eqv : IsEquivalence rel
    eqv = record
      { refl   = IsEquivalence.refl (is-equivalence θcon)
      ; sym    = IsEquivalence.sym (is-equivalence θcon)
      ; trans  = IsEquivalence.trans (is-equivalence θcon)
      }

    cmp : 𝑩 ∣≈ rel
    cmp g uv = is-compatible θcon (inj₂ (inj₁ g)) uv

    dec : ∀ x y → Dec (rel x y)
    dec x y = θdec (a* , x) (a* , y)

  -- Pair component congruences into a composite one (the product congruence).
  ⟨_,_⟩ᶜ : DecCon 𝑨 0ℓ → DecCon 𝑩 0ℓ → DecCon 𝑪 0ℓ
  ⟨ d₁@((_ , θcon₁) , θdec₁)  , d₂@((_ , θcon₂) , θdec₂) ⟩ᶜ =
    (rel , mkcon rfl eqv cmp) , dec
    where
    rel : 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → Type 0ℓ
    rel (p₁ , p₂) (q₁ , q₂) = ConRel d₁ p₁ q₁ × ConRel d₂ p₂ q₂

    rfl : ∀ {p q} → p ≈ₓ q → rel p q
    rfl (e₁ , e₂) = reflexive θcon₁ e₁ , reflexive θcon₂ e₂

    eqv : IsEquivalence rel
    eqv = record
      { refl   = IsEquivalence.refl (is-equivalence θcon₁)
               , IsEquivalence.refl (is-equivalence θcon₂)
      ; sym    = λ (p , q) → IsEquivalence.sym (is-equivalence θcon₁) p
                           , IsEquivalence.sym (is-equivalence θcon₂) q
      ; trans  = λ (p , q) (p' , q') → IsEquivalence.trans (is-equivalence θcon₁) p p'
                                     , IsEquivalence.trans (is-equivalence θcon₂) q q'
      }

    cmp : 𝑪 ∣≈ rel
    cmp (inj₁ f)               uv = is-compatible θcon₁ f (λ i → proj₁ (uv i))
                                  , reflexive θcon₂ refl₂
    cmp (inj₂ (inj₁ g))        uv = reflexive θcon₁ refl₁
                                  , is-compatible θcon₂ g (λ i → proj₂ (uv i))
    cmp (inj₂ (inj₂ (inj₁ i))) uv = reflexive θcon₁ refl₁ , proj₂ (uv 0F)
    cmp (inj₂ (inj₂ (inj₂ j))) uv = proj₁ (uv 0F) , reflexive θcon₂ refl₂

    dec : ∀ p q → Dec (rel p q)
    dec (p₁ , p₂) (q₁ , q₂) = θdec₁ p₁ q₁ ×-dec θdec₂ p₂ q₂
```

#### Every congruence of the composite splits

The two directions of the splitting `θ ≑ᵈ ⟨ θˡ , θʳ ⟩ᶜ`.  Both use the setters:
to land exactly on a basepoint (which need not be an enumerated element on the
nose) the setter overwrite is corrected up to `≈` by
`ConRel-resp`{.AgdaFunction}, using the surjectivity proof of the enumeration.

```agda
  -- One setter application, transported to the intended target coordinate value.
  private
    setʳ-onto : (d : DecCon 𝑪 0ℓ) (b : 𝕌[ 𝑩 ]) {p q : 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]}
      → ConRel d p q → ConRel d (proj₁ p , b) (proj₁ q , b)
    setʳ-onto d b pdq with 𝑭₂ .enum-sur b
    ... | j , pj =
      ConRel-resp d (refl₁ , pj) (refl₁ , pj)
        (is-compatible (proj₂ (proj₁ d)) (inj₂ (inj₂ (inj₂ j))) (λ _ → pdq))

    setˡ-onto : (d : DecCon 𝑪 0ℓ) (a : 𝕌[ 𝑨 ]) {p q : 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]}
      → ConRel d p q → ConRel d (a , proj₂ p) (a , proj₂ q)
    setˡ-onto d a pdq with 𝑭₁ .enum-sur a
    ... | i , pi =
      ConRel-resp d (pi , refl₂) (pi , refl₂)
        (is-compatible (proj₂ (proj₁ d)) (inj₂ (inj₂ (inj₁ i))) (λ _ → pdq))

  -- Related pairs restrict to related coordinates.
  restrict-pair-⊆ : (d : DecCon 𝑪 0ℓ) → d ⊆ᵈ ⟨ restrictˡ d , restrictʳ d ⟩ᶜ
  restrict-pair-⊆ d pdq = setʳ-onto d b* pdq , setˡ-onto d a* pdq

  -- Coordinatewise related pairs are related, chaining through a mixed point.
  restrict-pair-⊇ : (d : DecCon 𝑪 0ℓ) → ⟨ restrictˡ d , restrictʳ d ⟩ᶜ ⊆ᵈ d
  restrict-pair-⊇ d {p₁ , p₂} {q₁ , q₂} (r₁ , r₂) =
    IsEquivalence.trans (is-equivalence (proj₂ (proj₁ d)))
      (setʳ-onto d p₂ {p₁ , b*} {q₁ , b*} r₁) (setˡ-onto d q₁ {a* , p₂} {a* , q₂} r₂)
```

Restriction and pairing are monotone, and restricting a pair recovers its
components (up to `≑ᵈ`) — the four little lemmas the isomorphism's round trips
consume.

```agda
  restrictˡ-mono : {d e : DecCon 𝑪 0ℓ} → d ⊆ᵈ e → restrictˡ d ⊆ᵈ restrictˡ e
  restrictˡ-mono d⊆e p = d⊆e p

  restrictʳ-mono : {d e : DecCon 𝑪 0ℓ} → d ⊆ᵈ e → restrictʳ d ⊆ᵈ restrictʳ e
  restrictʳ-mono d⊆e p = d⊆e p

  pairᶜ-mono : {d₁ e₁ : DecCon 𝑨 0ℓ} {d₂ e₂ : DecCon 𝑩 0ℓ}
    → d₁ ⊆ᵈ e₁ → d₂ ⊆ᵈ e₂ → ⟨ d₁ , d₂ ⟩ᶜ ⊆ᵈ ⟨ e₁ , e₂ ⟩ᶜ
  pairᶜ-mono s₁ s₂ (r₁ , r₂) = s₁ r₁ , s₂ r₂

  restrictˡ-pair : (d₁ : DecCon 𝑨 0ℓ) (d₂ : DecCon 𝑩 0ℓ) → restrictˡ ⟨ d₁ , d₂ ⟩ᶜ ≑ᵈ d₁
  restrictˡ-pair _ ((_ , con₂) , _) = proj₁ , (λ r → r , reflexive con₂ refl₂)

  restrictʳ-pair : (d₁ : DecCon 𝑨 0ℓ) (d₂ : DecCon 𝑩 0ℓ) → restrictʳ ⟨ d₁ , d₂ ⟩ᶜ ≑ᵈ d₂
  restrictʳ-pair ((_ , con₁) , _) _ = proj₂ , (λ r → reflexive con₁ refl₁ , r)
```

#### The order isomorphism onto the product lattice

Composing the splitting with the two given isomorphisms, componentwise.  The
product lattice's order and equivalence are the componentwise ones
(definitionally — [Classical.Structures.Lattice.Product][]), so each obligation
splits into its two coordinates.

```agda
  module _ {𝑳₁ 𝑳₂ : Lattice} (iso₁ : ConIsoᵈ 𝑨 𝑳₁) (iso₂ : ConIsoᵈ 𝑩 𝑳₂) where
    open LatticeProduct 𝑳₁ 𝑳₂ using ( ≤ₓ-fst ; ≤ₓ-snd )
    open OrderIso iso₁ renaming  ( to        to to₁
                                 ; from      to from₁
                                 ; to-mono   to to-mono₁
                                 ; from-mono to from-mono₁
                                 ; to∘from   to to∘from₁
                                 ; from∘to   to from∘to₁ )

    open OrderIso iso₂ renaming  ( to        to to₂
                                 ; from      to from₂
                                 ; to-mono   to to-mono₂
                                 ; from-mono to from-mono₂
                                 ; to∘from   to to∘from₂
                                 ; from∘to   to from∘to₂ )

    open ConIsoᵈ-Consequences {𝑆 = 𝑆₁} {𝑨 = 𝑨} {𝑳 = 𝑳₁} iso₁ using ()
      renaming ( to-cong≑ to to-cong≑₁ )
    open ConIsoᵈ-Consequences {𝑆 = 𝑆₂} {𝑨 = 𝑩} {𝑳 = 𝑳₂} iso₂ using ()
      renaming ( to-cong≑ to to-cong≑₂ )

    open Setoid 𝔻[ proj₁ 𝑳₁ ] using () renaming ( trans to ≈transᴸ¹ )
    open Setoid 𝔻[ proj₁ 𝑳₂ ] using () renaming ( trans to ≈transᴸ² )

    𝑪-ConIsoᵈ : ConIsoᵈ 𝑪 (𝑳₁ ×ˡ 𝑳₂)
    𝑪-ConIsoᵈ = record
      { to         = λ d → to₁ (restrictˡ d) , to₂ (restrictʳ d)
      ; from       = λ uv → ⟨ from₁ (proj₁ uv) , from₂ (proj₂ uv) ⟩ᶜ
      ; to-mono    = λ {d} {e} d⊆e →  to-mono₁ (restrictˡ-mono {d} {e} d⊆e)
                                      , to-mono₂ (restrictʳ-mono {d} {e} d⊆e)
      ; from-mono  = λ {u} {v} u≤v →  pairᶜ-mono
                                      {d₁ = from₁ (proj₁ u)} {e₁ = from₁ (proj₁ v)}
                                      {d₂ = from₂ (proj₂ u)} {e₂ = from₂ (proj₂ v)}
                                      (from-mono₁ {proj₁ u} {proj₁ v} (≤ₓ-fst {u} {v} u≤v))
                                      (from-mono₂ {proj₂ u} {proj₂ v} (≤ₓ-snd {u} {v} u≤v))
      ; to∘from    = λ uv → ≈transᴸ¹  (to-cong≑₁ (restrictˡ-pair (from₁ (proj₁ uv)) (from₂ (proj₂ uv))))
                                      (to∘from₁ (proj₁ uv))
                            , ≈transᴸ²  (to-cong≑₂ (restrictʳ-pair (from₁ (proj₁ uv)) (from₂ (proj₂ uv))))
                                        (to∘from₂ (proj₂ uv))
      ; from∘to    = λ d →  ( λ (r₁ , r₂) → restrict-pair-⊇ d ( proj₁ (from∘to₁ (restrictˡ d)) r₁
                                                              , proj₁ (from∘to₂ (restrictʳ d)) r₂ ))
                            , λ pdq →  let s = restrict-pair-⊆ d pdq in
                                       proj₂ (from∘to₁ (restrictˡ d)) (proj₁ s)
                                       , proj₂ (from∘to₂ (restrictʳ d)) (proj₂ s)
      }
```

#### The closure theorem

Normalize both witnesses to inhabited carriers, instantiate the construction at
the resulting basepoints, and package the result.

```agda
product-Representableᵈ : {𝑳₁ 𝑳₂ : Lattice}
  → Representableᵈ 𝑳₁ → Representableᵈ 𝑳₂ → Representableᵈ (𝑳₁ ×ˡ 𝑳₂)
product-Representableᵈ {𝑳₁} {𝑳₂} r₁ r₂ =
  assemble (inhabited-witness r₁) (inhabited-witness r₂)
  where
  open Representableᵈ

  assemble : Σ[ r ∈ Representableᵈ 𝑳₁ ] 𝕌[ r .algᵈ ]
           → Σ[ r ∈ Representableᵈ 𝑳₂ ] 𝕌[ r .algᵈ ]
           → Representableᵈ (𝑳₁ ×ˡ 𝑳₂)
  assemble (r₁' , a*) (r₂' , b*) = record
    { sigᵈ      = P.𝑆ₓ
    ; algᵈ      = P.𝑪
    ; finiteᵈ   = P.𝑪-FiniteAlgebra
    ; finsigᵈ   = P.𝑆ₓ-FiniteSignature
    ; con-isoᵈ  = P.𝑪-ConIsoᵈ {𝑳₁ = 𝑳₁} {𝑳₂ = 𝑳₂} (r₁' .con-isoᵈ) (r₂' .con-isoᵈ)
    }
    where
    module P = ProductWitness
      (r₁' .algᵈ) (r₁' .finiteᵈ) (r₁' .finsigᵈ) a*
      (r₂' .algᵈ) (r₂' .finiteᵈ) (r₂' .finsigᵈ) b*
```

--------------------------------------

[^1]: Tůma 1986; see
      [`docs/papers/fin-lat-rep/SmallLatticeReps.tex`](docs/papers/fin-lat-rep/SmallLatticeReps.tex),
      § Closure properties.

[^2]: This is the isolated-equality locus for the proposed Cubical port.
