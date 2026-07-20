---
layout: default
file: "src/Setoid/Varieties/HSP.lagda.md"
title: "Setoid.Varieties.HSP module (Agda Universal Algebra Library)"
date: "2021-10-16"
author: "agda-algebras development team"
---

This is the [Setoid.Varieties.HSP][] module of the [Agda Universal Algebra Library][].  **This module is the canonical home of Birkhoff's HSP theorem in agda-algebras**, designated as such under [issue #259](https://github.com/ualib/agda-algebras/issues/259) (M2-4).  The theorem `Birkhoff` and its converse `Birkhoff-converse` defined below — joined to the identity-preservation lemma `V-id1` of [Setoid.Varieties.Preservation][] and the expansive-closure fact `V-expa` of [Setoid.Varieties.Closure][] — constitute the library's authoritative formalization of the variety theorem.  The proof is fully constructive (no function-extensionality postulate) and is stated against the setoid-typed `Algebra` of [Setoid.Algebras.Basic][], so the underlying equivalence can be mechanically substituted when the library ports to Cubical Agda (M5).  See [ADR-001](https://github.com/ualib/agda-algebras/blob/master/docs/adr/001-setoid-as-canonical.md) for the broader design rationale of the v3.0 Setoid-as-canonical migration.

Two other presentations of Birkhoff's theorem live in the source tree, and both reference this module as their canonical source.  [Examples.Demos.HSP][] is a single-file rendition extracted for the TYPES 2021 paper and retained as a self-contained teaching artifact; its theorem `Var⇒EqCl` plays the role of `Birkhoff` here.  [Legacy.Base.Varieties.FreeAlgebras][] holds the original bare-types proof, frozen as part of the v3.0 `Base → Legacy.Base` consolidation; new work does not land there.


#### The HSP Theorem

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.HSP where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ ; proj₁ ; proj₂ )
open import Function         using () renaming ( Func to _⟶_ )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )

-- -- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                           using  ( 𝓞 ; 𝓥 ; Signature ; 𝑆 )
open import Setoid.Algebras                    using  ( Algebra ; ov ; Lift-Alg ; ⨅ )
open import Setoid.Homomorphisms
open import Setoid.Relations                   using  ( fkerPred )
open import Setoid.Subalgebras                 using  ( _≤_ ; mon→≤ )
open import Setoid.Terms                       using  ( module Environment ; 𝑻
                                                      ; lift-hom ; free-lift
                                                      ; free-lift-interp )
open import Setoid.Varieties.Closure           using  ( S ; P ; S-idem ; V ; V′ ; V-≅-lc )
open import Setoid.Varieties.FreeAlgebras      using  ( module FreeHom
                                                      ; 𝔽-ModTh-epi-lift )
open import Setoid.Varieties.Preservation      using  ( S-id2 ; PS⊆SP )
open import Setoid.Varieties.SoundAndComplete  using  ( module FreeAlgebra ; _⊫_ ; ⊫-proof
                                                      ; _≈̇_ ; _⊢_▹_≈_ ; Mod ; Th )

open _⟶_          using () renaming ( to to _⟨$⟩_ )
open Setoid       using ( Carrier )
open Algebra      using ( Domain )
open Environment  using ( Env )
```
-->

```agda
module _
  {α ρᵃ ℓ : Level}
  (𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) (α ⊔ ρᵃ ⊔ ov {𝑆 = 𝑆} ℓ))
  {X : Type (α ⊔ ρᵃ ⊔ ℓ)}
  where

  private
    ι : Level
    ι = ov {𝑆 = 𝑆}(α ⊔ ρᵃ ⊔ ℓ)

  open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
  open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )
```

We want to pair each `(𝑨 , p)` (where p : 𝑨 ∈ S 𝒦) with an environment
`ρ : X → 𝕌[ 𝑨 ]` so that we can quantify over all algebras *and* all
assignments of values in the domain `𝕌[ 𝑨 ]` to variables in `X`.

```agda
  ℑ⁺ : Type ι
  ℑ⁺ = Σ[ 𝑨 ∈ (Algebra {𝑆 = 𝑆} α ρᵃ) ] (𝑨 ∈ S ℓ 𝒦) × (Carrier (Env 𝑨 X))

  𝔄⁺ : ℑ⁺ → Algebra {𝑆 = 𝑆} α ρᵃ
  𝔄⁺ i = (proj₁ i)

  ℭ : Algebra {𝑆 = 𝑆} ι ι
  ℭ = ⨅ 𝔄⁺
```

Next we define a useful type, `skEqual`, which we use to represent a term identity `p ≈ q` for any
given `i = (𝑨 , sA , ρ)` (where `𝑨` is an algebra, `sA : 𝑨 ∈ S 𝒦` is a proof that `𝑨` belongs
to `S 𝒦`, and `ρ` is a mapping from `X` to the domain of `𝑨`). Then we prove `AllEqual⊆ker𝔽` which
asserts that if the identity `p ≈ q` holds in all `𝑨 ∈ S 𝒦` (for all environments), then `p ≈ q`
holds in the relatively free algebra `𝔽[ X ]`; equivalently, the pair `(p , q)` belongs to the
kernel of the natural homomorphism from `𝑻 X` onto `𝔽[ X ]`. We will use this fact below to prove
that there is a monomorphism from `𝔽[ X ]` into `ℭ`, and thus `𝔽[ X ]` is a subalgebra of ℭ,
so belongs to `S (P 𝒦)`.

```agda
  skEqual : (i : ℑ⁺) → ∀{p q} → Type ρᵃ
  skEqual i {p}{q} = ⟦ p ⟧ ⟨$⟩ proj₂ (proj₂ i) ≈ ⟦ q ⟧ ⟨$⟩ proj₂ (proj₂ i)
    where
    open Setoid (Domain (𝔄⁺ i)) using ( _≈_ )
    open Environment (𝔄⁺ i) using ( ⟦_⟧ )

  AllEqual⊆ker𝔽 :  ∀ {p q}
   →               (∀ i → skEqual i {p}{q}) → (p , q) ∈ fkerPred (proj₁ (hom𝔽[ X ]))

  AllEqual⊆ker𝔽 {p} {q} x = Goal
    where
    open Algebra 𝔽[ X ]  using () renaming ( Domain to F )
    open Setoid F        using () renaming ( _≈_  to _≈F≈_ )
    S𝒦⊫pq : S{β = α}{ρᵃ} ℓ 𝒦 ⊫ (p ≈̇ q)
    S𝒦⊫pq .⊫-proof 𝑨 sA ρ = x (𝑨 , sA , ρ)
    Goal : p ≈F≈ q
    Goal = 𝒦⊫→ℰ⊢ (S-id2{ℓ = ℓ} S𝒦⊫pq)

  homℭ : hom (𝑻 X) ℭ
  homℭ = ⨅-hom-co 𝔄⁺ h
    where
    h : ∀ i → hom (𝑻 X) (𝔄⁺ i)
    h i = lift-hom (proj₂ (proj₂ i))

  open Algebra 𝔽[ X ]  using () renaming ( Domain to F )
  open Setoid F        using () renaming ( _≈_ to _≈F≈_ )


  ker𝔽⊆kerℭ : fkerPred (proj₁ (hom𝔽[ X ])) ⊆ fkerPred (proj₁ homℭ)
  ker𝔽⊆kerℭ {p , q} pKq (𝑨 , sA , ρ) = Goal
    where
    open Setoid (Domain 𝑨)  using ( _≈_ ; sym ; trans )
    open Environment 𝑨      using ( ⟦_⟧ )
    fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ρ ≈ free-lift ρ t
    fl t = free-lift-interp {𝑨 = 𝑨} ρ t
    subgoal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
    subgoal = ker𝔽⊆Equal{𝑨 = 𝑨}{sA} pKq ρ
    Goal : (free-lift{𝑨 = 𝑨} ρ p) ≈ (free-lift{𝑨 = 𝑨} ρ q)
    Goal = trans (sym (fl p)) (trans subgoal (fl q))

  hom𝔽ℭ : hom 𝔽[ X ] ℭ
  hom𝔽ℭ = (proj₁ (HomFactor homℭ hom𝔽[ X ] ker𝔽⊆kerℭ hom𝔽[ X ]-is-epic))

  open Environment ℭ

  kerℭ⊆ker𝔽 : ∀{p q} → (p , q) ∈ fkerPred (proj₁ homℭ) → (p , q) ∈ fkerPred (proj₁ (hom𝔽[ X ]))
  kerℭ⊆ker𝔽 {p}{q} pKq = E⊢pq
    where
    pqEqual : ∀ i → skEqual i {p}{q}
    pqEqual i = goal
      where
      open Environment (𝔄⁺ i)      using () renaming ( ⟦_⟧ to ⟦_⟧ᵢ )
      open Setoid (Domain (𝔄⁺ i))  using ( _≈_ ; sym ; trans )
      goal : ⟦ p ⟧ᵢ ⟨$⟩ proj₂ (proj₂ i) ≈ ⟦ q ⟧ᵢ ⟨$⟩ proj₂ (proj₂ i)
      goal = trans  (free-lift-interp{𝑨 = (proj₁ i)}(proj₂ (proj₂ i)) p)
                    (trans (pKq i)(sym (free-lift-interp{𝑨 = (proj₁ i)} (proj₂ (proj₂ i)) q)))
    E⊢pq : ℰ ⊢ X ▹ p ≈ q
    E⊢pq = AllEqual⊆ker𝔽 pqEqual


  mon𝔽ℭ : mon 𝔽[ X ] ℭ
  mon𝔽ℭ = (proj₁ hom𝔽ℭ) , isMon
    where
    open IsMon
    open IsHom
    isMon : IsMon 𝔽[ X ] ℭ (proj₁ hom𝔽ℭ)
    isHom isMon = (proj₂ hom𝔽ℭ)
    isInjective isMon {p} {q} φpq = kerℭ⊆ker𝔽 φpq
```

Now that we have proved the existence of a monomorphism from `𝔽[ X ]` to `ℭ` we are in a position
to prove that `𝔽[ X ]` is a subalgebra of ℭ, so belongs to `S (P 𝒦)`.  In fact, we will show
that `𝔽[ X ]` is a subalgebra of the *lift* of `ℭ`, denoted `ℓℭ`.

```agda
  𝔽≤ℭ : 𝔽[ X ] ≤ ℭ
  𝔽≤ℭ = mon→≤ mon𝔽ℭ

  SP𝔽 : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
  SP𝔽 = S-idem SSP𝔽
    where
    PSℭ : ℭ ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (S ℓ 𝒦)
    PSℭ = ℑ⁺ , (𝔄⁺ , ((λ i → proj₁ (proj₂ i)) , ≅-refl))

    SPℭ : ℭ ∈ S ι (P ℓ ι 𝒦)
    SPℭ = PS⊆SP {ℓ = ℓ} PSℭ

    SSP𝔽 : 𝔽[ X ] ∈ S ι (S ι (P ℓ ι 𝒦))
    SSP𝔽 = ℭ , (SPℭ , 𝔽≤ℭ)
```


#### Proof of the HSP theorem

Finally, we are in a position to prove Birkhoff's celebrated variety theorem.

The statement uses two `private` level abbreviations: `a = α ⊔ ρᵃ ⊔ ℓ` — the single
level at which the proof operates, the join of the generating class's carrier level
`α`, its relation level `ρᵃ`, and the variable level `ℓ` — and `ι = ov a`.  The
principal algebra `𝑨` is taken as an *implicit* argument pinned to `Algebra a a`.  It
is implicit because it is recovered from the model-membership argument
`𝑨 ∈ Mod (Th (V ℓ ι 𝒦))`, so the theorem reads as the textbook inclusion
`Mod (Th (V 𝒦)) ⊆ V 𝒦`; and it is pinned to level `(a , a)` so that its carrier
`∣A∣ : Type a` can serve as the generating set of the relatively free algebra
`𝔽[ ∣A∣ ]`.  (That free algebra and the lift `Lift-Alg 𝑨 ι ι` through which the proof
factors live one level up, at `(ι , ι)` with `ι = ov a`.)  This is a presentational
refinement of the equivalent
`∀ 𝑨 → …` form — it names the level the proof already fixes — not a change to the
theorem's content.

```agda
module _ {α ρᵃ ℓ : Level}{𝒦 : Pred(Algebra {𝑆 = 𝑆} α ρᵃ) (α ⊔ ρᵃ ⊔ ov {𝑆 = 𝑆} ℓ)} where
  private
    a ι : Level
    a = α ⊔ ρᵃ ⊔ ℓ
    ι = ov {𝑆 = 𝑆} a

  open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
  open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

  Birkhoff : {𝑨 : Algebra a a} → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
  Birkhoff {𝑨 = 𝑨} ModThA = V-≅-lc {α = α} {ρᵃ = ρᵃ} {ℓ = ℓ} 𝒦 𝑨 VlA
    where
    open Setoid (Domain 𝑨) using () renaming ( Carrier to ∣A∣ )
    sp𝔽A : 𝔽[ ∣A∣ ] ∈ S{ι} ι (P ℓ ι 𝒦)
    sp𝔽A = SP𝔽{ℓ = ℓ} 𝒦

    epi𝔽lA : epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι)
    epi𝔽lA = 𝔽-ModTh-epi-lift{ℓ = ℓ} (λ {p q} → ModThA{p = p}{q})

    lAimg𝔽A : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ ∣A∣ ]
    lAimg𝔽A = epi→ontohom 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι) epi𝔽lA

    VlA : Lift-Alg 𝑨 ι ι ∈ V ℓ ι 𝒦
    VlA = 𝔽[ ∣A∣ ] , sp𝔽A , lAimg𝔽A
```

The converse inclusion, `V 𝒦 ⊆ Mod (Th (V 𝒦))`, is a simple consequence of the
fact that `Mod Th` is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.[^1]

```agda
  module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} where
    open Setoid (Domain 𝑨) using () renaming ( Carrier to ∣A∣ )

    Birkhoff-converse : 𝑨 ∈ V′ ℓ ι 𝒦 → 𝑨 ∈ Mod{X = ∣A∣} (Th (V ℓ ι 𝒦))
    Birkhoff-converse vA pThq = pThq .⊫-proof 𝑨 vA
```

We have thus proved that every variety is an equational class.

Readers familiar with the classical formulation of the Birkhoff HSP theorem as an
"if and only if" assertion might worry that the proof is still incomplete. However,
recall that in the [Setoid.Varieties.Preservation][] module we proved the following
identity preservation lemma:

    V-id1 : 𝒦 ⊫ p ≈̇ q → V 𝒦 ⊫ p ≈̇ q

Thus, if `𝒦` is an equational class — that is, if 𝒦 is the class of algebras
satisfying all identities in some set — then `V 𝒦` ⊆ 𝒦`.  On the other hand, we
proved that `V` is expansive in the [Setoid.Varieties.Closure][] module:

    V-expa : 𝒦 ⊆ V 𝒦

so `𝒦` (= `V 𝒦` = `HSP 𝒦`) is a variety.

Taken together, `V-id1` and `V-expa` constitute formal proof that every equational
class is a variety.

This completes the formal proof of Birkhoff's variety theorem.

--------------------------------

[^1]: Recall, `V′` is simply a shorthand for `V` in the (not very special) case in which every pair of predicate level parameters is `α ρᵃ`.
