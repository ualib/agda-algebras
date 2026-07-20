---
layout: default
title : "Setoid.Varieties.FreeAlgebras module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "agda-algebras development team"
---

#### Free setoid algebras


<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.FreeAlgebras where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive   using ()                  renaming ( Set to Type )
open import Data.Product     using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Function         using ( _∘_ ; id )        renaming ( Func to _⟶_ )
open import Level            using ( Level ; _⊔_)
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library -------------------------------
open import Overture                           using  ( 𝓞 ; 𝓥 ; Signature ; 𝑆 )
open import Overture.Terms                     using  ( ℊ )
open import Setoid.Algebras                    using  ( Algebra ; ov ; Lift-Alg ; 𝔻[_] )
open import Setoid.Functions                   using  ( eq ; IsSurjective )
open import Setoid.Homomorphisms               using  ( epi ; IsEpi ; IsHom ; hom
                                                      ; epi→hom ; ⊙-epi ; ToLift-epi )
open import Setoid.Relations                   using  ( fkerPred )
open import Setoid.Terms                       using  ( 𝑻 ; _≐_ ; module Environment
                                                      ; free-lift ; free-lift-interp )
open import Setoid.Varieties.Closure           using  ( V ; S )
open import Setoid.Varieties.Preservation      using  ( classIds-⊆-VIds ; S-id1 )
open import Setoid.Varieties.SoundAndComplete  using  ( Eq ; _⊫_ ; ⊫-proof ; _≈̇_
                                                      ; Th ; Mod ; module Soundness
                                                      ; _⊢_▹_≈_ ; module FreeAlgebra )
open _⟶_      using ( cong ) renaming ( to to _⟨$⟩_ )
open Algebra  using ( Domain )
```
-->

In the code below, `X` will play the role of an arbitrary collection of variables; it
would suffice to take `X` to be the cardinality of the largest algebra in 𝒦, but
since we don't know that cardinality, we leave `X` arbitrary for now.

Alternatively, we could let `X` be the product of all algebras in the class `𝒦`, like so.

`𝕏 : Type oα`
`𝕏 = Carrier ( Domain (⨅ (𝔄{𝒦 = S 𝒦})) )`

```agda
module FreeHom (χ : Level){α ρᵃ ℓ : Level}
               {𝒦 : Pred(Algebra {𝑆 = 𝑆} α ρᵃ) (α ⊔ ρᵃ ⊔ ov {𝑆 = 𝑆} ℓ)} where
  private
    ι : Level
    ι = ov {𝑆 = 𝑆}(χ ⊔ α ⊔ ρᵃ ⊔ ℓ)

  open Eq
```

We now define the algebra `𝔽`, which plays the role of the relatively free algebra,
along with the natural epimorphism `epi𝔽 : epi (𝑻 𝕏) 𝔽` from `𝑻 𝕏` to `𝔽`.
The relatively free algebra (relative to `Th 𝒦`) is called `M` and is derived from
`TermSetoid 𝕏` and `TermInterp 𝕏` and imported from the EquationalLogic module.

```agda
 -- ℐ indexes the collection of equations modeled by 𝒦
  ℐ : Type ι
  ℐ = Σ[ eq ∈ Eq {χ = χ} ] 𝒦 ⊫ ((lhs eq) ≈̇ (rhs eq))

  ℰ : ℐ → Eq
  ℰ (eqv , p) = eqv

  ℰ⊢[_]▹Th𝒦 : (X : Type χ) → ∀{p q} → ℰ ⊢ X ▹ p ≈ q → 𝒦 ⊫ (p ≈̇ q)
  ℰ⊢[ X ]▹Th𝒦 x .⊫-proof 𝑨 kA = sound (λ i ρ → (proj₂ i) .⊫-proof 𝑨 kA ρ) x
    where open Soundness ℰ 𝑨

 ----------- THE RELATIVELY FREE ALGEBRA -----------
  open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )
```

Finally, we define an epimorphism from `𝑻 X` onto the relatively free algebra
`𝔽[ X ]`. Of course, the kernel of this epimorphism will be the congruence of
`𝑻 X` defined by identities modeled by (`S 𝒦`, hence) `𝒦`.

```agda
  epi𝔽[_] : (X : Type χ) → epi (𝑻 X) 𝔽[ X ]
  epi𝔽[ X ] = h , hepi
    where
    open Algebra 𝔽[ X ]  using() renaming ( Domain to F ; Interp to InterpF )
    open Setoid F        using() renaming ( _≈_  to _≈F≈_ ; refl to reflF )
    open Algebra (𝑻 X)   using() renaming (Domain to TX)
    open Setoid TX       using() renaming ( _≈_ to _≈T≈_ ; refl to reflT )

    open _≐_ ; open IsEpi ; open IsHom

    c : ∀ {x y} → x ≈T≈ y → x ≈F≈ y
    c (rfl {x}{y} ≡.refl) = reflF
    c (gnl {f}{s}{t} x) = cong InterpF (≡.refl , c ∘ x)

    h : TX ⟶ F
    h = record { to = id ; cong = c }

    hepi : IsEpi (𝑻 X) 𝔽[ X ] h
    compatible (isHom hepi) = cong h reflT
    isSurjective hepi {y} = eq y reflF


  hom𝔽[_] : (X : Type χ) → hom (𝑻 X) 𝔽[ X ]
  hom𝔽[ X ] = epi→hom (𝑻 X) 𝔽[ X ] epi𝔽[ X ]

  hom𝔽[_]-is-epic : (X : Type χ) → IsSurjective (proj₁ (hom𝔽[ X ]))
  hom𝔽[ X ]-is-epic = IsEpi.isSurjective (proj₂ (epi𝔽[ X ]))


  class-models-kernel : ∀{X p q} → (p , q) ∈ fkerPred (proj₁ (hom𝔽[ X ])) → 𝒦 ⊫ (p ≈̇ q)
  class-models-kernel {X = X}{p}{q} pKq = ℰ⊢[ X ]▹Th𝒦 pKq

  kernel-in-theory : {X : Type χ} → fkerPred (proj₁ (hom𝔽[ X ])) ⊆ Th (V ℓ ι 𝒦)
  kernel-in-theory {X = X} {p , q} pKq =
    classIds-⊆-VIds {ℓ = ℓ} (class-models-kernel pKq)


  module _  {X : Type χ} {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{sA : 𝑨 ∈ S {β = α}{ρᵃ} ℓ 𝒦} where
    open Environment 𝑨 using ( Equal )
    ker𝔽⊆Equal : ∀{p q} → (p , q) ∈ fkerPred (proj₁ (hom𝔽[ X ])) → Equal p q
    ker𝔽⊆Equal{p = p}{q} x = S-id1{ℓ = ℓ} (ℰ⊢[ X ]▹Th𝒦 x) .⊫-proof 𝑨 sA

  𝒦⊫→ℰ⊢ : {X : Type χ} → ∀{p q} → 𝒦 ⊫ p ≈̇ q → ℰ ⊢ X ▹ p ≈ q
  𝒦⊫→ℰ⊢ {p = p} {q} pKq = hyp (p ≈̇ q , pKq) where open _⊢_▹_≈_ using (hyp)

------------------------------------------------------------------------------

module _ {α ρᵃ ℓ : Level} {𝒦 : Pred(Algebra {𝑆 = 𝑆} α ρᵃ) (α ⊔ ρᵃ ⊔ ov {𝑆 = 𝑆} ℓ)} where
  private ι = ov {𝑆 = 𝑆}(α ⊔ ρᵃ ⊔ ℓ)
  open IsEpi ; open IsHom

  module lower-universe-version {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} where
    open FreeHom α {α}{ρᵃ}{ℓ}{𝒦}
    open FreeAlgebra {ι = ι}{I = ℐ} ℰ            using ( 𝔽[_] )
    open Algebra 𝑨  renaming (Domain to A)       using( Interp )
    open Setoid A   renaming ( Carrier to ∣A∣ )  using ( trans ; sym ; refl )

    𝔽-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ ∣A∣ ] 𝑨
    𝔽-ModTh-epi A∈ModThK = φ , isEpi
      where
      φ : (Domain 𝔽[ ∣A∣ ]) ⟶ A
      φ ⟨$⟩ x = free-lift{𝑨 = 𝑨} id x
      φ .cong {p} {q} pq =
        trans  (sym (free-lift-interp{𝑨 = 𝑨} id p))
               (trans  (A∈ModThK{p = p}{q} (kernel-in-theory pq) id )
                       (free-lift-interp{𝑨 = 𝑨} id q))
      isEpi : IsEpi 𝔽[ ∣A∣ ] 𝑨 φ
      isEpi .isHom .compatible = cong Interp (≡.refl , λ _ → refl)
      isEpi .isSurjective = eq (ℊ _) refl

    𝔽-ModTh-epi-lift :
      𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 (ov {𝑆 = 𝑆} α) (ov {𝑆 = 𝑆} α))
    𝔽-ModTh-epi-lift A∈ModThK = ⊙-epi (𝔽-ModTh-epi λ {p q} → A∈ModThK{p = p}{q}) ToLift-epi

  module _  -- higher-universe-version (needed by HSP theorem)
    {𝑨 : Algebra {𝑆 = 𝑆} (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)}
    where

    open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
    open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )
    open Algebra 𝑨 using( Interp ) renaming (Domain to A)
    open Environment 𝑨  using ( ⟦_⟧ )
    open Setoid A renaming ( Carrier to ∣A∣ )  using ( trans ; sym ; refl ; _≈_)
    open SetoidReasoning A

    𝔽-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ ∣A∣ ] 𝑨
    𝔽-ModTh-epi A∈ModThK = φ , isEpi
      where
      φ : 𝔻[ 𝔽[ ∣A∣ ] ] ⟶ A
      φ ⟨$⟩ x = free-lift id x
      φ .cong {p} {q} pq = begin
          free-lift id p  ≈˘⟨ free-lift-interp{𝑨 = 𝑨} id p ⟩
          ⟦ p ⟧ ⟨$⟩ id    ≈⟨ A∈ModThK{p = p}{q} (kernel-in-theory pq) id ⟩
          ⟦ q ⟧ ⟨$⟩ id    ≈⟨ free-lift-interp{𝑨 = 𝑨} id q ⟩
          free-lift id q  ∎

      isEpi : IsEpi 𝔽[ ∣A∣ ] 𝑨 φ
      isEpi .isHom .compatible = cong Interp (≡.refl , λ _ → refl)
      isEpi .isSurjective = eq (ℊ _) refl

    𝔽-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι)
    𝔽-ModTh-epi-lift A∈ModThK =
      ⊙-epi (𝔽-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi
```
