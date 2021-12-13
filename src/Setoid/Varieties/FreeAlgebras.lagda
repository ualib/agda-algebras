---
layout: default
title : "Setoid.Varieties.FreeAlgebras module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "agda-algebras development team"
---

#### <a id="free-setoid-algebras">Free setoid algebras</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.FreeAlgebras {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------------
open import Agda.Primitive   using ()                  renaming ( Set to Type )
open import Data.Product     using ( Σ-syntax ; _,_ )  renaming ( proj₁ to fst ; proj₂ to snd )
open import Function         using ( _∘_ ; id )        renaming ( Func to _⟶_ )
open import Level
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Base.Overture.Preliminaries                 using ( ∣_∣ ; ∥_∥ )
open import Base.Terms.Basic                   {𝑆 = 𝑆}  using ( ℊ )
open import Setoid.Overture.Inverses                    using ( eq )
open import Setoid.Overture.Surjective                  using ( IsSurjective )
open import Setoid.Relations.Discrete                   using ( fkerPred )
open import Setoid.Algebras.Basic              {𝑆 = 𝑆}  using ( Algebra ; ov ; Lift-Alg )
open import Setoid.Homomorphisms.Basic         {𝑆 = 𝑆}  using ( epi ; IsEpi ; IsHom ; hom ; epi→hom )
open import Setoid.Homomorphisms.Properties    {𝑆 = 𝑆}  using ( ∘-epi ; ToLift-epi )
open import Setoid.Terms.Basic                 {𝑆 = 𝑆}  using ( 𝑻 ; _≐_ ; module Environment )
open import Setoid.Terms.Properties            {𝑆 = 𝑆}  using ( free-lift )
open import Setoid.Terms.Operations            {𝑆 = 𝑆}  using ( free-lift-interp )
open import Setoid.Varieties.SoundAndComplete  {𝑆 = 𝑆}  using ( Eq ; _⊫_ ; _≈̇_ ; _⊢_▹_≈_ )
                                                        using ( module Soundness ; module FreeAlgebra )
                                                        using ( Th ; Mod )
open import Setoid.Varieties.Closure           {𝑆 = 𝑆}  using ( V ; S )
open import Setoid.Varieties.Preservation      {𝑆 = 𝑆}  using ( classIds-⊆-VIds ; S-id1 )

open _⟶_      using ( cong ) renaming ( f to _⟨$⟩_ )
open Algebra  using ( Domain )

\end{code}

In the code below, `X` will play the role of an arbitrary collection of variables; it would suffice to take `X` to be the cardinality of the largest algebra in 𝒦, but since we don't know that cardinality, we leave `X` aribtrary for now.

Alternatively, we could let `X` be the product of all algebras in the class `𝒦`, like so.

`𝕏 : Type oα`  
`𝕏 = Carrier ( Domain (⨅ (𝔄{𝒦 = S 𝒦})) )`

\begin{code}

module FreeHom (χ : Level){α ρᵃ ℓ : Level}
               {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private
  ι = ov(χ ⊔ α ⊔ ρᵃ ⊔ ℓ)

 open Eq

\end{code}

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 𝕏) 𝔽` from `𝑻 𝕏` to `𝔽`.
The relatively free algebra (relative to `Th 𝒦`) is called `M` and is derived from `TermSetoid 𝕏` and `TermInterp 𝕏` and imported from the EquationalLogic module.

\begin{code}

 -- ℐ indexes the collection of equations modeled by 𝒦
 ℐ : Type ι
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ ((lhs eq) ≈̇ (rhs eq))

 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

 ℰ⊢[_]▹Th𝒦 : (X : Type χ) → ∀{p q} → ℰ ⊢ X ▹ p ≈ q → 𝒦 ⊫ (p ≈̇ q)
 ℰ⊢[ X ]▹Th𝒦 x 𝑨 kA = sound (λ i ρ → ∥ i ∥ 𝑨 kA ρ) x
  where open Soundness ℰ 𝑨

 ----------- THE RELATIVELY FREE ALGEBRA -----------
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

\end{code}

Next we define an epimorphism from `𝑻 X` onto the relatively free algebra `𝔽[ X ]`.  Of course, the kernel of this epimorphism will be the congruence of `𝑻 X` defined by identities modeled by (`S 𝒦`, hence) `𝒦`.

\begin{code}

 epi𝔽[_] : (X : Type χ) → epi (𝑻 X) 𝔽[ X ]
 epi𝔽[ X ] = h , hepi
  where
  open Algebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
  open Setoid F using () renaming ( _≈_  to _≈F≈_ ; refl to reflF )

  open Algebra (𝑻 X) using () renaming (Domain to TX)
  open Setoid TX using () renaming ( _≈_ to _≈T≈_ ; refl to reflT )


  open _≐_ ; open IsEpi ; open IsHom

  c : ∀ {x y} → x ≈T≈ y → x ≈F≈ y
  c (rfl {x}{y} ≡.refl) = reflF
  c (gnl {f}{s}{t} x) = cong InterpF (≡.refl , c ∘ x)

  h : TX ⟶ F
  h = record { f = id ; cong = c }

  hepi : IsEpi (𝑻 X) 𝔽[ X ] h
  compatible (isHom hepi) = cong h reflT
  isSurjective hepi {y} = eq y reflF


 hom𝔽[_] : (X : Type χ) → hom (𝑻 X) 𝔽[ X ]
 hom𝔽[ X ] = epi→hom (𝑻 X) 𝔽[ X ] epi𝔽[ X ]

 hom𝔽[_]-is-epic : (X : Type χ) → IsSurjective ∣ hom𝔽[ X ] ∣
 hom𝔽[ X ]-is-epic = IsEpi.isSurjective (snd (epi𝔽[ X ]))


 class-models-kernel : ∀{X p q} → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣ → 𝒦 ⊫ (p ≈̇ q)
 class-models-kernel {X = X}{p}{q} pKq = ℰ⊢[ X ]▹Th𝒦 pKq

 kernel-in-theory : {X : Type χ} → fkerPred ∣ hom𝔽[ X ] ∣ ⊆ Th (V ℓ ι 𝒦)
 kernel-in-theory {X = X} {p , q} pKq vkA x = classIds-⊆-VIds {ℓ = ℓ} {p = p}{q}
                                      (class-models-kernel pKq) vkA x


 module _  {X : Type χ} {𝑨 : Algebra α ρᵃ}{sA : 𝑨 ∈ S {β = α}{ρᵃ} ℓ 𝒦} where
  open Environment 𝑨 using ( Equal )
  ker𝔽⊆Equal : ∀{p q} → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣ → Equal p q
  ker𝔽⊆Equal{p = p}{q} x = S-id1{ℓ = ℓ}{p = p}{q} (ℰ⊢[ X ]▹Th𝒦 x) 𝑨 sA


 𝒦⊫→ℰ⊢ : {X : Type χ} → ∀{p q} → 𝒦 ⊫ (p ≈̇ q) → ℰ ⊢ X ▹ p ≈ q
 𝒦⊫→ℰ⊢ {p = p} {q} pKq = hyp ((p ≈̇ q) , pKq) where open _⊢_▹_≈_ using (hyp)


------------------------------------------------------------------------------

module _ {α ρᵃ ℓ : Level}
         {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private
  ι = ov(α ⊔ ρᵃ ⊔ ℓ)

  open IsEpi ; open IsHom

 module lower-universe-version {𝑨 : Algebra α ρᵃ} where
  open FreeHom α {α}{ρᵃ}{ℓ}{𝒦}
  open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )
  open Algebra 𝑨 using( Interp ) renaming (Domain to A)
  open Setoid A using ( trans ; sym ; refl ) renaming ( Carrier to ∣A∣ )

  𝔽-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ ∣A∣ ] 𝑨
  𝔽-ModTh-epi A∈ModThK = φ , isEpi
    where
    φ : (Domain 𝔽[ ∣A∣ ]) ⟶ A
    _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
    cong φ {p} {q} pq =
     trans (sym (free-lift-interp{𝑨 = 𝑨} id p))
      (trans (A∈ModThK{p = p}{q} (kernel-in-theory pq) id)
      (free-lift-interp{𝑨 = 𝑨} id q))

    isEpi : IsEpi 𝔽[ ∣A∣ ] 𝑨 φ
    compatible (isHom isEpi) = cong Interp (≡.refl , (λ _ → refl))
    isSurjective isEpi {y} = eq (ℊ y) refl


  𝔽-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦))
   →                 epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 (ov α) (ov α))
  𝔽-ModTh-epi-lift A∈ModThK =
   ∘-epi (𝔽-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi


 module _ -- higher-universe-version
          -- (HSP theorem needs 𝑨 in higher universe level)
          {𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)} where

  open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
  open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

  open Algebra 𝑨 using( Interp ) renaming (Domain to A)
  open Setoid A using ( trans ; sym ; refl ) renaming ( Carrier to ∣A∣ )

  𝔽-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦))
   →            epi 𝔽[ ∣A∣ ] 𝑨
  𝔽-ModTh-epi A∈ModThK = φ , isEpi
   where
   φ : (Domain 𝔽[ ∣A∣ ]) ⟶ A
   _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
   cong φ {p} {q} pq = trans (sym (free-lift-interp{𝑨 = 𝑨} id p))
                      (trans (A∈ModThK{p = p}{q} (kernel-in-theory pq) id)
                      (free-lift-interp{𝑨 = 𝑨} id q))

   isEpi : IsEpi 𝔽[ ∣A∣ ] 𝑨 φ
   compatible (isHom isEpi) = cong Interp (≡.refl , (λ _ → refl))
   isSurjective isEpi {y} = eq (ℊ y) refl

  𝔽-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι)
  𝔽-ModTh-epi-lift A∈ModThK =
   ∘-epi (𝔽-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi

\end{code}

--------------------------------

<span style="float:left;">[← Setoid.Varieties.Closure](Setoid.Varieties.Closure.html)</span>
<span style="float:right;">[Setoid.Varieties.HSP](Setoid.Varieties.HSP.html)</span>

{% include UALib.Links.md %}

