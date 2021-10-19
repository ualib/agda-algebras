n---
layout: default
title : "Varieties.Func.FreeAlgebras module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "agda-algebras development team"
---

#### <a id="free-setoid-algebras">Free setoid algebras</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Func.FreeAlgebras {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( Σ-syntax ; _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function         using ( _∘_ ; id )
open import Function.Bundles using ( Func )
open import Level
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- -- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Preliminaries             using ( _⟶_ )
open import Overture.Func.Inverses                  using ( eq )
open import Overture.Func.Surjective                using ( IsSurjective )
open import Relations.Func.Discrete                 using ( fkerPred )
open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; Lift-Alg )
open import Homomorphisms.Func.Basic        {𝑆 = 𝑆} using ( epi ; IsEpi ; IsHom ; hom ; epi→hom )
open import Homomorphisms.Func.Properties   {𝑆 = 𝑆} using ( ∘-epi ; ToLift-epi )
open import Terms.Basic                     {𝑆 = 𝑆} using ( Term ; ℊ )
open import Terms.Func.Basic                {𝑆 = 𝑆} using ( 𝑻 ; _≐_ ; module Environment )
open import Terms.Func.Properties           {𝑆 = 𝑆} using ( free-lift )
open import Terms.Func.Operations           {𝑆 = 𝑆} using ( free-lift-interp )
open import Varieties.Func.SoundAndComplete {𝑆 = 𝑆} using ( Eq ; _⊫_ ; _≈̇_ ; _⊢_▹_≈_
                                                          ; module Soundness
                                                          ; module FreeAlgebra
                                                          ; ThPred ; ModPred )
open import Varieties.Func.Closure          {𝑆 = 𝑆} using ( V ; S )
open import Varieties.Func.Preservation  {𝑆 = 𝑆} using ( classIds-⊆-VIds ; S-id1 ; S-id2 )

open Func using ( cong ) renaming ( f to _⟨$⟩_ )
open SetoidAlgebra using ( Domain )


private variable
 χ : Level
\end{code}

In the code below, `X` will play the role of an arbitrary collection of variables; it would suffice to take `X` to be the cardinality of the largest algebra in 𝒦, but since we don't know that cardinality, we leave `X` aribtrary for now.

Alternatively, we could let `X` be the product of all algebras in the class `𝒦`, like so.

`𝕏 : Type oα`  
`𝕏 = Carrier ( Domain (⨅ (𝔄{𝒦 = S 𝒦})) )`

\begin{code}

module FreeHom (χ : Level){α : Level}(𝒦 : Pred (SetoidAlgebra α α) (ov α)) where
 private
  oα = ov α
  oαχ = ov (α ⊔ χ)
  ooα = ov oα

 open Eq

\end{code}

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 𝕏) 𝔽` from `𝑻 𝕏` to `𝔽`.
The relatively free algebra (relative to `Th 𝒦`) is called `M` and is derived from `TermSetoid 𝕏` and `TermInterp 𝕏` and imported from the EquationalLogic module.

\begin{code}

 -- ℐ indexes the collection of equations modeled by 𝒦
 ℐ : Type oαχ
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ ((lhs eq) ≈̇ (rhs eq))

 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

 ℰ⊢[_]▹Th𝒦 : (X : Type χ) → ∀{p q} → ℰ ⊢ X ▹ p ≈ q → 𝒦 ⊫ (p ≈̇ q)
 ℰ⊢[ X ]▹Th𝒦 x 𝑨 kA = sound (λ i ρ → ∥ i ∥ 𝑨 kA ρ) x
  where open Soundness ℰ 𝑨

 ----------- THE RELATIVELY FREE ALGEBRA -----------
 open FreeAlgebra {ι = oαχ}{I = ℐ} ℰ using ( 𝔽[_] )

\end{code}

Next we define an epimorphism from `𝑻 X` onto the relatively free algebra `𝔽[ X ]`.  Of course, the kernel of this epimorphism will be the congruence of `𝑻 X` defined by identities modeled by (`S 𝒦`, hence) `𝒦`.

\begin{code}

 epi𝔽[_] : (X : Type χ) → epi (𝑻 X) 𝔽[ X ]
 epi𝔽[ X ] = h , hepi
  where
  open SetoidAlgebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
  open Setoid F using () renaming ( _≈_  to _≈F≈_ ; refl to reflF )

  open SetoidAlgebra (𝑻 X) using () renaming (Domain to TX)
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

 kernel-in-theory : {X : Type χ} → fkerPred ∣ hom𝔽[ X ] ∣ ⊆ ThPred (V 𝒦)
 kernel-in-theory {X = X} {p , q} pKq vkA x = classIds-⊆-VIds{p = p}{q}
                                      (class-models-kernel pKq) vkA x


 module _  {X : Type χ} {𝑨 : SetoidAlgebra α α}{sA : 𝑨 ∈ S 𝒦} where
  open Environment 𝑨 using ( Equal )
  ker𝔽⊆Equal : ∀{p q} → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣ → Equal p q
  ker𝔽⊆Equal{p = p}{q} x = S-id1{p = p}{q} (ℰ⊢[ X ]▹Th𝒦 x) 𝑨 sA


 𝒦⊫→ℰ⊢ : {X : Type χ} → ∀{p q} → 𝒦 ⊫ (p ≈̇ q) → ℰ ⊢ X ▹ p ≈ q
 𝒦⊫→ℰ⊢ {p = p} {q} pKq = hyp ((p ≈̇ q) , pKq) where open _⊢_▹_≈_ using (hyp)


------------------------------------------------------------------------------

module _ {α : Level}(𝑨 : SetoidAlgebra α α)(𝒦 : Pred (SetoidAlgebra α α) (ov α)) where

 private
  oα = ov α

 open FreeHom α 𝒦
 open FreeAlgebra {ι = oα}{I = ℐ} ℰ using ( 𝔽[_] )
 open SetoidAlgebra 𝑨 using( Interp ) renaming (Domain to A)
 open Setoid A using ( trans ; sym ; refl ) renaming ( Carrier to ∣A∣ )

 𝔽-ModTh-epi : (𝑨 ∈ ModPred{X = ∣A∣} (ThPred{X = ∣A∣} (V 𝒦))) → epi 𝔽[ ∣A∣ ] 𝑨
 𝔽-ModTh-epi A∈ModThK = φ , isEpi
   where
   open IsEpi
   open IsHom

   φ : (Domain 𝔽[ ∣A∣ ]) ⟶ A
   _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
   cong φ {p} {q} pq = trans (sym (free-lift-interp{𝑨 = 𝑨} id p))
                      (trans (A∈ModThK{p = p}{q} (kernel-in-theory pq) id)
                      (free-lift-interp{𝑨 = 𝑨} id q))

   isEpi : IsEpi 𝔽[ ∣A∣ ] 𝑨 φ
   compatible (isHom isEpi) = cong Interp (≡.refl , (λ _ → refl))
   isSurjective isEpi {y} = eq (ℊ y) refl


 𝔽-ModTh-epi-lift : (𝑨 ∈ ModPred{X = ∣A∣}(ThPred{X = ∣A∣} (V 𝒦)))
  →                 epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 (ov α) (ov α))
 𝔽-ModTh-epi-lift A∈ModThK = ∘-epi (𝔽-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi

\end{code}

--------------------------------

<span style="float:left;">[← Varieties.Func.Closure](Varieties.Func.Closure.html)</span>
<span style="float:right;">[Varieties.Func.HSP](Varieties.Func.HSP.html)</span>

{% include UALib.Links.md %}

























--- OLD VERSION ---------------------------------------------------------




module _ {α : Level} {𝒦 : Pred (SetoidAlgebra α α) (ov α)}
        {𝔄I : ∀ i → 𝕌[ 𝔄{𝒦 = S 𝒦} i ] }  -- assume all algebras in 𝒦 are nonempty
        {_≟_ : Decidable{A = ℑ{𝒦 = S 𝒦}} _≡_}
         where

 private
  oα = ov α
  ooα = ov oα


 -- X is the "arbitrary" collection of variables; it suffices to take X to be the
 -- cardinality of the largest algebra in 𝒦, but since we don't have the luxury of
 -- knowing that cardinality, we simply let X be the product of all algebras in 𝒦.
 open SetoidAlgebra using ( Domain )
 open Setoid using ( Carrier )
 open Func using ( cong ) renaming ( f to _⟨$⟩_ )
 open img_∋_
 open Eq

 𝕏 : Type oα
 𝕏 = Carrier ( Domain (⨅ (𝔄{𝒦 = S 𝒦})) )

 -- hsurj : {𝑨 : SetoidAlgebra α α} → 𝑨 ∈ S 𝒦 → Σ[ h ∈ (𝕏 → 𝕌[ 𝑨 ]) ] onto h
 -- hsurj {𝑨 = 𝑨} sA = (proj _≟_ 𝔄I (𝑨 , sA)) , projIsOnto _≟_ 𝔄I

\end{code}

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 𝕏) 𝔽` from `𝑻 𝕏` to `𝔽`.
The relatively free algebra (relative to `Th 𝒦`) is called `M` and is derived from `TermSetoid 𝕏` and `TermInterp 𝕏` and imported from the EquationalLogic module.

begin{code}

 -- ℐ indexes the collection of equations modeled by 𝒦
 ℐ : Type ooα
 ℐ = Σ[ eq ∈ Eq{oα} ] 𝒦 ⊫ ((lhs eq) ≈̇ (rhs eq))
 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv
 open _⊢_▹_≈_ using ( hyp )

 ℰ⊢→𝒦⊫ : ∀{p q} → ℰ ⊢ 𝕏 ▹ p ≈ q → 𝒦 ⊫ (p ≈̇ q)
 ℰ⊢→𝒦⊫ x 𝑨 kA = sound (λ i ρ → ∥ i ∥ 𝑨 kA ρ) x
  where open Soundness ℰ 𝑨

 𝒦⊫→ℰ⊢ : ∀{p q} → 𝒦 ⊫ (p ≈̇ q) → ℰ ⊢ 𝕏 ▹ p ≈ q
 𝒦⊫→ℰ⊢ {p = p} {q} pKq = hyp ((p ≈̇ q) , pKq)

 S𝒦⊫→ℰ⊢ : ∀{p q} → (S 𝒦) ⊫ (p ≈̇ q) → ℰ ⊢ 𝕏 ▹ p ≈ q
 S𝒦⊫→ℰ⊢ {p = p} {q} pSKq = hyp ((p ≈̇ q) , S-id2{p = p}{q} pSKq)

 open _≐_
 open FreeAlgebra {ι = ooα}{I = ℐ} ℰ using ( 𝔽[_] )
 open SetoidAlgebra 𝔽[ 𝕏 ] using () renaming ( Domain to 𝔽 ; Interp to Interp𝔽 )
 open Setoid 𝔽 using () renaming ( _≈_  to _≈𝔽≈_ ; refl to refl𝔽 )

 open Setoid using (Carrier)
 open SetoidAlgebra (𝑻 𝕏) using () renaming (Domain to TX)
 open Setoid TX using () renaming ( _≈_ to _≈T≈_ ; refl to reflT )
--  open Term

\end{code}

We begin by constructing `ℭ`, using the techniques described in the section on <a href="https://ualib.gitlab.io/Varieties.Varieties.html#products-of-classes">products of classes</a>.

begin{code}

  -- ℭ is the product of all subalgebras of algebras in 𝒦.
 ℭ : SetoidAlgebra oα oα
 ℭ = ⨅ (𝔄{α = α}{ρ = α}{𝒦 = S 𝒦})

 ℓℭ≅⨅ℓ : Lift-Alg (⨅ (𝔄{α = α}{ρ = α}{𝒦 = S 𝒦})) ooα ooα ≅ ⨅ (λ x → Lift-Alg ∣ lower x ∣ ooα ooα)
 ℓℭ≅⨅ℓ = ℓ⨅≅⨅ℓ

 open SetoidAlgebra ℭ using () renaming ( Domain to C )
 open Setoid C using () renaming ( Carrier to ∣C∣ ; _≈_ to _≈C≈_ ; refl to reflℭ )
 open Environment ℭ using () renaming ( Env to EnvC )

\end{code}

Observe that the inhabitants of `ℭ` are maps from `ℑ` to `{𝔄 i : i ∈ ℑ}`.  A homomorphism from `𝑻 𝕏` to `ℭ` is obtained as follows.

begin{code}

 hsurj : {𝑨 : SetoidAlgebra α α} → 𝑨 ∈ S 𝒦 → Σ[ h ∈ (𝕏 → 𝕌[ 𝑨 ]) ] onto h
 hsurj {𝑨 = 𝑨} sA = proj _≟_ 𝔄I (𝑨 , sA) , projIsOnto _≟_ 𝔄I

 homℭ : hom (𝑻 𝕏) ℭ
 homℭ = ⨅-hom-co (𝔄{𝒦 = S 𝒦}) h
  where
  h : ∀ i → hom (𝑻 𝕏) ((𝔄{𝒦 = S 𝒦}) i)
  h i = lift-hom ∣ hsurj ∥ i ∥ ∣

\end{code}

Instead of defining the hom from `𝑻 𝕏` to `ℭ` for the single environment given by the (surjective) projection `hsurj`, we could let the homomorphism depend on a given (arbitrary) environment `ρ`.

begin{code}

 homℭ[_] : Carrier (EnvC 𝕏) → hom (𝑻 𝕏) ℭ
 homℭ[ ρ ] = ⨅-hom-co (𝔄{𝒦 = S 𝒦}) h
  where
  h : ∀ i → hom (𝑻 𝕏) ((𝔄{𝒦 = S 𝒦}) i)
  h i = lift-hom (λ x → ρ x i)

\end{code}

Next we define an epimorphism from `𝑻 𝕏` onto the relatively free algebra `𝔽[ 𝕏 ]`.  Of course, the kernel of this epimorphism will be the congruence of `𝑻 𝕏` defined by identities modeled by (`S 𝒦`, hence) `𝒦`.

begin{code}

 epi𝔽 : epi (𝑻 𝕏) 𝔽[ 𝕏 ]
 epi𝔽 = h , hepi
  where
  c : ∀ {x y} → x ≈T≈ y → x ≈𝔽≈ y
  c (_≐_.rfl {x}{y} ≡.refl) = refl𝔽
  c (gnl {f}{s}{t} x) = cong Interp𝔽 (≡.refl , (λ i → c (x i)))

  h : TX ⟶ 𝔽
  h ⟨$⟩ t = t
  cong h = c

  open IsEpi ; open IsHom

  hepi : IsEpi (𝑻 𝕏) 𝔽[ 𝕏 ] h
  compatible (isHom hepi) {f}{a} = cong Interp𝔽 (≡.refl , (λ i → refl𝔽))
  isSurjective hepi {y} = Image_∋_.eq y refl𝔽


 hom𝔽 : hom (𝑻 𝕏) 𝔽[ 𝕏 ]
 hom𝔽 = epi→hom (𝑻 𝕏) 𝔽[ 𝕏 ] epi𝔽

 hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
 hom𝔽-is-epic = IsEpi.isSurjective (snd (epi𝔽))

{-    TX ----->> 𝔽[ 𝕏 ]
        \       /
         \     /
          \   /
           v v
            ℭ                 -}

 ψ : SetoidAlgebra α α → Pred (𝕌[ 𝑻 𝕏 ] × 𝕌[ 𝑻 𝕏 ]) _
 ψ 𝑨 (p , q) = (sA : 𝑨 ∈ S 𝒦)(ρ : Carrier (EnvC 𝕏))
  →            (⟦ p ⟧ ⟨$⟩ (λ x → ρ x (𝑨 , sA))) ≈ (⟦ q ⟧ ⟨$⟩ (λ x → ρ x (𝑨 , sA)))
  where
  open Environment 𝑨 using (⟦_⟧)
  open SetoidAlgebra 𝑨 using() renaming (Domain to A)
  open Setoid A using ( _≈_ )

 Ψ : Pred (𝕌[ 𝑻 𝕏 ] × 𝕌[ 𝑻 𝕏 ]) _
 Ψ (p , q) = ∀ 𝑨 → ψ 𝑨 (p , q)


 ker𝔽→ℰ : ∀{p q} → (p , q) ∈ fkerPred ∣ hom𝔽 ∣ →  ℰ ⊢ 𝕏 ▹ p ≈ q
 ker𝔽→ℰ = id

 ℰ→ker𝔽 : ∀{p q} →  ℰ ⊢ 𝕏 ▹ p ≈ q → (p , q) ∈ fkerPred ∣ hom𝔽 ∣
 ℰ→ker𝔽 = id


 module _   {𝑨 : SetoidAlgebra α α}{sA : 𝑨 ∈ S 𝒦} where
  open Environment 𝑨 using ( Equal )
  ker𝔽⊆Equal : ∀{p q} → (p , q) ∈ fkerPred ∣ hom𝔽 ∣ → Equal p q
  ker𝔽⊆Equal{p = p}{q} x = S-id1{p = p}{q} (ℰ⊢→𝒦⊫ x) 𝑨 sA

 ker𝔽⊆kerℭ : fkerPred ∣ hom𝔽 ∣ ⊆ fkerPred ∣ homℭ ∣
 ker𝔽⊆kerℭ {p , q} pKq (𝑨 , sA) = Goal
  where
  open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈ₐ_ ; trans to transₐ ; sym to symₐ )
  open Environment 𝑨
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ∣ hsurj sA ∣ ≈ₐ free-lift ∣ hsurj sA ∣ t
  fl t = free-lift-interp{𝑨 = 𝑨} ∣ hsurj sA ∣ t

  subgoal : ⟦ p ⟧ ⟨$⟩ ∣ hsurj sA ∣ ≈ₐ ⟦ q ⟧ ⟨$⟩ ∣ hsurj sA ∣
  subgoal = ker𝔽⊆Equal{sA = sA}{p = p}{q} pKq ∣ hsurj sA ∣
  Goal : (free-lift{𝑨 = 𝑨} ∣ hsurj sA ∣ p) ≈ₐ (free-lift{𝑨 = 𝑨} ∣ hsurj sA ∣ q)
  Goal = transₐ (symₐ (fl p)) (transₐ subgoal (fl q)) --


 ker𝔽⊆kerℭ[_] : (ρ : Carrier (EnvC 𝕏)) → fkerPred ∣ hom𝔽 ∣ ⊆ fkerPred ∣ homℭ[ ρ ] ∣
 ker𝔽⊆kerℭ[ ρ ] {p , q} pKq (𝑨 , sA) = Goal
  where
  open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈ₐ_ ; trans to transₐ ; sym to symₐ )
  open Environment 𝑨
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ (λ x → ρ x (𝑨 , sA)) ≈ₐ free-lift (λ x → ρ x (𝑨 , sA)) t
  fl t = free-lift-interp {𝑨 = 𝑨} (λ x → ρ x (𝑨 , sA)) t

  subgoal : ⟦ p ⟧ ⟨$⟩ (λ x → ρ x (𝑨 , sA)) ≈ₐ ⟦ q ⟧ ⟨$⟩ (λ x → ρ x (𝑨 , sA))
  subgoal = ker𝔽⊆Equal{𝑨 = 𝑨}{sA} pKq (λ x → ρ x (𝑨 , sA))
  Goal : (free-lift{𝑨 = 𝑨} (λ x → ρ x (𝑨 , sA)) p) ≈ₐ (free-lift{𝑨 = 𝑨} (λ x → ρ x (𝑨 , sA)) q)
  Goal = transₐ (symₐ (fl p)) (transₐ subgoal (fl q))




 module _ where

  Ψlemma0 : ∀{p q}
   →       (∀(ρ : Carrier (EnvC 𝕏)) → ∣ homℭ[ ρ ] ∣ ⟨$⟩ p ≈C≈ ∣ homℭ[ ρ ] ∣ ⟨$⟩ q)
   →       (p , q) ∈ Ψ
  Ψlemma0 {p} {q} phomℭq 𝑨 sA ρ = Goal
   where
   open Environment 𝑨 using ( ⟦_⟧ )
   open Setoid (Domain 𝑨) using ( _≈_ ; trans ; sym )
   fl : free-lift (λ x → ρ x (𝑨 , sA)) p ≈ free-lift (λ x → ρ x (𝑨 , sA)) q
   fl = phomℭq ρ (𝑨 , sA)

   fli : ∀ p → ⟦ p ⟧ ⟨$⟩ (λ x → ρ x (𝑨 , sA)) ≈ free-lift (λ x → ρ x (𝑨 , sA)) p
   fli p = free-lift-interp{𝑨 = 𝑨} (λ x → ρ x (𝑨 , sA)) p

   Goal : ⟦ p ⟧ ⟨$⟩ (λ x → ρ x (𝑨 , sA)) ≈ ⟦ q ⟧ ⟨$⟩ (λ x → ρ x (𝑨 , sA))
   Goal = trans (fli p) (trans fl (sym (fli q)))

  Ψlemma0-ap : {𝑨 : SetoidAlgebra α α}{sA : 𝑨 ∈ S 𝒦}(ρ : Carrier (EnvC 𝕏))
   →           fkerPred ∣ hom𝔽 ∣ ⊆ fkerPred (free-lift-func{𝑨 = 𝑨} (λ x → ρ x (𝑨 , sA)))
  Ψlemma0-ap {𝑨} {sA} ρ {p , q} x = Goal
   where
   open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈₂_ )
   ν : ∣ homℭ[ ρ ] ∣ ⟨$⟩ p ≈C≈ ∣ homℭ[ ρ ] ∣ ⟨$⟩ q
   ν = ker𝔽⊆kerℭ[ ρ ] x

   Goal : (free-lift (λ x → ρ x (𝑨 , sA)) p) ≈₂ (free-lift (λ x → ρ x (𝑨 , sA)) q)
   Goal = ν (𝑨 , sA)

 𝔽-lift-hom : {ρ : Carrier (EnvC 𝕏)}(𝑨 : SetoidAlgebra α α) → 𝑨 ∈ S 𝒦 → hom 𝔽[ 𝕏 ] 𝑨
 𝔽-lift-hom {ρ = ρ} 𝑨 sA = ∣ HomFactor 𝑨 gh hom𝔽 kk hom𝔽-is-epic ∣
  where
  open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈₂_ ; sym to sym₂ )

  gh : hom (𝑻 𝕏) 𝑨
  gh = lift-hom λ x → ρ x (𝑨 , sA)
  kk : kernelRel _≈𝔽≈_ (_⟨$⟩_ ∣ hom𝔽 ∣) ⊆ kernelRel _≈₂_ (_⟨$⟩_ ∣ gh ∣)
  kk = Ψlemma0-ap{𝑨 = 𝑨}{sA} ρ

 hom𝔽ℭ[_] : Carrier (EnvC 𝕏) → hom 𝔽[ 𝕏 ] ℭ
 hom𝔽ℭ[ ρ ] = ∣ HomFactor ℭ homℭ[ ρ ] hom𝔽 ker𝔽⊆kerℭ[ ρ ] hom𝔽-is-epic ∣

 hom𝔽ℭ : hom 𝔽[ 𝕏 ] ℭ
 hom𝔽ℭ = ∣ HomFactor ℭ homℭ hom𝔽 ker𝔽⊆kerℭ hom𝔽-is-epic ∣

 open Environment ℭ
 kerℭlemma : ∀{p q}
  → (p , q) ∈ fkerPred ∣ homℭ ∣ → ∀ τ → free-lift{𝑨 = ℭ} τ p ≈C≈ free-lift{𝑨 = ℭ} τ q
 kerℭlemma {p}{q} x τ i = Goal
  where
  𝑨 : SetoidAlgebra α α  ; sA : 𝑨 ∈ S 𝒦
  𝑨 = ∣ i ∣ ;              sA = ∥ i ∥
  open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈ₐ_ ; trans to transₐ ; sym to symₐ )
  open Environment 𝑨
  have : (free-lift{𝑨 = 𝑨} (λ x → τ x (𝑨 , sA)) p) ≈ₐ (free-lift{𝑨 = 𝑨} (λ x → τ x (𝑨 , sA)) q)
  have = {!!} -- x {!𝑨 , sA!} -- x i
  Goal : (free-lift{𝑨 = ℭ} τ p i) ≈ₐ (free-lift{𝑨 = ℭ} τ q i)
  Goal = transₐ (symₐ (fl-lemma0{i = i} τ p)) (transₐ have (fl-lemma0{i = i} τ q))

 kerℭ⊆ker𝔽 : fkerPred ∣ homℭ ∣ ⊆ fkerPred ∣ hom𝔽[ ∣C∣ ] ∣
 kerℭ⊆ker𝔽 {p , q} pKq = E⊢pq
  where
  pqEqual : Equal p q
  pqEqual τ = trans (free-lift-interp {𝑨 = ℭ} τ p)
                    (trans (kerℭlemma{p = p}{q} pKq τ)
                           (sym (free-lift-interp {𝑨 = ℭ} τ q)))

  E⊢pq : ℰ ⊢ ∣C∣ ▹ p ≈ q
  E⊢pq = AllEqual⊆ker𝔽 (ℭEqual→skEqual{p = p}{q} pqEqual)


 Ψlem : ∀{p q} → ∣ hom𝔽ℭ ∣ ⟨$⟩ p ≈C≈ ∣ hom𝔽ℭ ∣ ⟨$⟩ q → ℰ ⊢ 𝕏 ▹ p ≈ q
 Ψlem {p} {q} hpq = Goal
  where
  S𝒦⊫ : (S 𝒦) ⊫ (p ≈̇ q)
  S𝒦⊫ 𝑨 x ρ = {!!}
  Goal : ℰ ⊢ 𝕏 ▹ p ≈ q
  Goal = S𝒦⊫→ℰ⊢ S𝒦⊫



 Ψlemma : ∀{p q} → ∣ hom𝔽ℭ ∣ ⟨$⟩ p ≈C≈ ∣ hom𝔽ℭ ∣ ⟨$⟩ q  → p ≈𝔽≈ q
 Ψlemma {p} {q} hpq = Goal
  where
  𝒦⊧pq : 𝒦 ⊫ (p ≈̇ q)
  𝒦⊧pq 𝑨 x ρ = {!!}
  Goal : p ≈𝔽≈ q
  Goal = 𝒦⊫→ℰ⊢ 𝒦⊧pq
 Ψlemmaρ : ∀{p q} → (∀ ρ → ∣ hom𝔽ℭ[ ρ ] ∣ ⟨$⟩ p ≈C≈ ∣ hom𝔽ℭ[ ρ ] ∣ ⟨$⟩ q) → p ≈𝔽≈ q
 Ψlemmaρ {p} {q} hpq = Goal
  where
  S𝒦⊧pq : (S 𝒦) ⊫ (p ≈̇ q)
  S𝒦⊧pq 𝑨 sA ρ = {!!}
  𝒦⊧pq : 𝒦 ⊫ (p ≈̇ q)
  𝒦⊧pq 𝑨 x ρ = {!!}
  Goal : p ≈𝔽≈ q
  Goal = 𝒦⊫→ℰ⊢ 𝒦⊧pq


 module _ (𝑨 : SetoidAlgebra oα oα)(A∈ModThK : 𝑨 ∈ Mod (Th{X = 𝕏} (V 𝒦))) where
  open IsEpi
  open Environment 𝑨 renaming ( Env to EnvA )
  open SetoidAlgebra 𝑨 using() renaming (Domain to A)
  open Setoid (EnvA 𝕏) using () renaming ( Carrier to X→A )
 -- open Environment 𝔽[ 𝕏 ]
 -- open Setoid (Env 𝕏) using () renaming ( Carrier to 𝕏→F )
 -- open Environment (𝑻 𝕏)
 -- open Setoid (Env 𝕏) using () renaming ( Carrier to 𝕏⇒T )

 class-models-kernel : ∀{p q} → (p , q) ∈ fkerPred ∣ hom𝔽 ∣ → 𝒦 ⊫ (p ≈̇ q)
 class-models-kernel {p = p} {q} pKq = ℰ⊢→𝒦⊫ pKq

 kernel-in-theory : fkerPred ∣ hom𝔽 ∣ ⊆ ThPred (V 𝒦)
 kernel-in-theory {p , q} pKq vkA x = classIds-⊆-VIds{p = p}{q}{𝒦 = 𝒦} (class-models-kernel pKq) vkA x

 PSℭ : ℭ ∈ P (Lift-class (S 𝒦))
 PSℭ = (ℑ{𝒦 = S 𝒦}) , ((λ x → Lift-Alg ∣ x ∣ oα oα) , ((λ i → Lift-class-lemma{𝒦 = S 𝒦}{𝑨 = ∣ i ∣} ∥ i ∥) , ⨅≅ (λ i → Lift-≅)))

 ℓℭ : SetoidAlgebra ooα ooα
 ℓℭ = Lift-Alg ℭ ooα ooα

 PSℓℭ : ℓℭ ∈ P (S (Lift-class 𝒦))
 PSℓℭ = Lift ooα ℑ , (λ x → Lift-Alg ∣ lower x ∣ ooα ooα) , ξ , ℓ⨅≅⨅ℓ
  where
  ξ : ∀ i → Lift-Alg ∣ lower i ∣ ooα ooα ∈ S (Lift-class 𝒦)
  ξ (lift (𝑩 , (𝑨 , (kA , B≤A)))) = (Lift-Alg 𝑨 ooα ooα)
                                   , ((Lift-class-lemma kA) , (Lift-≤-Lift B≤A))


 SPℓℭ : ℓℭ ∈ S (P (Lift-class 𝒦))
 SPℓℭ = PS⊆SP PSℓℭ

 mon𝔽ℭ : Carrier (EnvC 𝕏) → mon 𝔽[ 𝕏 ] ℭ
 mon𝔽ℭ ρ = φ , ismon
  where
  open IsMon
  φ : 𝔽 ⟶ C
  φ = ∣ hom𝔽ℭ[ ρ ] ∣
  ismon : IsMon 𝔽[ 𝕏 ] ℭ φ
  isHom ismon = ∥ hom𝔽ℭ[ ρ ] ∥
  isInjective ismon {p}{q} φpq = Goal
   where
   𝒦⊫pq : 𝒦 ⊫ (p ≈̇ q)
   𝒦⊫pq 𝑨 x ρ = {!!}
   Goal : p ≈𝔽≈ q
   Goal = 𝒦⊫→ℰ⊢ 𝒦⊫pq



 𝔽𝕏≤ℓℭ[_] : Carrier (EnvC 𝕏) → 𝔽[ 𝕏 ] ≤ ℓℭ
 𝔽𝕏≤ℓℭ[ ρ ] = φ , φM
  where
  φ : hom 𝔽[ 𝕏 ] ℓℭ
  φ = Lift-hom-snd hom𝔽ℭ[ ρ ] ooα ooα
  φM : IsInjective ∣ φ ∣
  φM {p}{q} φpq = {!!}


 SSP𝔽[_] : Carrier (EnvC 𝕏) → 𝔽[ 𝕏 ] ∈ S (S (P (Lift-class 𝒦)))
 SSP𝔽[ ρ ] = ℓℭ , (SPℓℭ , 𝔽𝕏≤ℓℭ[ ρ ])

 SP𝔽[_] : Carrier (EnvC 𝕏) → 𝔽[ 𝕏 ] ∈ S (P (Lift-class 𝒦))
 SP𝔽[ ρ ] = S-idem SSP𝔽[ ρ ]

 -- ℓ𝔽∈V : ℓ𝔽 ∈ V (Lift-class 𝒦)
 -- ℓ𝔽∈V = SP⊆V{𝒦 = Lift-class 𝒦} ℓ𝔽∈SP

\end{code}

To be continued...

(TODO: complete this module)

#### The HSP Theorem
Now that we have all of the necessary ingredients, it is all but trivial to
combine them to prove Birkhoff's HSP theorem. (Note that since the proof enlists
the help of the `𝔽-ModTh-epi` theorem, we must assume an environment exists,
which is manifested in the premise `∀ 𝑨 → X ↠ 𝑨`.

begin{code}

 𝔽-ModTh-epi : epi 𝔽[ 𝕏 ] 𝑨
 𝔽-ModTh-epi = φ , isEpi
  where
  TA : TX ⟶ A
  TA = free-lift-func{𝑨 = 𝑨} ∣ 𝕏↠A ∣
  φ : F ⟶ A
  φ = {!!}
  isEpi : IsEpi 𝔽[ 𝕏 ] 𝑨 φ
  isHom isEpi = {!!}
  isSurjective isEpi = {!!}

begin{code}

 Birkhoff[_] : Carrier(EnvC 𝕏) → Mod (Th{X = 𝕏} (V 𝒦)) ⊆ V (Lift-class 𝒦)
 Birkhoff[ ρ ] {𝑨} AMod = 𝔽[ 𝕏 ] , SP𝔽[ ρ ] , φ , φE
  where
  φ : hom 𝔽[ 𝕏 ] 𝑨
  φ = {!!}
  φE : IsSurjective ∣ φ ∣
  φE = {!!} -- 𝔽-ModTh-epi 𝑨 AMod

\end{code}

The converse inclusion, `V 𝒦 ⊆ Mod X (Th (V 𝒦))`, is a simple consequence of the
fact that `Mod Th` is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.

begin{code}

 -- Birkhoff-converse : V{α}{𝓕} 𝒦 ⊆ Mod{X = X} (Th (V 𝒦))
 -- Birkhoff-converse α p q pThq = pThq α

\end{code}












<!-- 


 -- ℓ𝔽 : SetoidAlgebra ooα ooα
 -- ℓ𝔽 = Lift-Alg 𝔽 ooα ooα

 -- ℓ𝔽≤ℓℭ : ℓ𝔽 ≤ ℓℭ
 -- ℓ𝔽≤ℓℭ = Lift-≤-Lift 𝔽≤ℭ

 Pℭ : ℭ ∈ P (Lift-class 𝒦)
 Pℭ = {!!}

 SPℭ : ℭ ∈ S (P (Lift-class 𝒦))
 SPℭ = ℭ , (Pℭ , ≤-reflexive)


 -- 𝔽∈SP : (Lift-Alg 𝔽[ X ] (ov (ov (α ⊔ ρ)))) ∈ (S{ov (α ⊔ ρ)}{ov (α ⊔ ρ)} (P{α}{ov (α ⊔ ρ)} 𝒦))
 -- 𝔽∈SP = {!!} -- ssub (class-prod-s-∈-sp hfe) 𝔽≤ℭ

 -- 𝕍𝒦 : Pred (SetoidAlgebra _ _) _
 -- 𝕍𝒦 = V 𝒦
 -- 𝔽-ModTh-epi : (𝑨 : SetoidAlgebra _ _) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
 -- 𝔽-ModTh-epi 𝑨 AinMTV = ?
\end{code}

#### The HSP Theorem
Now that we have all of the necessary ingredients, it is all but trivial to
combine them to prove Birkhoff's HSP theorem. (Note that since the proof enlists
the help of the `𝔽-ModTh-epi` theorem, we must assume an environment exists,
which is manifested in the premise `∀ 𝑨 → X ↠ 𝑨`.

begin{code}

 -- Birkhoff : Mod (Th (V 𝒦)) ⊆ V 𝒦
 -- Birkhoff {𝑨} AMod = vhimg {!!} {!!} -- vhimg{𝑩 = 𝑨} (𝔽∈𝕍 hfe) (𝑨 , epi-to-hom 𝑨 φE , snd ∥ φE ∥)
   -- where
   -- φE : epi 𝔽 𝑨
   -- φE = 𝔽-ModTh-epi 𝑨 (𝕏 𝑨) α

\end{code}

The converse inclusion, `V 𝒦 ⊆ Mod X (Th (V 𝒦))`, is a simple consequence of the
fact that `Mod Th` is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.

begin{code}

 -- Birkhoff-converse : V{α}{𝓕} 𝒦 ⊆ Mod{X = X} (Th (V 𝒦))
 -- Birkhoff-converse α p q pThq = pThq α

\end{code}

We have thus proved that every variety is an equational class.  Readers familiar
with the classical formulation of the Birkhoff HSP theorem, as an "if and only
if" result, might worry that we haven't completed the proof.  But recall that
in the [Varieties.Preservation][] module we proved the following identity
preservation lemmas:

* `𝒦 ⊫ p ≈ q → H 𝒦 ⊫ p ≈ q`
* `𝒦 ⊫ p ≈ q → S 𝒦 ⊫ p ≈ q`
* `𝒦 ⊫ p ≈ q → P 𝒦 ⊫ p ≈ q`

From these it follows that every equational class is a variety. Thus, our formal
proof of Birkhoff's theorem is complete.







 -- recall, 𝔽[ X ] : SetoidAlgebra oα oα
 -- 𝔽∈SP : 𝔽[ X ] ∈ S{ooα}{ooα} (P{α}{ooα} 𝒦)
 -- 𝔽∈SP = ssub {!SPℭ!} {!!}
 𝔽[X]∈SP : 𝔽[ X ] ∈ S (P 𝒦)
 𝔽[X]∈SP = Goal -- ssub {!SPℭ!} {!!}
  where
  lC : SetoidAlgebra _ _
  lC = Lift-Alg ℭ oα oα
  SPlC : lC ∈ S (P 𝒦)
  SPlC = sk→lsk SPℭ
   -- A≤B×B≅C→A≤C : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
  C≤lC : ℭ ≤ lC
  C≤lC = {!!}
  𝔽≤lC : 𝔽[ X ] ≤ lC
  𝔽≤lC = ≤-trans 𝔽[ X ]{𝑩 = ℭ} lC {!𝔽≤ℭ!} C≤lC -- A≤B×B≅C→A≤C {!𝔽≤ℭ!} {!!}
  Goal : 𝔽[ X ] ∈ S (P 𝒦)
  Goal = ssub {!SPℭ!} {!!}

 𝔽[X]∈V : 𝔽[ X ] ∈ V 𝒦
 𝔽[X]∈V = {!!}

 -- module _ (ρ : Carrier (Env 𝕏))(𝑨 : SetoidAlgebra oα oα)(A∈ModThK : 𝑨 ∈ Mod (Th{X = 𝕏} (V 𝒦))) where
 --  open Environment 𝑨 renaming (Env to EnvA)
 --  open Setoid (EnvA 𝕏) using () renaming ( Carrier to X→A )
 --  𝕏↠A : Σ[ h ∈ X→A ] isSurj{𝑨 = ≡.setoid 𝕏}{𝑩 = Domain 𝑨} h
 --  𝕏↠A = {!!} -- Goal
 --   where
 --   Goal : Σ[ h ∈ X→A ] isSurj{𝑨 = ≡.setoid 𝕏}{𝑩 = Domain 𝑨} h
 --   Goal = {!!} , {!!}

 --  𝔽-ModTh-epi : epi 𝔽 𝑨
 --  𝔽-ModTh-epi = goal
 --   where
 --   η : 𝕏 → 𝕌[ 𝑨 ]
 --   η = ∣ 𝕏↠A ∣
 --   φ : hom (𝑻 𝕏) 𝑨
 --   φ = lift-hom{𝑨 = 𝑨} η
 --   φE : IsSurjective ∣ φ ∣
 --   φE = lift-of-epi-is-epi η ∥ 𝕏↠A ∥
  -- pqlem2 : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝑨 ⊧ p ≈ q
  -- pqlem2 p q z = λ x → AinMTV p q (kernel-in-theory z) x

  -- kerincl : kernel ∣ hom𝔽 ∣ ⊆ kernel ∣ φ ∣
  -- kerincl {p , q} x = ∣ φ ∣ p      ≡⟨ (free-lift-interp (wd 𝓥 𝓕⁺) 𝑨 η p)⁻¹ ⟩
  --                     (𝑨 ⟦ p ⟧) η  ≡⟨ pqlem2 p q x η ⟩
  --                     (𝑨 ⟦ q ⟧) η  ≡⟨ free-lift-interp (wd 𝓥 𝓕⁺) 𝑨 η q ⟩
  --                     ∣ φ ∣ q      ∎
   -- goal : epi 𝔽 𝑨
   -- goal = {!!} -- ∣ HomFactorEpi 𝑨 φ hom𝔽 kerincl hom𝔽-is-epic φE)




------------------------------------------------------------------------------------------
 -- Alternative representation of the relatively free algebra is by the quotient
 -- with respect to the kernel of homℭ.


  -- 𝕏↠A : Σ[ h ∈ X→A ] isSurj{𝑨 = ≡.setoid 𝕏}{𝑩 = Domain 𝑨} h
  -- 𝕏↠A = {!!} -- Goal
  --  where
  --  Goal : Σ[ h ∈ X→A ] isSurj{𝑨 = ≡.setoid 𝕏}{𝑩 = Domain 𝑨} h
  --  Goal = {!!} , {!!}



 -- 𝔽 : SetoidAlgebra ooα oα
 -- 𝔽 = kerquo homℭ


 -- 𝔽≤ℭ' : 𝔽[ 𝕏 ] ≤ ℭ
 -- 𝔽≤ℭ' = {!!} , {!!}

 -- 𝔽≤ℭ : 𝔽 ≤ ℭ
 -- 𝔽≤ℭ = FirstHomCorollary homℭ


 -- 𝔽≅𝔽[𝕏] : 𝔽 ≅ 𝔽[ 𝕏 ]
 -- 𝔽≅𝔽[𝕏] = mkiso to𝕏 from𝕏 to𝕏∼from𝕏 from𝕏∼to𝕏
 --  where
 --  open SetoidAlgebra 𝔽[ 𝕏 ] using ( Interp ) renaming ( Domain to FX )
 --  open Setoid FX using () renaming ( _≈_  to _≈FX≈_ ; refl to reflFX ; Carrier to ∣FX∣ )
 --  open SetoidAlgebra 𝔽 using () renaming ( Domain to F )
 --  open Setoid F using () renaming ( _≈_  to _≈F≈_ ; refl to reflF ; Carrier to ∣F∣ )

 --  toXfunc : F ⟶ FX
 --  toXfunc ⟨$⟩ x = x
 --  cong toXfunc {x} {y} xy = {!!}
 --  to𝕏 : hom 𝔽 𝔽[ 𝕏 ]
 --  to𝕏 = toXfunc , {!!}
 --  from𝕏 : hom 𝔽[ 𝕏 ] 𝔽
 --  from𝕏 = {!!}
 --  to𝕏∼from𝕏 : (b : ∣FX∣) → (∣ to𝕏 ∣ ⟨$⟩ (∣ from𝕏 ∣ ⟨$⟩ b)) ≈FX≈ b
 --  to𝕏∼from𝕏 = {!!}
 --  from𝕏∼to𝕏 : (a : ∣F∣) → (∣ from𝕏 ∣ ⟨$⟩ (∣ to𝕏 ∣ ⟨$⟩ a)) ≈F≈ a
 --  from𝕏∼to𝕏 = {!!}



 skEqual : {X : Type χ}(p q : Term X) → Type (χ ⊔ oα)
 skEqual p q = ((𝑨 : SetoidAlgebra α α)(sA : 𝑨 ∈ S 𝒦) → (Environment.Equal 𝑨 p q))

 AllEqual⊆ker𝔽 : {X : Type χ}{p q : Term X}
  →              skEqual p q → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣
 AllEqual⊆ker𝔽 {X} {p} {q} x = Goal
  where
  open SetoidAlgebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
  open Setoid F using () renaming ( _≈_  to _≈F≈_ ; refl to reflF )
  S𝒦⊫pq : S 𝒦 ⊫ (p ≈̇ q)
  S𝒦⊫pq 𝑨 sA ρ = x 𝑨 sA ρ
  Goal : p ≈F≈ q
  Goal = 𝒦⊫→ℰ⊢ (S-id2{p = p}{q} S𝒦⊫pq)






-->
