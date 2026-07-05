---
layout: default
title : "Setoid.Homomorphisms.Isomoprhisms module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

#### Isomorphisms of setoid algebras

This is the [Setoid.Homomorphisms.Factor][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Isomorphisms {𝑆 : Signature 𝓞 𝓥}  where

-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Agda.Primitive              using () renaming ( Set to Type )
open import Data.Product                using ( _,_ ; proj₁ ; proj₂ )
open import Data.Unit.Polymorphic.Base  using ()      renaming ( ⊤ to 𝟙 ; tt to ∗ )
open import Data.Unit.Base              using ( ⊤ ; tt )
open import Function                    using ()  renaming ( Func to _⟶_ )
open import Level                       using ( Level ; Lift ; lift ; lower ; _⊔_ )
open import Relation.Binary             using ( Setoid ; Reflexive ; Sym ; Trans )

open import Relation.Binary.PropositionalEquality as ≡ using ()

-- Imports from the Agda Universal Algebra Library -----------------------------------------
open import Overture                         using  ( OperationSymbolsOf ; ArityOf )
open import Overture.Operations              using  ( Op )
open import Setoid.Functions                 using  ( eq ; IsInjective
                                                    ; IsSurjective ; SurjInv
                                                    ; SurjInvIsInverseʳ )
open import Setoid.Algebras {𝑆 = 𝑆}          using  ( Algebra ; Lift-Alg ; _^_ ; 𝔻[_]
                                                    ; 𝕌[_] ; mkAlgebra ; Lift-Algˡ
                                                    ; Lift-Algʳ ; ⨅ )

open import Setoid.Homomorphisms.Basic       using  ( hom ; IsHom ; 𝒾𝒹 ; mkIsHom )
open import Setoid.Homomorphisms.Properties  using  ( ⊙-hom ; ToLiftˡ ; FromLiftˡ
                                                    ; ToFromLiftˡ ; FromToLiftˡ
                                                    ; ToLiftʳ ; FromLiftʳ
                                                    ; ToFromLiftʳ ; FromToLiftʳ )

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

private variable  α ρᵃ β ρᵇ γ ρᶜ ι : Level
```

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e.,
`∀ x, f x ≡ g x`.  We use this notion of equality of functions in the following
definition of *isomorphism*.

We could define this using Sigma types, as in

    _≅_ : {α β : Level}(𝑨 : Algebra α 𝑆)(𝑩 : Algebra β ρᵇ) → Type _
    𝑨 ≅ 𝑩 =  Σ[ (f , _) ∈ hom 𝑨 𝑩 ] Σ[ (g , _) ∈ hom 𝑩 𝑨 ]
               ((f ∘ g ≈ (proj₁ (𝒾𝒹 𝑩))) × (g ∘ f ≈ (proj₁ (𝒾𝒹 𝑨))))

However, with four components, an equivalent record type is easier to work with.

```agda
module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
  open Setoid 𝔻[ 𝑨 ] using ( sym ; trans ) renaming ( _≈_ to _≈₁_ )
  open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈₂_ ; sym to sym₂ ; trans to trans₂)

  record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ) where
    constructor mkiso
    field
      to : hom 𝑨 𝑩
      from : hom 𝑩 𝑨
      to∼from : ∀ b → to .proj₁ ⟨$⟩ (from .proj₁ ⟨$⟩ b) ≈₂ b
      from∼to : ∀ a → from .proj₁ ⟨$⟩ (to .proj₁ ⟨$⟩ a) ≈₁ a

    toIsSurjective : IsSurjective (to .proj₁)
    toIsSurjective {y} = eq (from .proj₁ ⟨$⟩ y) (sym₂ (to∼from y))

    toIsInjective : IsInjective (to .proj₁)
    toIsInjective {x} {y} xy = Goal
      where
      ξ : from .proj₁ ⟨$⟩ (to .proj₁ ⟨$⟩ x) ≈₁ from .proj₁ ⟨$⟩ (to .proj₁ ⟨$⟩ y)
      ξ = cong (from .proj₁) xy
      Goal : x ≈₁ y
      Goal = trans (sym (from∼to x)) (trans ξ (from∼to y))

    fromIsSurjective : IsSurjective (from .proj₁)
    fromIsSurjective {y} = eq (to .proj₁ ⟨$⟩ y) (sym (from∼to y))

    fromIsInjective : IsInjective (from .proj₁)
    fromIsInjective {x} {y} xy = Goal
      where
      ξ : to .proj₁ ⟨$⟩ (from .proj₁ ⟨$⟩ x) ≈₂ to .proj₁ ⟨$⟩ (from .proj₁ ⟨$⟩ y)
      ξ = cong (to .proj₁) xy
      Goal : x ≈₂ y
      Goal = trans₂ (sym₂ (to∼from x)) (trans₂ ξ (to∼from y))
```

That is, two structures are *isomorphic* provided there are homomorphisms going back
and forth between them which compose to the identity map.


#### Properties of isomorphism of setoid algebras

```agda
open _≅_

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ _ → refl) λ _ → refl
  where open Setoid 𝔻[ 𝑨 ] using ( refl )

≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ})(_≅_{β}{ρᵇ})(_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν
  where
  f : hom 𝑨 𝑪
  f = ⊙-hom (to ab) (to bc)

  g : hom 𝑪 𝑨
  g = ⊙-hom (from bc) (from ab)

  open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈₃_ ; trans to trans₃ )
  τ : ∀ b → f .proj₁ ⟨$⟩ (g .proj₁ ⟨$⟩ b) ≈₃ b
  τ b = trans₃ (cong (to bc .proj₁) (to∼from ab (from bc .proj₁ ⟨$⟩ b))) (to∼from bc b)

  open Setoid 𝔻[ 𝑨 ] using () renaming ( _≈_ to _≈₁_ ; trans to trans₁ )
  ν : ∀ a → g .proj₁ ⟨$⟩ (f .proj₁ ⟨$⟩ a) ≈₁ a
  ν a = trans₁ (cong (from ab .proj₁) (from∼to bc (to ab .proj₁ ⟨$⟩ a))) (from∼to ab a)

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
 -- The "to" map of an isomorphism is injective.
 ≅toInjective : (φ : 𝑨 ≅ 𝑩) → IsInjective (proj₁ (to φ))
 ≅toInjective (mkiso (f , _) (g , _) _ g∼f){a₀}{a₁} fafb = Goal
   where
   open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; sym ; trans )
   lem1 : a₀ ≈ g ⟨$⟩ (f ⟨$⟩ a₀)
   lem1 = sym (g∼f a₀)

   lem2 : g ⟨$⟩ (f ⟨$⟩ a₀) ≈ g ⟨$⟩ (f ⟨$⟩ a₁)
   lem2 = cong g fafb

   lem3 : g ⟨$⟩ (f ⟨$⟩ a₁) ≈ a₁
   lem3 = g∼f a₁

   Goal : a₀ ≈ a₁
   Goal = trans lem1 (trans lem2 lem3)

 -- The "from" map of an isomorphism is injective.
≅fromInjective : {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} (φ : 𝑨 ≅ 𝑩)
  → IsInjective (proj₁ (from φ))
≅fromInjective φ = ≅toInjective (≅-sym φ)
```


#### Direct construction versus the smart constructor

Building an algebra directly (as a `record` whose `Interp` field is written out by
hand) and building one with the `mkAlgebra`{.AgdaFunction} smart constructor of
[Setoid.Algebras.Basic][] produce *isomorphic* algebras, provided the two agree on
their carrier and their operations.  The witnessing isomorphism is the identity map:
the only content is that the operations match, so the homomorphism condition in each
direction is exactly the pointwise hypothesis `ops≈` (read forwards, then backwards).

Concretely, an algebra `𝑨`{.AgdaBound} is isomorphic to the algebra
`mkAlgebra 𝔻[ 𝑨 ] f cong-f` built on `𝑨`{.AgdaBound}'s *own* domain from any
operations `f`{.AgdaBound} that agree with `𝑨`{.AgdaBound}'s interpretation pointwise.
The bespoke `cong-f`{.AgdaBound} demanded by the smart constructor plays no role in the
isomorphism — only the operations do — so it is accepted but never inspected.

```agda
module _ {𝑨 : Algebra α ρᵃ} where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym )

  ≅-mkAlgebra : (f : (o : OperationSymbolsOf 𝑆) → Op (ArityOf 𝑆 o) 𝕌[ 𝑨 ])
    (cong-f : ∀ o {u v : ArityOf 𝑆 o → 𝕌[ 𝑨 ]} → (∀ i → u i ≈ v i) → f o u ≈ f o v)
    → (∀ o a → (o ^ 𝑨) a ≈ f o a)
    → 𝑨 ≅ mkAlgebra 𝔻[ 𝑨 ] f cong-f
  ≅-mkAlgebra f cong-f ops≈ =
    mkiso  (idF , mkIsHom λ {o}{a} → ops≈ o a)
           (idF , mkIsHom λ {o}{a} → sym (ops≈ o a))
           (λ _ → refl) (λ _ → refl)
    where
    -- the identity map on 𝑨's carrier, as a setoid function
    idF : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑨 ]
    idF ⟨$⟩ x   = x
    idF .cong x≈y = x≈y
```

Since the source `𝑨`{.AgdaBound} is arbitrary, it may itself be a smart-constructor
algebra: instantiating `≅-mkAlgebra`{.AgdaFunction} at `𝑨 = mkAlgebra 𝔻[ 𝑨 ] g cong-g`
shows directly that two `mkAlgebra`{.AgdaFunction} algebras on the same domain with
pointwise-equal operations are isomorphic, with no extra work.

#### A bijective homomorphism is an isomorphism

A homomorphism that is both injective and surjective is an isomorphism.  The witness
is the surjective right inverse `g = SurjInv h`, which is a *two-sided* inverse because
`h` is injective; and `g` is again a homomorphism — to see `g (f b) ≈ f (g ∘ b)` it
suffices, by injectivity of `h`, to compare the `h`-images, where `h ∘ g` cancels.
This is the converse of `≅toInjective`/`toIsSurjective` and lets one promote a
bijective `hom` to an `_≅_` without exhibiting the inverse homomorphism by hand.

```agda
module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
  open Algebra using ( Interp )
  open IsHom

  Bijective→≅ :  (h : hom 𝑨 𝑩) → IsInjective (proj₁ h) → IsSurjective (proj₁ h) → 𝑨 ≅ 𝑩
  Bijective→≅ h hM hE = mkiso h (g , gHom) (λ _ → invʳ) (λ _ → hM invʳ)
    where
    open Setoid 𝔻[ 𝑨 ]  using () renaming ( _≈_ to _≈₁_ )
    open Setoid 𝔻[ 𝑩 ]  using ( sym ; trans ) renaming ( _≈_ to _≈₂_ )

    hf : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]
    hf = proj₁ h

    -- the surjective right inverse of h, made two-sided by injectivity
    ginv : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
    ginv = SurjInv hf hE

    invʳ : ∀ {b} → hf ⟨$⟩ (ginv b) ≈₂ b
    invʳ = SurjInvIsInverseʳ hf hE

    -- ginv preserves setoid equality: pull b₀ ≈ b₁ back through h and cancel h ∘ ginv
    gcong : ∀ {b₀ b₁} → b₀ ≈₂ b₁ → ginv b₀ ≈₁ ginv b₁
    gcong b₀≈b₁ = hM (trans invʳ (trans b₀≈b₁ (sym invʳ)))

    g : 𝔻[ 𝑩 ] ⟶ 𝔻[ 𝑨 ]
    g = record { to = ginv ; cong = gcong }

    -- ginv is a homomorphism: compare h-images (h injective) and cancel h ∘ ginv
    gHom : IsHom 𝑩 𝑨 g
    compatible gHom {f}{b} =
     hM (trans invʳ (sym (trans (compatible (proj₂ h))
                                (cong (Interp 𝑩) (≡.refl , λ _ → invʳ)))))
```

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic
invariant*). As our focus is universal algebra, this is important and is what
makes the lift operation a workable solution to the technical problems that arise
from the noncumulativity of Agda's universe hierarchy.

```agda
module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
  Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
  Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})

  Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
  Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{ℓᵃ ℓᵇ : Level} where

  Lift-Alg-isoˡ : 𝑨 ≅ 𝑩 → Lift-Algˡ 𝑨 ℓᵃ ≅ Lift-Algˡ 𝑩 ℓᵇ
  Lift-Alg-isoˡ A≅B = ≅-trans (≅-trans (≅-sym Lift-≅ˡ ) A≅B) Lift-≅ˡ

  Lift-Alg-isoʳ : 𝑨 ≅ 𝑩 → Lift-Algʳ 𝑨 ℓᵃ ≅ Lift-Algʳ 𝑩 ℓᵇ
  Lift-Alg-isoʳ A≅B = ≅-trans (≅-trans (≅-sym Lift-≅ʳ ) A≅B) Lift-≅ʳ


Lift-Alg-iso : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{ℓᵃ rᵃ ℓᵇ rᵇ : Level}
  → 𝑨 ≅ 𝑩 → Lift-Alg 𝑨 ℓᵃ rᵃ ≅ Lift-Alg 𝑩 ℓᵇ rᵇ
Lift-Alg-iso {ℓᵇ = ℓᵇ} A≅B =
  ≅-trans  (Lift-Alg-isoʳ{ℓᵇ = ℓᵇ}(≅-trans (Lift-Alg-isoˡ{ℓᵇ = ℓᵇ} A≅B) (≅-sym Lift-≅ˡ)))
           (Lift-Alg-isoʳ Lift-≅ˡ)
```

The lift is also associative, up to isomorphism at least.

```agda
module _ {𝑨 : Algebra α ρᵃ}{ℓ₁ ℓ₂ : Level} where

  Lift-assocˡ : Lift-Algˡ 𝑨 (ℓ₁ ⊔ ℓ₂) ≅  Lift-Algˡ (Lift-Algˡ 𝑨 ℓ₁) ℓ₂
  Lift-assocˡ = ≅-trans (≅-trans (≅-sym Lift-≅ˡ) Lift-≅ˡ) Lift-≅ˡ

  Lift-assocʳ : Lift-Algʳ 𝑨 (ℓ₁ ⊔ ℓ₂) ≅  Lift-Algʳ (Lift-Algʳ 𝑨 ℓ₁) ℓ₂
  Lift-assocʳ = ≅-trans (≅-trans (≅-sym Lift-≅ʳ) Lift-≅ʳ) Lift-≅ʳ

Lift-assoc : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level}
  → Lift-Alg 𝑨 ℓ ρ ≅  Lift-Algʳ (Lift-Algˡ 𝑨 ℓ) ρ
Lift-assoc = ≅-trans (≅-sym Lift-≅) (≅-trans Lift-≅ˡ Lift-≅ʳ)

Lift-assoc' : {𝑨 : Algebra α α}{β γ : Level}
  → Lift-Alg 𝑨 (β ⊔ γ) (β ⊔ γ) ≅ Lift-Alg (Lift-Alg 𝑨 β β) γ γ
Lift-assoc' = ≅-trans (≅-sym Lift-≅) (≅-trans Lift-≅ Lift-≅)
```

Products of isomorphic families of algebras are themselves isomorphic.  The proof
looks a bit technical, but it is as straightforward as it ought to be.

```agda
module _ {𝓘 : Level}{I : Type 𝓘} {𝒜 : I → Algebra α ρᵃ} {ℬ : I → Algebra β ρᵇ} where
  ⨅≅ : (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ
  ⨅≅ AB = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ∼ψ ψ∼ϕ
    where
    ϕ : 𝔻[ ⨅ 𝒜 ] ⟶ 𝔻[ ⨅ ℬ ]
    ϕ ⟨$⟩ a    = λ i → to (AB i) .proj₁ ⟨$⟩ (a i)
    ϕ .cong a  = λ i → to (AB i) .proj₁ .cong (a i)

    open IsHom
    ϕhom : IsHom (⨅ 𝒜) (⨅ ℬ) ϕ
    ϕhom .compatible = λ i → to (AB i) .proj₂ .compatible

    ψ : 𝔻[ ⨅ ℬ ] ⟶ 𝔻[ ⨅ 𝒜 ]
    ψ ⟨$⟩ b    = λ i → from (AB i) .proj₁ ⟨$⟩ (b i)
    ψ .cong b  = λ i → from (AB i) .proj₁ .cong (b i)

    ψhom : IsHom (⨅ ℬ) (⨅ 𝒜) ψ
    ψhom .compatible = λ i → from (AB i) .proj₂ .compatible

    open Setoid
    ϕ∼ψ : ∀ b → 𝔻[ ⨅ ℬ ] ._≈_ (ϕ ⟨$⟩ (ψ ⟨$⟩ b)) b
    ϕ∼ψ b = λ i → to∼from (AB i) (b i)

    ψ∼ϕ : ∀ a → 𝔻[ ⨅ 𝒜 ] ._≈_ (ψ ⟨$⟩ (ϕ ⟨$⟩ a)) a
    ψ∼ϕ a = λ i → from∼to (AB i)(a i)
```

A nearly identical proof goes through for isomorphisms of lifted products.

```agda
module _
  {𝓘 : Level}{I : Type 𝓘}
  {𝒜 : I → Algebra α ρᵃ}
  {ℬ : (Lift γ I) → Algebra β ρᵇ} where


  Lift-Alg-⨅≅ˡ : (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Algˡ (⨅ 𝒜) γ ≅ ⨅ ℬ
  Lift-Alg-⨅≅ˡ AB = ≅-trans (≅-sym Lift-≅ˡ) A≅B
    where
    ϕ : 𝔻[ ⨅ 𝒜 ] ⟶ 𝔻[ ⨅ ℬ ]
    ϕ ⟨$⟩ a    = λ i → to (AB (lower i)) .proj₁ ⟨$⟩ a (lower i)
    ϕ .cong a  = λ i → to (AB (lower i)) .proj₁ .cong (a (lower i))

    open IsHom
    ϕhom : IsHom (⨅ 𝒜) (⨅ ℬ) ϕ
    ϕhom .compatible = λ i → to (AB (lower i)) .proj₂ .compatible

    ψ : 𝔻[ ⨅ ℬ ] ⟶ 𝔻[ ⨅ 𝒜 ]
    ψ ⟨$⟩ b    = λ i → from (AB i) .proj₁ ⟨$⟩ b (lift i)
    ψ .cong b  = λ i → from (AB i) .proj₁ .cong (b (lift i))

    ψhom : IsHom (⨅ ℬ) (⨅ 𝒜) ψ
    ψhom .compatible = λ i → from (AB i) .proj₂ .compatible

    open Setoid
    ϕ∼ψ : ∀ b → 𝔻[ ⨅ ℬ ] ._≈_ (ϕ ⟨$⟩ (ψ ⟨$⟩ b)) b
    ϕ∼ψ b = λ i → to∼from (AB (lower i)) (b i)

    ψ∼ϕ : ∀ a → 𝔻[ ⨅ 𝒜 ] ._≈_ (ψ ⟨$⟩ (ϕ ⟨$⟩ a)) a
    ψ∼ϕ a = λ i → from∼to (AB i)(a i)

    A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
    A≅B = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ∼ψ ψ∼ϕ

module _ {𝓘 : Level}{I : Type 𝓘} {𝒜 : I → Algebra α ρᵃ} where

   ⨅≅⨅ℓ : ∀ {ℓ} → ⨅ 𝒜 ≅ ⨅ (λ i → Lift-Alg (𝒜 (lower{ℓ = ℓ} i)) ℓ ℓ)
   ⨅≅⨅ℓ {ℓ} = mkiso (φ , φhom) (ψ , ψhom) φ∼ψ ψ∼φ
     where
     ⨅ℓ𝒜 : Algebra _ _
     ⨅ℓ𝒜 = ⨅ (λ i → Lift-Alg (𝒜 (lower{ℓ = ℓ} i)) ℓ ℓ)

     φ : 𝔻[ ⨅ 𝒜 ] ⟶ 𝔻[ ⨅ℓ𝒜 ]
     φ ⟨$⟩ x    = λ i → lift (x (lower i))
     φ .cong x  = λ i → lift (x (lower i))

     open IsHom
     φhom : IsHom (⨅ 𝒜) ⨅ℓ𝒜  φ
     φhom .compatible = λ i → lift (Setoid.refl 𝔻[ 𝒜 (lower i) ])

     ψ : 𝔻[ ⨅ℓ𝒜 ] ⟶ 𝔻[ ⨅ 𝒜 ]
     ψ ⟨$⟩ x    = λ i → lower (x (lift i))
     ψ .cong x  = λ i → lower (x (lift i))

     ψhom : IsHom ⨅ℓ𝒜 (⨅ 𝒜) ψ
     ψhom .compatible = λ i → Setoid.refl 𝔻[ 𝒜 i ]

     open Setoid
     φ∼ψ : ∀ b i → 𝔻[ Lift-Alg (𝒜 (lower i)) ℓ ℓ ] ._≈_ ((φ ⟨$⟩ (ψ ⟨$⟩ b)) i) (b i)
     φ∼ψ _ = λ i → lift (Setoid.reflexive 𝔻[ 𝒜 (lower i) ] ≡.refl)

     ψ∼φ : ∀ a i → 𝔻[ 𝒜 i ] ._≈_ ((ψ ⟨$⟩ (φ ⟨$⟩ a)) i) (a i)
     ψ∼φ _ = λ i → Setoid.reflexive 𝔻[ 𝒜  i ] ≡.refl

module _ {ι : Level}{I : Type ι}{𝒜 : I → Algebra α ρᵃ} where

   ⨅≅⨅ℓρ : ∀ {ℓ ρ} → ⨅ 𝒜 ≅ ⨅ (λ i → Lift-Alg (𝒜 i) ℓ ρ)
   ⨅≅⨅ℓρ {ℓ}{ρ} = mkiso φ ψ φ∼ψ ψ∼φ
     where
     φfunc : 𝔻[ ⨅ 𝒜 ] ⟶ 𝔻[ ⨅ (λ i → Lift-Alg (𝒜 i) ℓ ρ) ]
     φfunc ⟨$⟩ x    = λ i → lift (x i)
     φfunc .cong x  = λ i → lift (x i)

     open IsHom
     φhom : IsHom (⨅ 𝒜) (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ) φfunc
     φhom .compatible i = Setoid.refl 𝔻[ Lift-Alg (𝒜 i) ℓ ρ ]

     φ : hom (⨅ 𝒜) (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ)
     φ = φfunc , φhom

     ψfunc : 𝔻[ ⨅ (λ i → Lift-Alg (𝒜 i) ℓ ρ) ] ⟶ 𝔻[ ⨅ 𝒜 ]
     ψfunc ⟨$⟩ x    = λ i → lower (x i)
     ψfunc .cong x  = λ i → lower (x i)

     ψhom : IsHom (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ) (⨅ 𝒜) ψfunc
     ψhom .compatible = λ i → Setoid.refl 𝔻[ 𝒜 i ]

     ψ : hom (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ) (⨅ 𝒜)
     ψ = ψfunc , ψhom

     open Setoid 𝔻[ ⨅ (λ i → Lift-Alg (𝒜 i) ℓ ρ) ]  using () renaming ( _≈_ to _≈₂_ )
     φ∼ψ : ∀ b → φ .proj₁ ⟨$⟩ (ψ .proj₁ ⟨$⟩ b) ≈₂ b
     φ∼ψ _ = λ i → Setoid.reflexive 𝔻[ Lift-Alg (𝒜 i) ℓ ρ ] ≡.refl

     open Setoid 𝔻[ ⨅ 𝒜 ] using (reflexive) renaming ( _≈_ to _≈₁_ )
     ψ∼φ : ∀ a → ψ .proj₁ ⟨$⟩ (φ .proj₁ ⟨$⟩ a) ≈₁ a
     ψ∼φ _ = reflexive ≡.refl

module _ {ℓᵃ : Level}{I : Type ℓᵃ}{𝒜 : I → Algebra α ρᵃ}where
  open IsHom
  open Setoid   using (_≈_ )

  ⨅≅⨅lowerℓρ : ∀ {ℓ ρ} → ⨅ 𝒜 ≅ ⨅ λ i → Lift-Alg (𝒜 (lower{ℓ = α ⊔ ρᵃ} i)) ℓ ρ
  ⨅≅⨅lowerℓρ {ℓ}{ρ} = mkiso φ ψ φ∼ψ ψ∼φ
    where
    open Algebra(⨅ λ i → Lift-Alg(𝒜 (lower i)) ℓ ρ)  using() renaming ( Domain to ⨅lA )

    φfunc : 𝔻[ ⨅ 𝒜 ] ⟶ ⨅lA
    φfunc ⟨$⟩ x    = λ i → lift (x (lower i))
    φfunc .cong x  = λ i → lift (x (lower i))

    φhom : IsHom (⨅ 𝒜) (⨅ λ i → Lift-Alg (𝒜 (lower i)) ℓ ρ) φfunc
    φhom .compatible = λ i → Setoid.refl 𝔻[ Lift-Alg (𝒜 (lower i)) ℓ ρ ]

    φ : hom (⨅ 𝒜) (⨅ λ i → Lift-Alg (𝒜 (lower i)) ℓ ρ)
    φ = φfunc , φhom

    ψfunc : ⨅lA ⟶ 𝔻[ ⨅ 𝒜 ]
    ψfunc ⟨$⟩ x    = λ i → lower (x (lift i))
    ψfunc .cong x  = λ i → lower (x (lift i))

    ψhom : IsHom (⨅ λ i → Lift-Alg (𝒜 (lower i)) ℓ ρ) (⨅ 𝒜) ψfunc
    ψhom .compatible = λ i → Setoid.refl 𝔻[ 𝒜 i ]

    ψ : hom (⨅ λ i → Lift-Alg (𝒜 (lower i)) ℓ ρ) (⨅ 𝒜)
    ψ = ψfunc , ψhom

    φ∼ψ : ∀ b → ⨅lA ._≈_ (φ .proj₁ ⟨$⟩ (ψ .proj₁ ⟨$⟩ b)) b
    φ∼ψ _ = λ i → Setoid.reflexive 𝔻[ Lift-Alg (𝒜 (lower i)) ℓ ρ ] ≡.refl

    open Setoid 𝔻[ ⨅ 𝒜 ] using(reflexive ) renaming ( _≈_ to _≈₁_ )
    ψ∼φ : ∀ a → ψ .proj₁ ⟨$⟩ (φ .proj₁ ⟨$⟩ a) ≈₁ a
    ψ∼φ _ = reflexive ≡.refl

  ℓ⨅≅⨅ℓ : ∀ {ℓ} → Lift-Alg (⨅ 𝒜) ℓ ℓ ≅ ⨅ λ i → Lift-Alg (𝒜 (lower{ℓ = ℓ} i)) ℓ ℓ
  ℓ⨅≅⨅ℓ {ℓ} = mkiso (φ , φhom) (ψ , ψhom) φ∼ψ ψ∼φ -- φ∼ψ ψ∼φ
    where
    ℓ⨅𝒜 : Algebra _ _
    ℓ⨅𝒜 = Lift-Alg (⨅ 𝒜) ℓ ℓ
    ⨅ℓ𝒜 : Algebra _ _
    ⨅ℓ𝒜 = ⨅ (λ i → Lift-Alg (𝒜 (lower{ℓ = ℓ} i)) ℓ ℓ)

    φ : 𝔻[ ℓ⨅𝒜 ] ⟶ 𝔻[ ⨅ℓ𝒜 ]
    φ ⟨$⟩ x    = λ i → lift ((lower x)(lower i))
    φ .cong x  = λ i → lift ((lower x)(lower i))

    φhom : IsHom ℓ⨅𝒜 ⨅ℓ𝒜  φ
    φhom .compatible = λ i → lift (Setoid.refl 𝔻[ 𝒜 (lower i) ])

    ψ : 𝔻[ ⨅ℓ𝒜 ] ⟶ 𝔻[ ℓ⨅𝒜 ]
    ψ ⟨$⟩ x    = lift λ i → lower (x (lift i))
    ψ .cong x  = lift λ i → lower (x (lift i))

    ψhom : IsHom ⨅ℓ𝒜 ℓ⨅𝒜 ψ
    ψhom .compatible .lower = λ i → Setoid.refl 𝔻[ 𝒜 i ]

    φ∼ψ : ∀ b → 𝔻[ ⨅ℓ𝒜 ] ._≈_ (φ ⟨$⟩ (ψ ⟨$⟩ b)) b
    φ∼ψ _ i .lower = Setoid.reflexive 𝔻[ 𝒜 (lower i) ] ≡.refl

    ψ∼φ : ∀ a → 𝔻[ ℓ⨅𝒜 ] ._≈_ (ψ ⟨$⟩ (φ ⟨$⟩ a)) a
    ψ∼φ _ .lower = λ i → Setoid.reflexive 𝔻[ 𝒜  i ] ≡.refl

module _ {ι : Level}{𝑨 : Algebra α ρᵃ} where
  private
    to𝟙 : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ (λ (i : 𝟙{ι}) → 𝑨) ]
    to𝟙 ⟨$⟩ x = λ _ → x
    to𝟙 .cong xy = λ _ → xy
    from𝟙 : 𝔻[ ⨅ (λ (i : 𝟙{ι}) → 𝑨) ] ⟶ 𝔻[ 𝑨 ]
    from𝟙 ⟨$⟩ x = x ∗
    from𝟙 .cong xy = xy ∗

    open IsHom
    open Setoid 𝔻[ 𝑨 ] using ( refl )
    to𝟙IsHom : IsHom 𝑨 (⨅ (λ _ → 𝑨)) to𝟙
    to𝟙IsHom .compatible = λ _ → refl
    from𝟙IsHom : IsHom (⨅ (λ _ → 𝑨)) 𝑨 from𝟙
    from𝟙IsHom .compatible = refl

  ≅⨅⁺-refl : 𝑨 ≅ ⨅ (λ (i : 𝟙) → 𝑨)
  ≅⨅⁺-refl .to = to𝟙 , to𝟙IsHom
  ≅⨅⁺-refl .from = from𝟙 , from𝟙IsHom
  ≅⨅⁺-refl .to∼from = λ _ _ → refl
  ≅⨅⁺-refl .from∼to = λ _ → refl

module _ {𝑨 : Algebra α ρᵃ} where
  private
    to⊤ : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ (λ (i : ⊤) → 𝑨) ]
    to⊤ ⟨$⟩ x = λ _ → x
    to⊤ .cong xy = λ _ → xy

    from⊤ : 𝔻[ ⨅ (λ (i : ⊤) → 𝑨) ] ⟶ 𝔻[ 𝑨 ]
    from⊤ ⟨$⟩ x = x tt
    from⊤ .cong xy = xy tt

    open Setoid 𝔻[ 𝑨 ] using ( refl )
    open IsHom

    to⊤IsHom : IsHom 𝑨 (⨅ λ _ → 𝑨) to⊤
    to⊤IsHom .compatible = λ _ → refl

    from⊤IsHom : IsHom (⨅ λ _ → 𝑨) 𝑨 from⊤
    from⊤IsHom .compatible = refl

  ≅⨅-refl : 𝑨 ≅ ⨅ (λ (i : ⊤) → 𝑨)
  ≅⨅-refl .to = to⊤ , to⊤IsHom
  ≅⨅-refl .from = from⊤ , from⊤IsHom
  ≅⨅-refl .to∼from = λ _ _ → refl
  ≅⨅-refl .from∼to = λ _ → refl
```
