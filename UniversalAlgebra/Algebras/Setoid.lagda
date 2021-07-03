---
layout: default
title : Algebras.Basic module (Agda Universal Algebra Library)
date : 2021-04-23
author: [the agda-algebras development team][]
---

### <a id="algebras">Basic Definitions</a>

This is the [Algebras.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Algebras.Setoid {𝑆 : Signature 𝓞 𝓥} where

-- -- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality  using    ( _≡_     ;   refl         )
open import Agda.Primitive         using    ( _⊔_                      )
                                   renaming ( Set     to Type          )
open import Category.Functor
open import Data.Product           using    ( _,_     ;  _×_
                                            ; Σ       ;  Σ-syntax      )
                                   renaming ( proj₁   to fst
                                             ; proj₂  to snd           )
open import Function               using    ( _∘_ ; id )
open import Function.Base          using    ( _on_    ; flip           )
open import Function.Bundles       using    ( Func                     )
open import Level                  renaming ( suc     to lsuc          )
open import Relation.Binary.Core   using    ( _=[_]⇒_ )
open import Relation.Binary        using    ( Setoid  ;  IsEquivalence )
                                   renaming ( Rel     to BinRel        )
import Relation.Binary.PropositionalEquality as PE

open import Relation.Unary                        using    ( Pred  ; _⊆_ ; _∈_  )

-- Imports from the Agda Universal Algebra Library
open import Overture.Preliminaries using ( ∥_∥ ; ∣_∣ )
open import Overture.Inverses using ( IsInjective ; IsSurjective )
open import Relations.Discrete using ( _|:_)

private variable
 α ρ ι : Level

\end{code}

#### Models (again)

Here we define algebras over a setoid, instead of a mere type with no equivalence on it.

(This approach is inspired by the one taken, e.g., by Andreas Abel in his formalization Birkhoff's completeness theorem; see http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf.)

First we define an operator that translates an ordinary signature into a signature over a setoid domain.

\begin{code}

open Setoid using    (_≈_ ; Carrier )
            renaming ( refl  to reflS
                     ; sym   to symS
                     ; trans to transS
                     ; isEquivalence to isEqv )
open Func renaming   ( f to _<$>_ )

⟦_⟧s : Signature 𝓞 𝓥 → Setoid α ρ → Setoid _ _

Carrier (⟦ 𝑆 ⟧s ξ) = Σ[ f ∈ ∣ 𝑆 ∣ ] ((∥ 𝑆 ∥ f) → ξ .Carrier)
_≈_ (⟦ 𝑆 ⟧s ξ) (f , u) (g , v) = Σ[ eqv ∈ f ≡ g ] EqArgs eqv u v
 where
 EqArgs : f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type _
 EqArgs refl u v = ∀ i → (_≈_ ξ) (u i) (v i)

IsEquivalence.refl  (isEqv (⟦ 𝑆 ⟧s ξ))                     = refl , λ _ → reflS  ξ
IsEquivalence.sym   (isEqv (⟦ 𝑆 ⟧s ξ))(refl , g)           = refl , λ i → symS   ξ (g i)
IsEquivalence.trans (isEqv (⟦ 𝑆 ⟧s ξ))(refl , g)(refl , h) = refl , λ i → transS ξ (g i) (h i)

\end{code}


##### Setoid Algebras

A setoid algebra is just like an algebra but we require that all basic operations of the algebra respect the underlying setoid equality.
The `Func` record packs a function (f, aka apply, aka _<$>_) with a proof (cong) that the function respects equality.

\begin{code}

Algebroid : (α ρ : Level) → Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ))
Algebroid α ρ = Σ[ A ∈ Setoid α ρ ]      -- the domain (a setoid)
                 Func (⟦ 𝑆 ⟧s A) A       -- the basic operations,
                                         -- along with congruence proofs that
                                         -- each operation espects setoid equality

record SetoidAlgebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
  field
    Domain : Setoid α ρ
    Interp : Func (⟦ 𝑆 ⟧s Domain) Domain
     --      ^^^^^^^^^^^^^^^^^^^^^^^ is a record type with two fields:
     --       1. a function  f : Carrier (⟦ 𝑆 ⟧s Domain)  → Carrier Domain
     --       2. a proof cong : f Preserves _≈₁_ ⟶ _≈₂_ (that f preserves the setoid equalities)


open SetoidAlgebra

-- Forgetful Functor
𝕌[_] : SetoidAlgebra α ρ →  Type α
𝕌[ 𝑨 ] = Carrier (Domain 𝑨)

𝔻[_] : SetoidAlgebra α ρ →  Setoid α ρ
𝔻[ 𝑨 ] = Domain 𝑨


-- Easier notation for application of an (interpreted) operation symbol.

_∙_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebroid α ρ) → (∥ 𝑆 ∥ f  →  Carrier ∣ 𝑨 ∣) → Carrier ∣ 𝑨 ∣

f ∙ 𝑨 = λ a → ∥ 𝑨 ∥ <$> (f , a)

open SetoidAlgebra
open RawFunctor

_̂_ : (f : ∣ 𝑆 ∣)(𝑨 : SetoidAlgebra α ρ) → (∥ 𝑆 ∥ f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]

f ̂ 𝑨 = λ a → (Interp 𝑨) <$> (f , a)

\end{code}

\end{code}

#### Products of Algebroids

\begin{code}

open Func           using    ( cong                     )
                    renaming ( f             to  _<$>_  )
open Setoid         using    ( Carrier       ;   _≈_    )
                    renaming ( isEquivalence to  isEqv  )
open IsEquivalence  renaming ( refl          to  reflE
                             ; sym           to  symE
                             ; trans         to  transE )

⨅ : {I : Type ι }(𝒜 : I → Algebroid α ρ) → Algebroid (α ⊔ ι) (ρ ⊔ ι)

⨅ {I} 𝒜 = domain , interp
 where
 domain : Setoid _ _
 domain = record { Carrier = ∀ i → Carrier ∣ 𝒜 i ∣
                 ; _≈_ = λ u v  → ∀ i → (_≈_ ∣ 𝒜 i ∣) (u i) (v i)
                 ; isEquivalence =
                    record { refl  =     λ i → reflE  (isEqv ∣ 𝒜 i ∣)
                           ; sym   =   λ x i → symE   (isEqv ∣ 𝒜 i ∣)(x i)
                           ; trans = λ u v i → transE (isEqv ∣ 𝒜 i ∣)(u i)(v i)
                           }
                 }

 interp : Func (⟦ 𝑆 ⟧s domain) domain
 interp <$> (f , as ) = λ i → ∥ 𝒜 i ∥ <$> (f , (flip as i ))
 cong  interp (refl , f=g) i = cong  ∥ 𝒜 i ∥ (refl , (flip f=g i))

\end{code}





#### Products of SetoidAlgebras

\begin{code}

open SetoidAlgebra

⨅s : {I : Type ι }(𝒜 : I → SetoidAlgebra α ρ) → SetoidAlgebra (α ⊔ ι) (ρ ⊔ ι)

Domain (⨅s {I} 𝒜) =

 record { Carrier = ∀ i → Carrier (Domain (𝒜 i))

        ; _≈_ = λ a b → ∀ i → Domain (𝒜 i) ._≈_ (a i) (b i)

        ; isEquivalence =
           record { refl  =     λ i → reflE  (isEqv (Domain (𝒜 i)))
                  ; sym   =   λ x i → symE   (isEqv (Domain (𝒜 i)))(x i)
                  ; trans = λ x y i → transE (isEqv (Domain (𝒜 i)))(x i)(y i)
                  }
        }

(Interp (⨅s {I} 𝒜)) <$> (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
cong (Interp (⨅s {I} 𝒜)) (refl , f=g ) = λ i → cong  (Interp (𝒜 i)) (refl , flip f=g i )


module _ {𝒦 : Pred (Algebroid α ρ) (𝓞 ⊔ 𝓥 ⊔ lsuc α)} where

 ℑ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ))
 ℑ = Σ[ 𝑨 ∈ (Algebroid α ρ) ] 𝑨 ∈ 𝒦

\end{code}

Taking the product over the index type `ℑ` requires a function that maps an
index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`,
where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the
function mapping an index to the corresponding algebra is simply the first
projection.

\begin{code}

 𝔄 : ℑ → Algebroid α ρ
 𝔄 i = ∣ i ∣

\end{code}

Finally, we define `class-product` which represents the product of all members of 𝒦.

\begin{code}

 class-product : Algebroid (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) _
 class-product = ⨅ 𝔄

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.

#### Level lifting setoid algebra types

\begin{code}

open Lift
Lift-SetoidAlg : SetoidAlgebra α ρ → (β : Level) → SetoidAlgebra (α ⊔ β) ρ
Domain (Lift-SetoidAlg 𝑨 β) =
 record { Carrier = Lift β 𝕌[ 𝑨 ]
        ; _≈_ = λ x y → (Domain 𝑨 ≈ (lower x))(lower y)
        ; isEquivalence =
           record { refl = reflS (Domain 𝑨)
                  ; sym = symS (Domain 𝑨)
                  ; trans = transS (Domain 𝑨)
                  }
        }
(Interp (Lift-SetoidAlg 𝑨 β)) <$> (f , la) = lift ((f ̂ 𝑨) (lower ∘ la))
cong (Interp (Lift-SetoidAlg 𝑨 β)) {(f , la)} {(.f , lb)} (refl , la=lb) = cong (Interp 𝑨) ((refl , la=lb))


\end{code}

What makes the `Lift-Alg` type so useful for resolving type level errors
involving algebras is the nice properties it possesses.  Indeed, the
[UniversalAlgebra][] library contains formal proofs of the following facts.

+ [`Lift-Alg` is a homomorphism](Homomorphisms.Basic.html#exmples-of-homomorphisms)
 (see [Homomorphisms.Basic][]) 

+ [`Lift-Alg` is an algebraic invariant](Homomorphisms.Isomorphisms.html#lift-is-an-algebraic-invariant")
  (see [Homomorphisms.Isomorphisms][])

+ [`Lift-Alg` of a subalgebra is a subalgebra](Subalgebras.Subalgebras.html#lifts-of-subalgebras)
  (see [Subalgebras.Subalgebras][])

+ [`Lift-Alg` preserves identities](Varieties.EquationalLogic.html#lift-invariance))
  (see [Varieties.EquationalLogic][])


### Homomorphisms for setoid algebras

\begin{code}

module _ {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
         {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ) where

 private
  A = 𝕌[ 𝑨 ] -- (𝕌 = forgetful functor)
  B = 𝕌[ 𝑩 ]

 compatible-op-map : ∣ 𝑆 ∣ → (A → B) → Type _
 compatible-op-map 𝑓 h = ∀ a → h ((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑩) (h ∘ a)

 -- The property of being a homomorphism.
 is-homomorphism : (A → B) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 is-homomorphism h = ∀ 𝑓  →  compatible-op-map 𝑓 h

 -- The type of homomorphisms from `𝑨` to `𝑩`.
 hom : Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 hom = Σ (A → B) is-homomorphism

-- The composition of homomorphisms is again a homomorphism.

open PE.≡-Reasoning
open PE renaming (cong to ≡-cong)

module _ {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
         {β ρᵇ : Level} {𝑩 : SetoidAlgebra β ρᵇ}
         {γ ρᶜ : Level} (𝑪 : SetoidAlgebra γ ρᶜ) where

 private
  A = 𝕌[ 𝑨 ]  -- carrier of domain of 𝑨
  B = 𝕌[ 𝑩 ]
  C = 𝕌[ 𝑪 ]


 ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
 ∘-hom (g , ghom) (h , hhom) = h ∘ g , Goal where

  Goal : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)
  Goal 𝑓 a = (h ∘ g)((𝑓 ̂ 𝑨) a)     ≡⟨ ≡-cong h ( ghom 𝑓 a ) ⟩
             h ((𝑓 ̂ 𝑩)(g ∘ a))     ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
             (𝑓 ̂ 𝑪)(h ∘ g ∘ a)     ∎


 ∘-is-hom : {f : A → B}{g : B → C}
  →         is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g → is-homomorphism 𝑨 𝑪 (g ∘ f)
 ∘-is-hom {f} {g} fhom ghom = ∥ ∘-hom (f , fhom) (g , ghom) ∥

-- Some important homs
-- 1. the identity homs
𝒾𝒹 : (𝑨 : SetoidAlgebra α ρ) → hom 𝑨 𝑨
𝒾𝒹 _ = id , λ 𝑓 a → refl
open Level
-- 2. the lift hom
𝓁𝒾𝒻𝓉 : {β : Level}(𝑨 : SetoidAlgebra α ρ) → hom 𝑨 (Lift-SetoidAlg 𝑨 β)
𝓁𝒾𝒻𝓉 _ = lift , (λ 𝑓 a → refl)
-- 3. the lower hom
𝓁ℴ𝓌ℯ𝓇 : {β : Level}(𝑨 : SetoidAlgebra α ρ) → hom (Lift-SetoidAlg 𝑨 β) 𝑨
𝓁ℴ𝓌ℯ𝓇 _ = (lower , λ 𝑓 a → refl)

module _ {α ρᵃ : Level} {𝑨 : SetoidAlgebra α ρᵃ}
         (ℓᵃ : Level)
         {β ρᵇ : Level}{𝑩 : SetoidAlgebra β ρᵇ}
         (ℓᵇ : Level) where

 Lift-hom : hom 𝑨 𝑩  →  hom (Lift-SetoidAlg 𝑨 ℓᵃ) (Lift-SetoidAlg 𝑩 ℓᵇ)

 Lift-hom (f , fhom) = lift ∘ f ∘ lower , Goal
  where
  lABh : is-homomorphism (Lift-SetoidAlg 𝑨 ℓᵃ) 𝑩 (f ∘ lower)
  lABh = ∘-is-hom (Lift-SetoidAlg 𝑨 ℓᵃ){𝑩 = 𝑨}  𝑩 {lower}{f} (λ _ _ → refl) fhom

  Goal : is-homomorphism(Lift-SetoidAlg 𝑨 ℓᵃ)(Lift-SetoidAlg 𝑩 ℓᵇ) (lift ∘ (f ∘ lower))
  Goal = ∘-is-hom (Lift-SetoidAlg 𝑨 ℓᵃ){𝑩 = 𝑩} (Lift-SetoidAlg 𝑩 ℓᵇ) {f ∘ lower}{lift} lABh λ _ _ → refl


-- Monomorphisms and epimorphisms
module _ {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
         {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ) where

 private
  A = 𝕌[ 𝑨 ]  -- carrier of domain of 𝑨
  B = 𝕌[ 𝑩 ]

 is-monomorphism : (A → B) → Type _
 is-monomorphism g = is-homomorphism 𝑨 𝑩 g × IsInjective g

 mon : Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 mon = Σ[ g ∈ (A → B) ] is-monomorphism g

 is-epimorphism : (A → B) → Type _
 is-epimorphism g = is-homomorphism 𝑨 𝑩 g × IsSurjective g

 epi : Type _
 epi = Σ[ g ∈ (A → B) ] is-epimorphism g


-- The "hom reduct" of a mon
-- N.B. 𝑨 explicit, 𝑩 implicit
module _ {α ρᵃ : Level} (𝑨 : SetoidAlgebra α ρᵃ)
         {β ρᵇ : Level} {𝑩 : SetoidAlgebra β ρᵇ} where

 mon-to-hom : mon 𝑨 𝑩 → hom 𝑨 𝑩
 mon-to-hom ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥


-- The "hom reduct" of an epi
-- N.B. 𝑨 implicit, 𝑩 explicit
module _ {α ρᵃ : Level} {𝑨 : SetoidAlgebra α ρᵃ}
         {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ) where

 epi-to-hom : epi 𝑨 𝑩 → hom 𝑨 𝑩
 epi-to-hom ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

\end{code}






#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation θ, there exists a homomorphism with kernel θ (namely, that canonical projection onto the quotient modulo θ).


module _ {α β : Level}{𝑨 : Algebra α 𝑆} where

 homker-comp : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆}(h : hom 𝑨 𝑩) → compatible 𝑨 (ker ∣ h ∣)
 homker-comp wd {𝑩} h f {u}{v} kuv = ∣ h ∣((f ̂ 𝑨) u)   ≡⟨ ∥ h ∥ f u ⟩
                                     (f ̂ 𝑩)(∣ h ∣ ∘ u) ≡⟨ wd(f ̂ 𝑩)(∣ h ∣ ∘ u)(∣ h ∣ ∘ v)kuv ⟩
                                     (f ̂ 𝑩)(∣ h ∣ ∘ v) ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
                                     ∣ h ∣((f ̂ 𝑨) v)   ∎


\end{code}

(Notice, it is here that the `swelldef` postulate comes into play, and because it is needed to prove `homker-comp`, it is postulated by all the lemmas below that depend upon `homker-comp`.)

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.


 kercon : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆} → hom 𝑨 𝑩 → Con{α}{β} 𝑨
 kercon wd {𝑩} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.


 kerquo : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆} → hom 𝑨 𝑩 → Algebra (α ⊔ lsuc β) 𝑆
 kerquo wd {𝑩} h = 𝑨 ╱ (kercon wd {𝑩} h)


ker[_⇒_]_↾_ : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → hom 𝑨 𝑩 → swelldef 𝓥 β → Algebra (α ⊔ lsuc β) 𝑆
ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo wd {𝑩} h

\end{code}

Thus, given `h : hom 𝑨 𝑩`, we can construct the quotient of `𝑨` modulo the kernel of `h`, and the syntax for this quotient in the [UniversalAlgebra][] library is `𝑨 [ 𝑩 ]/ker h ↾ fe`.



#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.


module _ {α β : Level}{𝑨 : Algebra α 𝑆} where
 πepi : (θ : Con{α}{β} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫)
  -- <<<<<<< Quotients
  -- cπ-is-epic (C , R-block a refl ) =  Image_∋_.im a
  -- =======
  -- cπ-is-epic (C , (a , refl)) =  Image_∋_.eq a refl
  -- >>>>>>> master
  -- wjd: not sure how this conflict occurred, but the following line seems to resolve it.
  cπ-is-epic (C , R-block a refl ) =  Image_∋_.eq a refl

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.


 πhom : (θ : Con{α}{β} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)


 πker : (wd : swelldef 𝓥 β){𝑩 : Algebra β 𝑆}(h : hom 𝑨 𝑩) → epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)
 πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.


 open IsCongruence

 ker-in-con : {wd : swelldef 𝓥 (α ⊔ lsuc β)}(θ : Con 𝑨)
  →           ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

 ker-in-con θ hyp = /-≡ θ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra β 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.


module _ {𝓘 β : Level}{I : Type 𝓘}(ℬ : I → Algebra β 𝑆) where

 ⨅-hom-co : funext 𝓘 β → {α : Level}(𝑨 : Algebra α 𝑆) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra α 𝑆 and ℬ : I → Algebra β 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.


 ⨅-hom : funext 𝓘 β → {α : Level}(𝒜 : I → Algebra α 𝑆) → (∀ (i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.


 ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.


--------------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
