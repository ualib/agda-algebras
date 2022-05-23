---
layout: default
title : "Base.Structures.Sigma.Homs"
date : "2021-06-22"
author: "agda-algebras development team"
---

#### <a id="homomorphisms-of-general-structures">Homomorphisms of general structures</a>


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Structures.Sigma.Homs where

-- Imports from the Agda Standard Library ----------------------------------------------------------
open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Level           using ( Level ; Lift ; lift ; lower )
open import Function.Base   using ( _∘_ ; id )
open import Relation.Binary.PropositionalEquality
                            using ( _≡_ ;  cong ; refl ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Base.Overture.Preliminaries  using ( ∣_∣ ; ∥_∥ ; _∙_ ; _⁻¹)
open import Base.Overture.Injective      using ( IsInjective )
open import Base.Overture.Surjective     using ( IsSurjective )
open import Base.Relations.Discrete      using ( _|:_ ; 0[_] ; ker )
open import Base.Relations.Quotients     using ( Equivalence ; Quotient ; 0[_]Equivalence )
                                         using ( ker-IsEquivalence ; kerlift-IsEquivalence )
                                         using ( ⟪_⟫ ; ⌞_⌟ ; ⟪_∼_⟫-elim ; _/_ )
open import Base.Equality.Welldefined    using ( swelldef )
open import Base.Structures.Sigma.Basic  using ( Signature ; Structure ; Compatible ; _ʳ_ ; _ᵒ_ )
                                         using ( Lift-Strucʳ ; Lift-Strucˡ ; Lift-Struc )
private variable 𝑅 𝐹 : Signature

-- Development for Structures (Sigma type representation)

module _ {α ρᵃ : Level}
         (𝑨 : Structure  𝑅 𝐹 {α}{ρᵃ})
         {β ρᵇ : Level}
         (𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}) where

 preserves : ∣ 𝑅 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 preserves r h = ∀ a → ((r ʳ 𝑨) a) → ((r ʳ 𝑩) (h ∘ a))

 is-hom-rel : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 is-hom-rel h = ∀ r →  preserves r h

 comp-op : ∣ 𝐹 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ β)
 comp-op f h = ∀ a → h ((f ᵒ 𝑨) a) ≡ (f ᵒ 𝑩) (h ∘ a)

 is-hom-op : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ β)
 is-hom-op h = ∀ f → comp-op f h

 is-hom : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-hom h = is-hom-rel h × is-hom-op h

 hom : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 hom = Σ[ h ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-hom h



module _ {𝑅 𝐹 : Signature}
         {α ρᵃ : Level}(𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ})
         {β ρᵇ : Level}{𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}}
         {γ ρᶜ : Level}(𝑪 : Structure 𝑅 𝐹 {γ}{ρᶜ}) where

 ∘-is-hom-rel : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →             is-hom-rel 𝑨 𝑩 f → is-hom-rel 𝑩 𝑪 g → is-hom-rel 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-rel {f}{g} fhr ghr R a = λ z → ghr R (λ z₁ → f (a z₁)) (fhr R a z)

 ∘-is-hom-op : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →            is-hom-op 𝑨 𝑩 f → is-hom-op 𝑩 𝑪 g → is-hom-op 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-op {f}{g} fho gho 𝑓 a = cong g (fho 𝑓 a) ∙ gho 𝑓 (f ∘ a)

 ∘-is-hom : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →         is-hom 𝑨 𝑩 f → is-hom 𝑩 𝑪 g → is-hom 𝑨 𝑪 (g ∘ f)
 ∘-is-hom {f} {g} fhro ghro = ihr , iho
  where
  ihr : is-hom-rel 𝑨 𝑪 (g ∘ f)
  ihr = ∘-is-hom-rel {f}{g} (fst fhro) (fst ghro)

  iho : is-hom-op 𝑨 𝑪 (g ∘ f)
  iho = ∘-is-hom-op {f}{g} (snd fhro) (snd ghro)

 ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪 → hom 𝑨 𝑪
 ∘-hom (f , fh) (g , gh) = g ∘ f , ∘-is-hom {f}{g} fh gh


module _ {α ρ : Level} where

 𝒾𝒹 : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → hom 𝑨 𝑨
 𝒾𝒹 _ = id , (λ R a z → z)  , (λ f a → refl)

module _ {α ρᵃ : Level}
         (𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ})
         {β ρᵇ : Level}
         (𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}) where

 is-mon : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-mon g = is-hom 𝑨 𝑩 g × IsInjective g

 mon : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 mon = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-mon g

 is-epi : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 is-epi g = is-hom 𝑨 𝑩 g × IsSurjective g

 epi : Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 epi = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-epi g

 mon→hom : mon → hom 𝑨 𝑩
 mon→hom ϕ = (fst ϕ) , fst (snd ϕ )

 epi→hom : epi → hom 𝑨 𝑩
 epi→hom ϕ = (fst ϕ) , fst (snd ϕ)


\end{code}

Next, `lift` and `lower` are (the maps of) homomorphisms.

\begin{code}


module _ {𝑅 𝐹 : Signature}
         {α ρᵃ : Level} where

 open Lift

 𝓁𝒾𝒻𝓉 : (ℓ ρ : Level)(𝑨 : Structure  𝑅 𝐹{α}{ρᵃ}) → hom 𝑨 (Lift-Struc ℓ ρ 𝑨)
 𝓁𝒾𝒻𝓉 = λ ℓ ρ 𝑨 → lift , ( (λ R a x → lift x) , λ f a → refl )

 𝓁ℴ𝓌ℯ𝓇 : (ℓ ρ : Level)(𝑨 : Structure  𝑅 𝐹{α}{ρᵃ}) → hom (Lift-Struc ℓ ρ 𝑨) 𝑨
 𝓁ℴ𝓌ℯ𝓇 = λ ℓ ρ 𝑨 → lower , (λ R a x → lower x) , (λ f a → refl)

module _ {𝑅 𝐹 : Signature}
         {α ρᵃ β ρᵇ : Level}{𝑅 𝐹 : Signature}
         {𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}}{𝑩 : Structure 𝑅 𝐹 {β}{ρᵇ}} where

 Lift-Hom : (ℓ ρ ℓ' ρ' : Level) → hom 𝑨 𝑩 → hom (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩)
 Lift-Hom ℓ ρ ℓ' ρ' (h , hhom) = lift ∘ h ∘ lower , Goal
  where
  lABh : is-hom (Lift-Struc ℓ ρ 𝑨) 𝑩 (h ∘ lower)
  lABh = ∘-is-hom{𝑅 = 𝑅}{𝐹} (Lift-Struc ℓ ρ 𝑨) 𝑩{lower}{h} ((λ R a x → lower x) , (λ f a → refl)) hhom

  Goal : is-hom (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩) (lift ∘ h ∘ lower)
  Goal = ∘-is-hom{𝑅 = 𝑅}{𝐹} (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩)
                {h ∘ lower}{lift} lABh ((λ R a x → lift x) , (λ f a → refl))

\end{code}



#### <a id="kernels-of-homomorphisms-of-structures-of-sigma-type">Kernels of homomorphisms of structures of sigma type</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation θ, there exists a homomorphism with kernel θ (namely, that canonical projection onto the quotient modulo θ).

\begin{code}

open ≡-Reasoning
module _ {𝑅 𝐹 : Signature}
         {α ρᵃ β ρᵇ : Level}
         {𝑨 : Structure 𝑅 𝐹 {α}{ρᵃ}}{𝑩 : Structure 𝑅 𝐹{β}{ρᵇ}} where

 Homker-comp : swelldef ℓ₀ β → (h : hom 𝑨 𝑩) → Compatible 𝑨 (ker ∣ h ∣)
 Homker-comp wd h f {u}{v} kuv = (∣ h ∣ ((f ᵒ 𝑨) u))  ≡⟨(snd ∥ h ∥) f u ⟩
                              ((f ᵒ 𝑩)(∣ h ∣ ∘ u)) ≡⟨ wd (f ᵒ 𝑩) (∣ h ∣ ∘ u) (∣ h ∣ ∘ v) kuv ⟩
                              ((f ᵒ 𝑩)(∣ h ∣ ∘ v)) ≡⟨((snd ∥ h ∥) f v)⁻¹ ⟩
                              (∣ h ∣((f ᵒ 𝑨) v))   ∎

\end{code}


--------------------------------

<br>

[← Base.Structures.Sigma.Congruences](Base.Structures.Sigma.Congruences.html)
<span style="float:right;">[Base.Structures.Sigma.Isos →](Base.Structures.Sigma.Isos.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team






<!-- ------- The rest is not yet integrated ------------------------------------------------

module _ {𝑅 𝐹 : Signature}
         {α ρᵃ β ρᵇ : Level}
         {𝑨 : Structure {α}{ρᵃ} 𝑅 𝐹}{𝑩 : Structure {β}{ρᵇ} 𝑅 𝐹} where

 KerCon : swelldef {!!} {!!} → Hom 𝑨 𝑩 → Con{α = α}{ρ = (β ⊔ ρᵃ)} (Lift-Strucʳ β 𝑨)
 KerCon wd h = θ , Cθ -- θ , Cθ
  where
  θ : Equivalence{α = α} ∣ 𝑨 ∣ {ρ = (α ⊔ β ⊔ ρᵃ)}
  θ = (λ x y → Lift (α ⊔ ρᵃ) (ker ∣ h ∣ x y)) , kerlift-IsEquivalence ∣ h ∣


  Cθ : Compatible (Lift-Strucʳ β 𝑨) ∣ θ ∣
  Cθ = {!Homker-comp{𝑨 = (Lift-Strucʳ β 𝑨)} wd (Lift-Hom ℓ₀ β ℓ₀ ℓ₀ h) ?!}

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.

begin{code}

module _ {α ρᵃ β ρᵇ : Level}{𝑅 𝐹 : Signature}
         {𝑨 : Structure {α}{ρᵃ} 𝑅 𝐹}{𝑩 : Structure {β}{ρᵇ} 𝑅 𝐹} where
 KerQuo : Hom 𝑨 𝑩 → Structure 𝑅 𝐹
 KerQuo h = {!!} -- 𝑨 ╱ KerCon{𝑨 = 𝑨}{𝑩 = 𝑩}{wd = wd} h
module _ {𝑨 : Structure {α} {ℓ₀} 𝑅 𝐹} {wd : swelldef ℓ₀ ℓ₀ } where
 KerQuo : {𝑩 : Structure {ℓ₀} {ℓ₀} 𝑅  𝐹} → Hom 𝑨 𝑩 → Structure {lsuc α} {ℓ₀} 𝑅 𝐹 -- lsuc ℓ₀ ⊔ α
 KerQuo {𝑩 = 𝑩} h = {!!} -- 𝑨 ╱ KerCon{𝑨 = 𝑨}{𝑩 = 𝑩}{wd = wd} h

module _ {α β ρ ρ : Level} {𝑨 : Structure {ρ} 𝑅 𝐹 {α}} where

 kerquo : {𝑩 : Structure {ρ} 𝑅 𝐹 {β}} → hom 𝑨 𝑩 → Structure {ρ} 𝑅 𝐹 {lsuc ρ ⊔ α} --  {𝓤 ⊔ lsuc 𝓦}
 kerquo {𝑩 = 𝑩} h = 𝑨 ╱ {!kercon h!} -- (kercon {𝑩 = 𝑩} h)


ker[_⇒_]_ : (𝑨 : Structure{ρ} 𝑅 𝐹 {α})(𝑩 : Structure{ρ} 𝑅 𝐹 {β}) → hom 𝑨 𝑩 → Structure 𝑅 𝐹
ker[ 𝑨 ⇒ 𝑩 ] h = kerquo {𝑩 = 𝑩} h

\end{code}

Thus, given `h : hom 𝑨 𝑩`, we can construct the quotient of `𝑨` modulo the kernel of `h`, and the syntax for this quotient in the [agda-algebras](https://github.com/ualib/agda-algebras) library is `𝑨 [ 𝑩 ]/ker h ↾ fe`.


#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.

begin{code}

module _ {𝑩 : Structure 𝑅 𝐹 {β}} where
 open Image_∋_
 πepi : (θ : Con{α} 𝑩) → epi 𝑩 (𝑩 ╱ θ)
 πepi θ = (λ a → ⟪ a / ∣ θ ∣ ⟫) , (γrel , (λ _ _ → refl)) , cπ-is-epic  where  -- (λ _ _ → refl)
  γrel : IsHom-rel 𝑩 (𝑩 ╱ θ) (λ a → ⟪ a / ∣ θ ∣ ⟫)
  γrel R a x = {!!}
  cπ-is-epic : IsSurjective (λ a → ⟪ a / ∣ θ ∣ ⟫)
  cπ-is-epic (C , (a , Ca)) =  eq (C , (a , Ca)) a λ i → {!!} , {!!} -- Image_∋_.im a

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.


 πhom : (θ : Con{𝓤}{𝓦} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)

begin{code}

 πker : (wd : swelldef 𝓥 𝓦){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩) → epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)
 πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.


 open IsCongruence

 ker-in-con : {wd : swelldef 𝓥 (𝓤 ⊔ lsuc 𝓦)}(θ : Con 𝑨)
  →           ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

 ker-in-con θ hyp = /-≡ θ hyp

\end{code}


#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra 𝓦 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.

begin{code}

module _ {𝓘 𝓦 : Level}{I : Type 𝓘}(ℬ : I → Algebra 𝓦 𝑆) where

 ⨅-hom-co : funext 𝓘 𝓦 → {𝓤 : Level}(𝑨 : Algebra 𝓤 𝑆) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co fe 𝑨 𝒽 = ((λ a i → ∣ 𝒽 i ∣ a)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra 𝓤 𝑆 and ℬ : I → Algebra 𝓦 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.

begin{code}

 ⨅-hom : funext 𝓘 𝓦 → {𝓤 : Level}(𝒜 : I → Algebra 𝓤 𝑆) → Π[ i ꞉ I ] hom (𝒜 i)(ℬ i) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.

begin{code}

 ⨅-projection-hom : Π[ i ꞉ I ] hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.

\end{code}

-->
















(Notice, it is here that the `swelldef` postulate comes into play, and because it is needed to prove `homker-comp`, it is postulated by all the lemmas below that depend upon `homker-comp`.)

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.


 kercon : swelldef 𝓥 𝓦 → {𝑩 : Algebra 𝓦 𝑆} → hom 𝑨 𝑩 → Con{𝓤}{𝓦} 𝑨
 kercon wd {𝑩} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.


 kerquo : swelldef 𝓥 𝓦 → {𝑩 : Algebra 𝓦 𝑆} → hom 𝑨 𝑩 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆
 kerquo wd {𝑩} h = 𝑨 ╱ (kercon wd {𝑩} h)


ker[_⇒_]_↾_ : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → hom 𝑨 𝑩 → swelldef 𝓥 𝓦 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆
ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo wd {𝑩} h

\end{code}

Thus, given `h : hom 𝑨 𝑩`, we can construct the quotient of `𝑨` modulo the kernel of `h`, and the syntax for this quotient in the [agda-algebras](https://github.com/ualib/agda-algebras) library is `𝑨 [ 𝑩 ]/ker h ↾ fe`.



#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.


module _ {𝓤 𝓦 : Level}{𝑨 : Algebra 𝓤 𝑆} where
 πepi : (θ : Con{𝓤}{𝓦} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫)
  cπ-is-epic (C , (a , refl)) =  Image_∋_.im a

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.


 πhom : (θ : Con{𝓤}{𝓦} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)


 πker : (wd : swelldef 𝓥 𝓦){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩) → epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)
 πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.


 open IsCongruence

 ker-in-con : {wd : swelldef 𝓥 (𝓤 ⊔ lsuc 𝓦)}(θ : Con 𝑨)
  →           ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

 ker-in-con θ hyp = /-≡ θ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra 𝓦 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.


module _ {𝓘 𝓦 : Level}{I : Type 𝓘}(ℬ : I → Algebra 𝓦 𝑆) where

 ⨅-hom-co : funext 𝓘 𝓦 → {𝓤 : Level}(𝑨 : Algebra 𝓤 𝑆) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra 𝓤 𝑆 and ℬ : I → Algebra 𝓦 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.


 ⨅-hom : funext 𝓘 𝓦 → {𝓤 : Level}(𝒜 : I → Algebra 𝓤 𝑆) → Π[ i ꞉ I ] hom (𝒜 i)(ℬ i) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.


 ⨅-projection-hom : Π[ i ꞉ I ] hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.

--------------------------------

<span style="float:left;">[← Base.Structures.Sigma.Congruences](Base.Structures.Sigma.Congruences.html)</span>
<span style="float:right;">[Base.Structures.Sigma.Isos →](Base.Structures.Sigma.Isos.html)</span>

{% include UALib.Links.md %}
