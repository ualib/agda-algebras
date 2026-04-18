
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Level            using ( Level )
open import Overture  using ( 𝓞 ; 𝓥 ; Signature )
module Base.Varieties.FreeAlgebras {α : Level} {𝑆 : Signature 𝓞 𝓥} where

open  import Agda.Primitive   using ( _⊔_ )renaming  ( Set to Type )
open  import Data.Product     using ( _,_ ; Σ-syntax ; _×_ )
                              renaming  ( proj₁ to fst ; proj₂ to snd )
open  import Function         using ( _∘_ )
open  import Level            using ( suc )
open  import Relation.Binary  using ( IsEquivalence ) renaming  ( Rel to BinRel )
open  import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ ; ｛_｝ ; _∪_ )

open  import Axiom.Extensionality.Propositional
      using () renaming  (Extensionality to funext)
open  import Relation.Binary.PropositionalEquality as ≡
      using ( _≡_ ; module ≡-Reasoning )

open  import Overture        using ( ∣_∣ ; ∥_∥ ; _∙_ ; _⁻¹ )
open  import Base.Functions  using ( IsSurjective )
open  import Base.Relations  using ( kernel ; ⟪_⟫ )
open  import Base.Equality
      using ( SwellDef ; swelldef ; is-set ; blk-uip ; hfunext ; DFunExt; pred-ext )

open  import Base.Algebras {𝑆 = 𝑆}
      using ( Algebra ; Lift-Alg ; compatible;  _̂_ ; ov ; ⨅ ; Con; mkcon ; IsCongruence )
open  import Base.Homomorphisms {𝑆 = 𝑆}
      using ( hom ; epi ; epi→hom ; kercon ; ker-in-con ; πker ; ker[_⇒_]_↾_ ; ∘-hom )
      using ( ⨅-hom-co ; HomFactor ; HomFactorEpi ; _≅_ ; ≅-refl ; ≅-sym ; Lift-≅ )
open  import Base.Terms {𝑆 = 𝑆}
      using ( Term ; 𝑻 ; free-lift ; lift-hom ; free-unique ; _⟦_⟧ )
      using ( lift-of-epi-is-epi ; comm-hom-term; free-lift-interp )
open  import Base.Subalgebras {𝑆 = 𝑆}
      using ( _≤_ ; FirstHomCorollary|Set )

open  import Base.Varieties.EquationalLogic {𝑆 = 𝑆}
      using ( _⊫_≈_; _⊧_≈_; Th; Mod )
open  import Base.Varieties.Closure {𝑆 = 𝑆}
      using ( S ; P ; V )
open  import Base.Varieties.Preservation {𝑆 = 𝑆}
      using ( module class-products-with-maps ; class-ids-⇒ ; class-ids ; SP⊆V')

open Term ; open S ; open V

𝓕 𝓕⁺ : Level
𝓕 = ov α
𝓕⁺ = suc (ov α)    -- (this will be the level of the free algebra)

module _ {X : Type α}(𝒦 : Pred (Algebra α) 𝓕) where

 ψ : Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) 𝓕
 ψ (p , q) = ∀(𝑨 : Algebra α)(sA : 𝑨 ∈ S{α}{α} 𝒦)(h : X → ∣ 𝑨 ∣ )
                 →  (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q

 ψRel : BinRel ∣ 𝑻 X ∣ 𝓕
 ψRel p q = ψ (p , q)

 open ≡-Reasoning

 ψcompatible : swelldef 𝓥 α → compatible (𝑻 X) ψRel
 ψcompatible wd 𝑓 {p} {q} ψpq 𝑨 sA h = γ
  where
  φ : hom (𝑻 X) 𝑨
  φ = lift-hom 𝑨 h

  γ : ∣ φ ∣ ((𝑓 ̂ 𝑻 X) p) ≡ ∣ φ ∣ ((𝑓 ̂ 𝑻 X) q)

  γ = ∣ φ ∣ ((𝑓 ̂ 𝑻 X) p)  ≡⟨ ∥ φ ∥ 𝑓 p ⟩
      (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ p)  ≡⟨ wd (𝑓 ̂ 𝑨)(∣ φ ∣ ∘ p)(∣ φ ∣ ∘ q)(λ x → ψpq x 𝑨 sA h) ⟩
      (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ q)  ≡⟨ (∥ φ ∥ 𝑓 q)⁻¹ ⟩
      ∣ φ ∣ ((𝑓 ̂ 𝑻 X) q)  ∎

 ψIsEquivalence : IsEquivalence ψRel
 ψIsEquivalence = record  { refl = λ 𝑨 sA h → ≡.refl
                          ; sym = λ x 𝑨 sA h → (x 𝑨 sA h)⁻¹
                          ; trans = λ pψq qψr 𝑨 sA h → (pψq 𝑨 sA h) ∙ (qψr 𝑨 sA h) }

 ψCon : swelldef 𝓥 α → Con (𝑻 X)
 ψCon wd = ψRel , mkcon ψIsEquivalence (ψcompatible wd)

module _ {fe : DFunExt}{wd : SwellDef}{X : Type α} {𝒦 : Pred (Algebra α) 𝓕} where

 open class-products-with-maps {X = X}{fe 𝓕 α}{fe 𝓕⁺ 𝓕⁺}{fe 𝓕 𝓕} 𝒦

 ℭ : Algebra 𝓕
 ℭ = ⨅ 𝔄'

 homℭ : hom (𝑻 X) ℭ
 homℭ = ⨅-hom-co 𝔄' (fe 𝓕 α){𝓕}(𝑻 X) λ i → lift-hom (𝔄' i)(snd ∥ i ∥)

 𝔽 : Algebra 𝓕⁺
 𝔽 = ker[ 𝑻 X ⇒ ℭ ] homℭ ↾ (wd 𝓥 (ov α))

 epi𝔽 : epi (𝑻 X) 𝔽
 epi𝔽 = πker (wd 𝓥 (ov α)) {ℭ} homℭ

 hom𝔽 : hom (𝑻 X) 𝔽
 hom𝔽 = epi→hom 𝔽 epi𝔽

 hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
 hom𝔽-is-epic = snd ∥ epi𝔽 ∥

 ψlemma0 : ∀ p q →  ∣ homℭ ∣ p ≡ ∣ homℭ ∣ q  → (p , q) ∈ ψ 𝒦
 ψlemma0 p q phomℭq 𝑨 sA h = ≡.cong-app phomℭq (𝑨 , sA , h)

 ψlemma0-ap : {𝑨 : Algebra α}{h : X → ∣ 𝑨 ∣} → 𝑨 ∈ S{α}{α} 𝒦
  →           kernel ∣ hom𝔽 ∣ ⊆ kernel (free-lift 𝑨 h)

 ψlemma0-ap {𝑨}{h} skA {p , q} x = γ where

  ν : ∣ homℭ ∣ p ≡ ∣ homℭ ∣ q
  ν = ker-in-con {α = (ov α)}{ov α}{𝑻 X}{wd 𝓥 (suc (ov α))}(kercon (wd 𝓥 (ov α)) {ℭ} homℭ) {p}{q} x

  γ : (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q
  γ = ((ψlemma0 p q) ν) 𝑨 skA h

 𝔽-lift-hom : (𝑨 : Algebra α) → 𝑨 ∈ S{α}{α} 𝒦 → (X → ∣ 𝑨 ∣) → hom 𝔽 𝑨
 𝔽-lift-hom 𝑨 skA h = fst(HomFactor (wd 𝓥 (suc (ov α)))  𝑨 (lift-hom 𝑨 h) hom𝔽 (ψlemma0-ap skA) hom𝔽-is-epic)

 open IsCongruence

 X↪𝔽 : X → ∣ 𝔽 ∣
 X↪𝔽 x = ⟪ ℊ x ⟫ -- (the implicit relation here is  ⟨ kercon (fe 𝓥 𝓕) ℭ homℭ ⟩ )

 𝔑 : hom (𝑻 X) 𝔽
 𝔑 = lift-hom 𝔽 X↪𝔽

 open ≡-Reasoning

 hom𝔽-is-lift-hom : ∀ p → ∣ 𝔑 ∣ p ≡ ∣ hom𝔽 ∣ p
 hom𝔽-is-lift-hom (ℊ x) = ≡.refl
 hom𝔽-is-lift-hom (node 𝑓 𝒕) =
  ∣ 𝔑 ∣ (node 𝑓 𝒕)              ≡⟨ ∥ 𝔑 ∥ 𝑓 𝒕 ⟩
  (𝑓 ̂ 𝔽)(λ i → ∣ 𝔑 ∣(𝒕 i))     ≡⟨ wd-proof ⟩
  (𝑓 ̂ 𝔽)(λ i → ∣ hom𝔽 ∣ (𝒕 i)) ≡⟨ (∥ hom𝔽 ∥ 𝑓 𝒕)⁻¹ ⟩
  ∣ hom𝔽 ∣ (node 𝑓 𝒕)           ∎
   where wd-proof = wd 𝓥 (suc (ov α))
                    (𝑓 ̂ 𝔽) (λ i → ∣ 𝔑 ∣(𝒕 i)) (λ i → ∣ hom𝔽 ∣ (𝒕 i))
                    (λ x → hom𝔽-is-lift-hom(𝒕 x))

 ψlemma1 : kernel ∣ 𝔑 ∣ ⊆ ψ 𝒦
 ψlemma1 {p , q} 𝔑pq 𝑨 sA h = γ
  where
   f : hom 𝔽 𝑨
   f = 𝔽-lift-hom 𝑨 sA h

   h' φ : hom (𝑻 X) 𝑨
   h' = ∘-hom (𝑻 X) 𝑨 𝔑 f
   φ = lift-hom 𝑨 h

   h≡φ : ∀ t → (∣ f ∣ ∘ ∣ 𝔑 ∣) t ≡ ∣ φ ∣ t
   h≡φ t = free-unique (wd 𝓥 α) 𝑨 h' φ (λ x → ≡.refl) t

   γ : ∣ φ ∣ p ≡ ∣ φ ∣ q
   γ = ∣ φ ∣ p             ≡⟨ (h≡φ p)⁻¹ ⟩
       ∣ f ∣ ( ∣ 𝔑 ∣ p )   ≡⟨ ≡.cong ∣ f ∣ 𝔑pq ⟩
       ∣ f ∣ ( ∣ 𝔑 ∣ q )   ≡⟨ h≡φ q ⟩
       ∣ φ ∣ q             ∎

 ψlemma2 : kernel ∣ hom𝔽 ∣ ⊆ ψ 𝒦
 ψlemma2 {p , q} x = ψlemma1 {p , q} γ
   where
    γ : (free-lift 𝔽 X↪𝔽) p ≡ (free-lift 𝔽 X↪𝔽) q
    γ = (hom𝔽-is-lift-hom p) ∙ x ∙ (hom𝔽-is-lift-hom q)⁻¹

 ψlemma3 : ∀ p q → (p , q) ∈ ψ{X = X} 𝒦 → 𝒦 ⊫ p ≈ q
 ψlemma3 p q pψq {𝑨} kA h = goal
   where
   goal : (𝑨 ⟦ p ⟧) h ≡ (𝑨 ⟦ q ⟧) h
   goal = (𝑨 ⟦ p ⟧) h       ≡⟨ free-lift-interp (wd 𝓥 α) 𝑨 h p ⟩
          (free-lift 𝑨 h) p ≡⟨ pψq 𝑨 (siso (sbase kA) (≅-sym Lift-≅)) h ⟩
          (free-lift 𝑨 h) q ≡⟨ (free-lift-interp (wd 𝓥 α) 𝑨 h q)⁻¹  ⟩
          (𝑨 ⟦ q ⟧) h       ∎

 class-models-kernel : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝒦 ⊫ p ≈ q
 class-models-kernel p q x = ψlemma3 p q (ψlemma2 x)

 𝕍𝒦 : Pred (Algebra 𝓕⁺) (suc 𝓕⁺)
 𝕍𝒦 = V{α = α}{β = 𝓕⁺} 𝒦

 kernel-in-theory' : kernel ∣ hom𝔽 ∣ ⊆ Th (V 𝒦)
 kernel-in-theory' {p , q} pKq = (class-ids-⇒ fe wd p q (class-models-kernel p q pKq))

 kernel-in-theory : kernel ∣ hom𝔽 ∣ ⊆ Th 𝕍𝒦
 kernel-in-theory {p , q} pKq vkA x = class-ids fe wd p q (class-models-kernel p q pKq) vkA x

 _↠_ : Type α → Algebra 𝓕⁺ → Type 𝓕⁺
 X ↠ 𝑨 = Σ[ h ∈ (X → ∣ 𝑨 ∣) ] IsSurjective h

 𝔽-ModTh-epi : (𝑨 : Algebra 𝓕⁺) → (X ↠ 𝑨) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
 𝔽-ModTh-epi 𝑨 (η , ηE) AinMTV = goal
  where
  φ : hom (𝑻 X) 𝑨
  φ = lift-hom 𝑨 η

  φE : IsSurjective ∣ φ ∣
  φE = lift-of-epi-is-epi 𝑨 ηE

  pqlem2 : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝑨 ⊧ p ≈ q
  pqlem2 p q z = λ x → AinMTV p q (kernel-in-theory z) x

  kerincl : kernel ∣ hom𝔽 ∣ ⊆ kernel ∣ φ ∣
  kerincl {p , q} x = ∣ φ ∣ p      ≡⟨ (free-lift-interp (wd 𝓥 𝓕⁺) 𝑨 η p)⁻¹ ⟩
                      (𝑨 ⟦ p ⟧) η  ≡⟨ pqlem2 p q x η ⟩
                      (𝑨 ⟦ q ⟧) η  ≡⟨ free-lift-interp (wd 𝓥 𝓕⁺) 𝑨 η q ⟩
                      ∣ φ ∣ q      ∎

  goal : epi 𝔽 𝑨
  goal = fst (HomFactorEpi (wd 𝓥 (suc (ov α))) 𝑨 φ hom𝔽 kerincl hom𝔽-is-epic φE)

 module _ (pe : pred-ext (ov α)(ov α))(wd : SwellDef) -- extensionality assumptions
          (Cset : is-set ∣ ℭ ∣)                       -- truncation assumptions
          (kuip : blk-uip(Term X)∣ kercon (wd 𝓥 (ov α)){ℭ}homℭ ∣)
  where

  𝔽≤ℭ : (ker[ 𝑻 X ⇒ ℭ ] homℭ ↾ (wd 𝓥 (ov α))) ≤ ℭ
  𝔽≤ℭ = FirstHomCorollary|Set (𝑻 X) ℭ homℭ pe (wd 𝓥 (ov α)) Cset kuip

  𝔽∈SP : hfunext (ov α)(ov α) → 𝔽 ∈ (S{𝓕}{𝓕⁺} (P{α}{𝓕} 𝒦))
  𝔽∈SP hfe = ssub (class-prod-s-∈-sp hfe) 𝔽≤ℭ

  𝔽∈𝕍 : hfunext (ov α)(ov α) → 𝔽 ∈ V 𝒦
  𝔽∈𝕍 hfe = SP⊆V' {α}{fe 𝓕 α}{fe 𝓕⁺ 𝓕⁺}{fe 𝓕 𝓕}{𝒦} (𝔽∈SP hfe)

  Birkhoff : hfunext (ov α)(ov α) → (∀ 𝑨 → X ↠ 𝑨) → Mod (Th (V 𝒦)) ⊆ V 𝒦
  Birkhoff hfe 𝕏 {𝑨} α = vhimg{𝑩 = 𝑨} (𝔽∈𝕍 hfe) (𝑨 , epi→hom 𝑨 φE , snd ∥ φE ∥)
   where
   φE : epi 𝔽 𝑨
   φE = 𝔽-ModTh-epi 𝑨 (𝕏 𝑨) α

  Birkhoff-converse : V{α}{𝓕} 𝒦 ⊆ Mod{X = X} (Th (V 𝒦))
  Birkhoff-converse α p q pThq = pThq α

