
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥} where

open  import Data.Product     using ( Σ-syntax ; _,_ ; _×_ )
                              renaming ( proj₁ to fst ; proj₂ to snd )
open  import Function         using ( _∘_ ; id )
open  import Level            using (Level )
open  import Relation.Binary  using ( IsEquivalence )

open  import Relation.Binary.PropositionalEquality as ≡
      using ( module ≡-Reasoning ; _≡_ )

open import Base.Relations         using ( ⌞_⌟ ; mkblk ; ⟪_⟫ )
open import Overture               using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Functions         using ( Image_∋_ ; IsInjective ; SurjInv )
                                   using ( IsSurjective ; SurjInvIsInverseʳ )

open import Base.Algebras {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; Con ; IsCongruence )

open  import Base.Homomorphisms.Kernels {𝑆 = 𝑆}
      using ( kercon ; ker[_⇒_]_↾_ ; πker )

open  import Base.Equality
      using ( swelldef ; is-set ; blk-uip ; is-embedding ; monic-is-embedding|Set )
      using ( pred-ext ; block-ext|uip )

open  import Base.Homomorphisms.Basic {𝑆 = 𝑆}
      using ( hom ; is-homomorphism ; epi ; epi→hom )

private variable α β γ : Level

open ≡-Reasoning

FirstHomTheorem|Set : (𝑨 : Algebra α)(𝑩 : Algebra β)(h : hom 𝑨 𝑩)
 {- extensionality assumptions -}  (pe : pred-ext α β)(fe : swelldef 𝓥 β)
 {- truncation assumptions -}      (Bset : is-set ∣ 𝑩 ∣)
                                   (buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe {𝑩} h ∣)
 →   Σ[ φ ∈ hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩  ]
     ( ∣ h ∣ ≡ ∣ φ ∣ ∘ ∣ πker fe{𝑩}h ∣ × IsInjective ∣ φ ∣  ×  is-embedding ∣ φ ∣  )

FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip = (φ , φhom) , ≡.refl , φmon , φemb
 where
  θ : Con 𝑨
  θ = kercon fe{𝑩} h
  ξ : IsEquivalence ∣ θ ∣
  ξ = IsCongruence.is-equivalence ∥ θ ∥

  φ : ∣ (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) ∣ → ∣ 𝑩 ∣
  φ a = ∣ h ∣ ⌞ a ⌟

  φhom : is-homomorphism (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩 φ
  φhom 𝑓 a =  ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌞ a x ⌟) )  ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌞ a x ⌟)  ⟩
              (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌞ a x ⌟))  ≡⟨ ≡.cong (𝑓 ̂ 𝑩) ≡.refl     ⟩
              (𝑓 ̂ 𝑩) (λ x → φ (a x))            ∎

  φmon : IsInjective φ
  φmon {_ , mkblk u ≡.refl} {_ , mkblk v ≡.refl} φuv = block-ext|uip pe buip ξ φuv

  φemb : is-embedding φ
  φemb = monic-is-embedding|Set φ Bset φmon

FirstIsoTheorem|Set : (𝑨 : Algebra α) (𝑩 : Algebra β) (h : hom 𝑨 𝑩)
 {- extensionality assumptions -}  (pe : pred-ext α β) (fe : swelldef 𝓥 β)
 {- truncation assumptions -}      (Bset : is-set ∣ 𝑩 ∣)
                                   (buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe{𝑩}h ∣)
 →                                 IsSurjective ∣ h ∣
 →                                 Σ[ f ∈ (epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)]
                                   ( ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
                                   × IsInjective ∣ f ∣ × is-embedding ∣ f ∣ )

FirstIsoTheorem|Set 𝑨 𝑩 h pe fe Bset buip hE =
 (fmap , fhom , fepic) , ≡.refl , (snd ∥ FHT ∥)
  where
  FHT = FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip

  fmap : ∣ ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe ∣ → ∣ 𝑩 ∣
  fmap = fst ∣ FHT ∣

  fhom : is-homomorphism (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩 fmap
  fhom = snd ∣ FHT ∣

  fepic : IsSurjective fmap
  fepic b = Goal where
   a : ∣ 𝑨 ∣
   a = SurjInv ∣ h ∣ hE b

   bfa : b ≡ fmap ⟪ a ⟫
   bfa = ((SurjInvIsInverseʳ ∣ h ∣ hE) b)⁻¹

   Goal : Image fmap ∋ b
   Goal = Image_∋_.eq ⟪ a ⟫ bfa

module _ {fe : swelldef 𝓥 β}(𝑨 : Algebra α)(𝑩 : Algebra β)(h : hom 𝑨 𝑩) where

 FirstHomUnique :  (f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                ∀ a  →  ∣ f ∣ a ≡ ∣ g ∣ a

 FirstHomUnique f g hfk hgk (_ , mkblk a ≡.refl) =
  ∣ f ∣ (_ , mkblk a ≡.refl)  ≡⟨ ≡.cong-app(hfk ⁻¹)a ⟩
  ∣ h ∣ a                     ≡⟨ ≡.cong-app(hgk)a ⟩
  ∣ g ∣ (_ , mkblk a ≡.refl)  ∎

 FirstIsoUnique :  (f g : epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                ∀ a → ∣ f ∣ a ≡ ∣ g ∣ a

 FirstIsoUnique f g hfk hgk = FirstHomUnique (epi→hom 𝑩 f) (epi→hom 𝑩 g) hfk hgk

