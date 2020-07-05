--FILE: birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--REF: Based on the file `birkhoff.agda` (23 Jan 2020).

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π')
open import relations using (ker-pred; Rel; con; _//_)
open import homomorphisms using (HOM; Hom; hom; is-homomorphism; 𝑯-closed)
open import terms using (Term; generator; 𝔉; _̇_; comm-hom-term';
                         lift-hom; interp-prod)

open import subuniverses using (Subuniverse; mksub; var; app; Sg;
          _is-subalgebra-of_; Subalgebra; 𝑺-closed; hom-image-alg)

-- open import closure using (_⊧_≈_; _⊧_≋)

module birkhoff
 {S : Signature 𝓞 𝓥}
 {𝓤 : Universe}
 {𝓤★ : Univalence}
 {X : 𝓤 ̇ } -- {X : 𝓧 ̇ }
 (gfe : global-dfunext)
 (dfe : dfunext 𝓤 𝓤)
 {X' : 𝓧 ̇ }  where

-- Duplicating definition of ⊧ so we don't have to import from closure module.
-- (Remove these definitions later once closure module is working.)
_⊧_≈_ : Algebra 𝓤 S
 →      Term{X = X} → Term → 𝓤 ̇

𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : Pred (Algebra 𝓤 S) 𝓦
 →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇

_⊧_≋_ 𝓚 p q = {A : Algebra _ S} → 𝓚 A → A ⊧ p ≈ q

--Equalizers of functions
𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
𝑬 g h x = g x ≡ h x

--Equalizers of homomorphisms
𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 S} (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x
--cf. definition 𝓔 in the homomorphisms module

𝑬𝑯-is-closed : funext 𝓥 𝓤
 →      {𝑓 : ∣ S ∣ } {𝑨 𝑩 : Algebra 𝓤 S}
        (g h : hom 𝑨 𝑩)  (𝒂 : (∥ S ∥ 𝑓) → ∣ 𝑨 ∣)
 →      ((x : ∥ S ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
        --------------------------------------------------
 →       ∣ g ∣ (∥ 𝑨 ∥ 𝑓 𝒂) ≡ ∣ h ∣ (∥ 𝑨 ∥ 𝑓 𝒂)

𝑬𝑯-is-closed fe {𝑓 = 𝑓}{𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ}
 (g , ghom)(h , hhom) 𝒂 p =
   g (Fᴬ 𝑓 𝒂)    ≡⟨ ghom 𝑓 𝒂 ⟩
   Fᴮ 𝑓 (g ∘ 𝒂)  ≡⟨ ap (Fᴮ _ )(fe p) ⟩
   Fᴮ 𝑓 (h ∘ 𝒂)  ≡⟨ (hhom 𝑓 𝒂)⁻¹ ⟩
   h (Fᴬ 𝑓 𝒂)    ∎

-- Equalizer of homs is a subuniverse.
𝑬𝑯-is-subuniverse : funext 𝓥 𝓤
 →  {𝑨 𝑩 : Algebra 𝓤 S}(g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}
𝑬𝑯-is-subuniverse fe {𝑨 = 𝑨} {𝑩 = 𝑩} g h =
 mksub (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h)
  λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑨 = 𝑨} {𝑩 = 𝑩} g h 𝒂 x

HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S}
           (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →         (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
         ---------------------------------------------------
 →        (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg {𝑨 = 𝑨} X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x
HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
 (g , ghom) (h , hhom) gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
  g (Fᴬ 𝑓 𝒂)     ≡⟨ ghom 𝑓 𝒂 ⟩
  Fᴮ 𝑓 (g ∘ 𝒂 )   ≡⟨ ap (Fᴮ 𝑓) (fe induction-hypothesis) ⟩
  Fᴮ 𝑓 (h ∘ 𝒂)    ≡⟨ ( hhom 𝑓 𝒂 )⁻¹ ⟩
  h ( Fᴬ 𝑓 𝒂 )   ∎
 where
  induction-hypothesis =
    λ x → HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
    (g , ghom)(h , hhom) gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

module _
 (gfe : global-dfunext)
 (𝓚 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
 where

 -- ⇒ (the "only if" direction)
 identities-are-compatible-with-homs : (p q : Term{X = X})
  →                𝓚 ⊧ p ≋ q
       ----------------------------------------------------
  →     ∀ 𝑨 KA h → ∣ h ∣ ∘ (p ̇ (𝔉{X = X})) ≡ ∣ h ∣ ∘ (q ̇ 𝔉)
 -- Here, the inferred types are
 -- 𝑨 : Algebra 𝓤 S, KA : 𝓚 𝑨, h : hom (𝔉{X = X}) 𝑨

 identities-are-compatible-with-homs p q 𝓚⊧p≋q 𝑨 KA h = γ
  where
   pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
   pA≡qA = 𝓚⊧p≋q KA

   pAh≡qAh : ∀(𝒂 : X → ∣ 𝔉 ∣)
    →        (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
   pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

   hpa≡hqa : ∀(𝒂 : X → ∣ 𝔉 ∣)
    →        ∣ h ∣ ((p ̇ 𝔉) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝔉) 𝒂)
   hpa≡hqa 𝒂 =
    ∣ h ∣ ((p ̇ 𝔉) 𝒂)  ≡⟨ comm-hom-term' gfe 𝔉 𝑨 h p 𝒂 ⟩
    (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
    (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term' gfe 𝔉 𝑨 h q 𝒂)⁻¹ ⟩
    ∣ h ∣ ((q ̇ 𝔉) 𝒂)  ∎

   γ : ∣ h ∣ ∘ (p ̇ 𝔉) ≡ ∣ h ∣ ∘ (q ̇ 𝔉)
   γ = gfe hpa≡hqa

 -- ⇐ (the "if" direction)
 homs-are-compatible-with-identities : (p q : Term)
  →    (∀ 𝑨 KA h  →  ∣ h ∣ ∘ (p ̇ 𝔉) ≡ ∣ h ∣ ∘ (q ̇ 𝔉))
       -----------------------------------------------
  →                𝓚 ⊧ p ≋ q
 --inferred types: 𝑨 : Algebra 𝓤 S, KA : 𝑨 ∈ 𝓚, h : hom 𝔉 𝑨

 homs-are-compatible-with-identities p q all-hp≡hq {A = 𝑨} KA = γ
  where
   h : (𝒂 : X → ∣ 𝑨 ∣) → hom 𝔉 𝑨
   h 𝒂 = lift-hom{𝑨 = 𝑨} 𝒂

   γ : 𝑨 ⊧ p ≈ q
   γ = gfe λ 𝒂 →
    (p ̇ 𝑨) 𝒂
      ≡⟨ refl _ ⟩
    (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ generator)
      ≡⟨(comm-hom-term' gfe 𝔉 𝑨 (h 𝒂) p generator)⁻¹ ⟩
    (∣ h 𝒂 ∣ ∘ (p ̇ 𝔉)) generator
      ≡⟨ ap (λ - → - generator) (all-hp≡hq 𝑨 KA (h 𝒂)) ⟩
    (∣ h 𝒂 ∣ ∘ (q ̇ 𝔉)) generator
      ≡⟨ (comm-hom-term' gfe 𝔉 𝑨 (h 𝒂) q generator) ⟩
    (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ generator)
      ≡⟨ refl _ ⟩
    (q ̇ 𝑨) 𝒂
      ∎

 compatibility-of-identities-and-homs : (p q : Term)
  →  (𝓚 ⊧ p ≋ q)
      ⇔ (∀ 𝑨 ka hh → ∣ hh ∣ ∘ (p ̇ 𝔉) ≡ ∣ hh ∣ ∘ (q ̇ 𝔉))
 --inferred types: 𝑨 : algebra 𝓤 s, ka : 𝑨 ∈ 𝓚, hh : hom 𝔉 𝑨.

 compatibility-of-identities-and-homs p q =
   identities-are-compatible-with-homs p q ,
   homs-are-compatible-with-identities p q

-- Product Closure
𝑷-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ))
 →      (𝓤 : Universe)(𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓤 S)
 →      (( i : I ) → 𝒜 i ∈ 𝓛𝓚 𝓤 ) → 𝓤 ⁺ ⊔ 𝓘 ⁺ ̇
𝑷-closed 𝓛𝓚 = λ 𝓤 𝓘 I 𝒜 𝒜i∈𝓛𝓚 →  Π' 𝒜  ∈ (𝓛𝓚 (𝓤 ⊔ 𝓘))

data PClo (𝓚 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 pbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ PClo 𝓚
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S}
  →     (∀ i → 𝒜 i ∈ PClo 𝓚)
  →     Π' 𝒜 ∈ PClo 𝓚

-- Subalgebra Closure
data SClo (𝓚 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 sbase : {𝑨 :  Algebra _ S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ SClo 𝓚
 sub : {𝑨 : Algebra _ S} → 𝑨 ∈ SClo 𝓚 → (sa : Subalgebra {𝑨 = 𝑨} 𝓤★) → ∣ sa ∣ ∈ SClo 𝓚

-- Homomorphic Image Closure
data HClo (𝓚 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 hbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
 hhom : {𝑨 𝑩 : Algebra 𝓤 S}{f : hom 𝑨 𝑩}
  →     𝑨 ∈ HClo 𝓚
  →     hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ HClo 𝓚

-- Variety Closure
data VClo (𝓚 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 vbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ VClo 𝓚
 vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S} → (∀ i → 𝒜 i ∈ VClo 𝓚) → Π' 𝒜 ∈ VClo 𝓚
 vsub : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ VClo 𝓚 → (sa : Subalgebra {𝑨 = 𝑨} 𝓤★) → ∣ sa ∣ ∈ VClo 𝓚
 vhom : {𝑨 𝑩 : Algebra 𝓤 S}{f : hom 𝑨 𝑩}
  →     𝑨 ∈ VClo 𝓚 → hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ VClo 𝓚

TH : (𝒦 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ )) → _ ̇
TH 𝒦 = Σ (p , q) ꞉ (Term{X = X} × Term) , 𝒦 ⊧ p ≋ q

Th : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) → Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

MOD : (Σ' : Pred (Term{X = X} × Term) 𝓤) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) ̇
MOD Σ' = Σ 𝑨 ꞉ (Algebra 𝓤 S) , ∀ p q → (p , q) ∈ Σ' → 𝑨 ⊧ p ≈ q

Mod : Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) → Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ )
Mod Σ' = λ 𝑨 → ∀ p q → (p , q) ∈ Σ' → 𝑨 ⊧ p ≈ q

--Birkhoff's theorem: every variety is an equational class.
birkhoff : (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺))
 →         (𝑨 : Algebra 𝓤 S) → 𝑨 ∈ Mod (Th (VClo 𝒦)) → 𝑨 ∈ VClo 𝒦
birkhoff 𝒦 𝑨 𝑨∈ModThV = {!!}
 --let 𝒲 be a class of algebras that is closed under 𝑯, 𝑺, and 𝑷.
 --we must find a set Σ of equations such that 𝒲 = Mod(Σ). For this will prove that 𝒲
 --is the class of algebras satisfying the set of equations Σ (i.e., 𝒲 is an equational class).
 --The obvious choice for Σ is the set of all equations that hold in 𝒲.
 --So, let Σ = Th(𝒲). let 𝒲' = Mod(Σ). Clearly, 𝒲 ⊆ 𝒲'. We prove the reverse inclusion.
 --Let 𝑨 ∈ 𝒲' and 𝑌 a set of cardinality max(∣𝐴∣, ω). Choose a surjection ℎ₀ : 𝑌 → 𝐴.
 --By :numref:`Obs %s <obs 9>`, ℎ₀ extends to an epimorphism ℎ : 𝔉(𝑌) → 𝑨`.
 --Since 𝔽_𝒲(Y) = 𝑻(Y)/θ_𝒲, there is an epimorphism g: 𝔉(Y) → 𝔽_𝒲.
 --We claim Ker g ⊆ Ker h. If the claim is true, then by :numref:`Obs %s <obs 5>`
 --∃ 𝑓 : 𝔽_𝒲(𝑌) → 𝐴 such that f ∘ g = h. Since ℎ is epic, so is 𝑓.
 --Hence 𝑨 ∈ 𝑯(𝔽_{𝒲}(Y)) ⊆ 𝒲` completing the proof.

-- 𝕍-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
--  →         (𝓤 : Universe) → (Algebra (𝓤 ⁺) S)
--  →         (𝓤' : Universe)(𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓤' S)
--  →         (( i : I ) → 𝒜 i ∈ 𝓛𝓚 𝓤' )
--  →         _ ̇
-- 𝕍-closed 𝓛𝓚 = λ 𝓤 𝑩 𝓤' 𝓘 I 𝒜 𝒜i∈𝓛𝓚 → (𝑯-closed 𝓛𝓚 𝓤 𝑩) × (𝑺-closed 𝓛𝓚 (𝓤 ⁺) 𝑩) × (𝑷-closed 𝓛𝓚 𝓤' 𝓘 I 𝒜 𝒜i∈𝓛𝓚)


-- Th : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
--  →   𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ ((𝓤 ⁺) ⁺) ̇
-- Th 𝓛𝓚 = λ 𝓤 → Σ (p , q) ꞉ (Term{X = X} × Term) , (𝓛𝓚 𝓤) ⊧ p ≋ q
