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
                                _is-subalgebra-of_; Subalgebra)

module birkhoff {S : Signature 𝓞 𝓥} {X : 𝓧 ̇ }  where

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

𝑷-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ))
 →      (𝓘 : Universe) (I : 𝓘 ̇ ) (𝓐 : I → Algebra 𝓘 S)
 →      (( i : I ) → 𝓐 i ∈ 𝓛𝓚 𝓘 ) → 𝓘 ⁺ ̇
𝑷-closed 𝓛𝓚 = λ 𝓘 I 𝓐 𝓐i∈𝓛𝓚 →  Π' 𝓐  ∈ (𝓛𝓚 𝓘)

module _
  (gfe : global-dfunext)
  (𝓚 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))) { X : 𝓧 ̇ } where

  products-preserve-identities : (p q : Term{X = X})
        (I : 𝓤 ̇ ) (𝓐 : I → Algebra 𝓤 S)
   →    𝓚 ⊧ p ≋ q  →  ((i : I) → 𝓐 i ∈ 𝓚)
   →    Π' 𝓐 ⊧ p ≈ q
  products-preserve-identities p q I 𝓐 𝓚⊧p≋q all𝓐i∈𝓚 = γ
   where
    all𝓐⊧p≈q : ∀ i → (𝓐 i) ⊧ p ≈ q
    all𝓐⊧p≈q i = 𝓚⊧p≋q (all𝓐i∈𝓚 i)

    γ : (p ̇ Π' 𝓐) ≡ (q ̇ Π' 𝓐)
    γ = gfe λ 𝒂 →
     (p ̇ Π' 𝓐) 𝒂
       ≡⟨ interp-prod gfe p 𝓐 𝒂 ⟩
     (λ i → ((p ̇ (𝓐 i)) (λ x → (𝒂 x) i)))
       ≡⟨ gfe (λ i → cong-app (all𝓐⊧p≈q i) (λ x → (𝒂 x) i)) ⟩
     (λ i → ((q ̇ (𝓐 i)) (λ x → (𝒂 x) i)))
       ≡⟨ (interp-prod gfe q 𝓐 𝒂)⁻¹ ⟩
     (q ̇ Π' 𝓐) 𝒂
       ∎
_is-subalgebra-of-class_ : {𝓤 : Universe}(𝑩 : Algebra 𝓤 S)
 →                         Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
𝑩 is-subalgebra-of-class 𝓚 =
 Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × (𝑩 is-subalgebra-of 𝑨)

module _
 (𝓚 : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ))
 (𝓚' : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))){X : 𝓧 ̇ }
 (𝓤★ : Univalence) where

 gfe : global-dfunext
 gfe = univalence-gives-global-dfunext 𝓤★

 SubalgebrasOfClass : Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 SubalgebrasOfClass 𝓚 =
  Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × Subalgebra{𝑨 = 𝑨} 𝓤★

 𝑺-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
  →      (𝓤 : Universe) → (𝑩 : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 𝑺-closed 𝓛𝓚 =
  λ 𝓤 𝑩 → (𝑩 is-subalgebra-of-class (𝓛𝓚 𝓤)) → (𝑩 ∈ 𝓛𝓚 𝓤)

 subalgebras-preserve-identities : (p q : Term{X = X})
  →  (𝓚 ⊧ p ≋ q) → (SAK : SubalgebrasOfClass 𝓚)
  →  (pr₁ ∥ (pr₂ SAK) ∥) ⊧ p ≈ q
 subalgebras-preserve-identities p q 𝓚⊧p≋q SAK = γ
  where

   𝑨 : Algebra 𝓤 S
   𝑨 = ∣ SAK ∣

   𝑨∈𝓚 : 𝑨 ∈ 𝓚
   𝑨∈𝓚 = ∣ pr₂ SAK ∣

   𝑨⊧p≈q : 𝑨 ⊧ p ≈ q
   𝑨⊧p≈q = 𝓚⊧p≋q 𝑨∈𝓚

   subalg : Subalgebra{𝑨 = 𝑨} 𝓤★
   subalg = ∥ pr₂ SAK ∥

   𝑩 : Algebra 𝓤 S
   𝑩 = pr₁ subalg

   h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   h = ∣ pr₂ subalg ∣

   h-emb : is-embedding h
   h-emb = pr₁ ∥ pr₂ subalg ∥

   h-hom : is-homomorphism 𝑩 𝑨 h
   h-hom = pr₂ ∥ pr₂ subalg ∥

   ξ : (𝒃 : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) 𝒃) ≡ h ((q ̇ 𝑩) 𝒃)
   ξ 𝒃 =
    h ((p ̇ 𝑩) 𝒃)  ≡⟨ comm-hom-term' gfe 𝑩 𝑨 (h , h-hom) p 𝒃 ⟩
    (p ̇ 𝑨)(h ∘ 𝒃) ≡⟨ intensionality 𝑨⊧p≈q (h ∘ 𝒃) ⟩
    (q ̇ 𝑨)(h ∘ 𝒃) ≡⟨ (comm-hom-term' gfe 𝑩 𝑨 (h , h-hom) q 𝒃)⁻¹ ⟩
    h ((q ̇ 𝑩) 𝒃)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h h-emb) hb≡hb'

   γ : 𝑩 ⊧ p ≈ q
   γ = gfe λ 𝒃 → hlc (ξ 𝒃)

module _
 (gfe : global-dfunext)
 (𝓚 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
 { X : 𝓧 ̇ } where

 -- ⇒ (the "only if" direction)
 identities-are-compatible-with-homs : (p q : Term)
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
 --Inferred types: 𝑨 : Algebra 𝓤 S, KA : 𝑨 ∈ 𝓚, h : hom 𝔉 𝑨

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
      ⇔ (∀ 𝑨 KA hh → ∣ hh ∣ ∘ (p ̇ 𝔉) ≡ ∣ hh ∣ ∘ (q ̇ 𝔉))
 --inferred types: 𝑨 : Algebra 𝓤 S, KA : 𝑨 ∈ 𝓚, hh : hom 𝔉 𝑨.

 compatibility-of-identities-and-homs p q =
   identities-are-compatible-with-homs p q ,
   homs-are-compatible-with-identities p q

 𝕍-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
  →         (𝓤 : Universe) → (Algebra (𝓤 ⁺) S)
  →         _ ̇
 𝕍-closed 𝓛𝓚 = λ 𝓤 𝑩 → (𝑯-closed 𝓛𝓚 𝓤 𝑩) × (𝑺-closed 𝓛𝓚 (𝓤 ⁺) 𝑩) × (𝑷-closed 𝓛𝓚 𝓤 𝑩)



 Th : (𝒦 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
  →   𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ ((𝓤 ⁺) ⁺) ̇
 Th 𝒦 = Σ (p , q) ꞉ (Term{X = X} × Term) , 𝒦 ⊧ p ≋ q

 Mod : (Σ' : Pred (Term{X = X} × Term) 𝓤)
  →    𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ (𝓤 ⁺) ̇
 Mod Σ' = Σ 𝑨 ꞉ (Algebra 𝓤 S) , ∀ p q → (p , q) ∈ Σ' → 𝑨 ⊧ p ≈ q

 --Birkhoff's Theorem: Every variety is an equational class.

 Birkhoff : (𝒦 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
  →         𝕍-closed 𝒦  →  Mod Th 𝒦 ⊆ 𝒦
 Birkhoff = ?
 --Let 𝒲 be a class of algebras that is closed under H, S, and P.
 --We must find a set Σ of equations such that 𝒲 = Mod(Σ).  For this will prove that 𝒲
 --is the class of algebras satisfying the set of equations Σ (i.e., 𝒲 is an equational class).
 --The obvious choice for Σ is the set of all equations that hold in 𝒲.
 --Let Σ = Th(𝒲). Let :math:`𝒲^† :=` Mod(Σ).

-- Clearly, :math:`𝒲 ⊆ 𝒲^†`. We shall prove the reverse inclusion.

-- Let :math:`𝑨 ∈ 𝒲^†` and 𝑌 a set of cardinality max(∣𝐴∣, ω). Choose a surjection ℎ₀ : 𝑌 → 𝐴.

-- By :numref:`Obs %s <obs 9>`, ℎ₀ extends to an epimorphism ℎ : 𝔉(𝑌) → 𝑨`.

-- Furthermore, since :math:`𝔽_𝒲(Y) = 𝑻(Y)/Θ_𝒲`, there is an epimorphism :math:`g: 𝑻(Y) → 𝔽_𝒲`.

-- We claim that :math:`\ker g ⊆ \ker h`. If the claim is true, then by :numref:`Obs %s <obs 5>` there is a map 𝑓 : 𝔽_𝒲(𝑌) → 𝐴 such that :math:`f ∘ g = h`.

-- Since ℎ is epic, so is 𝑓. Hence :math:`𝑨 ∈ 𝑯(𝔽_{𝒲}(Y)) ⊆ 𝒲` completing the proof.
 -- Let Σ = Th(𝒲). Let 𝒲† := Mod(Σ).
 -- Clearly, :math:`𝒲 ⊆ 𝒲^†`. We shall prove the reverse inclusion.

    -- Let :math:`𝑨 ∈ 𝒲^†` and 𝑌 a set of cardinality max(∣𝐴∣, ω). Choose a surjection ℎ₀ : 𝑌 → 𝐴.

    -- By :numref:`Obs %s <obs 9>`, ℎ₀ extends to an epimorphism ℎ : 𝔉(𝑌) → 𝑨`.

    -- Furthermore, since :math:`𝔽_𝒲(Y) = 𝑻(Y)/Θ_𝒲`, there is an epimorphism :math:`g: 𝑻(Y) → 𝔽_𝒲`.

    -- We claim that :math:`\ker g ⊆ \ker h`. If the claim is true, then by :numref:`Obs %s <obs 5>` there is a map 𝑓 : 𝔽_𝒲(𝑌) → 𝐴 such that :math:`f ∘ g = h`.

    -- Since ℎ is epic, so is 𝑓. Hence :math:`𝑨 ∈ 𝑯(𝔽_{𝒲}(Y)) ⊆ 𝒲` completing the proof.

