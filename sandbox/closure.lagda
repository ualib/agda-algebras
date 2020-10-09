\begin{code}
--FILE: closure.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 4 Aug 2020
--UPDATE: 19 Sep 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import prelude using (global-dfunext; dfunext; im)

module closure
 {𝑆 : Signature 𝓞 𝓥}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨} 
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤} where

open import homomorphisms {𝑆 = 𝑆} public
open import terms {𝑆 = 𝑆}{𝕏 = 𝕏}{gfe = gfe} renaming (generator to ℊ) public
open import subuniverses {𝑆 = 𝑆}{𝕏 = 𝕏}{fe = gfe} public
open import congruences public

module closure-definitions
 {𝓤 : Universe} {X : 𝓤 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)} where

 _⊧_≈_ : Algebra 𝓤 𝑆 → Term{𝓤}{X} → Term → 𝓤 ̇
 𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

 _⊧_≋_ : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Term → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 _⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

 ------------------------------------------------------------------------
 -- Equational theories and classes
 -- TH : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → _ ̇
 -- TH 𝒦 = Σ (p , q) ꞉ (Term × Term) , 𝒦 ⊧ p ≋ q

 Th :  Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Pred (Term × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

 -- MOD : (ℰ : Pred (Term × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 --  →    𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 -- MOD ℰ = Σ A ꞉ (Algebra 𝓤 𝑆) , ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

 Mod : Pred (Term × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

 ----------------------------------------------------------------------
 --Closure under products
 data PClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  pbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo
  prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆}
   →     (∀ i → 𝒜 i ∈ PClo)
   →     ⨅ 𝒜 ∈ PClo

 P-closed : (ℒ𝒦 : (𝓣 : Universe) → Pred (Algebra 𝓣 𝑆) (𝓣 ⁺ ))
  →      (𝓘 : Universe)(I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓘 𝑆)
  →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓘 ) → 𝓘 ⁺ ̇
 P-closed ℒ𝒦 = λ 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  ⨅ 𝒜  ∈ (ℒ𝒦 𝓘)

 ----------------------------------------------------------------------
 --Closure under hom images
 data HClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo
  hhom : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ HClo → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo

 ----------------------------------------------------------------------
 -- Subalgebra Closure
 data SClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) where
   sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo
   sub : {𝑨 : Algebra _ 𝑆}
    →    𝑨 ∈ SClo → (sa : SubalgebrasOf 𝑨)
    →    ∣ sa ∣ ∈ SClo

 ----------------------------------------------------------------------
 -- Variety Closure
 data VClo : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) where
  vbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo

  vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆}
   →      (∀ i → 𝒜 i ∈ VClo) → ⨅ 𝒜 ∈ VClo

  vsub : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo
   →     (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ VClo

  vhom : {𝑨 : Algebra 𝓤 𝑆}
   →     𝑨 ∈ VClo → ((𝑩 , _ , _) : HomImagesOf 𝑨)
   →     𝑩 ∈ VClo

 -- ThVClo⊆ThSClo : Th (VClo 𝒦) ⊆ Th (SClo 𝒦)
 -- ThVClo⊆ThSClo = ?

 ---------------------------
 --The free algebra in Agda
 ---------------------------
 𝑻HI = HomImagesOf (𝑻{𝓤}{X})

 𝑻img : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 𝑻img = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) ,
         Σ ϕ ꞉ hom (𝑻{𝓤}{X}) 𝑨 , (𝑨 ∈ SClo) × Epic ∣ ϕ ∣

 𝑻𝑨 : (ti : 𝑻img) → Algebra 𝓤 𝑆
 𝑻𝑨 ti = ∣ ti ∣

 𝑻𝑨∈SClo𝒦 : (ti : 𝑻img) → (𝑻𝑨 ti) ∈ SClo
 𝑻𝑨∈SClo𝒦 ti = ∣ pr₂ ∥ ti ∥ ∣

 𝑻ϕ : (ti : 𝑻img) → hom 𝑻 (𝑻𝑨 ti)
 𝑻ϕ ti = pr₁ ∥ ti ∥

 𝑻ϕE : (ti : 𝑻img) → Epic ∣ (𝑻ϕ ti) ∣
 𝑻ϕE ti = ∥ pr₂ ∥ ti ∥ ∥

 𝑻KER : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 𝑻KER = Σ (p , q) ꞉ (∣ 𝑻 ∣ × ∣ 𝑻 ∣) ,
    ∀ ti → (p , q) ∈ KER-pred{B = ∣ (𝑻𝑨 ti) ∣} ∣ 𝑻ϕ ti ∣

 Ψ : Pred (∣ 𝑻{𝓤}{X} ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 Ψ (p , q) =
  ∀ ti → ∣ (𝑻ϕ ti) ∣ ∘ (p ̇ 𝑻) ≡ ∣ (𝑻ϕ ti) ∣ ∘ (q ̇ 𝑻)

 Ψ' : Pred (∣ 𝑻 ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 Ψ' (p , q) = ∀ ti → ∣ (𝑻ϕ ti) ∣ p ≡ ∣ (𝑻ϕ ti) ∣ q

 -- N.B. Ψ is the kernel of 𝑻 → 𝔽(𝒦, 𝑻).  Therefore, to prove 𝑨 is a homomorphic image of 𝔽(𝒦, 𝑻),
 -- it suffices to show that the kernel of the lift h : 𝑻 → 𝑨 contains Ψ.

 -- .. code-block::

 --    𝑻---- g --->>𝔽  (ker g = Ψ)
 --     \         .
 --      \       .
 --       h     ∃ϕ     (want: Ψ ⊆ ker h)
 --        \   .
 --         \ .
 --          V
 --          𝑨

-----------------------------------
--More tools for Birkhoff's theorem
--Here are some key facts/identities needed to complete the proof of Birkhoff's HSP theorem.

 SClo𝒦→𝑻img : (𝑪 : Algebra 𝓤 𝑆) → 𝑪 ∈ SClo → 𝑻img
 SClo𝒦→𝑻img 𝑪 𝑪∈SClo𝒦 =
  𝑪 , (fst (𝑻hom-gen 𝑪)) , (𝑪∈SClo𝒦 , (snd (𝑻hom-gen 𝑪)))

 𝑻img→𝑻⊧ : ∀ p q   →   (p , q) ∈ Ψ'
  →        (ti : 𝑻img)
          ---------------------------
  →       ∣ (𝑻ϕ ti) ∣ ((p ̇ 𝑻) ℊ)
          ≡ ∣ (𝑻ϕ ti) ∣ ((q ̇ 𝑻) ℊ)
 𝑻img→𝑻⊧ p q pΨq ti = goal1
   where
    𝑪 : Algebra 𝓤 𝑆
    𝑪 = ∣ ti ∣

    ϕ : hom 𝑻 𝑪
    ϕ = 𝑻ϕ ti

    pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
    pCq = pΨq ti

    𝓅 𝓆 : ∣ 𝑻 ∣  -- Notation: 𝓅 = \Mcp
    𝓅 = ∣ tg p ∣
    𝓆 = ∣ tg q ∣

    p≡𝓅 : p ≡ (𝓅 ̇ 𝑻) ℊ
    p≡𝓅 = ∥ tg p ∥

    q≡𝓆 : q ≡ (𝓆 ̇ 𝑻) ℊ
    q≡𝓆 = ∥ tg q ∥

    ξ : ∣ ϕ ∣ ((𝓅 ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((𝓆 ̇ 𝑻) ℊ)
    ξ = (ap ∣ ϕ ∣ p≡𝓅)⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣ q≡𝓆)

    goal1 : ∣ ϕ ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)
    goal1 = (ap ∣ ϕ ∣ (term-gen-agreement p))
             ∙ ξ ∙ (ap ∣ ϕ ∣ (term-gen-agreement q))⁻¹

 Ψ⊆ThSClo𝒦 : Ψ ⊆ (Th SClo)
 Ψ⊆ThSClo𝒦 {p , q} pΨq {𝑪} 𝑪∈SClo𝒦 = 𝑪⊧p≈q
  where
   ti : 𝑻img
   ti = SClo𝒦→𝑻img 𝑪 𝑪∈SClo𝒦

   ϕ : hom 𝑻 𝑪
   ϕ = 𝑻ϕ ti

   ϕE : Epic ∣ ϕ ∣
   ϕE = 𝑻ϕE ti

   ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
   ϕsur 𝒄 x = ϕE (𝒄 x)

   pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 ∣
   pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

   ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
   ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

   γ : ∣ ϕ ∣ ∘ (p ̇ 𝑻) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻)
   γ = pΨq ti

   𝑪⊧p≈q : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
   𝑪⊧p≈q = gfe λ 𝒄 →
    (p ̇ 𝑪) 𝒄
        ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
    (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))
        ≡⟨ (comm-hom-term gfe 𝑻 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
    ∣ ϕ ∣ ((p ̇ 𝑻)(pre 𝒄))
        ≡⟨ intensionality γ (pre 𝒄) ⟩
    ∣ ϕ ∣ ((q ̇ 𝑻)(pre 𝒄))
        ≡⟨ comm-hom-term gfe 𝑻 𝑪 ϕ q (pre 𝒄) ⟩
    (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))
        ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
    (q ̇ 𝑪) 𝒄
        ∎

 Ψ⊆Th𝒦 : ∀ p q → (p , q) ∈ Ψ → 𝒦 ⊧ p ≋ q
 Ψ⊆Th𝒦 p q pΨq {𝑨} KA = Ψ⊆ThSClo𝒦{p , q} pΨq (sbase KA)

module compatibility
 {𝓤 : Universe}{X : 𝓤 ̇ }
 {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 {fevu : dfunext 𝓥 𝓤} where

 open closure-definitions {𝓤 = 𝓤}{X = X}{𝒦 = 𝒦}

 products-preserve-identities : (p q : Term{𝓤}{X}) (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
  →                             ((i : I) → (𝒜 i) ⊧ p ≈ q)
                                ------------------------------------------------------
  →                             ⨅ 𝒜 ⊧ p ≈ q

 products-preserve-identities p q I 𝒜 𝒜⊧p≈q = γ
   where
    γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
    γ = gfe λ a →
     (p ̇ ⨅ 𝒜) a                           ≡⟨ interp-prod{𝓤 = 𝓤} fevu p 𝒜 a ⟩
     (λ i → ((p ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ gfe (λ i → cong-app (𝒜⊧p≈q i) (λ x → (a x) i)) ⟩
     (λ i → ((q ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ (interp-prod gfe q 𝒜 a)⁻¹ ⟩
     (q ̇ ⨅ 𝒜) a                           ∎

 products-in-class-preserve-identities : (p q : Term{𝓤}{X}) (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
  →                                      𝒦 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝒦)
                                         -----------------------------------------------------
  →                                       ⨅ 𝒜 ⊧ p ≈ q

 products-in-class-preserve-identities p q I 𝒜 𝒦⊧p≋q all𝒜i∈𝒦 = γ
   where
    𝒜⊧p≈q : ∀ i → (𝒜 i) ⊧ p ≈ q
    𝒜⊧p≈q i = 𝒦⊧p≋q (all𝒜i∈𝒦 i)

    γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
    γ = products-preserve-identities p q I 𝒜 𝒜⊧p≈q

 subalgebras-preserve-identities : (p q : Term) (p≋q : 𝒦 ⊧ p ≋ q)
                                   (SAK : SubalgebrasOfClass' 𝒦)
                                   ----------------------------------
  →                                (pr₁ ∥ (pr₂ SAK) ∥) ⊧ p ≈ q

 subalgebras-preserve-identities p q p≋q SAK = γ
  where
   𝑨 : Algebra 𝓤 𝑆
   𝑨 = ∣ SAK ∣

   A∈𝒦 : 𝑨 ∈ 𝒦
   A∈𝒦 = ∣ pr₂ SAK ∣

   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = p≋q A∈𝒦

   subalg : SubalgebrasOf 𝑨
   subalg = ∥ pr₂ SAK ∥

   𝑩 : Algebra 𝓤 𝑆
   𝑩 = pr₁ subalg

   h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   h = ∣ pr₂ subalg ∣

   hem : is-embedding h
   hem = pr₁ ∥ pr₂ subalg ∥

   hhm : is-homomorphism 𝑩 𝑨 h
   hhm = pr₂ ∥ pr₂ subalg ∥

   ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
   ξ b =
    h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
    (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ 𝑩) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : 𝑩 ⊧ p ≈ q
   γ = gfe λ b → hlc (ξ b)


 -- ⇒ (the "only if" direction)
 identities-compatible-with-homs : (p q : Term{𝓤}{X})
                                   (p≋q : 𝒦 ⊧ p ≋ q)
                                  ------------------------------------------------------
  →                                ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝒦 𝑨)(h : hom (𝑻{𝓤}{X}) 𝑨)
                                   →  ∣ h ∣ ∘ (p ̇ 𝑻{𝓤}{X}) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)

 identities-compatible-with-homs
  p q p≋q 𝑨 KA h = γ
   where
   pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
   pA≡qA = p≋q KA

   pAh≡qAh : ∀(𝒂 : X → ∣ 𝑻 ∣ ) → (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
   pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

   hpa≡hqa : ∀(𝒂 : X → ∣ 𝑻 ∣ ) → ∣ h ∣ ((p ̇ 𝑻) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻) 𝒂)
   hpa≡hqa 𝒂 =
    ∣ h ∣ ((p ̇ 𝑻) 𝒂)  ≡⟨ comm-hom-term{𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺} fevu (𝑻{𝓤}{X}) 𝑨 h p 𝒂 ⟩
    (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
    (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term{𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺} fevu 𝑻 𝑨 h q 𝒂)⁻¹ ⟩
    ∣ h ∣ ((q ̇ 𝑻) 𝒂)  ∎

   γ : ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)
   γ = gfe hpa≡hqa


 -- ⇐ (the "if" direction)
 homs-compatible-with-identities : (p q : Term{𝓤}{X})
                                   (hp≡hq : ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦) (h : hom (𝑻{𝓤}{X}) 𝑨)
                                            → ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻))
                                   ----------------------------------------------------------------
  →                                 𝒦 ⊧ p ≋ q

 --inferred types: 𝑨 : Algebra 𝓤 𝑆, KA : 𝑨 ∈ 𝒦, h : hom 𝑻 𝑨

 homs-compatible-with-identities p q hp≡hq {𝑨} KA = γ
   where
    h : (𝒂 : X → ∣ 𝑨 ∣) → hom 𝑻 𝑨
    h 𝒂 = lift-hom{𝑨 = 𝑨} 𝒂

    γ : 𝑨 ⊧ p ≈ q
    γ = gfe λ 𝒂 →
     (p ̇ 𝑨) 𝒂            ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
     (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨(comm-hom-term gfe 𝑻 𝑨 (h 𝒂) p ℊ)⁻¹ ⟩
     (∣ h 𝒂 ∣ ∘ (p ̇ 𝑻)) ℊ  ≡⟨ ap (λ - → - ℊ) (hp≡hq 𝑨 KA (h 𝒂)) ⟩
     (∣ h 𝒂 ∣ ∘ (q ̇ 𝑻)) ℊ  ≡⟨ (comm-hom-term gfe 𝑻 𝑨 (h 𝒂) q ℊ) ⟩
     (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
     (q ̇ 𝑨) 𝒂             ∎

 compatibility-of-identities-and-homs : (p q : Term{𝓤}{X})
                                        -------------------------------------------------------
  →                                      (𝒦 ⊧ p ≋ q) ⇔ (∀(𝑨 : Algebra 𝓤 𝑆)
                                                           (KA : 𝑨 ∈ 𝒦)
                                                            (hh : hom (𝑻{𝓤}{X}) 𝑨)
                                                          →   ∣ hh ∣ ∘ (p ̇ 𝑻) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻))

 compatibility-of-identities-and-homs p q = identities-compatible-with-homs p q ,
                                              homs-compatible-with-identities p q

 ---------------------------------------------------------------
 --Compatibility of identities with interpretation of terms
 hom-id-compatibility : (p q : ∣ 𝑻{𝓤}{X} ∣ ) (𝑨 : Algebra 𝓤 𝑆)
                        (ϕ : hom 𝑻 𝑨) (p≈q : 𝑨 ⊧ p ≈ q)
                       ----------------------------------------
  →                     ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q

 hom-id-compatibility p q 𝑨 ϕ p≈q =
    ∣ ϕ ∣ p              ≡⟨ ap ∣ ϕ ∣ (term-agreement p) ⟩
    ∣ ϕ ∣ ((p ̇ 𝑻) ℊ)    ≡⟨ (comm-hom-term fevu (𝑻{𝓤}{X}) 𝑨 ϕ p ℊ) ⟩
    (p ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ intensionality p≈q (∣ ϕ ∣ ∘ ℊ)  ⟩
    (q ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ (comm-hom-term fevu (𝑻{𝓤}{X}) 𝑨 ϕ q ℊ)⁻¹ ⟩
    ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)    ≡⟨ (ap ∣ ϕ ∣ (term-agreement q))⁻¹ ⟩
    ∣ ϕ ∣ q              ∎


--------------------
--Closure under HSP
--------------------

--Finally, we have a datatype that represents classes of algebras that are close under the taking of
--homomorphic images, subalgebras, and products of algebras in the class.

module closure-identities
 {𝓤 : Universe} {X : 𝓤 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 {fevu : dfunext 𝓥 𝓤} where

 open closure-definitions {𝓤 = 𝓤}{X = X}{𝒦 = 𝒦}
 open compatibility {𝓤 = 𝓤}{X = X}{𝒦 = 𝒦}{fevu = fevu}

 --Identities for product closure
 --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 pclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (PClo ⊧ p ≋ q)
 pclo-id1 {p} {q} α (pbase x) = α x
 pclo-id1 {p} {q} α (prod{I}{𝒜} 𝒜-P𝒦 ) = γ
  where
   IH : (i : I)  → (p ̇ 𝒜 i) ≡ (q ̇ 𝒜 i)
   IH = λ i → pclo-id1{p}{q} α  ( 𝒜-P𝒦  i )
   γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 pclo-id2 : ∀{p q} → ((PClo) ⊧ p ≋ q ) → (𝒦 ⊧ p ≋ q)
 pclo-id2 p A∈𝒦 = p (pbase A∈𝒦)

 --Identities for subalgebra closure
 --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 sclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (SClo ⊧ p ≋ q)
 sclo-id1 {p} {q} 𝒦⊧p≋q (sbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 sclo-id1 {p} {q} 𝒦⊧p≋q (sub {𝑨 = 𝑨} A∈SClo𝒦 sa) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = sclo-id1{p}{q} 𝒦⊧p≋q A∈SClo𝒦

   B : Algebra 𝓤 𝑆
   B = ∣ sa ∣

   h : ∣ B ∣ → ∣ 𝑨 ∣
   h = pr₁ ∥ sa ∥

   hem : is-embedding h
   hem = ∣ pr₂ ∥ sa ∥ ∣

   hhm : is-homomorphism B 𝑨 h
   hhm = ∥ pr₂ ∥ sa ∥ ∥

   ξ : (b : X → ∣ B ∣ ) → h ((p ̇ B) b) ≡ h ((q ̇ B) b)
   ξ b =
    h ((p ̇ B) b)  ≡⟨ comm-hom-term gfe B 𝑨 (h , hhm) p b ⟩
    (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe B 𝑨 (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ B) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : p ̇ B ≡ q ̇ B
   γ = gfe λ b → hlc (ξ b)

 sclo-id2 : ∀ {p q} → (SClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 sclo-id2 p A∈𝒦 = p (sbase A∈𝒦)


 --Identities for hom image closure
 --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 hclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (HClo ⊧ p ≋ q)
 hclo-id1 {p}{q} 𝒦⊧p≋q (hbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 hclo-id1 {p}{q} 𝒦⊧p≋q (hhom{𝑨} A∈HClo𝒦 𝑩ϕhE) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = (hclo-id1{p}{q} 𝒦⊧p≋q ) A∈HClo𝒦

   𝑩 : Algebra 𝓤 𝑆
   𝑩 = ∣ 𝑩ϕhE ∣

   ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
   ϕ = ∣ ∥ 𝑩ϕhE ∥ ∣

   ϕhom : is-homomorphism 𝑨 𝑩 ϕ
   ϕhom = ∣ pr₂ ∥ 𝑩ϕhE ∥ ∣

   ϕsur : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
   ϕsur 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhE ∥ ∥ (𝒃 x)

   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕsur 𝒃 x))

   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕsur 𝒃 x)

   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
   γ = gfe λ 𝒃 →
    (p ̇ 𝑩) 𝒃
        ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃))
        ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) p (preim 𝒃))⁻¹ ⟩
    ϕ((p ̇ 𝑨)(preim 𝒃))
        ≡⟨ ap ϕ (intensionality A⊧p≈q (preim 𝒃)) ⟩
    ϕ((q ̇ 𝑨)(preim 𝒃))
        ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))
        ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
    (q ̇ 𝑩) 𝒃
        ∎

 hclo-id2 : ∀ {p q} → (HClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 hclo-id2 p A∈𝒦 = p (hbase A∈𝒦)

 --Identities for HSP closure
 --~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 vclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (VClo ⊧ p ≋ q)
 vclo-id1 {p} {q} α (vbase A∈𝒦) = α A∈𝒦
 vclo-id1 {p} {q} α (vprod{I = I}{𝒜 = 𝒜} 𝒜∈VClo𝒦) = γ
  where
   IH : (i : I) → 𝒜 i ⊧ p ≈ q
   IH i = vclo-id1{p}{q} α (𝒜∈VClo𝒦 i)

   γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 vclo-id1 {p} {q} α ( vsub {𝑨 = 𝑨} A∈VClo𝒦 sa ) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

   𝑩 : Algebra 𝓤 𝑆
   𝑩 = ∣ sa ∣

   h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   h = pr₁ ∥ sa ∥

   hem : is-embedding h
   hem = ∣ pr₂ ∥ sa ∥ ∣

   hhm : is-homomorphism 𝑩 𝑨 h
   hhm = ∥ pr₂ ∥ sa ∥ ∥

   ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
   ξ b =
    h ((p ̇ 𝑩) b) ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
    (p ̇ 𝑨)(h ∘ b)≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ 𝑨)(h ∘ b)≡⟨(comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ 𝑩) b) ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : p ̇ 𝑩 ≡ q ̇ 𝑩
   γ = gfe λ b → hlc (ξ b)

 vclo-id1 {p}{q} α (vhom{𝑨 = 𝑨} A∈VClo𝒦 𝑩ϕhE) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

   𝑩 : Algebra 𝓤 𝑆
   𝑩 = ∣ 𝑩ϕhE ∣

   ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
   ϕ = ∣ ∥ 𝑩ϕhE ∥ ∣

   ϕh : is-homomorphism 𝑨 𝑩 ϕ
   ϕh = ∣ pr₂ ∥ 𝑩ϕhE ∥ ∣

   ϕE : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
   ϕE 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhE ∥ ∥ (𝒃 x)

   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕE 𝒃 x))

   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕE 𝒃 x)

   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
   γ = gfe λ 𝒃 →
    (p ̇ 𝑩) 𝒃
        ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃))
        ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) p (preim 𝒃))⁻¹ ⟩
    ϕ((p ̇ 𝑨)(preim 𝒃))
        ≡⟨ ap ϕ (intensionality A⊧p≈q (preim 𝒃)) ⟩
    ϕ((q ̇ 𝑨)(preim 𝒃))
        ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) q (preim 𝒃) ⟩
    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))
        ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
    (q ̇ 𝑩) 𝒃 ∎

 vclo-id2 : ∀ {p q} → (VClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 vclo-id2 p A∈𝒦 = p (vbase A∈𝒦)


---------------------------
--Axiomatization of a class
---------------------------

--We conclude the `closure module`_ by proving that a class 𝒦 of structures is axiomatized by ``Th (VClo 𝒦)``,
--which is the set of equations satisfied by all members of the varietal closure of 𝒦.

 -- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
 ThHSP-axiomatizes : (p q : ∣ 𝑻 ∣)
        ---------------------------------------
  →     𝒦 ⊧ p ≋ q  ⇔  ((p , q) ∈ Th (VClo))

 ThHSP-axiomatizes p q =
  (λ 𝒦⊧p≋q 𝑨∈VClo𝒦 → vclo-id1{p = p}{q = q} 𝒦⊧p≋q 𝑨∈VClo𝒦) ,
  λ pq∈Th 𝑨∈𝒦 → pq∈Th (vbase 𝑨∈𝒦)
\end{code}
