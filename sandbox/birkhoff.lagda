\begin{code}
--FILE: birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--REF: Based on the file `birkhoff.agda` (23 Jan 2020).

-- {-# OPTIONS --without-K --exact-split --safe #-}
{-# OPTIONS --without-K --exact-split #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; funext; Pred)

module birkhoff
 {𝑆 : Signature 𝓞 𝓥}
 {𝓦 : Universe}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {fevu : dfunext 𝓥 𝓤} where

open import closure {𝑆 = 𝑆}{𝓦 = 𝓦}{𝕏 = 𝕏}{gfe = gfe}{dfe = dfe}{fevu = fevu}

--Equalizers of functions
𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
𝑬 g h x = g x ≡ h x

--Equalizers of homomorphisms
𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 𝑆} (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x

𝑬𝑯-is-closed : funext 𝓥 𝓤
 →     {𝑓 : ∣ 𝑆 ∣ } {𝑨 𝑩 : Algebra 𝓤 𝑆}
       (g h : hom 𝑨 𝑩)  (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ 𝑨 ∣)
 →     ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
       --------------------------------------------------
 →      ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 p =
   (∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂))    ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
   (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)  ≡⟨ ap (_ ̂ 𝑩)(fe p) ⟩
   (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
   ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)    ∎

-- Equalizer of homs is a subuniverse.
𝑬𝑯-is-subuniverse : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}(g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}

𝑬𝑯-is-subuniverse fe {𝑨} {𝑩} g h = mksub (𝑬𝑯 {𝑨}{𝑩} g h) λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 x

HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}
            (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →          (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
            ---------------------------------------------
 →          (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x

HomUnique fe {𝑨}{𝑩} X g h gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
  ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)     ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 )   ≡⟨ ap (𝑓 ̂ 𝑩)(fe induction-hypothesis) ⟩
  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)    ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )    ∎
 where induction-hypothesis = λ x → HomUnique fe {𝑨}{𝑩} X g h gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

module _
 {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 {𝒦₁ : Pred (Algebra W 𝑆) ( W ⁺ )}
 {𝒦' : Pred (Algebra 𝓤 𝑆) ( 𝓤 ⁺ )}
 {𝒦+ : Pred (Algebra OVU+ 𝑆) (OVU+ ⁺)}
 {𝒦4 : Pred (Algebra (OVU+ ⁺ ⁺ ⁺) 𝑆) (OVU+ ⁺ ⁺ ⁺ ⁺)} where

 ---------------------------
 --The free algebra in Agda
 ---------------------------

 𝑻img : _ ̇
 𝑻img = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , Σ ϕ ꞉ hom (𝑻{𝓧}{X}) 𝑨 , (𝑨 ∈ SClo 𝒦) × Epic ∣ ϕ ∣

 -- SClo→𝑻img : (𝑨 : Algebra W 𝑆) → 𝑨 ∈ SClo 𝒦₁ → 𝑻img
 -- SClo→𝑻img 𝑨 SCloA = 𝑨 , (fst (𝑻hom-gen 𝑨)) , (SCloA , (snd (𝑻hom-gen 𝑨)))

 mkti : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ SClo 𝒦 → 𝑻img
 mkti {𝑨} SCloA = (𝑨 , fst thg , SCloA , snd thg)
  where
   thg : Σ h ꞉ (hom (𝑻{𝓧}{X}) 𝑨), Epic ∣ h ∣
   thg = 𝑻hom-gen 𝑨

 𝑻𝑨 : 𝑻img → Algebra _ 𝑆
 𝑻𝑨 ti = ∣ ti ∣

 𝑻ϕ : {ti : 𝑻img} → hom 𝑻 (𝑻𝑨 ti)
 𝑻ϕ {ti} = fst (snd ti)

 𝑻ϕE : {ti : 𝑻img} → Epic ∣ 𝑻ϕ {ti} ∣
 𝑻ϕE {ti} = snd (snd ∥ ti ∥)

 𝑻KER : _ ̇
 𝑻KER = Σ (p , q) ꞉ (∣ 𝑻 ∣ × ∣ 𝑻 ∣) ,
          ∀ 𝑨 → (SCloA : 𝑨 ∈ SClo 𝒦) → (p , q) ∈ KER-pred{B = ∣ 𝑨 ∣} ∣ 𝑻ϕ {mkti SCloA} ∣

 Ψ : Pred (∣ 𝑻{𝓧}{X} ∣ × ∣ 𝑻 ∣) _
 Ψ (p , q) = ∀ 𝑨 → (SCloA : 𝑨 ∈ SClo 𝒦)
               → ∣ 𝑻ϕ {mkti SCloA} ∣ ∘ (p ̇ 𝑻) ≡ ∣ 𝑻ϕ {mkti SCloA} ∣ ∘ (q ̇ 𝑻)

 ψ : Pred (∣ 𝑻 ∣ × ∣ 𝑻 ∣) {!!}
 ψ (p , q) = ∀ 𝑨 → (SCloA : 𝑨 ∈ SClo 𝒦) → ∣ 𝑻ϕ {mkti SCloA} ∣ p ≡ ∣ 𝑻ϕ {mkti SCloA} ∣ q

 ψRel : Rel ∣ 𝑻 ∣ {!!}
 ψRel p q = ψ (p , q)

 -- ψcompatible : compatible (𝑻{W ⁺}) ψRel
 -- ψcompatible f {i} {j} iψj 𝑨 SCloA = γ
 --  where
 --   ti : 𝑻img
 --   ti = mkti {𝑨 = 𝑨} SCloA

 --   ϕ : hom 𝑻 𝑨
 --   ϕ = 𝑻ϕ {ti = ti}

 --   γ : ∣ ϕ ∣ ((f ̂ 𝑻) i) ≡ ∣ ϕ ∣ ((f ̂ 𝑻) j)
 --   γ = ∣ ϕ ∣ ((f ̂ 𝑻) i) ≡⟨ ∥ ϕ ∥ f i ⟩
 --       (f ̂ 𝑨) (∣ ϕ ∣ ∘ i) ≡⟨ ap (f ̂ 𝑨) (gfe λ x → ((iψj x) 𝑨 SCloA)) ⟩
 --       (f ̂ 𝑨) (∣ ϕ ∣ ∘ j) ≡⟨ (∥ ϕ ∥ f j)⁻¹ ⟩
 --       ∣ ϕ ∣ ((f ̂ 𝑻) j) ∎

 ψSym : symmetric ψRel
 ψSym p q pψRelq 𝑪 ϕ = (pψRelq 𝑪 ϕ)⁻¹

 ψTra : transitive ψRel
 ψTra p q r pψq qψr 𝑪 ϕ = (pψq 𝑪 ϕ) ∙ (qψr 𝑪 ϕ)

 ψIsEquivalence : IsEquivalence ψRel
 ψIsEquivalence = record { rfl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁 ; sym = ψSym ; trans = ψTra }

 -- ψCon : Congruence (𝑻{𝓤}{X})
 -- ψCon = mkcon ψRel ψcompatible ψIsEquivalence

 -- 𝔽 : Algebra ((𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺)) 𝑆
 -- 𝔽 = 𝑻{𝓤}{X} ╱ ψCon


 --More tools for Birkhoff's theorem
 --Here are some key facts/identities needed to complete the proof of Birkhoff's HSP theorem.

 𝑻i⊧ψ : {p q : ∣ 𝑻 ∣}{𝑪 : Algebra 𝓤 𝑆}{SCloC : 𝑪 ∈ SClo 𝒦}
  →       (p , q) ∈ ψ
         ----------------------------------------------------------------
  →       ∣ 𝑻ϕ{ti = mkti SCloC} ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ 𝑻ϕ{ti = mkti SCloC} ∣ ((q ̇ 𝑻) ℊ)

 𝑻i⊧ψ {p}{q}{𝑪}{SCloC} pψq = γ
  where

   ϕ : hom 𝑻 𝑪
   ϕ = 𝑻ϕ{ti = mkti SCloC}

   pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
   pCq = pψq 𝑪 SCloC

   γ : ∣ ϕ ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)
   γ = (ap ∣ ϕ ∣(term-agree p))⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣(term-agree q))




 Ψ⊆ThSClo : Ψ ⊆ (Th (SClo 𝒦))
 Ψ⊆ThSClo {p , q} pΨq {𝑪} SCloC = γ
  where
   ti : 𝑻img
   ti = mkti {𝑪} SCloC -- SClo→𝑻img 

   ϕ : hom 𝑻 𝑪
   ϕ = 𝑻ϕ{ti}

   ϕE : Epic ∣ ϕ ∣
   ϕE = 𝑻ϕE{ti}

   ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
   ϕsur 𝒄 x = ϕE (𝒄 x)

   pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 ∣
   pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

   ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
   ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

   β : ∣ ϕ ∣ ∘ (p ̇ 𝑻) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻)
   β = pΨq 𝑪 SCloC

   γ : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
   γ = gfe λ 𝒄 →
    (p ̇ 𝑪) 𝒄                  ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
    (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ (comm-hom-term gfe 𝑻 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
    ∣ ϕ ∣ ((p ̇ 𝑻)(pre 𝒄))       ≡⟨ intensionality β (pre 𝒄) ⟩
    ∣ ϕ ∣ ((q ̇ 𝑻)(pre 𝒄))       ≡⟨ comm-hom-term gfe 𝑻 𝑪 ϕ q (pre 𝒄) ⟩
    (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
    (q ̇ 𝑪) 𝒄                   ∎

 Ψ⊆Th𝒦 : (p q : ∣ 𝑻 ∣) → (p , q) ∈ Ψ → 𝒦 ⊧ p ≋ q
 Ψ⊆Th𝒦 p q pΨq {𝑨} KA = Ψ⊆ThSClo{p , q} pΨq (sbase KA)





------------------
--Class Identities
------------------

--It follows from `vclo-id1` that, if 𝒦 is a class of structures, the set of identities
-- modeled by all structures in 𝒦 is the same as the set of identities modeled by all structures in VClo 𝒦.

-- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
class-identities : {𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 →                 (p q : ∣ 𝑻{𝓧}{X} ∣)
                  ----------------------------------------------------------
 →                 (_⊧_≋_ {𝓤}{𝓧}{X} 𝒦 p q)  ⇔  ((p , q) ∈ Th (VClo 𝒦))

class-identities {𝓧}{X}{𝒦} p q = (λ α VCloA → vclo-id1{𝒦}{𝓧} p q α VCloA) ,  λ Thpq KA → Thpq (vbase KA)



-- Birkhoff's theorem: every variety is an equational class.
-- birkhoff : {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
--            (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ Mod (Th (VClo{𝒦}))
--           --------------------------------------------
--  →                     𝑨 ∈ VClo{𝒦}

-- birkhoff {𝒦} 𝑨 ModThVCloA = γ
--  where
--   h₀ : X → ∣ 𝑨 ∣
--   h₀ = fst (𝕏 𝑨)

--   h : hom 𝑻 𝑨
--   h = lift-hom{𝑨 = 𝑨} h₀

--   Ψ⊆ThVClo : Ψ ⊆ Th VClo
--   Ψ⊆ThVClo {p , q} pΨq =
--    (lr-implication (class-identities p q)) (Ψ⊆Th𝒦 p q pΨq)

--   Ψ⊆A⊧ : ∀{p}{q} → (p , q) ∈ Ψ → 𝑨 ⊧ p ≈ q
--   Ψ⊆A⊧ {p} {q} pΨq = ModThVCloA p q (Ψ⊆ThVClo {p , q} pΨq)

--   Ψ⊆Kerh : Ψ ⊆ KER-pred{B = ∣ 𝑨 ∣} ∣ h ∣
--   Ψ⊆Kerh {p , q} pΨq = hp≡hq
--    where
--     hp≡hq : ∣ h ∣ p ≡ ∣ h ∣ q
--     hp≡hq = hom-id-compatibility{𝒦} p q 𝑨 h (Ψ⊆A⊧{p}{q} pΨq)

--   gg : Σ g ꞉ hom (𝑻{𝓤}{X}) (𝔽{𝒦}) , Epic ∣ g ∣
--   gg = (lift-hom{𝑨 = 𝔽} g₀) , {!!} -- (lift-of-epic-is-epic{𝓤 = (𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺)} g₀ g₀E)

--    where
--     g₀ : X → ∣ 𝔽 ∣
--     g₀ = fst (𝕏 𝔽)

--     g₀E : Epic g₀
--     g₀E = snd (𝕏 𝔽)

--   g : hom (𝑻{𝓤}{X}) (𝔽{𝒦})
--   g = fst gg

--   gE : Epic ∣ g ∣
--   gE = snd gg

--   -- N.B. Ψ is the kernel of 𝑻 → 𝔽(𝒦, 𝑻).  Therefore, to prove 𝑨 is a homomorphic image of 𝔽(𝒦, 𝑻),
--   -- it suffices to show that the kernel of the lift h : 𝑻 → 𝑨 contains Ψ.
--   --
--   --    𝑻---- g --->>𝑻/ψ    ψ = ker g ⊆ ker h => ∃ ϕ: T/ψ → A
--   --    𝑻---- g --->>𝔽  (ker g = Ψ)
--   --     \         .
--   --      \       .
--   --       h     ∃ϕ     (want: Ψ ⊆ ker h)
--   --        \   .
--   --         \ .
--   --          V
--   --          𝑨

--   -----------------------------------
--   kerg⊆kerh : KER-pred ∣ g ∣ ⊆ KER-pred ∣ h ∣
--   kerg⊆kerh = {!!}

--   ϕ' : Σ ϕ ꞉ (hom (𝔽{𝒦}) 𝑨) , ∣ h ∣ ≡ ∣ ϕ ∣ ∘ ∣ g ∣
--   ϕ' = HomFactor gfe {𝑻{𝓤}{X}} {𝑨} {𝔽{𝒦}} h g kerg⊆kerh gE

--   --We need to find F : Algebra 𝒰 𝑆 such that F ∈ VClo and ∃ ϕ : hom F 𝑨 with ϕE : Epic ∣ ϕ ∣.
--   --Then we can prove 𝑨 ∈ VClo 𝒦 by vhom F∈VClo (𝑨 , ∣ ϕ ∣ , (∥ ϕ ∥ , ϕE))
--   -- since vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦

--   vcloF : (𝔽{𝒦}) ∈ VClo{𝒦}
--   vcloF = {!!}

--   ϕ : Σ h ꞉ (hom (𝔽{𝒦}) 𝑨) , Epic ∣ h ∣
--   ϕ = {!∣ ϕ' ∣ , ?!}

--   hiF : HomImagesOf (𝔽{𝒦})
--   hiF = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) )

--   γ : 𝑨 ∈ VClo
--   γ = vhom{𝒦}{𝔽{𝒦}} vcloF hiF
