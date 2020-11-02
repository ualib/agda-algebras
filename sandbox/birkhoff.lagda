\begin{code}
--FILE: birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--REF: Based on the file `birkhoff.agda` (23 Jan 2020).

-- {-# OPTIONS --without-K --exact-split --safe #-}
{-# OPTIONS --without-K --exact-split #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; funext; Pred; _↪_; inl; inr; ∘-embedding; id-is-embedding)

module birkhoff
 {𝑆 : Signature 𝓞 𝓥}
 {𝕏 : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {fevu : dfunext 𝓥 𝓤} where

open import closure {𝑆 = 𝑆}{𝕏 = 𝕏}{gfe = gfe}{dfe = dfe}{fevu = fevu}

--Equalizers of functions
𝑬 : {𝓠 𝓤 : Universe}{A : 𝓠 ̇ }{B : 𝓤 ̇} → (g h : A → B) → Pred A 𝓤
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


--------------------------------------------------------------------------------------------
--The free algebra

--Making this more general than the old code in that we only require 𝑨 ∈ 𝒦 instead
--of 𝑨 ∈ SClo 𝒦, because we can simply apply 𝑻img with, e.g., 𝒦 = SClo 𝒦 if necessary.
𝑻img : {𝓧 𝓤 : Universe}(X : 𝓧 ̇) → Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺ ̇
𝑻img X 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , Σ ϕ ꞉ hom (𝑻 X) 𝑨 , (𝑨 ∈ 𝒦) × Epic ∣ ϕ ∣

mkti : {𝓧 𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
       (X : 𝓧 ̇)(𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ 𝒦 → 𝑻img X 𝒦
mkti X 𝑨 KA = (𝑨 , fst thg , KA , snd thg)
 where
  thg : Σ h ꞉ (hom (𝑻 X) 𝑨), Epic ∣ h ∣
  thg = 𝑻hom-gen 𝑨

𝑻𝑨 : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 →   𝑻img X 𝒦 → Algebra 𝓤 𝑆
𝑻𝑨 ti = ∣ ti ∣

𝑻ϕ : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
     (ti : 𝑻img X 𝒦) → hom (𝑻 X) (𝑻𝑨 ti)
𝑻ϕ 𝒦 ti = fst (snd ti)

𝑻ϕE : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
      (ti : 𝑻img X 𝒦) → Epic ∣ 𝑻ϕ 𝒦 ti ∣ -- X 𝒦
𝑻ϕE ti = snd (snd ∥ ti ∥)

𝑻KER : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺ ̇
𝑻KER X 𝒦 = Σ (p , q) ꞉ (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) , ∀ 𝑨 → (KA : 𝑨 ∈ 𝒦) → (p , q) ∈ KER-pred{B = ∣ 𝑨 ∣} ∣ 𝑻ϕ 𝒦 (mkti X 𝑨 KA) ∣

Ψ : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →  Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)
Ψ X 𝒦 (p , q) = ∀(𝑨 : Algebra _ 𝑆) → (SCloA : 𝑨 ∈ SClo 𝒦)
 →  ∣ 𝑻ϕ (SClo 𝒦) (mkti X 𝑨 SCloA) ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ 𝑻ϕ (SClo 𝒦) (mkti X 𝑨 SCloA) ∣ ∘ (q ̇ 𝑻 X)

------------------------------------------------------------------
-- Alternative development
ψ : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →  Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
ψ X 𝒦 (p , q) = ∀(𝑨 : Algebra _ 𝑆) → (SCloA : 𝑨 ∈ SClo 𝒦)
 →  ∣ 𝑻ϕ (SClo 𝒦) (mkti X 𝑨 SCloA) ∣ p ≡ ∣ 𝑻ϕ (SClo 𝒦) (mkti X 𝑨 SCloA) ∣ q

ψRel : {𝓧 𝓠 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺))
 →     Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)
ψRel X 𝒦 p q = ψ X 𝒦 (p , q)

ψcompatible : {𝓧 𝓠 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺))
 →            compatible (𝑻 X) (ψRel X 𝒦)
ψcompatible X 𝒦 f {i} {j} iψj 𝑨 SCloA = γ
 where
  ti : 𝑻img X (SClo 𝒦)
  ti = mkti X 𝑨 SCloA

  ϕ : hom (𝑻 X) 𝑨
  ϕ = 𝑻ϕ (SClo 𝒦) ti

  γ : ∣ ϕ ∣ ((f ̂ 𝑻 X) i) ≡ ∣ ϕ ∣ ((f ̂ 𝑻 X) j)
  γ = ∣ ϕ ∣ ((f ̂ 𝑻 X) i) ≡⟨ ∥ ϕ ∥ f i ⟩
      (f ̂ 𝑨) (∣ ϕ ∣ ∘ i) ≡⟨ ap (f ̂ 𝑨) (gfe λ x → ((iψj x) 𝑨 SCloA)) ⟩
      (f ̂ 𝑨) (∣ ϕ ∣ ∘ j) ≡⟨ (∥ ϕ ∥ f j)⁻¹ ⟩
      ∣ ϕ ∣ ((f ̂ 𝑻 X) j) ∎

ψSym : {𝓧 𝓠 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →     symmetric (ψRel X 𝒦)
ψSym p q pψRelq 𝑪 ϕ = (pψRelq 𝑪 ϕ)⁻¹

ψTra : {𝓧 𝓠 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →     transitive (ψRel X 𝒦)
ψTra p q r pψq qψr 𝑪 ϕ = (pψq 𝑪 ϕ) ∙ (qψr 𝑪 ϕ)

ψIsEquivalence : {𝓧 𝓠 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →               IsEquivalence (ψRel X 𝒦)
ψIsEquivalence = record { rfl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁 ; sym = ψSym ; trans = ψTra }

ψCon : {𝓧 𝓠 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺))
 →     Congruence (𝑻 X) -- {𝓠 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}
ψCon X 𝒦 = mkcon (ψRel X (SClo 𝒦)) (ψcompatible X (SClo 𝒦)) ψIsEquivalence


-- Properties of ψ ------------------------------------------------------------

𝑻i⊧ψ : {𝓧 𝓤 : Universe}
       (X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
       (𝑪 : Algebra 𝓤 𝑆)(SCloC : 𝑪 ∈ SClo{𝓤} 𝒦)
       (p q : ∣ (𝑻 X) ∣)  →  (p , q) ∈ ψ X 𝒦
      --------------------------------------------------
 →     ∣ 𝑻ϕ (SClo{𝓤} 𝒦)(mkti X 𝑪 SCloC) ∣ p
         ≡ ∣ 𝑻ϕ (SClo{𝓤} 𝒦)(mkti X 𝑪 SCloC) ∣ q

𝑻i⊧ψ X 𝒦 𝑪 SCloC p q pψq = pψq 𝑪 SCloC


ψ⊆ThSClo : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →         ψ X 𝒦 ⊆ (Th (SClo 𝒦))
ψ⊆ThSClo X 𝒦 {p , q} pψq {𝑪} SCloC = γ
 where
  ti : 𝑻img X (SClo 𝒦)
  ti = mkti X 𝑪 SCloC

  ϕ : hom (𝑻 X) 𝑪
  ϕ = 𝑻ϕ (SClo 𝒦) ti

  ϕE : Epic ∣ ϕ ∣
  ϕE = 𝑻ϕE ti

  ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
  ϕsur 𝒄 x = ϕE (𝒄 x)

  pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 X ∣
  pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

  ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
  ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

-- β : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
-- β = pψq 𝑪 SCloC

  β : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
  β = pψq 𝑪 SCloC

  β' : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
  β' = {!!}
  -- ap (λ - → ∣ ϕ ∣ -) (term-agreement p)⁻¹
  γ : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
  γ = gfe λ 𝒄 →
   (p ̇ 𝑪) 𝒄                  ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
   (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
   ∣ ϕ ∣ ((p ̇ 𝑻 X)(pre 𝒄))       ≡⟨ intensionality β' (pre 𝒄) ⟩
   ∣ ϕ ∣ ((q ̇ 𝑻 X)(pre 𝒄))       ≡⟨ comm-hom-term gfe (𝑻 X) 𝑪 ϕ q (pre 𝒄) ⟩
   (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
   (q ̇ 𝑪) 𝒄                   ∎

ψ⊆Th𝒦 : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
         (p q : ∣ (𝑻 X) ∣) → (p , q) ∈ ψ X 𝒦 → 𝒦 ⊧ p ≋ q
ψ⊆Th𝒦  X 𝒦 p q pψq {𝑨} KA = ψ⊆ThSClo X 𝒦 {p , q} pψq (sbase KA)






































-- Recall, `mkti X 𝑨 SCloA` has type `𝑻img X (SClo 𝒦)` and consists of a quadruple:
-- (𝑨 , ϕ , SCloA , ϕE), where 𝑨 : Algebra _ 𝑆 , ϕ : hom (𝑻 X) 𝑨 , SCloA : 𝑨 ∈ SClo 𝒦 , ϕE : Epic ∣ ϕ ∣

ΨRel : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) → Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)
ΨRel X 𝒦 p q = Ψ X 𝒦 (p , q)

Ψcompatible : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →            compatible{𝓤 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓦 = (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⊔ 𝓧 ⁺)} (𝑻 X)(ΨRel X 𝒦)
Ψcompatible X 𝒦 f {𝒕} {𝒔} 𝒕Ψ𝒔 𝑨 SCloA = γ
 where
  ϕ : hom (𝑻 X) 𝑨
  ϕ = 𝑻ϕ (SClo 𝒦) (mkti X 𝑨 SCloA)

  ΨH : ∀ 𝒂 i → (∣ ϕ ∣ ∘ (𝒕 i ̇ 𝑻 X)) 𝒂 ≡ (∣ ϕ ∣ ∘ (𝒔 i ̇ 𝑻 X))𝒂
  ΨH 𝒂 i = ap (λ - → - 𝒂)((𝒕Ψ𝒔 i) 𝑨 SCloA)

  γ : ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻 X)(λ i → (𝒕 i ̇ 𝑻 X)𝒂)) ≡ ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻 X)(λ i → (𝒔 i ̇ 𝑻 X)𝒂))
  γ =
    ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻 X)(λ i → (𝒕 i ̇ 𝑻 X) 𝒂))  ≡⟨ i  ⟩
    (λ 𝒂 → (f ̂ 𝑨)(λ i → ((∣ ϕ ∣ ∘ (𝒕 i ̇ 𝑻 X))𝒂))) ≡⟨ ii ⟩
    (λ 𝒂 → (f ̂ 𝑨)(λ i → ((∣ ϕ ∣ ∘ (𝒔 i ̇ 𝑻 X))𝒂))) ≡⟨ iii ⟩
    ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻 X)(λ i → (𝒔 i ̇ 𝑻 X)𝒂))   ∎
   where
    i = gfe (λ 𝒂 → ∥ ϕ ∥ f (λ i → (𝒕 i ̇ 𝑻 X) 𝒂))
    ii = gfe (λ 𝒂 → ap (f ̂ 𝑨) (gfe λ i → ΨH 𝒂 i) )
    iii = (gfe (λ 𝒂 → ∥ ϕ ∥ f (λ i → (𝒔 i ̇ 𝑻 X) 𝒂)))⁻¹

ΨSym : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 →     symmetric (ΨRel X 𝒦)
ΨSym p q pΨRelq 𝑪 ϕ = (pΨRelq 𝑪 ϕ)⁻¹

ΨTra : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 →     transitive (ΨRel X 𝒦)
ΨTra p q r pΨq qΨr 𝑪 ϕ = (pΨq 𝑪 ϕ) ∙ (qΨr 𝑪 ϕ)

ΨIsEquivalence : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 →               IsEquivalence (ΨRel X 𝒦)
ΨIsEquivalence = record { rfl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁 ; sym = ΨSym ; trans = ΨTra }

ΨCon : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →     Congruence{𝓠 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓤 = (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)} (𝑻 X)
ΨCon X 𝒦 = mkcon (ΨRel X 𝒦) (Ψcompatible X 𝒦) ΨIsEquivalence


-- Properties of Ψ ------------------------------------------------------------

𝑻i⊧Ψ : {𝓧 𝓤 : Universe}
       (X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
       (𝑪 : Algebra 𝓤 𝑆)(SCloC : 𝑪 ∈ SClo{𝓤 = 𝓤} 𝒦)
       (p q : ∣ (𝑻 X) ∣)  →  (p , q) ∈ Ψ X 𝒦
      --------------------------------------------------
 →     ∣ 𝑻ϕ (SClo 𝒦) (mkti X 𝑪 SCloC) ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ 𝑻ϕ (SClo 𝒦) (mkti X 𝑪 SCloC) ∣ ∘ (q ̇ 𝑻 X)

𝑻i⊧Ψ X 𝒦 𝑪 SCloC p q pΨq = pCq
 where

  ϕ : hom (𝑻 X) 𝑪
  ϕ = 𝑻ϕ (SClo 𝒦) (mkti X 𝑪 SCloC)

  pCq : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
  pCq = pΨq 𝑪 SCloC


Ψ⊆ThSClo : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →         Ψ X 𝒦 ⊆ (Th (SClo 𝒦))
Ψ⊆ThSClo X 𝒦 {p , q} pΨq {𝑪} SCloC = γ
 where
  ti : 𝑻img X (SClo 𝒦)
  ti = mkti X 𝑪 SCloC

  ϕ : hom (𝑻 X) 𝑪
  ϕ = 𝑻ϕ (SClo 𝒦) ti

  ϕE : Epic ∣ ϕ ∣
  ϕE = 𝑻ϕE ti

  ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
  ϕsur 𝒄 x = ϕE (𝒄 x)

  pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 X ∣
  pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

  ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
  ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

  β : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
  β = pΨq 𝑪 SCloC

  γ : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
  γ = gfe λ 𝒄 →
   (p ̇ 𝑪) 𝒄                  ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
   (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
   ∣ ϕ ∣ ((p ̇ 𝑻 X)(pre 𝒄))       ≡⟨ intensionality β (pre 𝒄) ⟩
   ∣ ϕ ∣ ((q ̇ 𝑻 X)(pre 𝒄))       ≡⟨ comm-hom-term gfe (𝑻 X) 𝑪 ϕ q (pre 𝒄) ⟩
   (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
   (q ̇ 𝑪) 𝒄                   ∎

Ψ⊆Th𝒦 : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
         (p q : ∣ (𝑻 X) ∣) → (p , q) ∈ Ψ X 𝒦 → 𝒦 ⊧ p ≋ q
Ψ⊆Th𝒦  X 𝒦 p q pΨq {𝑨} KA = Ψ⊆ThSClo X 𝒦 {p , q} pΨq (sbase KA)


------------------
--Class Identities

--It follows from `vclo-id1` that, if 𝒦 is a class of structures, the set of identities
-- modeled by all structures in 𝒦 is the same as the set of identities modeled by all structures in VClo 𝒦.

-- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
class-identities : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
                   (p q : ∣ 𝑻 X ∣)
                  ----------------------------------------------------------
 →                 𝒦 ⊧ p ≋ q  ⇔  ((p , q) ∈ Th (VClo 𝒦))

class-identities p q = (λ α VCloA → vclo-id1 p q α VCloA) , (λ Thpq KA → Thpq (vbase KA))



-----------------------------------------------------------------------------------
-- Lemma 4.27. Let 𝒦 be a class of algebras, and ΨCon defined as above.
-- Then 𝔽 := 𝑻/ΨCon is isomorphic to an algebra in SP(𝒦).
-- Proof. 𝔽 ↪ ⨅ 𝒜, where 𝒜 = {𝑨/θ : 𝑨/θ ∈ S(𝒦)}.
--        Therefore, 𝔽 ≅ 𝑩, where 𝑩 is a subalgebra of ⨅ 𝒜 ∈ PS(𝒦).
--        Thus 𝔽 is isomorphic to an algebra in SPS(𝒦).
--        By SPS⊆SP, 𝔽 is isomorphic to an algebra in SP(𝒦).
-- _IsSubalgebraOf_ : {𝓤 𝓠 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇
-- 𝑩 IsSubalgebraOf 𝑨 = Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) , is-embedding h × is-homomorphism 𝑩 𝑨 h

-----------------------------------------------------------------------------------
-- The (relatively) free algebra

𝔽 : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →   Algebra ((𝓞  ⊔ 𝓥 ⊔ (𝓧 ⊔ 𝓤)⁺) ⁺) 𝑆
𝔽 X 𝒦 = 𝑻 X ╱ (ΨCon X 𝒦)


𝔽free-lift : {𝓧 𝓠 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
              (𝑨 : Algebra 𝓤 𝑆)(f : X → ∣ 𝑨 ∣) → ∣ 𝔽 X 𝒦 ∣ → ∣ 𝑨 ∣
𝔽free-lift {𝓧}{𝓠}{𝓤} 𝑨 f (_ , x , _) = (free-lift{𝓧}{𝓤} 𝑨 f) x

𝔽free-lift-interpretation : {𝓧 𝓠 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
              (𝑨 : Algebra 𝓤 𝑆)(f : X → ∣ 𝑨 ∣)(𝒙 : ∣ 𝔽 X 𝒦 ∣)
 →             (⌜ 𝒙 ⌝ ̇ 𝑨) f ≡ 𝔽free-lift 𝑨 f 𝒙
𝔽free-lift-interpretation 𝑨 f 𝒙 = free-lift-interpretation 𝑨 f ⌜ 𝒙 ⌝


𝔽lift-hom : {𝓧 𝓠 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) _)
             (𝑨 : Algebra 𝓤 𝑆)(f : X → ∣ 𝑨 ∣) → hom (𝔽 X 𝒦) 𝑨
𝔽lift-hom {𝓧}{𝓠}{𝓤} X 𝒦 𝑨 f = h , hhm
 where
  h : ∣ 𝔽 X 𝒦 ∣ → ∣ 𝑨 ∣
  h = 𝔽free-lift 𝑨 f

  h₀ : hom (𝑻 X) 𝑨
  h₀ = lift-hom 𝑨 f

  θ : Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ (𝓠 ⊔ 𝓧)⁺)
  θ = Congruence.⟨ ΨCon X 𝒦 ⟩

  hhm : is-homomorphism (𝔽 X 𝒦) 𝑨 h
  hhm 𝑓 𝒂 = ∥ h₀ ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝  )

𝔽lift-agrees-on-X : {𝓧 𝓠 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) _)
                     (𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣)(x : X)
                     ----------------------------------------
 →                    h₀ x ≡ ( ∣ 𝔽lift-hom X 𝒦 𝑨 h₀ ∣ ⟦ Term.generator x ⟧ )

𝔽lift-agrees-on-X _ _ _ h₀ x = 𝓇ℯ𝒻𝓁

𝔽lift-of-epic-is-epic : {𝓧 𝓠 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) _)
                         (𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣)
 →                        Epic h₀
                         -----------------------
 →                        Epic ∣ 𝔽lift-hom X 𝒦 𝑨 h₀ ∣

𝔽lift-of-epic-is-epic {𝓧}{𝓠}{𝓤} X 𝒦 𝑨 h₀ hE y = γ
 where
  h₀pre : Image h₀ ∋ y
  h₀pre = hE y

  h₀⁻¹y : X
  h₀⁻¹y = Inv h₀ y (hE y)

  η : y ≡ ( ∣ 𝔽lift-hom X 𝒦 𝑨 h₀ ∣ ⟦ Term.generator (h₀⁻¹y) ⟧ )
  η = y          ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
      h₀ h₀⁻¹y   ≡⟨ (𝔽lift-agrees-on-X) X 𝒦 𝑨 h₀ h₀⁻¹y ⟩
      ∣ 𝔽lift-hom X 𝒦 𝑨 h₀ ∣ ⟦ (Term.generator h₀⁻¹y) ⟧ ∎

  γ : Image ∣ 𝔽lift-hom X 𝒦 𝑨 h₀ ∣ ∋ y
  γ = eq y (⟦ Term.generator h₀⁻¹y ⟧) η

X↪𝔽 : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 →      X → ∣ 𝔽 X 𝒦 ∣
X↪𝔽 x = ⟦ Term.generator x ⟧

Ψlem : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →     (p q : ∣ 𝑻 X ∣ )
 →     ∣ lift-hom (𝔽 X 𝒦) X↪𝔽 ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ lift-hom (𝔽 X 𝒦) X↪𝔽 ∣ ∘ (q ̇ 𝑻 X)
      ---------------------------
 →     (p , q) ∈ Ψ X 𝒦

Ψlem X 𝒦 p q gpgq 𝑨 SCloA = γ
 where
  g : hom (𝑻 X) (𝔽 X 𝒦)
  g = lift-hom (𝔽 X 𝒦) (X↪𝔽)

  h₀ : X → ∣ 𝑨 ∣
  h₀ = fst (𝕏 𝑨)

  f : hom (𝔽 X 𝒦) 𝑨
  f = 𝔽lift-hom X 𝒦 𝑨 h₀

  h h' : hom (𝑻 X) 𝑨
  h = lift-hom 𝑨 h₀
  h' = HCompClosed (𝑻 X) (𝔽 X 𝒦) 𝑨 g f

  ϕ : hom (𝑻 X) 𝑨
  ϕ = 𝑻ϕ (SClo 𝒦) (mkti X 𝑨 SCloA)

  lift-agreement : (x : X) → h₀ x ≡ ∣ f ∣ ⟦ Term.generator x ⟧
  lift-agreement x = 𝔽lift-agrees-on-X X 𝒦 𝑨 h₀ x

  fgx≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ g ∣) (Term.generator x) ≡ ∣ ϕ ∣ (Term.generator x)
  fgx≡ϕ x = (lift-agreement x)⁻¹

  h'≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ g ∣) t ≡ ∣ ϕ ∣ t
  h'≡ϕ t = free-unique gfe 𝑨 h' ϕ fgx≡ϕ t

  η : ∀ t → ∣ g ∣ ((p ̇ 𝑻 X) t) ≡ ∣ g ∣ ((q ̇ 𝑻 X) t)
  η t = intensionality gpgq t

  γ : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
  γ = gfe λ x →
   ∣ ϕ ∣ ((p ̇ 𝑻 X) x) ≡⟨ (h'≡ϕ ((p ̇ 𝑻 X) x))⁻¹ ⟩
   (∣ f ∣ ∘ ∣ g ∣) ((p ̇ 𝑻 X) x) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
   ∣ f ∣ ( ∣ g ∣ ((p ̇ 𝑻 X) x)) ≡⟨ ap ∣ f ∣ (η x) ⟩
   ∣ f ∣ ( ∣ g ∣ ((q ̇ 𝑻 X) x)) ≡⟨ h'≡ϕ ((q ̇ 𝑻 X) x) ⟩
   ∣ ϕ ∣ ((q ̇ 𝑻 X) x) ∎



-- Alternative development (with little ψ)


𝔉 : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →   Algebra ((𝓞  ⊔ 𝓥 ⊔ (𝓧 ⊔ 𝓤)⁺) ⁺) 𝑆
𝔉 X 𝒦 = 𝑻 X ╱ (ψCon X 𝒦)

𝔉≤IAS : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝑲 : (𝓠 : Universe) → Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →      Σ 𝑰 ꞉ (𝕀{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (SClo (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)))) ,
             (𝔉 X (𝑲 𝓤)) IsSubalgebraOf (I→Alg{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺}{SClo (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺))} 𝑰)
𝔉≤IAS = {!!}

𝔉∈SP : {𝓤 : Universe} → hfunext ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)
 →      {X : 𝓤 ̇}{𝑲 : (𝓠 : Universe) → Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →      (𝔉{𝓤}{𝓤} X (𝑲 𝓤)) ∈ (SClo{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (PClo{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺))))
𝔉∈SP{𝓤} hfe {X}{𝑲} = γ
 where
  IAS = 𝔉≤IAS{𝓤}{𝓤}{X}{𝑲}

  𝑰 :  𝕀{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (SClo{((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)} (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)))
  𝑰 = ∣ IAS ∣

  𝑨 : Algebra ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺) 𝑆
  𝑨 = I→Alg{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺}{SClo (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺))} 𝑰

  𝑨∈SP : 𝑨 ∈ (SClo{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (PClo{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺))))
  𝑨∈SP = IAS∈SP{𝓤} hfe{𝑲} 𝑰

  𝔉isSub : (𝔉 X (𝑲 𝓤)) IsSubalgebraOf (I→Alg{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺}{SClo (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺))} 𝑰)
  𝔉isSub = ∥ IAS ∥

  γ : 𝔉 X (𝑲 𝓤) ∈ SClo{𝓤 = ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)} (PClo{𝓤 = ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)} (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)))
  γ = sub{𝓤 = ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)} {𝑨 = 𝑨} 𝑨∈SP (𝔉 X (𝑲 𝓤) , 𝔉isSub)

𝔉∈V : {𝓤 : Universe} → hfunext ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)
 →      {X : 𝓤 ̇}{𝑲 : (𝓠 : Universe) → Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →      (𝔉{𝓤}{𝓤} X (𝑲 𝓤)) ∈ (VClo{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)))
𝔉∈V {𝓤} hfe {X}{𝑲} = SP⊆V{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (𝔉∈SP{𝓤} hfe {X}{𝑲})


𝔉-free-lift : {𝓧 𝓠 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
              (𝑨 : Algebra 𝓤 𝑆)(f : X → ∣ 𝑨 ∣) → ∣ 𝔉 X 𝒦 ∣ → ∣ 𝑨 ∣
𝔉-free-lift {𝓧}{𝓠}{𝓤} 𝑨 f (_ , x , _) = (free-lift{𝓧}{𝓤} 𝑨 f) x

𝔉-free-lift-interpretation : {𝓧 𝓠 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
              (𝑨 : Algebra 𝓤 𝑆)(f : X → ∣ 𝑨 ∣)(𝒙 : ∣ 𝔉 X 𝒦 ∣)
 →             (⌜ 𝒙 ⌝ ̇ 𝑨) f ≡ 𝔉-free-lift 𝑨 f 𝒙
𝔉-free-lift-interpretation 𝑨 f 𝒙 = free-lift-interpretation 𝑨 f ⌜ 𝒙 ⌝


𝔉-lift-hom : {𝓧 𝓠 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) _)
             (𝑨 : Algebra 𝓤 𝑆)(f : X → ∣ 𝑨 ∣) → hom (𝔉 X 𝒦) 𝑨
𝔉-lift-hom {𝓧}{𝓠}{𝓤} X 𝒦 𝑨 f = h , hhm
 where
  h : ∣ 𝔉 X 𝒦 ∣ → ∣ 𝑨 ∣
  h = 𝔉-free-lift 𝑨 f

  h₀ : hom (𝑻 X) 𝑨
  h₀ = lift-hom 𝑨 f

  θ : Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)
  θ = Congruence.⟨ ψCon X 𝒦 ⟩

  hhm : is-homomorphism (𝔉 X 𝒦) 𝑨 h
  hhm 𝑓 𝒂 = ∥ h₀ ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝  )

𝔉-lift-agrees-on-X : {𝓧 𝓠 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) _)
                     (𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣)(x : X)
                     ----------------------------------------
 →                    h₀ x ≡ ( ∣ 𝔉-lift-hom X 𝒦 𝑨 h₀ ∣ ⟦ Term.generator x ⟧ )

𝔉-lift-agrees-on-X _ _ _ h₀ x = 𝓇ℯ𝒻𝓁

𝔉-lift-of-epic-is-epic : {𝓧 𝓠 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) _)
                         (𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣)
 →                        Epic h₀
                         -----------------------
 →                        Epic ∣ 𝔉-lift-hom X 𝒦 𝑨 h₀ ∣

𝔉-lift-of-epic-is-epic {𝓧}{𝓠}{𝓤} X 𝒦 𝑨 h₀ hE y = γ
 where
  h₀pre : Image h₀ ∋ y
  h₀pre = hE y

  h₀⁻¹y : X
  h₀⁻¹y = Inv h₀ y (hE y)

  η : y ≡ ( ∣ 𝔉-lift-hom X 𝒦 𝑨 h₀ ∣ ⟦ Term.generator (h₀⁻¹y) ⟧ )
  η = y          ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
      h₀ h₀⁻¹y   ≡⟨ (𝔉-lift-agrees-on-X) X 𝒦 𝑨 h₀ h₀⁻¹y ⟩
      ∣ 𝔉-lift-hom X 𝒦 𝑨 h₀ ∣ ⟦ (Term.generator h₀⁻¹y) ⟧ ∎

  γ : Image ∣ 𝔉-lift-hom X 𝒦 𝑨 h₀ ∣ ∋ y
  γ = eq y (⟦ Term.generator h₀⁻¹y ⟧) η

X↪𝔉 : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 →      X → ∣ 𝔉 X 𝒦 ∣
X↪𝔉 x = ⟦ Term.generator x ⟧


ψlem : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →     (p q : ∣ 𝑻 X ∣ )
 →     ∣ lift-hom (𝔉 X 𝒦) X↪𝔉 ∣ p ≡ ∣ lift-hom (𝔉 X 𝒦) X↪𝔉 ∣ q
      ---------------------------
 →     (p , q) ∈ ψ X 𝒦

ψlem X 𝒦 p q gpgq 𝑨 SCloA = γ
 where
  g : hom (𝑻 X) (𝔉 X 𝒦)
  g = lift-hom (𝔉 X 𝒦) (X↪𝔉)

  h₀ : X → ∣ 𝑨 ∣
  h₀ = fst (𝕏 𝑨)

  f : hom (𝔉 X 𝒦) 𝑨
  f = 𝔉-lift-hom X 𝒦 𝑨 h₀

  h h' : hom (𝑻 X) 𝑨
  h = lift-hom 𝑨 h₀
  h' = HCompClosed (𝑻 X) (𝔉 X 𝒦) 𝑨 g f

  ϕ : hom (𝑻 X) 𝑨
  ϕ = 𝑻ϕ (SClo 𝒦) (mkti X 𝑨 SCloA)

  lift-agreement : (x : X) → h₀ x ≡ ∣ f ∣ ⟦ Term.generator x ⟧
  lift-agreement x = 𝔉-lift-agrees-on-X X 𝒦 𝑨 h₀ x

  fgx≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ g ∣) (Term.generator x) ≡ ∣ ϕ ∣ (Term.generator x)
  fgx≡ϕ x = (lift-agreement x)⁻¹

  h'≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ g ∣) t ≡ ∣ ϕ ∣ t
  h'≡ϕ t = free-unique gfe 𝑨 h' ϕ fgx≡ϕ t

  η : ∣ g ∣ p ≡ ∣ g ∣ q
  η = gpgq

  γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
  γ = ∣ ϕ ∣ p ≡⟨ (h'≡ϕ p)⁻¹ ⟩ (∣ f ∣ ∘ ∣ g ∣) p
             ≡⟨ 𝓇ℯ𝒻𝓁 ⟩ ∣ f ∣ ( ∣ g ∣ p )
             ≡⟨ ap ∣ f ∣ η ⟩ ∣ f ∣ ( ∣ g ∣ q )
             ≡⟨ h'≡ϕ q ⟩ ∣ ϕ ∣ q ∎


--Example
-- ⨅SClo : {𝓤 : Universe} → Pred (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) 𝑆) ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)  → Algebra ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺) 𝑆
-- ⨅SClo{𝓤} 𝒦 = ⨅Class{𝓤} (SClo 𝒦)

-- ⨅S≤PS : {𝓤 : Universe}{𝒦 : Pred (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) 𝑆) ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)}
--  →       Σ 𝑨 ꞉ Algebra _ 𝑆 , (𝑨 ∈ PClo{𝓤 = (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)} 𝒦) × ((⨅SClo{𝓤 = 𝓤} 𝒦) IsSubalgebraOf 𝑨)
-- ⨅S≤PS = {!!} , {!!}

-- Birkhoff's theorem (ψ version): every variety is an equational class.
birkhoff : {𝓤 : Universe} → hfunext ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺)
 →         {X : 𝓤 ̇} {𝑲 : (𝓠 : Universe) → Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
           (𝑨 : Algebra ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺) 𝑆)
 →          𝑨 ∈ Mod (Th (VClo{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺))))
           -------------------------------------------------------------------------------
 →          𝑨 ∈ VClo (𝑲 ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺))

birkhoff {𝓤} hfe {X}{𝑲} 𝑨 ModThVCloA = γ
 where
  FU : Universe
  FU = (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺

  𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
  𝒦 = 𝑲 𝓤

  𝒦' : Pred (Algebra FU 𝑆) (𝓞 ⊔ 𝓥 ⊔ FU ⁺)
  𝒦' = 𝑲 FU

  F : Algebra FU 𝑆
  F = 𝔉 X 𝒦

  T : Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) 𝑆
  T = 𝑻 X

  h₀ : X → ∣ 𝑨 ∣
  h₀ = fst (𝕏 𝑨)

  h₀E : Epic h₀
  h₀E = snd (𝕏 𝑨)

  h : hom T 𝑨
  h = lift-hom 𝑨 h₀

  hE : Epic ∣ h ∣
  hE = lift-of-epic-is-epic 𝑨 h₀ h₀E

  ψ⊆ThVClo : ψ X 𝒦' ⊆ Th{FU}{𝓤} (VClo{𝓤 = FU} 𝒦')
  ψ⊆ThVClo {p , q} pψq =
   (lr-implication (class-identities p q)) (ψ⊆Th𝒦 X 𝒦' p q pψq)

  ψ⊆A⊧ : ∀{p}{q} → (p , q) ∈ ψ X 𝒦' → 𝑨 ⊧ p ≈ q
  ψ⊆A⊧ {p} {q} pψq = ModThVCloA p q (ψ⊆ThVClo {p , q} pψq)

  ψ⊆Kerh : ψ X 𝒦' ⊆ KER-pred{B = ∣ 𝑨 ∣} ∣ h ∣
  ψ⊆Kerh {p , q} pψq = hp≡hq
   where
    hp≡hq : ∣ h ∣ p ≡ ∣ h ∣ q
    hp≡hq = hom-id-compatibility p q 𝑨 h (ψ⊆A⊧{p}{q} pψq)

  gg : Σ g ꞉ hom T F , Epic ∣ g ∣
  gg = (lift-hom F g₀) , (lift-of-epic-is-epic{𝓤}{(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)⁺} F g₀ g₀E)

   where
    g₀ : X → ∣ F ∣
    g₀ = fst (𝕏 F)

    g₀E : Epic g₀
    g₀E = snd (𝕏 F)

  g' : hom (𝑻 X)(𝔉 X 𝒦')
  g' = lift-hom (𝔉 X 𝒦') X↪𝔉

  g : hom T F
  g = fst gg

  gE : Epic ∣ g ∣
  gE = snd gg

  τ : (𝑨 : Algebra FU 𝑆)(SCloA : SClo 𝒦' 𝑨) → hom (𝑻 X) 𝑨
  τ 𝑨 SCloA = 𝑻ϕ (SClo 𝒦') (mkti X 𝑨 SCloA)

  kerg : (KER-pred{A = ∣ 𝑻 X ∣}{B = ∣ 𝔉 X 𝒦' ∣} ∣ g' ∣) ⊆ ψ X 𝒦'
  kerg {p , q} gpgq = ψlem X 𝒦' p q gpgq

  kerg⊆kerh : KER-pred ∣ g' ∣ ⊆ KER-pred ∣ h ∣
  kerg⊆kerh {x , y} gx≡gy = ψ⊆Kerh {x , y}(kerg{x , y} gx≡gy)

  -- N.B. Ψ is the kernel of 𝑻 → 𝔽(𝒦, 𝑻).  Therefore, to prove 𝑨 is a homomorphic image of 𝔽(𝒦, 𝑻),
  -- it suffices to show that the kernel of the lift h : 𝑻 → 𝑨 contains Ψ.
  --
  --    𝑻---- g --->>𝑻/ψ    ψ = ker g ⊆ ker h => ∃ ϕ: T/ψ → A
  --    𝑻---- g --->>𝔽  (ker g = Ψ)
  --     \         .
  --      \       .
  --       h     ∃ϕ     (want: Ψ ⊆ ker h)
  --        \   .
  --         \ .
  --          V
  --          𝑨
  -- ϕ' : Σ ϕ ꞉ (hom F 𝑨) , ∣ h ∣ ≡ ∣ ϕ ∣ ∘ ∣ g ∣
  -- ϕ' = HomFactor {𝓠 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓤 = FU}{𝓦 = FU}
  --                gfe {T} {𝑨} {F} h g kerg⊆kerh gE

  --We need to find F : Algebra 𝒰 𝑆 such that F ∈ VClo and ∃ ϕ : hom F 𝑨 with ϕE : Epic ∣ ϕ ∣.
  --Then we can prove 𝑨 ∈ VClo 𝒦 by vhom F∈VClo (𝑨 , ∣ ϕ ∣ , (∥ ϕ ∥ , ϕE))
  -- since vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦

  vcloF : F ∈ VClo{𝓤 = FU} 𝒦'
  vcloF = 𝔉∈V{𝓤} hfe{X}{𝑲}

  ϕ : Σ h ꞉ (hom F 𝑨) , Epic ∣ h ∣
  ϕ = (𝔉-lift-hom X 𝒦 𝑨 h₀) , 𝔉-lift-of-epic-is-epic X 𝒦 𝑨 h₀ h₀E

  hiF : HomImagesOf F
  hiF = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) )

  -- Finally, use 𝔽∈SP𝒦 to get an algebra 𝑩 ∈ VClo 𝒦 such that 𝔽 ≅ 𝑩.
  -- Then ∃ hom h : hom 𝑩 𝔽, so we can simply compose ϕ ∘ h : hom 𝑩 𝑨,
  -- which proves that 𝑨 ∈ VClo 𝒦, as desired.

  γ : 𝑨 ∈ VClo 𝒦'
  γ = vhom vcloF hiF

























-- Original development (with big Ψ)
-- Birkhoff's theorem: every variety is an equational class.
-- Birkhoff : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
--            {𝑲 : (𝓠 : Universe) → Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--            (𝑨 : Algebra ((𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)⁺) 𝑆)
--  →          𝑨 ∈ Mod (Th (VClo{𝓤 = (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)⁺} (𝑲 ((𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)⁺))))
--            -------------------------------------------------------------------------------
--  →          𝑨 ∈ VClo (𝑲 ((𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)⁺))

-- Birkhoff {𝓤}{𝓧}{X}{𝑲} 𝑨 ModThVCloA = γ
--  where
--   FU : Universe
--   FU = (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)⁺

--   𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
--   𝒦 = 𝑲 𝓤

--   𝒦' : Pred (Algebra FU 𝑆) (𝓞 ⊔ 𝓥 ⊔ FU ⁺)
--   𝒦' = 𝑲 FU

--   F : Algebra FU 𝑆
--   F = 𝔽 X 𝒦

--   T : Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺) 𝑆
--   T = 𝑻 X

--   h₀ : X → ∣ 𝑨 ∣
--   h₀ = fst (𝕏 𝑨)

--   h₀E : Epic h₀
--   h₀E = snd (𝕏 𝑨)

--   h : hom T 𝑨
--   h = lift-hom 𝑨 h₀

--   hE : Epic ∣ h ∣
--   hE = lift-of-epic-is-epic 𝑨 h₀ h₀E

--   Ψ⊆ThVClo : Ψ X 𝒦' ⊆ Th{𝓤 = FU}{𝓧} (VClo{𝓤 = FU} 𝒦')
--   Ψ⊆ThVClo {p , q} pΨq =
--    (lr-implication (class-identities p q)) (Ψ⊆Th𝒦 X 𝒦' p q pΨq)

--   Ψ⊆A⊧ : ∀{p}{q} → (p , q) ∈ Ψ X 𝒦' → 𝑨 ⊧ p ≈ q
--   Ψ⊆A⊧ {p} {q} pΨq = ModThVCloA p q (Ψ⊆ThVClo {p , q} pΨq)

--   Ψ⊆Kerh : Ψ X 𝒦' ⊆ KER-pred{B = ∣ 𝑨 ∣} ∣ h ∣
--   Ψ⊆Kerh {p , q} pΨq = hp≡hq
--    where
--     hp≡hq : ∣ h ∣ p ≡ ∣ h ∣ q
--     hp≡hq = hom-id-compatibility p q 𝑨 h (Ψ⊆A⊧{p}{q} pΨq)

--   gg : Σ g ꞉ hom T F , Epic ∣ g ∣
--   gg = (lift-hom F g₀) , (lift-of-epic-is-epic{𝓤 = (𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ (𝓤 ⊔ 𝓧) ⁺ ⁺)} F g₀ g₀E)

--    where
--     g₀ : X → ∣ F ∣
--     g₀ = fst (𝕏 F)

--     g₀E : Epic g₀
--     g₀E = snd (𝕏 F)

--   g' : hom (𝑻 X)(𝔽 X 𝒦')
--   g' = lift-hom (𝔽 X 𝒦') X↪𝔽

--   g : hom T F
--   g = fst gg

--   gE : Epic ∣ g ∣
--   gE = snd gg

--   τ : (𝑨 : Algebra FU 𝑆)(SCloA : SClo 𝒦' 𝑨) → hom (𝑻 X) 𝑨
--   τ 𝑨 SCloA = 𝑻ϕ (SClo 𝒦') (mkti X 𝑨 SCloA)

--   kerg : (KER-pred{A = ∣ 𝑻 X ∣}{B = ∣ 𝔽 X 𝒦' ∣} ∣ g' ∣) ⊆ Ψ X 𝒦'
--   kerg {p , q} gpgq = Ψlem X 𝒦' p q μ
--    where
--     gpq : ∣ g' ∣ p ≡ ∣ g' ∣ q
--     gpq = gpgq
--     μ : ∣ g' ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ g' ∣ ∘ (q ̇ 𝑻 X)
--     μ = {!!}

--   kerg⊆kerh : KER-pred ∣ g' ∣ ⊆ KER-pred ∣ h ∣
--   kerg⊆kerh {x , y} gx≡gy = Ψ⊆Kerh {x , y}(kerg{x , y} gx≡gy)

--   vcloF : F ∈ VClo{𝓤 = FU} 𝒦'
--   vcloF = {!!}

--   ϕ : Σ h ꞉ (hom F 𝑨) , Epic ∣ h ∣
--   ϕ = (𝔽lift-hom X 𝒦 𝑨 h₀) , 𝔽lift-of-epic-is-epic X 𝒦 𝑨 h₀ h₀E

--   hiF : HomImagesOf F
--   hiF = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) )

--   γ : 𝑨 ∈ VClo 𝒦'
--   γ = vhom vcloF hiF































-- 𝔽∈SPS : {𝓧 𝓠 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺))
--  →       Σ 𝑨 ꞉ (Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺) 𝑆) , (𝑨 ∈ SClo (PClo (SClo 𝒦))) × (𝑨 ≅ 𝔽 X 𝒦)
-- 𝔽∈SPS{𝓧}{𝓠}{𝓤} X 𝒦 = {!⨅SClo{𝓠} 𝒦!} , {!!}

-- 𝔽≤⨅SClo : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra (𝓞 ⊔ 𝓥 ⊔ (𝓧 ⊔ 𝓤)) 𝑆) (𝓞 ⊔ 𝓥 ⊔ (𝓞 ⊔ 𝓥 ⊔ (𝓧 ⊔ 𝓤))⁺))
--  -- →       𝔽{𝓧}{((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))} X 𝒦 IsSubalgebraOf (⨅SClo 𝒦)
--  →       𝔽 X 𝒦 IsSubalgebraOf (⨅SClo{𝓤 = ((𝓞 ⊔ 𝓥 ⊔ (𝓧 ⊔ 𝓤)))} 𝒦)
-- 𝔽≤⨅SClo{𝓧}{𝓤} X 𝒦 = ∣ 𝔥 ∣ , (𝔥emb , ∥ 𝔥 ∥)
--  where
--   f : X → ∣ ⨅SClo 𝒦 ∣
--   f = ∣ 𝕏 (⨅SClo 𝒦) ∣

--   𝔥 : hom (𝔽 X 𝒦) (⨅SClo 𝒦)
--   𝔥 = 𝔽lift-hom X 𝒦 (⨅SClo 𝒦) f

--   𝔥emb : is-embedding ∣ 𝔥 ∣
--   𝔥emb 𝒂 fib1 fib2 = γ
--    where
--     h1h2 : ∣ 𝔥 ∣ (∣ fib1 ∣) ≡ ∣ 𝔥 ∣ (∣ fib2 ∣)
--     h1h2 = (snd fib1) ∙ (snd fib2)⁻¹

--     -- Notice that ∣ 𝔥 ∣ x ≡ ∣ 𝔥 ∣ y means that the pair (x, y) ∈ ∣ 𝔽 X 𝒦 ∣ satisfies the following:
--     -- For *every* 𝑨 ∈ SClo 𝒦, the equation  We should be able to prove (x , y) ∈ Ψ X 𝒦
--     -- 𝔥11 : ∀ x y → ∣ 𝔥 ∣ x ≡ ∣ 𝔥 ∣ y →  x ≡ y
--     -- 𝔥11 (pr₃ , pr₄) y hxhy = {!!}

--     𝔥e : ∀ x y → ∣ 𝔥 ∣ x ≡ ∣ 𝔥 ∣ y
--      →   (𝑨 : Algebra _ 𝑆)(h : X → ∣ 𝑨 ∣ ) → 𝑨 ∈ SClo 𝒦
--      →   (⌜ x ⌝ ̇ 𝑨) h ≡ (⌜ y ⌝ ̇ 𝑨) h
--     𝔥e x y hxhy 𝑨 h SCloA = {!!}

--     -- Ψ⊆ker𝔥 : (Ψ X 𝒦)  ⊆  KER-pred{𝓦 = (𝓞 ⊔ 𝓥 ⊔ (𝓧 ⊔ 𝓤) ⁺)}{A = ∣ 𝔽 X 𝒦 ∣ }{B = ∣ ⨅SClo{𝓤 = 𝓤} 𝒦 ∣} ∣ 𝔥 ∣
--     -- Ψ⊆ker𝔥 = ?

--     γ : fib1 ≡ fib2
--     γ = {!!}


-- 𝔽∈SPS : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧) ⁺) 𝑆) (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧) ⁺))
--  →       (𝔽 X 𝒦) ∈ SClo (PClo (SClo{𝓤 = (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧) ⁺)} 𝒦))
-- 𝔽∈SPS = ?

  -- 𝔥 : ∣ 𝔽 X 𝒦 ∣ → ∣ ⨅SClo 𝒦 ∣
  -- 𝔥 x 𝑰 i = α
  --  where
  --   I = ∣ 𝑰 ∣                                 --   I : 𝓤 ̇
  --   𝒜 = fst ∥ 𝑰 ∥                            --   𝒜 : I → Algebra 𝓤 𝑆
  --   SCloA j = snd ∥ 𝑰 ∥ j                    --   SCloA : (i : I) → (𝒜 i) ∈ SClo 𝒦
  --   Timg i = mkti X (𝒜 i) (SCloA i)         --   Timg : ∀ i → 𝑻img X (SClo 𝒦)
  --   ϕ i = 𝑻ϕ X (SClo 𝒦) (Timg i)            --   ϕ : (i : I) → hom (𝑻 X) (𝑻𝑨 (Timg i))
  --   α = ∣ ϕ i ∣ (fst ∥ x ∥)                     --   α : ∣ 𝒜 i ∣
-- 𝔽≤SP : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
--  →       𝔽{𝓤}{𝓧}{X}{𝒦} IsSubalgebraOfClass SClo (PClo 𝒦)
-- 𝔽≤SP = {!!} , ({!!} , ({!!} , {!!}))

-- 𝔽∈SP𝒦 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
--  →       Σ I ꞉ 𝓤 ̇ , Σ 𝒜 ꞉ (I → Algebra 𝓤 𝑆) , Σ sa ꞉ (Subalgebra (⨅ 𝒜)) ,
--            (∀ i → 𝒜 i ∈ 𝒦) × ((𝔽{𝓤}{𝓧}{X}{𝒦}) ≅ ∣ sa ∣)
-- 𝔽∈SP𝒦 = ?







-- ΣSClo : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)} → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
-- ΣSClo {𝓤}{𝒦} = Σ I ꞉ 𝓤 ̇ , Σ 𝒜 ꞉ (I → Algebra 𝓤 𝑆) , ((i : I) → 𝒜 i ∈ SClo{𝓤 = 𝓤} 𝒦)

-- ⨅SClo : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →       ΣSClo{𝓠}{𝒦} → Algebra 𝓠 𝑆

-- ⨅SClo SS = ⨅ (fst ∥ SS ∥)

-- ⨅Sclo∈SP : {𝓠 : Universe} → hfunext 𝓠 𝓠 → {𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--            (SS : ΣSClo{𝓠}{𝒦})
--            -----------------------------
--  →         (⨅SClo SS) ∈ (SClo (PClo 𝒦))

-- ⨅Sclo∈SP {𝓠} hfe {𝒦} SS = γ
--  where
--   I : 𝓠 ̇
--   I = ∣ SS ∣
--   𝒜 : I → Algebra 𝓠 𝑆
--   𝒜 = fst ∥ SS ∥

--   h₀ : ((i : I) → 𝒜 i ∈ SClo{𝓤 = 𝓠} 𝒦)
--   h₀ = snd ∥ SS ∥

--   h₁ : ((i : I) → 𝒜 i ∈ PClo (SClo 𝒦))
--   h₁ i = pbase (h₀ i)

--   P : Algebra 𝓠 𝑆
--   P = ⨅SClo SS

--   ζ : P ∈ PClo (SClo 𝒦)
--   ζ = prod{I = I}{𝒜 = 𝒜} h₁

--   γ : P ∈ SClo (PClo 𝒦)
--   γ = PS⊆SP hfe ζ



-- 𝔽embedding : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →            ∣ 𝔽{𝓠}{𝓧}{X}{𝒦} ∣ ↪ ⨅ (SClo{𝓤 = 𝓠} 𝒦)
-- 𝔽embedding = ?
-- ∀ (𝑨 : Algebra 𝓠 𝑆) → (SCloA : 𝑨 ∈ SClo{𝓤 = 𝓠} 𝒦)
--               → ∣ 𝑻ϕ{𝓠}{𝓧}{X}{𝒦} (mkti 𝑨 SCloA) ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ 𝑻ϕ (mkti 𝑨 SCloA) ∣ ∘ (q ̇ 𝑻 X)

--        This proves that 𝔽 is isomorphic to an algebra in SPS(𝒦).
--        By SPS⊆SP, 𝔽 is isomorphic to an algebra in SP(𝒦).





























-- OLD STUFF
-- ⨅SClo' : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
-- {I : 𝓠 ̇}(𝒜 : I → Algebra 𝓠 𝑆) → ((i : I) → 𝒜 i ∈ SClo{𝓤 = 𝓠} 𝒦)
-- →        Algebra 𝓠 𝑆
-- ⨅SClo' 𝒜 h₀ = ⨅ 𝒜



--More tools for Birkhoff's theorem
--Here are some key facts/identities needed to complete the proof of Birkhoff's HSP theorem.

-- 𝑻i⊧ψ : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--        (𝑪 : Algebra 𝓠 𝑆)(SCloC : 𝑪 ∈ SClo{𝓤 = 𝓠} 𝒦)
--        (p q : ∣ (𝑻 X) ∣)  →  (p , q) ∈ ψ
--       ----------------------------------------------------------------
--  →     ∣ 𝑻ϕ(mkti 𝑪 SCloC) ∣ ((p ̇ 𝑻 X) ℊ) ≡ ∣ 𝑻ϕ(mkti 𝑪 SCloC) ∣ ((q ̇ 𝑻 X) ℊ)

-- 𝑻i⊧ψ 𝑪 SCloC p q pψq = γ
--  where

--   ϕ : hom 𝑻 𝑪
--   ϕ = 𝑻ϕ(mkti 𝑪 SCloC)

--   pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
--   pCq = pψq 𝑪 SCloC

--   γ : ∣ ϕ ∣ ((p ̇ 𝑻 X) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻 X) ℊ)
--   γ = (ap ∣ ϕ ∣(term-agree p))⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣(term-agree q))

-- PS⊆SP : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →      PClo (SClo 𝒦) ⊆ SClo (PClo 𝒦)
-- PS⊆SP {𝓠} {𝒦} {𝑨} (pbase {𝑨 = 𝑨} (sbase x)) = sbase (pbase x)
-- PS⊆SP {𝓠} {𝒦} {.(fst sa)} (pbase {𝑨 = .(fst sa)} (sub x sa)) = PS⊆SP{𝓠}{𝒦} (pbase (sub x sa))
-- PS⊆SP {𝓠} {𝒦} {.((∀ i → fst (_ i)) , (λ f proj i → snd (_ i) f (λ args → proj args i)))}
--  (prod{𝒜 = 𝒜} PCloSCloA) = γ
--   where
--    SCloPCloA : ∀ i → 𝒜 i ∈ SClo (PClo 𝒦)
--    SCloPCloA i = PS⊆SP (PCloSCloA i)

--    ⨅𝒜∈PS : ⨅ 𝒜 ∈ PClo (SClo 𝒦)
--    ⨅𝒜∈PS = prod PCloSCloA

--    γ : SClo (PClo 𝒦) (⨅ 𝒜)
--    γ = {!!}






















----=====================================================================
----=====================================================================
----=====================================================================
----=====================================================================
----=====================================================================
-- _⊗_ : (𝑨₁ 𝑨₂ : Algebra 𝓤 𝑆) → Algebra (𝓤₀ ⊔ 𝓤) 𝑆
-- 𝑨₁ ⊗ 𝑨₂ = ⨅ 𝒜
--  where
--   𝒜 : 𝟚 → Algebra 𝓤 𝑆
--   𝒜 (inl x) = 𝑨₁
--   𝒜 (inr x) = 𝑨₂

-- lemma0 : {𝑨₁ 𝑨₂ : Algebra 𝓤 𝑆}(B1 : Subalgebra 𝑨₁)(B2 : Subalgebra 𝑨₂)
--  →       (∣ B1 ∣ ⊗ ∣ B2 ∣) IsSubalgebraOf (𝑨₁ ⊗ 𝑨₂)
-- lemma0 {𝑨₁}{𝑨₂}(𝑩₁ , k , kem , khom) (𝑩₂ , g , gem , ghom) = α , β , γ
--  where
--   𝑲 : hom (𝑩₁ ⊗ 𝑩₂) (𝑨₁ ⊗ 𝑩₂)
--   𝑲 = Kmap , Khom
--    where
--     Kmap : ∣ 𝑩₁ ⊗ 𝑩₂ ∣ → ∣ 𝑨₁ ⊗ 𝑩₂ ∣
--     Kmap bb (inl x) = k (bb (inl x))
--     Kmap bb (inr x) = id (bb (inr x))

--     ζ : ∀ x f 𝒃 → Kmap ((f ̂ (𝑩₁ ⊗ 𝑩₂)) 𝒃) x ≡ (f ̂ (𝑨₁ ⊗ 𝑩₂)) (λ x₁ → Kmap (𝒃 x₁)) x
--     ζ (inl x) f 𝒃 = khom f (λ z → 𝒃 z (inl x))
--     ζ (inr x) f 𝒃 = ∥ 𝒾𝒹 𝑩₂ ∥ f (λ z → 𝒃 z (inr x))

--     Khom : is-homomorphism (𝑩₁ ⊗ 𝑩₂) (𝑨₁ ⊗ 𝑩₂) Kmap
--     Khom f 𝒃 = gfe λ x → ζ x f 𝒃

--   Kemb : is-embedding ∣ 𝑲 ∣
--   Kemb ab bb bb' = {!!}

--   𝑮 : hom (𝑨₁ ⊗ 𝑩₂) (𝑨₁ ⊗ 𝑨₂)
--   𝑮 = Gmap , Ghom
--    where
--     Gmap : ∣ 𝑨₁ ⊗ 𝑩₂ ∣ → ∣ 𝑨₁ ⊗ 𝑨₂ ∣
--     Gmap ab (inl x) = id (ab (inl x))
--     Gmap ab (inr x) = g (ab (inr x))

--     ζ : ∀ x f 𝒃 → Gmap ((f ̂ (𝑨₁ ⊗ 𝑩₂)) 𝒃) x ≡ (f ̂ (𝑨₁ ⊗ 𝑨₂)) (λ x₁ → Gmap (𝒃 x₁)) x
--     ζ (inl x) f 𝒃 = ∥ 𝒾𝒹 𝑨₁ ∥ f (λ z → 𝒃 z (inl x))
--     ζ (inr x) f 𝒃 = ghom f (λ z → 𝒃 z (inr x))

--     Ghom : is-homomorphism (𝑨₁ ⊗ 𝑩₂) (𝑨₁ ⊗ 𝑨₂) Gmap
--     Ghom f 𝒃 = gfe λ x → ζ x f 𝒃

--   Gemb : is-embedding ∣ 𝑮 ∣
--   Gemb = {!!}

--   α : ∣ 𝑩₁ ⊗ 𝑩₂ ∣ → ∣ 𝑨₁ ⊗ 𝑨₂ ∣
--   α = ∣ 𝑮 ∣ ∘ ∣ 𝑲 ∣

--   β : is-embedding α
--   β  = ∘-embedding Gemb Kemb

--   γ : is-homomorphism (𝑩₁ ⊗ 𝑩₂) (𝑨₁ ⊗ 𝑨₂) α
--   γ = ∘-hom (𝑩₁ ⊗ 𝑩₂) (𝑨₁ ⊗ 𝑩₂) (𝑨₁ ⊗ 𝑨₂) {∣ 𝑲 ∣} {∣ 𝑮 ∣} ∥ 𝑲 ∥ ∥ 𝑮 ∥



-- lemma2 : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--         {I : 𝓠 ̇}{𝒜 : I → Algebra 𝓠 𝑆}
--  →      ((i : I) → (𝒜 i) ∈ SClo 𝒦)
--  →      (⨅ 𝒜)  ∈ SClo (PClo 𝒦)
-- lemma2 {𝓠}{𝒦}{I}{𝒜} SClo𝒜 = {!!}
--  where
  -- AK : I → Algebra 𝓠 𝑆
  -- AK i = ∣ SClo𝒜 i ∣
  -- γ : ⨅ 𝒜 ∈ SClo (PClo 𝒦)
  -- γ = {!!}
-- 𝑻imgPred : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
--  →         Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) ⊔ (𝓧 ⁺))
-- 𝑻imgPred {𝓤}{𝓧}{X}{𝒦} 𝑨 = Σ ϕ ꞉ hom (𝑻 X) 𝑨 , (𝑨 ∈ 𝒦) × Epic ∣ ϕ ∣

