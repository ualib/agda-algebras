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

𝑻ϕ : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
     (ti : 𝑻img X 𝒦) → hom (𝑻 X) (𝑻𝑨 ti)
𝑻ϕ _ _ ti = fst (snd ti)

𝑻ϕE : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
      (ti : 𝑻img X 𝒦) → Epic ∣ 𝑻ϕ X 𝒦 ti ∣
𝑻ϕE ti = snd (snd ∥ ti ∥)

𝑻KER : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺ ̇
𝑻KER X 𝒦 = Σ (p , q) ꞉ (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) , ∀ 𝑨 → (KA : 𝑨 ∈ 𝒦) → (p , q) ∈ KER-pred{B = ∣ 𝑨 ∣} ∣ 𝑻ϕ X 𝒦 (mkti X 𝑨 KA) ∣

Ψ : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →  Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)
Ψ X 𝒦 (p , q) = ∀(𝑨 : Algebra _ 𝑆) → (SCloA : 𝑨 ∈ SClo 𝒦)
 →  ∣ 𝑻ϕ X (SClo 𝒦) (mkti X 𝑨 SCloA) ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ 𝑻ϕ X (SClo 𝒦) (mkti X 𝑨 SCloA) ∣ ∘ (q ̇ 𝑻 X)

ΨRel : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) → Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)
ΨRel X 𝒦 p q = Ψ X 𝒦 (p , q)

Ψcompatible : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →            compatible{𝓤 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓦 = (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⊔ 𝓧 ⁺)} (𝑻 X)(ΨRel X 𝒦)
Ψcompatible X 𝒦 f {𝒕} {𝒔} 𝒕Ψ𝒔 𝑨 SCloA = γ
 where
  ϕ : hom (𝑻 X) 𝑨
  ϕ = 𝑻ϕ X (SClo 𝒦) (mkti X 𝑨 SCloA)

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
 →     ∣ 𝑻ϕ X (SClo 𝒦)(mkti X 𝑪 SCloC) ∣ ∘ (p ̇ 𝑻 X)
         ≡ ∣ 𝑻ϕ X (SClo 𝒦)(mkti X 𝑪 SCloC) ∣ ∘ (q ̇ 𝑻 X)

𝑻i⊧Ψ X 𝒦 𝑪 SCloC p q pΨq = pCq
 where

  ϕ : hom (𝑻 X) 𝑪
  ϕ = 𝑻ϕ X (SClo 𝒦)(mkti X 𝑪 SCloC)

  pCq : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
  pCq = pΨq 𝑪 SCloC


Ψ⊆ThSClo : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →         Ψ X 𝒦 ⊆ (Th (SClo 𝒦))
Ψ⊆ThSClo X 𝒦 {p , q} pΨq {𝑪} SCloC = γ
 where
  ti : 𝑻img X (SClo 𝒦)
  ti = mkti X 𝑪 SCloC

  ϕ : hom (𝑻 X) 𝑪
  ϕ = 𝑻ϕ X (SClo 𝒦) ti

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

class-identities {𝓤}{𝓧}{X}{𝒦} p q = (λ α VCloA → vclo-id1 p q α VCloA) ,
                                      (λ Thpq KA → Thpq (vbase KA))



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
 →   Algebra (𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺ ⊔ 𝓧 ⁺ ⁺) 𝑆
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


𝔽∈SPS : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →       𝔽 X 𝒦 ∈ SClo (PClo (SClo 𝒦))
𝔽∈SPS{𝓧}{𝓤} X 𝒦 = ?

𝔽≤⨅SClo : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
 →       𝔽 X 𝒦 IsSubalgebraOf (⨅SClo 𝒦)
𝔽≤⨅SClo{𝓧}{𝓤} X 𝒦 = ∣ 𝔥 ∣ , (𝔥emb , ∥ 𝔥 ∥)
 where
  f : X → ∣ ⨅SClo 𝒦 ∣
  f = ∣ 𝕏 (⨅SClo 𝒦) ∣

  𝔥 : hom (𝔽 X 𝒦) (⨅SClo 𝒦)
  𝔥 = 𝔽lift-hom X 𝒦 (⨅SClo 𝒦) f

-- Ψ : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺))
--  →  Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)
-- Ψ X 𝒦 (p , q) = ∀(𝑨 : Algebra _ 𝑆) → (SCloA : 𝑨 ∈ SClo 𝒦)
--  →  ∣ 𝑻ϕ X (SClo 𝒦) (mkti X 𝑨 SCloA) ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ 𝑻ϕ X (SClo 𝒦) (mkti X 𝑨 SCloA) ∣ ∘ (q ̇ 𝑻 X)

-- ΨRel : {𝓧 𝓤 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) → Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)
-- ΨRel X 𝒦 p q = Ψ X 𝒦 (p , q)
  𝔥emb : is-embedding ∣ 𝔥 ∣
  𝔥emb 𝒂 fib1 fib2 = γ
   where
    h1h2 : ∣ 𝔥 ∣ (∣ fib1 ∣) ≡ ∣ 𝔥 ∣ (∣ fib2 ∣)
    h1h2 = (snd fib1) ∙ (snd fib2)⁻¹

    -- Notice that ∣ 𝔥 ∣ x ≡ ∣ 𝔥 ∣ y means that the pair (x, y) ∈ ∣ 𝔽 X 𝒦 ∣ satisfies the following:
    -- For *every* 𝑨 ∈ SClo 𝒦, the equation  We should be able to prove (x , y) ∈ Ψ X 𝒦
    -- 𝔥11 : ∀ x y → ∣ 𝔥 ∣ x ≡ ∣ 𝔥 ∣ y →  x ≡ y
    -- 𝔥11 (pr₃ , pr₄) y hxhy = {!!}

    𝔥e : ∀ x y → ∣ 𝔥 ∣ x ≡ ∣ 𝔥 ∣ y
     →   (𝑨 : Algebra _ 𝑆)(h : X → ∣ 𝑨 ∣ ) → 𝑨 ∈ SClo 𝒦
     →   (⌜ x ⌝ ̇ 𝑨) h ≡ (⌜ y ⌝ ̇ 𝑨) h
    𝔥e x y hxhy 𝑨 h SCloA = {!!}

    -- Ψ⊆ker𝔥 : (Ψ X 𝒦)  ⊆  KER-pred{𝓦 = (𝓞 ⊔ 𝓥 ⊔ (𝓧 ⊔ 𝓤) ⁺)}{A = ∣ 𝔽 X 𝒦 ∣ }{B = ∣ ⨅SClo{𝓤 = 𝓤} 𝒦 ∣} ∣ 𝔥 ∣
    -- Ψ⊆ker𝔥 = ?

    γ : fib1 ≡ fib2
    γ = {!!}


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


-- Birkhoff's theorem: every variety is an equational class.
birkhoff : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
           (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ Mod (Th (VClo{𝓤} 𝒦))
          --------------------------------------------
 →                     𝑨 ∈ VClo 𝒦

birkhoff {𝓤}{𝓧}{X}{𝒦} 𝑨 ModThVCloA = γ
 where
  F T : Algebra _ 𝑆
  F = 𝔽 X 𝒦
  T = 𝑻 X

  h₀ : X → ∣ 𝑨 ∣
  h₀ = fst (𝕏 𝑨)

  h₀E : Epic h₀
  h₀E = snd (𝕏 𝑨)

  h : hom T 𝑨
  h = lift-hom 𝑨 h₀

  Ψ⊆ThVClo : Ψ X 𝒦 ⊆ Th{𝓤}{𝓧} (VClo{𝓤} 𝒦)
  Ψ⊆ThVClo {p , q} pΨq =
   (lr-implication (class-identities p q)) (Ψ⊆Th𝒦 X 𝒦 p q pΨq)

  Ψ⊆A⊧ : ∀{p}{q} → (p , q) ∈ Ψ X 𝒦 → 𝑨 ⊧ p ≈ q
  Ψ⊆A⊧ {p} {q} pΨq = ModThVCloA p q (Ψ⊆ThVClo {p , q} pΨq)

  Ψ⊆Kerh : Ψ X 𝒦 ⊆ KER-pred{B = ∣ 𝑨 ∣} ∣ h ∣
  Ψ⊆Kerh {p , q} pΨq = hp≡hq
   where
    hp≡hq : ∣ h ∣ p ≡ ∣ h ∣ q
    hp≡hq = hom-id-compatibility p q 𝑨 h (Ψ⊆A⊧{p}{q} pΨq)

  gg : Σ g ꞉ hom T F , Epic ∣ g ∣
  gg = (lift-hom F g₀) , (lift-of-epic-is-epic{𝓤 = (𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ (𝓤 ⊔ 𝓧) ⁺ ⁺)} F g₀ g₀E)

   where
    g₀ : X → ∣ F ∣
    g₀ = fst (𝕏 F)

    g₀E : Epic g₀
    g₀E = snd (𝕏 F)

  g : hom T F
  g = fst gg

  gE : Epic ∣ g ∣
  gE = snd gg

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
  -- KER-pred : {A : 𝓤 ̇}{B : 𝓦 ̇} → (A → B) → Pred (A × A) 𝓦
  -- KER-pred g (x , y) = g x ≡ g y
  -- _⊆_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
  -- P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

  kerg⊆kerh : KER-pred ∣ g ∣ ⊆ KER-pred ∣ h ∣
  kerg⊆kerh {(x , y)} gx≡gy = kgoal
   where
    kgoal : ∣ h ∣ x ≡ ∣ h ∣ y
    kgoal = {!!}

  -- ϕ' : Σ ϕ ꞉ (hom F 𝑨) , ∣ h ∣ ≡ ∣ ϕ ∣ ∘ ∣ g ∣
  -- ϕ' = HomFactor gfe {T} {𝑨} {F} h g kerg⊆kerh gE

  --We need to find F : Algebra 𝒰 𝑆 such that F ∈ VClo and ∃ ϕ : hom F 𝑨 with ϕE : Epic ∣ ϕ ∣.
  --Then we can prove 𝑨 ∈ VClo 𝒦 by vhom F∈VClo (𝑨 , ∣ ϕ ∣ , (∥ ϕ ∥ , ϕE))
  -- since vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦

  -- vcloF : F ∈ VClo 𝒦
  -- vcloF = {!!}


  ϕ : Σ h ꞉ (hom F 𝑨) , Epic ∣ h ∣
  ϕ = (𝔽lift-hom X 𝒦 𝑨 h₀) , {!!}

  hiF : HomImagesOf F
  hiF = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) )

  -- Finally, use 𝔽∈SP𝒦 to get an algebra 𝑩 ∈ VClo 𝒦 such that 𝔽 ≅ 𝑩.
  -- Then ∃ hom h : hom 𝑩 𝔽, so we can simply compose ϕ ∘ h : hom 𝑩 𝑨,
  -- which proves that 𝑨 ∈ VClo 𝒦, as desired.

  γ : 𝑨 ∈ VClo{𝓤} 𝒦
  γ = {!!} -- vhom{𝓤 = 𝓤} {!!} {!!} -- vcloF hiF









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

