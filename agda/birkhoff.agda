--FILE: birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--REF: Based on the file `birkhoff.agda` (23 Jan 2020).

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π'; Op; _̂_)
open import relations using (ker-pred; Rel; con; _//_)
open import homomorphisms using (HOM; Hom; hom; is-homomorphism; H-closed)
open import terms using (Term; generator; 𝑻; _̇_; comm-hom-term;
                         lift-hom; interp-prod)

open import subuniverses using (Subuniverse; mksub; var; app; Sg;
          _is-subalgebra-of_; Subalgebra; S-closed)

module birkhoff
 {𝑆 : Signature 𝓞 𝓥}
 {𝓤 : Universe}
 {ua : Univalence}
 {X : 𝓤 ̇ }
 (gfe : global-dfunext)
 (dfe : dfunext 𝓤 𝓤)
   where

open import closure{𝑆 = 𝑆}{𝓤 = 𝓤}{ua = ua}{X = X}{gfe = gfe}{dfe = dfe} using (VClo; _⊧_≈_; _⊧_≋_)

--Equalizers of functions
E :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
E g h x = g x ≡ h x

--Equalizers of homomorphisms
EH : {A B : Algebra 𝓤 𝑆} (g h : hom A B) → Pred ∣ A ∣ 𝓤
EH g h x = ∣ g ∣ x ≡ ∣ h ∣ x
--cf. definition 𝓔 in the homomorphisms module

EH-is-closed : funext 𝓥 𝓤
 →      {𝑓 : ∣ 𝑆 ∣ } {A B : Algebra 𝓤 𝑆}
        (g h : hom A B)  (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ A ∣)
 →      ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (EH {A = A}{B = B} g h))
        --------------------------------------------------
 →       ∣ g ∣ (∥ A ∥ 𝑓 𝒂) ≡ ∣ h ∣ (∥ A ∥ 𝑓 𝒂)

EH-is-closed fe {𝑓 = 𝑓}{A = A , FA}{B = B , FB}
 (g , ghom)(h , hhom) 𝒂 p =
   g (FA 𝑓 𝒂)    ≡⟨ ghom 𝑓 𝒂 ⟩
   FB 𝑓 (g ∘ 𝒂)  ≡⟨ ap (FB _ )(fe p) ⟩
   FB 𝑓 (h ∘ 𝒂)  ≡⟨ (hhom 𝑓 𝒂)⁻¹ ⟩
   h (FA 𝑓 𝒂)    ∎

-- Equalizer of homs is a subuniverse.
EH-is-subuniverse : funext 𝓥 𝓤
 →  {A B : Algebra 𝓤 𝑆}(g h : hom A B) → Subuniverse {A = A}
EH-is-subuniverse fe {A = A} {B = B} g h =
 mksub (EH {A = A}{B = B} g h)
  λ 𝑓 𝒂 x → EH-is-closed fe {A = A} {B = B} g h 𝒂 x

HomUnique : funext 𝓥 𝓤 → {A B : Algebra 𝓤 𝑆}
           (X : Pred ∣ A ∣ 𝓤)  (g h : hom A B)
 →         (∀ (x : ∣ A ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
         ---------------------------------------------------
 →        (∀ (a : ∣ A ∣) → a ∈ Sg {A = A} X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x
HomUnique fe {A = A , FA}{B = B , FB} X
 (g , ghom) (h , hhom) gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
  g (FA 𝑓 𝒂)     ≡⟨ ghom 𝑓 𝒂 ⟩
  FB 𝑓 (g ∘ 𝒂 )   ≡⟨ ap (FB 𝑓) (fe induction-hypothesis) ⟩
  FB 𝑓 (h ∘ 𝒂)    ≡⟨ ( hhom 𝑓 𝒂 )⁻¹ ⟩
  h ( FA 𝑓 𝒂 )   ∎
 where
  induction-hypothesis =
    λ x → HomUnique fe {A = A , FA}{B = B , FB} X
    (g , ghom)(h , hhom) gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

module _
 (gfe : global-dfunext)
 (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
 where

 -- ⇒ (the "only if" direction)
 identities-are-compatible-with-homs : (p q : Term{X = X})
  →                𝒦 ⊧ p ≋ q
       ----------------------------------------------------
  →     ∀ A KA h → ∣ h ∣ ∘ (p ̇ (𝑻(X))) ≡ ∣ h ∣ ∘ (q ̇ (𝑻(X)))
 -- Here, the inferred types are
 -- A : Algebra 𝓤 𝑆, KA : 𝒦 A, h : hom ((𝑻(X))) A

 identities-are-compatible-with-homs p q 𝒦⊧p≋q A KA h = γ
  where
   pA≡qA : p ̇ A ≡ q ̇ A
   pA≡qA = 𝒦⊧p≋q KA

   pAh≡qAh : ∀(𝒂 : X → ∣ 𝑻(X) ∣ )
    →        (p ̇ A)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ A)(∣ h ∣ ∘ 𝒂)
   pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

   hpa≡hqa : ∀(𝒂 : X → ∣ 𝑻(X) ∣ )
    →        ∣ h ∣ ((p ̇ (𝑻(X))) 𝒂) ≡ ∣ h ∣ ((q ̇ (𝑻(X))) 𝒂)
   hpa≡hqa 𝒂 =
    ∣ h ∣ ((p ̇ (𝑻(X))) 𝒂)  ≡⟨ comm-hom-term gfe (𝑻(X)) A h p 𝒂 ⟩
    (p ̇ A)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
    (q ̇ A)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term gfe (𝑻(X)) A h q 𝒂)⁻¹ ⟩
    ∣ h ∣ ((q ̇ (𝑻(X))) 𝒂)  ∎

   γ : ∣ h ∣ ∘ (p ̇ (𝑻(X))) ≡ ∣ h ∣ ∘ (q ̇ (𝑻(X)))
   γ = gfe hpa≡hqa

 -- ⇐ (the "if" direction)
 homs-are-compatible-with-identities : (p q : Term)
  →    (∀ A KA h  →  ∣ h ∣ ∘ (p ̇ (𝑻 X)) ≡ ∣ h ∣ ∘ (q ̇ (𝑻 X)))
       --------------------------------------------------
  →                𝒦 ⊧ p ≋ q
 --inferred types: A : Algebra 𝓤 𝑆, KA : A ∈ 𝒦, h : hom (𝑻(X)) A

 homs-are-compatible-with-identities p q all-hp≡hq {A = A} KA = γ
  where
   h : (𝒂 : X → ∣ A ∣) → hom (𝑻(X)) A
   h 𝒂 = lift-hom{A = A} 𝒂

   γ : A ⊧ p ≈ q
   γ = gfe λ 𝒂 →
    (p ̇ A) 𝒂
      ≡⟨ refl _ ⟩
    (p ̇ A)(∣ h 𝒂 ∣ ∘ generator)
      ≡⟨(comm-hom-term gfe (𝑻 X) A (h 𝒂) p generator)⁻¹ ⟩
    (∣ h 𝒂 ∣ ∘ (p ̇ (𝑻(X)))) generator
      ≡⟨ ap (λ - → - generator) (all-hp≡hq A KA (h 𝒂)) ⟩
    (∣ h 𝒂 ∣ ∘ (q ̇ (𝑻(X)))) generator
      ≡⟨ (comm-hom-term gfe (𝑻 X) A (h 𝒂) q generator) ⟩
    (q ̇ A)(∣ h 𝒂 ∣ ∘ generator)
      ≡⟨ refl _ ⟩
    (q ̇ A) 𝒂
      ∎

 compatibility-of-identities-and-homs : (p q : Term)
  →  (𝒦 ⊧ p ≋ q)
      ⇔ (∀ A ka hh → ∣ hh ∣ ∘ (p ̇ (𝑻(X))) ≡ ∣ hh ∣ ∘ (q ̇ (𝑻(X))))
 --inferred types: A : algebra 𝓤 s, ka : A ∈ 𝒦, hh : hom (𝑻(X)) A.

 compatibility-of-identities-and-homs p q =
   identities-are-compatible-with-homs p q ,
   homs-are-compatible-with-identities p q

-- Product Closure
P-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺ ))
 →      (𝓤 : Universe)(𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓤 ) → 𝓤 ⁺ ⊔ 𝓘 ⁺ ̇
P-closed ℒ𝒦 = λ 𝓤 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  Π' 𝒜  ∈ (ℒ𝒦 (𝓤 ⊔ 𝓘))

data PClo (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 pbase : {A : Algebra 𝓤 𝑆} → A ∈ 𝒦 → A ∈ PClo 𝒦
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆}
  →     (∀ i → 𝒜 i ∈ PClo 𝒦)
  →     Π' 𝒜 ∈ PClo 𝒦

-- Subalgebra Closure
data SClo (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 sbase : {A :  Algebra _ 𝑆} → A ∈ 𝒦 → A ∈ SClo 𝒦
 sub : {A : Algebra _ 𝑆} → A ∈ SClo 𝒦 → (sa : Subalgebra {A = A} ua) → ∣ sa ∣ ∈ SClo 𝒦

-- module _
--  {𝒦 : Pred (Algebra 𝓤 𝑆) ( 𝓤 ⁺ )} where

HomImages : Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
HomImages 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
                          is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

module _ {𝑨 𝑩 : Algebra 𝓤 𝑆} (ϕ : hom 𝑨 𝑩)  where

 HomImage : ∣ 𝑩 ∣ → 𝓤 ̇
 HomImage = λ b → Image ∣ ϕ ∣ ∋ b

 hom-image : 𝓤 ̇
 hom-image = Σ (Image_∋_ ∣ ϕ ∣)

 fres : ∣ 𝑨 ∣ → Σ (Image_∋_ ∣ ϕ ∣)
 fres a = ∣ ϕ ∣ a , im a

 hom-image-alg : Algebra 𝓤 𝑆
 hom-image-alg = hom-image , ops-interp
  where
   a : {f : ∣ 𝑆 ∣ }(x : ∥ 𝑆 ∥ f → hom-image) → ∥ 𝑆 ∥ f → ∣ 𝑨 ∣
   a x y = Inv ∣ ϕ ∣  ∣ x y ∣ ∥ x y ∥

   ops-interp : (f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) hom-image
   ops-interp = λ f x → (∣ ϕ ∣ ((f ̂ 𝑨) (a x)) , im ((f ̂ 𝑨)(a x)))


-- Homomorphic Image Closure
data HClo (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo 𝒦
 hhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ HClo 𝒦 → ((𝑩 , _ ) : HomImages 𝑨) → 𝑩 ∈ HClo 𝒦


module _ (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)) where

 hclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (HClo 𝒦 ⊧ p ≋ q)
 hclo-id1 {p}{q} 𝒦⊧p≋q (hbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 hclo-id1 {p}{q} 𝒦⊧p≋q (hhom{𝑨} A∈HClo𝒦 𝑩ϕhomSur) = γ
  where
  A⊧p≈q : 𝑨 ⊧ p ≈ q
  A⊧p≈q = (hclo-id1{p}{q} 𝒦⊧p≋q ) A∈HClo𝒦

  IH : (p ̇ 𝑨) ≡ (q ̇ 𝑨)
  IH = A⊧p≈q

  𝑩 : Algebra 𝓤 𝑆
  𝑩 = ∣ 𝑩ϕhomSur ∣

  ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
  ϕ = ∣ ∥ 𝑩ϕhomSur ∥ ∣

  ϕhom : is-homomorphism 𝑨 𝑩 ϕ
  ϕhom = ∣ pr₂ ∥ 𝑩ϕhomSur ∥ ∣

  ϕsur : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
  ϕsur 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhomSur ∥ ∥ (𝒃 x)

  preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
  preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕsur 𝒃 x))

  ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕsur 𝒃 x)

  γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
  γ = gfe λ 𝒃 →
   (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
   (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) p (preim 𝒃))⁻¹ ⟩
   ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality IH (preim 𝒃)) ⟩
   ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
   (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
   (q ̇ 𝑩) 𝒃 ∎

hclo-id2 : ∀ {𝒦 p q} → (HClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
hclo-id2 p A∈𝒦 = p (hbase A∈𝒦)


TH : (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ )) → _ ̇
TH 𝒦 = Σ (p , q) ꞉ (Term{X = X} × Term) , 𝒦 ⊧ p ≋ q

Th : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) → Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

MOD : (Σ' : Pred (Term{X = X} × Term) 𝓤) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) ̇
MOD Σ' = Σ A ꞉ (Algebra 𝓤 𝑆) , ∀ p q → (p , q) ∈ Σ' → A ⊧ p ≈ q

Mod : Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) → Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ )
Mod Σ' = λ A → ∀ p q → (p , q) ∈ Σ' → A ⊧ p ≈ q

-- Birkhoff's theorem: every variety is an equational class.
birkhoff : (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺))
           (𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣ )(eg : Epic h₀)
 →         𝑨 ∈ Mod (Th (VClo 𝒦)) → 𝑨 ∈ VClo 𝒦
birkhoff 𝒦 𝑨 h₀ eg A∈ModThV = γ
 where
  h : hom (𝑻 X) 𝑨
  h = lift-hom{𝑨 = 𝑨}{X = X} h₀

  γ : 𝑨 ∈ VClo 𝒦
  γ = {!!}
 --Let 𝒲 be a class of algebras that is closed under H, S, and P.
 --We must find a set Σ of equations such that 𝒲 = Mod(Σ). For this will prove that 𝒲
 --is the class of algebras satisfying a particular set of equations (i.e., 𝒲 is an
 --equational class). The obvious choice is the set of all equations that hold in 𝒲, that
 --is, Th(𝒲). So, let 𝒲' = Mod(Th(𝒲)). Clearly, 𝒲 ⊆ 𝒲'. We prove the reverse inclusion.
 --Let A ∈ 𝒲' and let 𝑋 be a set of cardinality max(∣𝐴∣, ω). Choose a surjection ℎ₀ : 𝑋 → 𝐴.
 --By :numref:`Obs %s <obs 9>`, ℎ₀ extends to an epimorphism ℎ : 𝑻(𝑋) → A`.
 --Since 𝔽(𝒲, 𝑋) = 𝑻(𝑋)/Ψ(𝒲, 𝑋), there is an epimorphism 𝑔 : 𝑻(𝑋) → 𝔽(𝒲, 𝑋).
 --We claim ker 𝑔 ⊆ ker ℎ. If the claim is true, then by :numref:`Obs %s <obs 5>`
 --∃ 𝑓 : 𝔽(𝒲, 𝑋) → 𝐴 such that 𝑓 ∘ 𝑔 = ℎ and since ℎ is epic, so is 𝑓, so
 --A ∈ H(𝔽(𝒲, 𝑋)) ⊆ 𝒲` which will complete the proof.
 --So it remains to prove the claim that ker 𝑔 ⊆ ker ℎ.
 --Let 𝑢, 𝑣 ∈ 𝑻(𝑋) and assume 𝑔(𝑢) = 𝑔(𝑣). Since 𝑻(𝑋) is generated by 𝑋, there are terms
 --𝑝, 𝑞 ∈ 𝑻(𝑋) and 𝒙 such that :math:`𝑢 = p^{𝑻(𝑋)}(𝒙)`
 --and :math:`𝑣 = q^{𝑻(X)}(𝒙)`. Therefore, :math:`p^{𝔽(𝒲, 𝑋)} 𝒙 = 𝑔(𝑢) = 𝑔(𝑣) = q^{𝔽(𝒲, 𝑋)} 𝒙`.
 --Thus 𝒲 ⊧ 𝑝 ≈ 𝑞, hence (𝑝, 𝑞) ∈ Σ. Since A ∈ Mod(Σ) we get A ⊧ 𝑝 ≈ 𝑞.
 --Therefore, :math:`ℎ(𝑢) = 𝑝^A(ℎ₀ ∘ 𝒙) = 𝑞^A(ℎ₀ ∘ 𝒙) = ℎ(𝑣)`, as desired.

