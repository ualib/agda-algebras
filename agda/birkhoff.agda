--FILE: birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--REF: Based on the file `birkhoff.agda` (23 Jan 2020).

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π')
open import relations using (ker-pred; Rel; con; _//_)
open import homomorphisms using (HOM; Hom; hom; is-homomorphism; H-closed)
open import terms using (Term; generator; 𝑻; _̇_; comm-hom-term';
                         lift-hom; interp-prod)

open import subuniverses using (Subuniverse; mksub; var; app; Sg;
          _is-subalgebra-of_; Subalgebra; S-closed; hom-image-alg)

-- open import closure using (_⊧_≈_; _⊧_≋)

module birkhoff
 {S : Signature 𝓞 𝓥}
 {𝓤 : Universe}
 {UV : Univalence}
 {X : 𝓤 ̇ } -- {X : 𝓧 ̇ }
 (gfe : global-dfunext)
 (dfe : dfunext 𝓤 𝓤)
 {X' : 𝓧 ̇ }  where

-- Duplicating definition of ⊧ so we don't have to import from closure module.
-- (Remove these definitions later once closure module is working.)
_⊧_≈_ : Algebra 𝓤 S
 →      Term{X = X} → Term → 𝓤 ̇

A ⊧ p ≈ q = (p ̇ A) ≡ (q ̇ A)

_⊧_≋_ : Pred (Algebra 𝓤 S) 𝓦
 →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇

_⊧_≋_ 𝒦 p q = {A : Algebra _ S} → 𝒦 A → A ⊧ p ≈ q

--Equalizers of functions
E :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
E g h x = g x ≡ h x

--Equalizers of homomorphisms
EH : {A B : Algebra 𝓤 S} (g h : hom A B) → Pred ∣ A ∣ 𝓤
EH g h x = ∣ g ∣ x ≡ ∣ h ∣ x
--cf. definition 𝓔 in the homomorphisms module

EH-is-closed : funext 𝓥 𝓤
 →      {𝑓 : ∣ S ∣ } {A B : Algebra 𝓤 S}
        (g h : hom A B)  (𝒂 : (∥ S ∥ 𝑓) → ∣ A ∣)
 →      ((x : ∥ S ∥ 𝑓) → (𝒂 x) ∈ (EH {A = A}{B = B} g h))
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
 →  {A B : Algebra 𝓤 S}(g h : hom A B) → Subuniverse {A = A}
EH-is-subuniverse fe {A = A} {B = B} g h =
 mksub (EH {A = A}{B = B} g h)
  λ 𝑓 𝒂 x → EH-is-closed fe {A = A} {B = B} g h 𝒂 x

HomUnique : funext 𝓥 𝓤 → {A B : Algebra 𝓤 S}
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
 (𝒦 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
 where

 -- ⇒ (the "only if" direction)
 identities-are-compatible-with-homs : (p q : Term{X = X})
  →                𝒦 ⊧ p ≋ q
       ----------------------------------------------------
  →     ∀ A KA h → ∣ h ∣ ∘ (p ̇ (𝑻(X))) ≡ ∣ h ∣ ∘ (q ̇ (𝑻(X)))
 -- Here, the inferred types are
 -- A : Algebra 𝓤 S, KA : 𝒦 A, h : hom ((𝑻(X))) A

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
    ∣ h ∣ ((p ̇ (𝑻(X))) 𝒂)  ≡⟨ comm-hom-term' gfe (𝑻(X)) A h p 𝒂 ⟩
    (p ̇ A)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
    (q ̇ A)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term' gfe (𝑻(X)) A h q 𝒂)⁻¹ ⟩
    ∣ h ∣ ((q ̇ (𝑻(X))) 𝒂)  ∎

   γ : ∣ h ∣ ∘ (p ̇ (𝑻(X))) ≡ ∣ h ∣ ∘ (q ̇ (𝑻(X)))
   γ = gfe hpa≡hqa

 -- ⇐ (the "if" direction)
 homs-are-compatible-with-identities : (p q : Term)
  →    (∀ A KA h  →  ∣ h ∣ ∘ (p ̇ (𝑻(X))) ≡ ∣ h ∣ ∘ (q ̇ (𝑻(X))))
       -----------------------------------------------
  →                𝒦 ⊧ p ≋ q
 --inferred types: A : Algebra 𝓤 S, KA : A ∈ 𝒦, h : hom (𝑻(X)) A

 homs-are-compatible-with-identities p q all-hp≡hq {A = A} KA = γ
  where
   h : (𝒂 : X → ∣ A ∣) → hom (𝑻(X)) A
   h 𝒂 = lift-hom{A = A} 𝒂

   γ : A ⊧ p ≈ q
   γ = gfe λ 𝒂 →
    (p ̇ A) 𝒂
      ≡⟨ refl _ ⟩
    (p ̇ A)(∣ h 𝒂 ∣ ∘ generator)
      ≡⟨(comm-hom-term' gfe (𝑻(X)) A (h 𝒂) p generator)⁻¹ ⟩
    (∣ h 𝒂 ∣ ∘ (p ̇ (𝑻(X)))) generator
      ≡⟨ ap (λ - → - generator) (all-hp≡hq A KA (h 𝒂)) ⟩
    (∣ h 𝒂 ∣ ∘ (q ̇ (𝑻(X)))) generator
      ≡⟨ (comm-hom-term' gfe (𝑻(X)) A (h 𝒂) q generator) ⟩
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
P-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ))
 →      (𝓤 : Universe)(𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓤 S)
 →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓤 ) → 𝓤 ⁺ ⊔ 𝓘 ⁺ ̇
P-closed ℒ𝒦 = λ 𝓤 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  Π' 𝒜  ∈ (ℒ𝒦 (𝓤 ⊔ 𝓘))

data PClo (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 pbase : {A : Algebra 𝓤 S} → A ∈ 𝒦 → A ∈ PClo 𝒦
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S}
  →     (∀ i → 𝒜 i ∈ PClo 𝒦)
  →     Π' 𝒜 ∈ PClo 𝒦

-- Subalgebra Closure
data SClo (𝒦 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 sbase : {A :  Algebra _ S} → A ∈ 𝒦 → A ∈ SClo 𝒦
 sub : {A : Algebra _ S} → A ∈ SClo 𝒦 → (sa : Subalgebra {A = A} UV) → ∣ sa ∣ ∈ SClo 𝒦

-- Homomorphic Image Closure
data HClo (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 hbase : {A : Algebra 𝓤 S} → A ∈ 𝒦 → A ∈ HClo 𝒦
 hhom : {A B : Algebra 𝓤 S}{ϕ : hom A B}
  →     A ∈ HClo 𝒦
  →     hom-image-alg {A = A}{B = B} ϕ ∈ HClo 𝒦

-- Variety Closure
data VClo (𝒦 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 vbase : {A : Algebra 𝓤 S} → A ∈ 𝒦 → A ∈ VClo 𝒦
 vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ S} → (∀ i → 𝒜 i ∈ VClo 𝒦) → Π' 𝒜 ∈ VClo 𝒦
 vsub : {A : Algebra 𝓤 S} → A ∈ VClo 𝒦 → (sa : Subalgebra {A = A} UV) → ∣ sa ∣ ∈ VClo 𝒦
 vhom : {A B : Algebra 𝓤 S}{ϕ : hom A B}
  →     A ∈ VClo 𝒦 → hom-image-alg {A = A}{B = B} ϕ ∈ VClo 𝒦

TH : (𝒦 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ )) → _ ̇
TH 𝒦 = Σ (p , q) ꞉ (Term{X = X} × Term) , 𝒦 ⊧ p ≋ q

Th : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) → Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

MOD : (Σ' : Pred (Term{X = X} × Term) 𝓤) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) ̇
MOD Σ' = Σ A ꞉ (Algebra 𝓤 S) , ∀ p q → (p , q) ∈ Σ' → A ⊧ p ≈ q

Mod : Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) → Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ )
Mod Σ' = λ A → ∀ p q → (p , q) ∈ Σ' → A ⊧ p ≈ q

--Birkhoff's theorem: every variety is an equational class.
birkhoff : (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺))
           (A : Algebra 𝓤 S)(g : X → ∣ A ∣ )(eg : Epic g)
 →         A ∈ Mod (Th (VClo 𝒦)) → A ∈ VClo 𝒦
birkhoff 𝒦 A g eg A∈ModThV = γ
 where
  h : hom (𝑻(X)) A
  h = lift-hom{A = A}{X = X} g

  γ : A ∈ VClo 𝒦
  γ = {!!}
 --Let 𝒲 be a class of algebras that is closed under H, 𝑺, and P.
 --We must find a set Σ of equations such that 𝒲 = Mod(Σ). For this will prove that 𝒲
 --is the class of algebras satisfying a particular set of equations (i.e., 𝒲 is an
 --equational class). The obvious choice is the set of all equations that hold in 𝒲, that
 --is, Th(𝒲). So, let 𝒲' = Mod(Th(𝒲)). Clearly, 𝒲 ⊆ 𝒲'. We prove the reverse inclusion.
 --Let A ∈ 𝒲' and let 𝑌 be a set of cardinality max(∣𝐴∣, ω). Choose a surjection ℎ₀ : 𝑌 → 𝐴.
 --By :numref:`Obs %s <obs 9>`, ℎ₀ extends to an epimorphism ℎ : 𝑻(𝑌) → A`.
 --Since 𝔽_𝒲(Y) = 𝑻(Y)/θ_𝒲, there is an epimorphism g: 𝑻(Y) → 𝔽_𝒲.
 --We claim Ker g ⊆ Ker h. If the claim is true, then by :numref:`Obs %s <obs 5>`
 --∃ 𝑓 : 𝔽_𝒲(𝑌) → 𝐴 such that f ∘ g = h and since ℎ is epic, so is 𝑓, so
 --A ∈ H(𝔽_{𝒲}(Y)) ⊆ 𝒲` which will complete the proof.
 --So it remains to prove the claim that Ker g ⊆ Ker h.
 --Let u, v ∈ 𝑻(Y) and assume g(u) = g(v).
 --Since 𝑻(Y) is generated by 𝑌, there are terms 𝑝, 𝑞 ∈ 𝑻(Y) and 𝒚 such that u = p^{𝑻(X)}(𝒚)
 --and v = q^{𝑻(X)}(𝒚). Therefore, p^{𝔽_𝒲} 𝒚 = g(u) = g(v) = q^{𝔽_𝒲} 𝒚.
 --Thus 𝒲 ⊧ 𝑝 ≈ 𝑞, hence (𝑝, 𝑞) ∈ Σ. Since A ∈ Mod(Σ) we get A ⊧ 𝑝 ≈ 𝑞.
 --Therefore, ℎ(𝑢) = 𝑝^A(ℎ₀ ∘ 𝒚) = 𝑞^A(ℎ₀ ∘ 𝒚) = ℎ(𝑣), as desired.

-- 𝕍-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
--  →         (𝓤 : Universe) → (Algebra (𝓤 ⁺) S)
--  →         (𝓤' : Universe)(𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓤' S)
--  →         (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓤' )
--  →         _ ̇
-- 𝕍-closed ℒ𝒦 = λ 𝓤 B 𝓤' 𝓘 I 𝒜 𝒜i∈ℒ𝒦 → (H-closed ℒ𝒦 𝓤 B) × (𝑺-closed ℒ𝒦 (𝓤 ⁺) B) × (P-closed ℒ𝒦 𝓤' 𝓘 I 𝒜 𝒜i∈ℒ𝒦)


-- Th : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
--  →   𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ ((𝓤 ⁺) ⁺) ̇
-- Th ℒ𝒦 = λ 𝓤 → Σ (p , q) ꞉ (Term{X = X} × Term) , (ℒ𝒦 𝓤) ⊧ p ≋ q
