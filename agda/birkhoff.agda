--FILE: birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--REF: Based on the file `birkhoff.agda` (23 Jan 2020).

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; _̂_)
open import congruences using (KER-pred) -- ; ker-pred; con; Congruence)

module birkhoff
 {𝑆 : Signature 𝓞 𝓥}
 {ua : Univalence}
 {X : 𝓤 ̇ }
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤} where

open import closure
 {𝑆 = 𝑆}
 {ua = ua}
 {X = X}
 {gfe = gfe}
 {dfe = dfe}

--Equalizers of functions
𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
𝑬 g h x = g x ≡ h x

--Equalizers of homomorphisms
𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 𝑆} (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x
--cf. definition 𝓔 in the homomorphisms module

𝑬𝑯-is-closed : funext 𝓥 𝓤
 →     {𝑓 : ∣ 𝑆 ∣ } {𝑨 𝑩 : Algebra 𝓤 𝑆}
       (g h : hom 𝑨 𝑩)  (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ 𝑨 ∣)
 →     ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
       --------------------------------------------------
 →      ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 p = 
 --(g , ghom)(h , hhom) 𝒂 p =
   ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)    ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
   (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)  ≡⟨ ap (_ ̂ 𝑩)(fe p) ⟩
   (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
   ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)    ∎

-- Equalizer of homs is a subuniverse.
𝑬𝑯-is-subuniverse : funext 𝓥 𝓤
 →  {𝑨 𝑩 : Algebra 𝓤 𝑆}(g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}
𝑬𝑯-is-subuniverse fe {𝑨} {𝑩} g h =
 mksub (𝑬𝑯 {𝑨}{𝑩} g h)
  λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 x

HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}
           (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →         (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
         ---------------------------------------------------
 →        (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg {𝑨 = 𝑨} X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x
HomUnique fe {𝑨}{𝑩} X g h gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
  ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)     ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 )   ≡⟨ ap (𝑓 ̂ 𝑩)(fe induction-hypothesis) ⟩
  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)    ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )   ∎
 where
  induction-hypothesis =
    λ x → HomUnique fe {𝑨}{𝑩} X g h gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

-- Equational classes
TH : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) → _ ̇
TH 𝒦 = Σ (p , q) ꞉ (Term{X = X} × Term) , 𝒦 ⊧ p ≋ q

Th : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) → Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

MOD : (ℰ : Pred (Term{X = X} × Term) 𝓤) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) ̇
MOD ℰ = Σ A ꞉ (Algebra 𝓤 𝑆) , ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

Mod : Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) → Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ )
Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

-- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
ThHSP-axiomatizes : {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)}
                    (p q : ∣ (𝑻 X) ∣ )
                  -----------------------------------------
 →                 𝒦 ⊧ p ≋ q  ⇔  ((p , q) ∈ Th (VClo 𝒦))

ThHSP-axiomatizes p q =
 (λ 𝒦⊧p≋q 𝑨∈VClo𝒦 → vclo-id1{p = p}{q = q} 𝒦⊧p≋q 𝑨∈VClo𝒦) ,
  λ pq∈Th 𝑨∈𝒦 → pq∈Th (vbase 𝑨∈𝒦)

-- Birkhoff's theorem: every variety is an equational class.
birkhoff : (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺))
           (𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣ )(eg : Epic h₀)
 →         𝑨 ∈ Mod (Th (VClo 𝒦)) → 𝑨 ∈ VClo 𝒦
birkhoff 𝒦 𝑨 h₀ eg A∈ModThV = γ
 where
  h : hom (𝑻 X) 𝑨
  h = lift-hom{𝑨 = 𝑨}{X = X} h₀

  A⊧ : ∀ p q →  𝒦 ⊧ p ≋ q → 𝑨 ⊧ p ≈ q
  A⊧ p q 𝒦⊧p≋q = ξ
   where
    pq∈ : (p , q) ∈ Th (VClo 𝒦)
    pq∈ = (lr-implication (ThHSP-axiomatizes p q)) 𝒦⊧p≋q

    ξ : 𝑨 ⊧ p ≈ q
    ξ = A∈ModThV p q pq∈

  Ψ⊆Kerh : ∀ pair → pair ∈ Ψ {𝒦 = 𝒦} → pair ∈ KER-pred{B = ∣ 𝑨 ∣} ∣ h ∣
  Ψ⊆Kerh (p , q) pΨq = hp≡hq
   where
    𝒦⊧p≋q : 𝒦 ⊧ p ≋ q
    𝒦⊧p≋q = {!!}

    𝑨⊧p≈q : 𝑨 ⊧ p ≈ q
    𝑨⊧p≈q = A⊧ p q 𝒦⊧p≋q

    ζ : (𝒕 : X → ∣ 𝑻(X) ∣) → ∣ h ∣ ((p ̇ 𝑻(X)) 𝒕) ≡ ∣ h ∣ ((q ̇ 𝑻(X)) 𝒕)
    ζ = λ 𝒕 →
     ∣ h ∣ ((p ̇ 𝑻(X)) 𝒕) ≡⟨ comm-hom-term gfe (𝑻 X) 𝑨 h p 𝒕 ⟩
     (p ̇ 𝑨) (∣ h ∣ ∘ 𝒕) ≡⟨ intensionality 𝑨⊧p≈q (∣ h ∣ ∘ 𝒕) ⟩
     (q ̇ 𝑨) (∣ h ∣ ∘ 𝒕) ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 h q 𝒕)⁻¹ ⟩
     ∣ h ∣ ((q ̇ 𝑻(X)) 𝒕) ∎

    -- Want: (𝒕 : X → ∣ 𝑻(X) ∣) → ((p ̇ 𝑻(X)) 𝒕) ≡ p 𝒕

    hp≡hq : ∣ h ∣ p ≡ ∣ h ∣ q
    hp≡hq = let ζx = ζ (λ x → generator x) in {!!}

  --h 𝑝 x = (𝑝 ̇ 𝑨) h x and h 𝑞 y = (𝑞 ̇ 𝑨) h y
  -- Given generators x and y
  --Therefore, ℎ(𝑢) = (𝑝 ̇ 𝑨)(ℎ₀ ∘ 𝑥) = (𝑞 ̇ 𝑨)(ℎ₀ ∘ 𝑥) = ℎ(𝑣),
   --  𝑢 = (𝑝 ̇ 𝑻)(𝑥) and 𝑣 = (𝑞 ̇ 𝑻)(𝑥)
   -- ℎ(𝑢) = ℎ ((𝑝 ̇ 𝑻) 𝑥) = (𝑝 ̇ 𝑨)(ℎ ∘ 𝑥) = (𝑞 ̇ 𝑨)(ℎ ∘ 𝑥) = ℎ ((𝑞 ̇ 𝑻) 𝑥) = ℎ(𝑣).

  -- Ψ⊆Kerh (generator x , generator y) pΨq = {!!}
  -- Ψ⊆Kerh (generator x , node f t) pΨq = {!!}
  -- Ψ⊆Kerh (node f t , generator y) pΨq = {!!}
  -- Ψ⊆Kerh (node f t , node g s) pΨq = {!!}
  -- 𝒦⊧ : {p q : ∣ (𝑻 X) ∣} → (p , q) ∈ Th (VClo 𝒦) → 𝒦 ⊧ p ≋ q
  -- 𝒦⊧ = λ z z₁ → z (vbase z₁)

  γ : 𝑨 ∈ VClo 𝒦
  γ = {!!}

  -- Since
  -- vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦
  -- We need to show there is some 𝑭 ∈ VClo 𝒦 such that (𝑨 , _ , _ ) : HomImagesOf 𝑭

 --Let 𝒲 be a class of algebras that is closed under H, S, and P.
 --We must find a set Σ of equations such that 𝒲 = Mod(Σ). For this will prove that 𝒲
 --is the class of algebras satisfying a particular set of equations (i.e., 𝒲 is an
 --equational class). The obvious choice is the set of all equations that hold in 𝒲, that
 --is, Th(𝒲). So, let 𝒲' = Mod(Th(𝒲)). Clearly, 𝒲 ⊆ 𝒲'. We prove the reverse inclusion.
 --Let A ∈ 𝒲' and let 𝑋 be a set of cardinality max(∣𝐴∣, ω). Choose a surjection ℎ₀ : 𝑋 → 𝐴.
 --By :numref:`Obs %s <obs 9>`, ℎ₀ extends to an epimorphism ℎ : 𝑻(𝑋) → A.
 --Since 𝔽(𝒲, 𝑋) = 𝑻(𝑋)/Ψ(𝒲, 𝑋), there is an epimorphism 𝑔 : 𝑻(𝑋) → 𝔽(𝒲, 𝑋).
 --We claim ker 𝑔 ⊆ ker ℎ. If the claim is true, then by :numref:`Obs %s <obs 5>`
 --∃ 𝑓 : 𝔽(𝒲, 𝑋) → 𝐴 such that 𝑓 ∘ 𝑔 = ℎ and since ℎ is epic, so is 𝑓, so
 --A ∈ H(𝔽(𝒲, 𝑋)) ⊆ 𝒲` which will complete the proof.
 --So it remains to prove the claim that ker 𝑔 ⊆ ker ℎ.
 --Let 𝑢, 𝑣 ∈ 𝑻(𝑋) and assume 𝑔(𝑢) = 𝑔(𝑣). Since 𝑻(𝑋) is generated by 𝑋, there are terms
 --𝑝, 𝑞 ∈ 𝑻(𝑋) and 𝒙 such that :math:`𝑢 = p^{𝑻(𝑋)}(𝒙)`
 --and :math:`𝑣 = q^{𝑻(X)}(𝒙)`. Therefore, :math:`p^{𝔽(𝒲, 𝑋)} 𝒙 = 𝑔(𝑢) = 𝑔(𝑣) = q^{𝔽(𝒲, 𝑋)} 𝒙`.
 --Thus 𝒲 ⊧ 𝑝 ≈ 𝑞, hence (𝑝, 𝑞) ∈ Σ. Since A ∈ Mod(Σ) we get A ⊧ 𝑝 ≈ 𝑞.
 --Therefore, :math:`ℎ(𝑢) = 𝑝 ̇ 𝑨 (ℎ₀ ∘ 𝒙) = 𝑞^A(ℎ₀ ∘ 𝒙) = ℎ(𝑣)`, as desired.



-- -- Product Closure
-- P-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺ ))
--  →      (𝓤 : Universe)(𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
--  →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓤 ) → 𝓤 ⁺ ⊔ 𝓘 ⁺ ̇
-- P-closed ℒ𝒦 = λ 𝓤 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  ⨅ 𝒜  ∈ (ℒ𝒦 (𝓤 ⊔ 𝓘))

-- data PClo (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
--  pbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo 𝒦
--  prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆}
--   →     (∀ i → 𝒜 i ∈ PClo 𝒦)
--   →     ⨅ 𝒜 ∈ PClo 𝒦

-- -- Subalgebra Closure
-- data SClo (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
--  sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo 𝒦
--  sub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ SClo 𝒦 → (sa : Subalgebra {𝑨 = 𝑨} ua) → ∣ sa ∣ ∈ SClo 𝒦

-- -- module _
-- --  {𝒦 : Pred (Algebra 𝓤 𝑆) ( 𝓤 ⁺ )} where

-- HomImages : Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
-- HomImages 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
--                           is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

-- module _ {𝑨 𝑩 : Algebra 𝓤 𝑆} (ϕ : hom 𝑨 𝑩)  where

--  HomImage : ∣ 𝑩 ∣ → 𝓤 ̇
--  HomImage = λ b → Image ∣ ϕ ∣ ∋ b

--  hom-image : 𝓤 ̇
--  hom-image = Σ (Image_∋_ ∣ ϕ ∣)

--  fres : ∣ 𝑨 ∣ → Σ (Image_∋_ ∣ ϕ ∣)
--  fres a = ∣ ϕ ∣ a , im a

--  hom-image-alg : Algebra 𝓤 𝑆
--  hom-image-alg = hom-image , ops-interp
--   where
--    a : {f : ∣ 𝑆 ∣ }(x : ∥ 𝑆 ∥ f → hom-image) → ∥ 𝑆 ∥ f → ∣ 𝑨 ∣
--    a x y = Inv ∣ ϕ ∣  ∣ x y ∣ ∥ x y ∥

--    ops-interp : (f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) hom-image
--    ops-interp = λ f x → (∣ ϕ ∣ ((f ̂ 𝑨) (a x)) , im ((f ̂ 𝑨)(a x)))


-- -- Homomorphic Image Closure
-- data HClo (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
--  hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo 𝒦
--  hhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ HClo 𝒦 → ((𝑩 , _ ) : HomImages 𝑨) → 𝑩 ∈ HClo 𝒦


-- module _ (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)) where

--  hclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (HClo 𝒦 ⊧ p ≋ q)
--  hclo-id1 {p}{q} 𝒦⊧p≋q (hbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
--  hclo-id1 {p}{q} 𝒦⊧p≋q (hhom{𝑨} A∈HClo𝒦 𝑩ϕhomSur) = γ
--   where
--   A⊧p≈q : 𝑨 ⊧ p ≈ q
--   A⊧p≈q = (hclo-id1{p}{q} 𝒦⊧p≋q ) A∈HClo𝒦

--   IH : (p ̇ 𝑨) ≡ (q ̇ 𝑨)
--   IH = A⊧p≈q

--   𝑩 : Algebra 𝓤 𝑆
--   𝑩 = ∣ 𝑩ϕhomSur ∣

--   ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
--   ϕ = ∣ ∥ 𝑩ϕhomSur ∥ ∣

--   ϕhom : is-homomorphism 𝑨 𝑩 ϕ
--   ϕhom = ∣ pr₂ ∥ 𝑩ϕhomSur ∥ ∣

--   ϕsur : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
--   ϕsur 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhomSur ∥ ∥ (𝒃 x)

--   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
--   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕsur 𝒃 x))

--   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
--   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕsur 𝒃 x)

--   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
--   γ = gfe λ 𝒃 →
--    (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
--    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) p (preim 𝒃))⁻¹ ⟩
--    ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality IH (preim 𝒃)) ⟩
--    ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
--    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
--    (q ̇ 𝑩) 𝒃 ∎

-- hclo-id2 : ∀ {𝒦 p q} → (HClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
-- hclo-id2 p A∈𝒦 = p (hbase A∈𝒦)
