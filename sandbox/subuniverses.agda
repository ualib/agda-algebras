-- FILE: subuniverses.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext)

module subuniverses
 {𝑆 : Signature 𝓞 𝓥}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {fe : global-dfunext} where

open import homomorphisms {𝑆 = 𝑆}

open import terms
 {𝑆 = 𝑆}
 {𝕏 = 𝕏}
 {gfe = fe} renaming (generator to ℊ)

open import Relation.Unary using (⋂)

open import prelude using (Im_⊆_; Univalence; embeddings-are-lc;
 univalence-gives-global-dfunext; 𝓟; _∈₀_; _⊆₀_; pr₁; domain;
 is-subsingleton; Π-is-subsingleton;is-equiv; lr-implication; ×-is-subsingleton;
 ∈-is-subsingleton; is-embedding; pr₁-embedding; rl-implication; inverse;
 embedding-gives-ap-is-equiv; is-set;_⇔_;transport; subset-extensionality';
 equiv-to-subsingleton; powersets-are-sets'; _≃_; id; _●_;
 logically-equivalent-subsingletons-are-equivalent) public



Subuniverses : (𝑨 : Algebra 𝓤 𝑆)
 →             Pred (Pred ∣ 𝑨 ∣ 𝓣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣)

Subuniverses 𝑨 B =
 (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → Im a ⊆ B → (f ̂ 𝑨) a ∈ B

data _is-supalgebra-of_ {𝓤 : Universe}
 (𝑨 : Algebra 𝓤 𝑆) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  mem : (B : Pred ∣ 𝑨 ∣ 𝓤) (F : (f : ∣ 𝑆 ∣)
   →    Op (∥ 𝑆 ∥ f) (Σ B)) → ((f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → Σ B)
   →    ∣ F f a ∣ ≡ (f ̂ 𝑨)(λ i → ∣ a i ∣))
   →    𝑨 is-supalgebra-of (Σ B , F)

_is-subalgebra-of_ : {𝓤 : Universe} → Algebra 𝓤 𝑆 → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
𝑩 is-subalgebra-of 𝑨 = 𝑨 is-supalgebra-of 𝑩

_is-subalgebra-of-class_ : {𝓤 : Universe} (𝑩 : Algebra 𝓤 𝑆)
 →            Pred (Algebra 𝓤 𝑆)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
𝑩 is-subalgebra-of-class 𝒦 =
   Σ 𝑨 ꞉ (Algebra _ 𝑆) , (𝑨 ∈ 𝒦) × (𝑩 is-subalgebra-of 𝑨)

module _
 {𝑨 : Algebra 𝓤 𝑆} {B : Pred ∣ 𝑨 ∣ 𝓤}
 {F : (f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) (Σ B)}
 (B∈SubA : B ∈ Subuniverses 𝑨) where

 SubunivAlg : Algebra 𝓤 𝑆
 SubunivAlg =
  Σ B , λ f x → (f ̂ 𝑨)(∣_∣ ∘ x) , B∈SubA f (∣_∣ ∘ x)(∥_∥ ∘ x)

 subuniv-to-subalg : SubunivAlg is-subalgebra-of 𝑨
 subuniv-to-subalg = mem B ∥ SubunivAlg ∥ λ f a → (refl _)

record Subuniverse {𝑨 : Algebra 𝓤 𝑆} : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ where
 constructor mksub
 field
   sset  : Pred ∣ 𝑨 ∣ 𝓤
   isSub : sset ∈ Subuniverses 𝑨

module _ {𝑨 : Algebra 𝓤 𝑆} where

 data Sg (X : Pred ∣ 𝑨 ∣ 𝓣) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣) where
  var : ∀ {v} → v ∈ X → v ∈ Sg X
  app :  ( f : ∣ 𝑆 ∣ ) { a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣ }
   →       Im a ⊆ Sg X
          -----------------
   →       (f ̂ 𝑨) a ∈ Sg X

 sgIsSub : (X : Pred ∣ 𝑨 ∣ 𝓤) → Sg X ∈ Subuniverses 𝑨
 sgIsSub _ f a α = app f α

 sgIsSmallest : {X : Pred ∣ 𝑨 ∣ 𝓡} {Y : Pred ∣ 𝑨 ∣ 𝓢}
  →             Y ∈ Subuniverses 𝑨
  →             X ⊆ Y
               -----------------
  →              Sg X ⊆ Y

 -- By induction on x ∈ Sg X, show x ∈ Y
 sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X

 sgIsSmallest {Y = Y} YIsSub X⊆Y (app f {a} ima⊆SgX) = app∈Y
  where
   -- First, show the args are in Y
   ima⊆Y : Im a ⊆ Y
   ima⊆Y i = sgIsSmallest YIsSub X⊆Y (ima⊆SgX i)

   --Since Y is a subuniverse of 𝑨, it contains the application
   app∈Y : (f ̂ 𝑨) a ∈ Y          --           of f to said args.
   app∈Y = YIsSub f a ima⊆Y

module _
 {𝑨 : Algebra 𝓤 𝑆} {I : 𝓘 ̇}
 {𝒜 : I → Pred ∣ 𝑨 ∣ 𝓣} where

 sub-inter-is-sub : ((i : I) → 𝒜 i ∈ Subuniverses 𝑨)
  →                 ⋂ I 𝒜 ∈ Subuniverses 𝑨

 sub-inter-is-sub Ai-is-Sub f a ima⊆⋂A = α
  where
   α : (f ̂ 𝑨) a ∈ ⋂ I 𝒜
   α i = Ai-is-Sub i f a λ j → ima⊆⋂A j i


module _
 {𝓤 : Universe}
 {X : 𝓤 ̇}
 {𝑨 𝑩 : Algebra 𝓤 𝑆}
 {B : Pred ∣ 𝑨 ∣ 𝓤}
 (Y : 𝓤 ̇) where

 sub-term-closed : B ∈ Subuniverses 𝑨
  →                (t : Term)(b : X → ∣ 𝑨 ∣)
  →                (∀ i → b i ∈ B)
                 ---------------------------
  →                ((t ̇ 𝑨) b) ∈ B

 sub-term-closed B≤A (ℊ x) b b∈B = b∈B x

 sub-term-closed B≤A (node f t) b b∈B =
   B≤A f (λ z → (t z ̇ 𝑨) b)
         (λ x → sub-term-closed B≤A (t x) b b∈B)

 data TermImage (Y : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤) where
  var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage Y
  app : (f : ∣ 𝑆 ∣) (t : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣)
   →    (∀ i  →  t i ∈ TermImage Y)
       -------------------------------
   →    (f ̂ 𝑨) t ∈ TermImage Y

 --1. TermImage is a subuniverse
 TermImageIsSub : (Y : Pred ∣ 𝑨 ∣ 𝓤)
  →               TermImage Y ∈ Subuniverses 𝑨

 TermImageIsSub Y = λ f a x → app f a x

 --2. Y ⊆ TermImageY
 Y⊆TermImageY : (Y : Pred ∣ 𝑨 ∣ 𝓤)
  →             Y ⊆ TermImage Y

 Y⊆TermImageY Y {a} a∈Y = var a∈Y

 -- 3. Sg^A(Y) is the smallest subuniverse containing Y
 --    Proof: see `sgIsSmallest`

 SgY⊆TermImageY : (Y : Pred ∣ 𝑨 ∣ 𝓤) → Sg Y ⊆ TermImage Y
 SgY⊆TermImageY Y = sgIsSmallest (TermImageIsSub Y)
                                 (Y⊆TermImageY Y)



module mhe_subgroup_generalization {𝓦 : Universe} {𝑨 : Algebra 𝓦 𝑆} (ua : Univalence) where

 gfe : global-dfunext
 gfe = univalence-gives-global-dfunext ua

 op-closed : (∣ 𝑨 ∣ → 𝓦 ̇) → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ̇
 op-closed B = (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣)
  → ((i : ∥ 𝑆 ∥ f) → B (a i)) → B ((f ̂ 𝑨) a)

 subuniverse : 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 subuniverse = Σ B ꞉ (𝓟 ∣ 𝑨 ∣) , op-closed ( _∈₀ B)

 being-op-closed-is-subsingleton : (B : 𝓟 ∣ 𝑨 ∣)
  →           is-subsingleton (op-closed ( _∈₀ B ))
 being-op-closed-is-subsingleton B = Π-is-subsingleton gfe
  (λ f → Π-is-subsingleton gfe
   (λ a → Π-is-subsingleton gfe
    (λ _ → ∈-is-subsingleton B ((f ̂ 𝑨) a))))

 pr₁-is-embedding : is-embedding ∣_∣
 pr₁-is-embedding = pr₁-embedding being-op-closed-is-subsingleton

 --so equality of subalgebras is equality of their underlying
 --subsets in the powerset:
 ap-pr₁ : (B C : subuniverse) → B ≡ C → ∣ B ∣ ≡ ∣ C ∣
 ap-pr₁ B C = ap ∣_∣

 ap-pr₁-is-equiv : (B C : subuniverse) → is-equiv (ap-pr₁ B C)
 ap-pr₁-is-equiv =
  embedding-gives-ap-is-equiv ∣_∣ pr₁-is-embedding

 subuniverse-is-a-set : is-set subuniverse
 subuniverse-is-a-set B C = equiv-to-subsingleton
                           (ap-pr₁ B C , ap-pr₁-is-equiv B C)
                           (powersets-are-sets' ua ∣ B ∣ ∣ C ∣)

 subuniverse-equality-gives-membership-equiv : (B C : subuniverse)
  →                                  B ≡ C
                      -----------------------------------
  →                   ( x : ∣ 𝑨 ∣ ) → (x ∈₀ ∣ B ∣) ⇔ (x ∈₀ ∣ C ∣)
 subuniverse-equality-gives-membership-equiv B C B≡C x =
  transport (λ - → x ∈₀ ∣ - ∣) B≡C ,
   transport (λ - → x ∈₀ ∣ - ∣ ) ( B≡C ⁻¹ )

 membership-equiv-gives-carrier-equality : (B C : subuniverse)
  →          ((x : ∣ 𝑨 ∣) →  x ∈₀ ∣ B ∣  ⇔  x ∈₀ ∣ C ∣)
            -----------------------------------------
  →                       ∣ B ∣ ≡ ∣ C ∣
 membership-equiv-gives-carrier-equality B C φ =
  subset-extensionality' ua α β
   where
    α :  ∣ B ∣ ⊆₀ ∣ C ∣
    α x = lr-implication (φ x)

    β : ∣ C ∣ ⊆₀ ∣ B ∣
    β x = rl-implication (φ x)

 membership-equiv-gives-subuniverse-equality : (B C : subuniverse)
  →            (( x : ∣ 𝑨 ∣ ) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣)
               ---------------------------------------
  →                          B ≡ C
 membership-equiv-gives-subuniverse-equality B C =
  inverse (ap-pr₁ B C)
  (ap-pr₁-is-equiv B C)
     ∘ (membership-equiv-gives-carrier-equality B C)

 membership-equiv-is-subsingleton : (B C : subuniverse)
  →    is-subsingleton (( x : ∣ 𝑨 ∣) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣)
 membership-equiv-is-subsingleton B C =
  Π-is-subsingleton gfe
   (λ x → ×-is-subsingleton
    (Π-is-subsingleton gfe (λ _ → ∈-is-subsingleton ∣ C ∣ x ))
      (Π-is-subsingleton gfe (λ _ → ∈-is-subsingleton ∣ B ∣ x )))

 subuniverse-equality : (B C : subuniverse)
  →    (B ≡ C)  ≃  ((x : ∣ 𝑨 ∣)  → (x ∈₀ ∣ B ∣) ⇔ (x ∈₀ ∣ C ∣))

 subuniverse-equality B C =
  logically-equivalent-subsingletons-are-equivalent _ _
    (subuniverse-is-a-set B C)
     (membership-equiv-is-subsingleton B C)
      (subuniverse-equality-gives-membership-equiv B C ,
        membership-equiv-gives-subuniverse-equality B C)

 carrier-equality-gives-membership-equiv : (B C : subuniverse)
  →                            ∣ B ∣ ≡ ∣ C ∣
                ----------------------------------------
  →              ( ( x : ∣ 𝑨 ∣ ) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣ )
 carrier-equality-gives-membership-equiv B C (refl _) x = id , id

 --so we have...
 carrier-equiv : (B C : subuniverse)
  →   ((x : ∣ 𝑨 ∣) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣) ≃ (∣ B ∣ ≡ ∣ C ∣)
 carrier-equiv B C =
  logically-equivalent-subsingletons-are-equivalent _ _
   (membership-equiv-is-subsingleton B C)
    (powersets-are-sets' ua ∣ B ∣ ∣ C ∣)
     (membership-equiv-gives-carrier-equality B C ,
       carrier-equality-gives-membership-equiv B C)

 -- ...which yields an alternative subuniverse equality lemma.
 subuniverse-equality' : (B C : subuniverse)
  →                      (B ≡ C) ≃ (∣ B ∣ ≡ ∣ C ∣)
 subuniverse-equality' B C =
  (subuniverse-equality B C) ● (carrier-equiv B C)


-- module _ {𝓤 : Universe} (UV : Univalence) where

 -- new definition of subalgebra (includes an embedding)
SubalgebrasOf : {𝓢 : Universe} → Algebra 𝓢 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓢 ⁺ ̇
SubalgebrasOf {𝓢} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓢 𝑆) ,
                Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) ,
                  is-embedding h × is-homomorphism 𝑩 𝑨 h

SubalgebrasOfClass : {𝓢 : Universe} → Pred (Algebra 𝓢 𝑆)(𝓢 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓢 ⁺ ̇
SubalgebrasOfClass 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , (𝑨 ∈ 𝒦) × SubalgebrasOf 𝑨

-- module _
--  {𝓤 : Universe}
--  {X : 𝓧 ̇ }
--  {UV : Univalence} where

--  _⊧_≈_ : {X : 𝓧 ̇ } → Algebra 𝓤 𝑆
--   →      Term{X = X} → Term → 𝓧 ⊔ 𝓤 ̇

--  𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

--  _⊧_≋_ : Pred (Algebra 𝓤 𝑆) 𝓦
--   →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇

--  _⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

--  gdfe : global-dfunext
--  gdfe = univalence-gives-global-dfunext UV

--  SubalgebrasOfClass : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
--  SubalgebrasOfClass 𝒦 =
--   Σ 𝑨 ꞉ (Algebra _ 𝑆) , (𝑨 ∈ 𝒦) × Subalgebra{𝑨 = 𝑨} UV

--  data SClo (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
--   sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo 𝒦
--   sub : (SAK : SubalgebrasOfClass 𝒦) → (pr₁ ∥ (pr₂ SAK) ∥) ∈ SClo 𝒦

--  S-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺))
--   →      (𝓤 : Universe) → (𝑩 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
--  S-closed ℒ𝒦 =
--   λ 𝓤 B → (B is-subalgebra-of-class (ℒ𝒦 𝓤)) → (B ∈ ℒ𝒦 𝓤)

--  subalgebras-preserve-identities : (𝒦 : Pred (Algebra 𝓤 𝑆) ( 𝓤 ⁺ ))(p q : Term{X = X})
--   →  (𝒦 ⊧ p ≋ q) → (SAK : SubalgebrasOfClass 𝒦)
--   →  (pr₁ ∥ (pr₂ SAK) ∥) ⊧ p ≈ q
--  subalgebras-preserve-identities 𝒦 p q 𝒦⊧p≋q SAK = γ
--   where

--   𝑨 : Algebra 𝓤 𝑆
--   𝑨 = ∣ SAK ∣

--   A∈𝒦 : 𝑨 ∈ 𝒦
--   A∈𝒦 = ∣ pr₂ SAK ∣

--   A⊧p≈q : 𝑨 ⊧ p ≈ q
--   A⊧p≈q = 𝒦⊧p≋q A∈𝒦

--   subalg : Subalgebra{𝑨 = 𝑨} UV
--   subalg = ∥ pr₂ SAK ∥

--   𝑩 : Algebra 𝓤 𝑆
--   𝑩 = pr₁ subalg

--   h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
--   h = ∣ pr₂ subalg ∣

--   hem : is-embedding h
--   hem = pr₁ ∥ pr₂ subalg ∥

--   hhm : is-homomorphism 𝑩 𝑨 h
--   hhm = pr₂ ∥ pr₂ subalg ∥

--   ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
--   ξ b =
--    h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gdfe 𝑩 𝑨 (h , hhm) p b ⟩
--    (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
--    (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gdfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
--    h ((q ̇ 𝑩) b)  ∎

--   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
--   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

--   γ : 𝑩 ⊧ p ≈ q
--   γ = gdfe λ b → hlc (ξ b)


-- Hom image is subuniverse
module _ {𝑨 𝑩 : Algebra 𝓤 𝑆} (ϕ : hom 𝑨 𝑩)  where
 hom-image-is-sub : {funext 𝓥 𝓤} → (HomImage{𝑨 = 𝑨} 𝑩 ϕ) ∈ Subuniverses 𝑩
 hom-image-is-sub {fe} f b b∈Imf =
  eq ((f ̂ 𝑩) b) ((f ̂ 𝑨) ar) γ
   where
    ar : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣
    ar = λ x → Inv ∣ ϕ ∣ (b x) (b∈Imf x)

    ζ : ∣ ϕ ∣ ∘ ar ≡ b
    ζ = fe (λ x → InvIsInv ∣ ϕ ∣ (b x) (b∈Imf x))

    γ : (f ̂ 𝑩)  b
         ≡ ∣ ϕ ∣ ((f ̂ 𝑨)(λ x → Inv ∣ ϕ ∣ (b x)(b∈Imf x)))
    γ = (f ̂ 𝑩) b            ≡⟨ ap (f ̂ 𝑩) (ζ ⁻¹) ⟩
        (f ̂ 𝑩)(∣ ϕ ∣ ∘ ar) ≡⟨ ( ∥ ϕ ∥ f ar ) ⁻¹ ⟩
        ∣ ϕ ∣ ((f ̂ 𝑨) ar)    ∎




-- --------------------------------------------------------------------------------------------------

-- Notes on homomorphic images and their types
-- --------------------------------------------

-- The homomorphic image of `f : Hom A B` is the image of `∣ A ∣` under `f`, which, in "set-builder" notation, is simply `Im f = {f a : a ∈ ∣ A ∣ }`.

-- As we have proved, `Im f` is a subuniverse of `B`.

-- However, there is another means of representing the collection "H A" of all homomorphic images of A without ever referring to codomain algebras (like B above).

-- Here's how: by the first isomorphism theorem, for each `f : Hom A B`, there exists a congruence `θ` of `A` (which is the kernel of `f`) that satisfies `A / θ ≅ Im f`.

-- Therefore, we have a handle on the collection `H A` of all homomorphic images of `A` if we simply consider the collection `Con A` of all congruence relations of `A`.  Indeed, by the above remark, we have

--   `H A = { A / θ : θ ∈ Con A }`.

-- So, we could define the following:

-- .. code-block::

--    hom-closed : (𝒦 : Pred (Algebra (𝓤 ⁺) S) l)
--     →           Pred (Algebra 𝓤 S) _
--     hom-closed 𝒦 = λ A → (𝒦 (A / (∥𝟎∥ A)))
--       →             (∃ θ : Congruence A)
--       →             (∃ C : Algebra (𝓤 ⁺) S)
--       →             (𝒦 C) × ((A / θ) ≅ C)

-- To get this to type check, we have an apparent problem, and we need a trick to resolve it. The class 𝒦 is a collection of algebras whose universes live at some level. (Above we use `𝓤 ⁺`.)

-- However, if `A` is an algebra with `∣ A ∣ : 𝓤 ̇`, then the quotient structure  (as it is now defined in Con.agda), has type `A / θ : 𝓤 ⁺ ̇`. So, in order for the class `𝒦` to contain both `A` and all its quotients `A / θ` (i.e. all its homomorphic images), we need to somehow define a class of algebras that have different universe levels.

-- Can we define a data type with such "universe level polymorphism"?

-- Without that, we use a trick to get around the problem. Instead of assuming that `A` itself belongs to `𝒦`, we could instead take the "quotient" `A / ∥𝟎∥` (which is isomorphic to `A`) as belonging to `𝒦`.

-- This is a hack and, worse, it won't do for us. We need something inductive because we will also need that if `C ≅ A / θ ∈ 𝒦`, then also `C / ψ ≅ (A / θ) / ψ ∈ 𝒦`.

-- So, if we want `𝒦` to be closed under all quotients, we cannot determine in advance the universe levels of the algebras that belong to `𝒦`.

-- We are trying to come up with a datatype for classes of algebras that has some sort of inductive notion of the universe levels involved.

-- It seems we may be testing the limits of Agda's universe level paradigm. Maybe we can invent a new type to solve the problem, or we may have to try to extend Agda's capabilities.

-- ..
--    record AlgebraClass (𝓤 : Universe) : 𝓤 ̇ where
--     algebras : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ )
--     nextclass : AlgebraClass ( 𝓤 ⁺ )

--    record AlgebraClass : Set _ where
--     algebras : (ℓ : Level) -> Pred (Algebra ℓ S) (lsuc ℓ)

--    module _ {S : Signature 𝓞 𝓥} where

--     hom-closed : Pred (AlgebraClass lzero) _
--     hom-closed 𝒦 = ∀ A -> (algebras 𝒦) A -- (𝒦 (A / (⟦𝟎⟧ A)))
--      -> ∀ (θ : Congruence A) -> (∃ C : Algebra lsuc ℓ S)
--           ------------------------------
--      ->     (𝒦 C) × ((A / θ) ≅ C)


--    module _  {S : Signature 𝓞 𝓥}  where
--     open AlgebraClass

--     data HomClo {ℓ : Level} (𝒦 : AlgebraClass) : Pred AlgebraClass _ where
--      hombase : {A : Algebra ℓ S} → A ∈ (algebras 𝒦) ℓ  → A ∈ HomClo 𝒦
--      homstep : {A : Algebra ℓ S} ->  A ∈ HomClo 𝒦
--        ->     (∃ θ : Congruence A)
--        ->     (C : Algebra (lsuc ℓ) S)
--              ------------------------------
--        ->     C ∈ (algebras (lsuc ℓ) 𝒦) × ((A / θ) ≅ C)


