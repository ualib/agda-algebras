\begin{code}
-- FILE: subuniverses.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext)

module subuniverses
 {𝑆 : Signature 𝓞 𝓥}
 {𝕏 : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {fe : global-dfunext} where

open import homomorphisms {𝑆 = 𝑆}

open import terms
 {𝑆 = 𝑆}
 {𝕏 = 𝕏}
 {gfe = fe} renaming (generator to ℊ)

open import Relation.Unary using (⋂)

open import prelude using (Im_⊆_; Univalence; embeddings-are-lc; univalence-gives-global-dfunext;
 𝓟; _∈₀_; _⊆₀_; pr₁; domain; Π-is-subsingleton;is-equiv; lr-implication; ×-is-subsingleton; id-is-embedding;
 ∈-is-subsingleton; pr₁-embedding; rl-implication; inverse; embedding-gives-ap-is-equiv; is-set;_⇔_;
 transport; subset-extensionality'; equiv-to-subsingleton; powersets-are-sets'; _●_; ∘-embedding;
 logically-equivalent-subsingletons-are-equivalent) public

Subuniverses : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆) → Pred (Pred ∣ 𝑨 ∣ 𝓤) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤)
Subuniverses 𝑨 B = (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → Im a ⊆ B → (f ̂ 𝑨) a ∈ B


SubunivAlg : {𝓠 𝓤 : Universe} (𝑨 : Algebra 𝓠 𝑆)(B : Pred ∣ 𝑨 ∣ 𝓤)
 →           B ∈ Subuniverses 𝑨
 →           Algebra (𝓠 ⊔ 𝓤) 𝑆
SubunivAlg 𝑨 B B∈SubA = Σ B , λ f x → (f ̂ 𝑨)(∣_∣ ∘ x) ,
                                            B∈SubA f (∣_∣ ∘ x)(∥_∥ ∘ x)

record Subuniverse {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆} : 𝓞 ⊔ 𝓥 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇ where
 constructor mksub
 field
   sset  : Pred ∣ 𝑨 ∣ 𝓤
   isSub : sset ∈ Subuniverses 𝑨

data Sg {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆) (X : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤) where
 var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
 app : (f : ∣ 𝑆 ∣){a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣} → Im a ⊆ Sg 𝑨 X
       ---------------------------------------------
  →       (f ̂ 𝑨) a ∈ Sg 𝑨 X

sgIsSub : {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆}{X : Pred ∣ 𝑨 ∣ 𝓤} → Sg 𝑨 X ∈ Subuniverses 𝑨
sgIsSub f a α = app f α

sgIsSmallest : {𝓠 𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓠 𝑆){X : Pred ∣ 𝑨 ∣ 𝓤}(Y : Pred ∣ 𝑨 ∣ 𝓦)
 →             Y ∈ Subuniverses 𝑨  →  X ⊆ Y
              ------------------------------
 →                     Sg 𝑨 X ⊆ Y

-- By induction on x ∈ Sg X, show x ∈ Y
sgIsSmallest _ _ _ X⊆Y (var v∈X) = X⊆Y v∈X

sgIsSmallest 𝑨 Y YIsSub X⊆Y (app f {a} ima⊆SgX) = app∈Y
 where
  -- First, show the args are in Y
  ima⊆Y : Im a ⊆ Y
  ima⊆Y i = sgIsSmallest 𝑨 Y YIsSub X⊆Y (ima⊆SgX i)

  --Since Y is a subuniverse of 𝑨, it contains the application
  app∈Y : (f ̂ 𝑨) a ∈ Y          --           of f to said args.
  app∈Y = YIsSub f a ima⊆Y

sub-inter-is-sub : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)
                   (I : 𝓤 ̇)(𝒜 : I → Pred ∣ 𝑨 ∣ 𝓤)
 →                 ((i : I) → 𝒜 i ∈ Subuniverses 𝑨)
                  -------------------------------------
 →                  ⋂ I 𝒜 ∈ Subuniverses 𝑨

sub-inter-is-sub 𝑨 I 𝒜 Ai-is-Sub f a ima⊆⋂A = α
 where
  α : (f ̂ 𝑨) a ∈ ⋂ I 𝒜
  α i = Ai-is-Sub i f a λ j → ima⊆⋂A j i

sub-term-closed : {𝓧 𝓠 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓠 𝑆)(B : Pred ∣ 𝑨 ∣ 𝓤)
 →                B ∈ Subuniverses 𝑨
 →                (t : Term)(b : X → ∣ 𝑨 ∣)
 →                (∀ x → b x ∈ B)
                ---------------------------
 →                ((t ̇ 𝑨) b) ∈ B

sub-term-closed _ _ B≤A (ℊ x) b b∈B = b∈B x

sub-term-closed 𝑨 B B≤A (node f t) b b∈B =
   B≤A f (λ z → (t z ̇ 𝑨) b)
          (λ x → sub-term-closed 𝑨 B B≤A (t x) b b∈B)

data TermImage {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(Y : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤) where
 var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
 app : (f : ∣ 𝑆 ∣) (t : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → (∀ i  →  t i ∈ TermImage 𝑨 Y)
      ---------------------------------------------------------------
  →              (f ̂ 𝑨) t ∈ TermImage 𝑨 Y

--1. TermImage is a subuniverse
TermImageIsSub : {𝓠 𝓤 : Universe}
                 {𝑨 : Algebra 𝓠 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
                 ------------------------------------
 →                TermImage 𝑨 Y ∈ Subuniverses 𝑨

TermImageIsSub = app -- λ f a x → app f a x

--2. Y ⊆ TermImageY
Y⊆TermImageY : {𝓠 𝓤 : Universe}
               {𝑨 : Algebra 𝓠 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
              ------------------------------------
 →              Y ⊆ TermImage 𝑨 Y

Y⊆TermImageY {a} a∈Y = var a∈Y

-- 3. Sg^A(Y) is the smallest subuniverse containing Y
--    Proof: see `sgIsSmallest`

SgY⊆TermImageY : {𝓠 𝓤 : Universe}
                 (𝑨 : Algebra 𝓠 𝑆)  (Y : Pred ∣ 𝑨 ∣ 𝓤)
                --------------------------------------
 →                Sg 𝑨 Y ⊆ TermImage 𝑨 Y

SgY⊆TermImageY 𝑨 Y = sgIsSmallest 𝑨 (TermImage 𝑨 Y) TermImageIsSub Y⊆TermImageY


hom-image-is-sub : {𝓠 𝓤 : Universe} → global-dfunext
 →                 {𝑨 : Algebra 𝓠 𝑆} {𝑩 : Algebra 𝓤 𝑆} (ϕ : hom 𝑨 𝑩)
                  -------------------------------------------------
 →                 (HomImage 𝑩 ϕ) ∈ Subuniverses 𝑩

hom-image-is-sub gfe {𝑨}{𝑩} ϕ f b b∈Imf = eq ((f ̂ 𝑩) b) ((f ̂ 𝑨) ar) γ
 where
  ar : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣
  ar = λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)

  ζ : ∣ ϕ ∣ ∘ ar ≡ b
  ζ = gfe (λ x → InvIsInv ∣ ϕ ∣(b x)(b∈Imf x))

  γ : (f ̂ 𝑩) b ≡ ∣ ϕ ∣((f ̂ 𝑨)(λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)))

  γ = (f ̂ 𝑩) b          ≡⟨ ap (f ̂ 𝑩)(ζ ⁻¹) ⟩
      (f ̂ 𝑩)(∣ ϕ ∣ ∘ ar)  ≡⟨(∥ ϕ ∥ f ar)⁻¹ ⟩
      ∣ ϕ ∣((f ̂ 𝑨) ar)   ∎

--------------------------------------------------------------------------------------------
-- SUBALGEBRAS
----------------
_IsSubalgebraOf_ : {𝓤 𝓠 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇
𝑩 IsSubalgebraOf 𝑨 = Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) , is-embedding h × is-homomorphism 𝑩 𝑨 h 

SUBALGEBRA : {𝓤 𝓠 : Universe} → Algebra 𝓠 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ⁺ ̇
SUBALGEBRA {𝓤} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , 𝑩 IsSubalgebraOf 𝑨

Subalgebra : {𝓤 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
Subalgebra {𝓤} = SUBALGEBRA {𝓤}{𝓤}

getSub : {𝓤 𝓠 : Universe}{𝑨 : Algebra 𝓠 𝑆} → SUBALGEBRA{𝓤}{𝓠} 𝑨 → Algebra 𝓤 𝑆
getSub SA = ∣ SA ∣

_IsSubalgebraOfClass_ : {𝓤 𝓠 𝓦 : Universe}(𝑩 : Algebra 𝓤 𝑆)
 →                      Pred (Algebra 𝓠 𝑆) 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓤 ⊔ 𝓠) ⁺ ̇
_IsSubalgebraOfClass_ {𝓤} 𝑩 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , Σ SA ꞉ (SUBALGEBRA{𝓤} 𝑨) , (𝑨 ∈ 𝒦) × (𝑩 ≅ ∣ SA ∣)

SUBALGEBRAOFCLASS : {𝓤 𝓠 𝓦 : Universe} → Pred (Algebra 𝓠 𝑆) 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇
SUBALGEBRAOFCLASS {𝓤} 𝒦 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , 𝑩 IsSubalgebraOfClass 𝒦

SubalgebraOfClass : {𝓤 𝓠 : Universe} → Pred (Algebra 𝓠 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺) → 𝓞 ⊔ 𝓥 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇
SubalgebraOfClass {𝓤}{𝓠} = SUBALGEBRAOFCLASS {𝓤}{𝓠}{𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺}

getSubOfClass : {𝓤 𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) 𝓦} → SUBALGEBRAOFCLASS 𝒦 → Algebra 𝓤 𝑆
getSubOfClass SAC = ∣ SAC ∣


SUBALGEBRAOFCLASS' : {𝓤 𝓠 𝓦 : Universe} → Pred (Algebra 𝓠 𝑆) 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇
SUBALGEBRAOFCLASS' {𝓤}{𝓠} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓠 𝑆) , (𝑨 ∈ 𝒦) × SUBALGEBRA{𝓤}{𝓠} 𝑨

-- Sugar.
_≤_ : {𝓤 𝓠 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇
𝑩 ≤ 𝑨 = 𝑩 IsSubalgebraOf 𝑨

trans-≤ : {𝓦 𝓤 𝓠 : Universe}(𝑪 : Algebra 𝓦 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆)
 →         𝑪 ≤ 𝑩   →    𝑩 ≤ 𝑨
          ---------------------
 →              𝑪 ≤ 𝑨
trans-≤ 𝑪 𝑩 𝑨 CB BA =
 ∣ BA ∣ ∘ ∣ CB ∣ , ∘-embedding (fst ∥ BA ∥) (fst ∥ CB ∥) , ∘-hom 𝑪 𝑩 𝑨{∣ BA ∣}{∣ CB ∣} (snd ∥ BA ∥) (snd ∥ CB ∥)

mono-≤ : {𝓤 𝓠 𝓦 : Universe}(𝑩 : Algebra 𝓤 𝑆){𝒦 𝒦' : Pred (Algebra 𝓠 𝑆) 𝓦}
 →       𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'
mono-≤ 𝑩 KK' KB = ∣ KB ∣ , fst ∥ KB ∥ , KK' (∣ snd ∥ KB ∥ ∣) , ∥ (snd ∥ KB ∥) ∥

refl-≤ : {𝓠 : Universe}(𝑨 : Algebra 𝓠 𝑆) → 𝑨 ≤ 𝑨
refl-≤ 𝑨 = 𝑖𝑑 ∣ 𝑨 ∣ , id-is-embedding , id-is-hom

iso-≤ : {𝓦 𝓤 𝓠 : Universe}(𝑪 : Algebra 𝓦 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆)
 →         𝑪 ≅ 𝑩   →    𝑩 ≤ 𝑨
          ---------------------
 →              𝑪 ≤ 𝑨
iso-≤ 𝑪 𝑩 𝑨 C≅B B≤A = f , femb , fhom
 where

  f : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  f = ∣ B≤A ∣ ∘ (fst ∣ C≅B ∣)

  femb : is-embedding f
  femb = ∘-embedding (fst ∥ B≤A ∥) (iso→embedding C≅B)

  fhom : is-homomorphism 𝑪 𝑨 f
  fhom = ∘-hom 𝑪 𝑩 𝑨{∣ B≤A ∣}{fst ∣ C≅B ∣} (snd ∥ B≤A ∥) (snd ∣ C≅B ∣)

----------------------------------------------------------------------------------

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


