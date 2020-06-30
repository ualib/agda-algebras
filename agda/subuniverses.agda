-- FILE: subuniverses.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Op)
open import relations using (transitive)
open import homomorphisms using (HOM; Hom; hom; is-homomorphism)

open import terms
 using (Term; _̇_; _̂_; generator; node; comm-hom-term)

open import Relation.Unary using (⋂)

module subuniverses {S : Signature 𝓞 𝓥} where

Subuniverses : (𝑨 : Algebra 𝓤 S)
 →             Pred (Pred ∣ 𝑨 ∣ 𝓣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣)

Subuniverses (A , Fᴬ) B =
 (𝑓 : ∣ S ∣)(𝒂 : ∥ S ∥ 𝑓 → A) → Im 𝒂 ⊆ B → Fᴬ 𝑓 𝒂 ∈ B

data _is-supalgebra-of_
 (𝑨 : Algebra 𝓤 S) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  mem : (B : Pred ∣ 𝑨 ∣ 𝓤) (𝐹 : (𝑓 : ∣ S ∣)
   →    Op (∥ S ∥ 𝑓) (Σ B)) → ((𝑓 : ∣ S ∣)(𝒂 : ∥ S ∥ 𝑓 → Σ B)
   →    ∣ 𝐹 𝑓 𝒂 ∣ ≡ ∥ 𝑨 ∥ 𝑓 (λ i → ∣ 𝒂 i ∣))
   →    𝑨 is-supalgebra-of (Σ B , 𝐹)

_is-subalgebra-of_ : Algebra 𝓤 S → Algebra 𝓤 S → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
𝑩 is-subalgebra-of 𝑨 = 𝑨 is-supalgebra-of 𝑩

module _
 {𝑨 : Algebra 𝓤 S} {B : Pred ∣ 𝑨 ∣ 𝓤}
 {𝐹 : (𝑓 : ∣ S ∣) → Op (∥ S ∥ 𝑓) (Σ B)}
 (B∈SubA : B ∈ Subuniverses 𝑨) where

 SubunivAlg : Algebra 𝓤 S
 SubunivAlg =
  Σ B , λ 𝑓 x → ∥ 𝑨 ∥ 𝑓 (∣_∣ ∘ x) , B∈SubA 𝑓 (∣_∣ ∘ x)(∥_∥ ∘ x)

 subuniv-to-subalg : SubunivAlg is-subalgebra-of 𝑨
 subuniv-to-subalg = mem B ∥ SubunivAlg ∥ λ 𝑓 𝒂 → (refl _)

record Subuniverse {𝑨 : Algebra 𝓤 S} : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ where
 constructor mksub
 field
   sset  : Pred ∣ 𝑨 ∣ 𝓤
   isSub : sset ∈ Subuniverses 𝑨

module _ {𝑨 : Algebra 𝓤 S} where

 data Sg (X : Pred ∣ 𝑨 ∣ 𝓣) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣) where
  var : ∀ {v} → v ∈ X → v ∈ Sg X
  app :  ( 𝑓 : ∣ S ∣ ) { 𝒂 : ∥ S ∥ 𝑓 → ∣ 𝑨 ∣ }
   →       Im 𝒂 ⊆ Sg X
          -----------------
   →       ∥ 𝑨 ∥ 𝑓 𝒂 ∈ Sg X

 sgIsSub : (X : Pred ∣ 𝑨 ∣ 𝓤) → Sg X ∈ Subuniverses 𝑨
 sgIsSub _ 𝑓 𝒂 α = app 𝑓 α

 sgIsSmallest : {X : Pred ∣ 𝑨 ∣ 𝓡} {Y : Pred ∣ 𝑨 ∣ 𝓢}
  →             Y ∈ Subuniverses 𝑨
  →             X ⊆ Y
               -----------------
  →              Sg X ⊆ Y

 -- By induction on x ∈ Sg X, show x ∈ Y
 sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X

 sgIsSmallest {Y = Y} YIsSub X⊆Y (app 𝑓 {𝒂} im𝒂⊆SgX) = app∈Y
  where
   -- First, show the args are in Y
   im𝒂⊆Y : Im 𝒂 ⊆ Y
   im𝒂⊆Y i = sgIsSmallest YIsSub X⊆Y (im𝒂⊆SgX i)

   --Since Y is a subuniverse of 𝑨, it contains the application
   app∈Y : ∥ 𝑨 ∥ 𝑓 𝒂 ∈ Y          --           of 𝑓 to said args.
   app∈Y = YIsSub 𝑓 𝒂 im𝒂⊆Y

module _
 {𝑨 : Algebra 𝓤 S} {I : 𝓘 ̇}
 {𝐴 : I → Pred ∣ 𝑨 ∣ 𝓣} where

 sub-inter-is-sub : ((i : I) → 𝐴 i ∈ Subuniverses 𝑨)
  →                 ⋂ I 𝐴 ∈ Subuniverses 𝑨

 sub-inter-is-sub Ai-is-Sub 𝑓 𝒂 im𝒂⊆⋂A = α
  where
   α : ∥ 𝑨 ∥ 𝑓 𝒂 ∈ ⋂ I 𝐴
   α i = Ai-is-Sub i 𝑓 𝒂 λ j → im𝒂⊆⋂A j i

module _ {𝑨 𝑩 : Algebra 𝓤 S} (ℎ : hom 𝑨 𝑩)  where

 HomImage : ∣ 𝑩 ∣ → 𝓤 ̇
 HomImage = λ b → Image ∣ ℎ ∣ ∋ b

 hom-image : 𝓤 ̇
 hom-image = Σ (Image_∋_ ∣ ℎ ∣)

 fres : ∣ 𝑨 ∣ → Σ (Image_∋_ ∣ ℎ ∣)
 fres a = ∣ ℎ ∣ a , im a

 hom-image-alg : Algebra 𝓤 S
 hom-image-alg = hom-image , ops-interp
  where
   𝒂 : {𝑓 : ∣ S ∣ }(x : ∥ S ∥ 𝑓 → hom-image)(y : ∥ S ∥ 𝑓) → ∣ 𝑨 ∣
   𝒂 x y = Inv ∣ ℎ ∣  ∣ x y ∣ ∥ x y ∥

   ops-interp : (𝑓 : ∣ S ∣) → Op (∥ S ∥ 𝑓) hom-image
   ops-interp =
    λ 𝑓 x → (∣ ℎ ∣  (∥ 𝑨 ∥ 𝑓 (𝒂 x)) , im (∥ 𝑨 ∥ 𝑓 (𝒂 x)))

 hom-image-is-sub : {funext 𝓥 𝓤} → HomImage ∈ Subuniverses 𝑩
 hom-image-is-sub {fe} 𝑓 𝒃 𝒃∈Imf =
  eq (∥ 𝑩 ∥ 𝑓 (λ x → 𝒃 x)) ( ∥ 𝑨 ∥ 𝑓 ar) γ
   where
    ar : ∥ S ∥ 𝑓 → ∣ 𝑨 ∣
    ar = λ x → Inv ∣ ℎ ∣ (𝒃 x) (𝒃∈Imf x)

    ζ : (λ x → ∣ ℎ ∣ (ar x)) ≡ (λ x → 𝒃 x)
    ζ = fe (λ x → InvIsInv ∣ ℎ ∣ (𝒃 x) (𝒃∈Imf x))

    γ : ∥ 𝑩 ∥ 𝑓 (λ x → 𝒃 x)
         ≡ ∣ ℎ ∣ (∥ 𝑨 ∥ 𝑓 (λ x → Inv ∣ ℎ ∣ (𝒃 x)(𝒃∈Imf x)))
    γ = ∥ 𝑩 ∥ 𝑓 (λ x → 𝒃 x)  ≡⟨ ap ( ∥ 𝑩 ∥ 𝑓 ) (ζ ⁻¹) ⟩
        (∥ 𝑩 ∥ 𝑓)(∣ ℎ ∣ ∘ ar) ≡⟨ ( ∥ ℎ ∥ 𝑓 ar ) ⁻¹ ⟩
        ∣ ℎ ∣ (∥ 𝑨 ∥ 𝑓 ar)    ∎

module _
 {X : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇}
 {𝑨 𝑩 : Algebra 𝓤 S}
 {B : Pred ∣ 𝑨 ∣ 𝓤}
 (Y : 𝓤 ̇) where

 sub-term-closed : B ∈ Subuniverses 𝑨
  →                (𝒕 : Term)(𝒃 : X → ∣ 𝑨 ∣)
  →                (∀ i → 𝒃 i ∈ B)
                 ---------------------------
  →                ((𝒕 ̇ 𝑨) 𝒃) ∈ B

 sub-term-closed B≤𝑨 (generator x) 𝒃 𝒃∈B = 𝒃∈B x

 sub-term-closed B≤𝑨 (node 𝑓 𝒕) 𝒃 𝒃∈B =
   B≤𝑨 𝑓 (λ z → (𝒕 z ̇ 𝑨) 𝒃)
         (λ x → sub-term-closed B≤𝑨 (𝒕 x) 𝒃 𝒃∈B)

 data TermImage (Y : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤) where
  var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage Y
  app : (𝑓 : ∣ S ∣) (𝒕 : ∥ S ∥ 𝑓 → ∣ 𝑨 ∣)
   →    (∀ i  →  𝒕 i ∈ TermImage Y)
       -------------------------------
   →    (∥ 𝑨 ∥ 𝑓 𝒕) ∈ TermImage Y

 --1. TermImage is a subuniverse
 TermImageIsSub : (Y : Pred ∣ 𝑨 ∣ 𝓤)
  →               TermImage Y ∈ Subuniverses 𝑨

 TermImageIsSub Y = λ 𝑓 𝒂 x → app 𝑓 𝒂 x

 --2. Y ⊆ TermImageY
 Y⊆TermImageY : (Y : Pred ∣ 𝑨 ∣ 𝓤)
  →             Y ⊆ TermImage Y

 Y⊆TermImageY Y {a} a∈Y = var a∈Y

 -- 3. Sg^𝑨(Y) is the smallest subuniverse containing Y
 --    Proof: see `sgIsSmallest`

 SgY⊆TermImageY : (Y : Pred ∣ 𝑨 ∣ 𝓤) → Sg Y ⊆ TermImage Y
 SgY⊆TermImageY Y = sgIsSmallest (TermImageIsSub Y)
                                 (Y⊆TermImageY Y)

module _ {𝑨 : Algebra 𝓤 S} (𝓤★ : Univalence) where

 gfe : global-dfunext
 gfe = univalence-gives-global-dfunext 𝓤★

 op-closed : (∣ 𝑨 ∣ → 𝓦 ̇) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 op-closed B = (𝑓 : ∣ S ∣)(𝒂 : ∥ S ∥ 𝑓 → ∣ 𝑨 ∣)
  → ((i : ∥ S ∥ 𝑓) → B (𝒂 i)) → B (∥ 𝑨 ∥ 𝑓 𝒂)

 subuniverse : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 subuniverse = Σ B ꞉ (𝓟 ∣ 𝑨 ∣) , op-closed ( _∈₀ B)

 being-op-closed-is-subsingleton : (B : 𝓟 ∣ 𝑨 ∣)
  →           is-subsingleton (op-closed ( _∈₀ B ))
 being-op-closed-is-subsingleton B = Π-is-subsingleton gfe
  (λ 𝑓 → Π-is-subsingleton gfe
   (λ 𝒂 → Π-is-subsingleton gfe
    (λ _ → ∈-is-subsingleton B (∥ 𝑨 ∥ 𝑓 𝒂))))

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
                           (powersets-are-sets' 𝓤★ ∣ B ∣ ∣ C ∣)

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
  subset-extensionality' 𝓤★ α β
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
    (powersets-are-sets' 𝓤★ ∣ B ∣ ∣ C ∣)
     (membership-equiv-gives-carrier-equality B C ,
       carrier-equality-gives-membership-equiv B C)

 -- ...which yields an alternative subuniverse equality lemma.
 subuniverse-equality' : (B C : subuniverse)
  →                      (B ≡ C) ≃ (∣ B ∣ ≡ ∣ C ∣)
 subuniverse-equality' B C =
  (subuniverse-equality B C) ● (carrier-equiv B C)

 Subalgebra : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 Subalgebra = Σ 𝑩 ꞉ (Algebra 𝓤 S) ,
                 Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) ,
                   is-embedding h × is-homomorphism 𝑩 𝑨 h

-- HOM image is subuniverse
module intensional-hom-image
 {𝑨 𝑩 : Algebra 𝓤 S} (f : HOM 𝑨 𝑩)  where

 HOMImage : ∣ 𝑩 ∣ → 𝓤 ̇
 HOMImage = λ b → Image ∣ f ∣ ∋ b

 HOM-image : 𝓤 ̇
 HOM-image = Σ (Image_∋_ ∣ f ∣)

 fres' : ∣ 𝑨 ∣ → Σ (Image_∋_ ∣ f ∣)
 fres' a = ∣ f ∣ a , im a

 HOM-image-alg : Algebra 𝓤 S
 HOM-image-alg = HOM-image , ops-interp
  where
   𝒂 : {𝑓 : ∣ S ∣} (x : ∥ S ∥ 𝑓 → HOM-image) (y : ∥ S ∥ 𝑓)
    →  ∣ 𝑨 ∣
   𝒂 x y = Inv ∣ f ∣  ∣ x y ∣ ∥ x y ∥

   ops-interp : ( 𝑓 : ∣ S ∣ ) → Op (∥ S ∥ 𝑓) HOM-image
   ops-interp = λ 𝑓 x →(∣ f ∣ (∥ 𝑨 ∥ 𝑓 (𝒂 x)) , im (∥ 𝑨 ∥ 𝑓 (𝒂 x)))

 HOM-image-is-sub : funext 𝓥 𝓤 → HOMImage ∈ Subuniverses 𝑩
 HOM-image-is-sub fe 𝑓 𝒃 𝒃∈Imf = eq (∥ 𝑩 ∥ 𝑓 𝒃) (∥ 𝑨 ∥ 𝑓 ar) γ
  where
   ar : ∥ S ∥ 𝑓 → ∣ 𝑨 ∣
   ar = λ x → Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)

   ζ : (λ x → ∣ f ∣ (ar x)) ≡ (λ x → 𝒃 x)
   ζ = fe (λ x → InvIsInv ∣ f ∣ (𝒃 x) (𝒃∈Imf x) )

   γ : ∥ 𝑩 ∥ 𝑓 (λ x → 𝒃 x)
        ≡ ∣ f ∣ (∥ 𝑨 ∥ 𝑓 (λ x → Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)))
   γ =   ∥ 𝑩 ∥ 𝑓 (λ x → 𝒃 x)      ≡⟨ ap ( ∥ 𝑩 ∥ 𝑓 ) ζ ⁻¹ ⟩
         ( ∥ 𝑩 ∥ 𝑓 ) ( ∣ f ∣ ∘ ar ) ≡⟨ intensionality ξ ar ⟩
          ∣ f ∣ ( ∥ 𝑨 ∥ 𝑓 ar )      ∎
    where
     τ : (λ 𝑓 ar → (∥ 𝑩 ∥ 𝑓)(∣ f ∣ ∘ ar))
          ≡ (λ 𝑓 ar → ∣ f ∣ (∥ 𝑨 ∥ 𝑓 ar ))
     τ = (∥ f ∥)⁻¹
     ξ : (λ (ar : ∥ S ∥ 𝑓 → ∣ 𝑨 ∣) → (∥ 𝑩 ∥ 𝑓)(∣ f ∣ ∘ ar))
          ≡ (λ (ar : ∥ S ∥ 𝑓 → ∣ 𝑨 ∣) → ∣ f ∣ (∥ 𝑨 ∥ 𝑓 ar))
     ξ = dep-intensionality τ 𝑓

 finv' : {X : 𝓤 ̇ } (𝒃 : X → ∣ HOM-image-alg ∣) (x : X) → ∣ 𝑨 ∣
 finv' = λ 𝒃 x → Inv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥



-- --------------------------------------------------------------------------------------------------

-- Notes on homomorphic images and their types
-- --------------------------------------------

-- The homomorphic image of `f : Hom 𝑨 𝑩` is the image of `∣ 𝑨 ∣` under `f`, which, in "set-builder" notation, is simply `Im f = {f a : a ∈ ∣ 𝑨 ∣ }`.

-- As we have proved, `Im f` is a subuniverse of `𝑩`.

-- However, there is another means of representing the collection "H 𝑨" of all homomorphic images of 𝑨 without ever referring to codomain algebras (like 𝑩 above).

-- Here's how: by the first isomorphism theorem, for each `f : Hom 𝑨 𝑩`, there exists a congruence `θ` of `𝑨` (which is the kernel of `f`) that satisfies `𝑨 / θ ≅ Im f`.

-- Therefore, we have a handle on the collection `H 𝑨` of all homomorphic images of `𝑨` if we simply consider the collection `Con 𝑨` of all congruence relations of `𝑨`.  Indeed, by the above remark, we have

--   `H 𝑨 = { 𝑨 / θ : θ ∈ Con 𝑨 }`.

-- So, we could define the following:

-- .. code-block::

--    hom-closed : (𝓚 : Pred (Algebra (𝓤 ⁺) S) l)
--     →           Pred (Algebra 𝓤 S) _
--     hom-closed 𝓚 = λ 𝑨 → (𝓚 (𝑨 / (∥𝟎∥ 𝑨)))
--       →             (∃ θ : Congruence 𝑨)
--       →             (∃ 𝑪 : Algebra (𝓤 ⁺) S)
--       →             (𝓚 𝑪) × ((𝑨 / θ) ≅ 𝑪)

-- To get this to type check, we have an apparent problem, and we need a trick to resolve it. The class 𝓚 is a collection of algebras whose universes live at some level. (Above we use `𝓤 ⁺`.)

-- However, if `𝑨` is an algebra with `∣ 𝑨 ∣ : 𝓤 ̇`, then the quotient structure  (as it is now defined in Con.agda), has type `𝑨 / θ : 𝓤 ⁺ ̇`. So, in order for the class `𝓚` to contain both `𝑨` and all its quotients `𝑨 / θ` (i.e. all its homomorphic images), we need to somehow define a class of algebras that have different universe levels.

-- Can we define a data type with such "universe level polymorphism"?

-- Without that, we use a trick to get around the problem. Instead of assuming that `𝑨` itself belongs to `𝓚`, we could instead take the "quotient" `𝑨 / ∥𝟎∥` (which is isomorphic to `𝑨`) as belonging to `𝓚`.

-- This is a hack and, worse, it won't do for us. We need something inductive because we will also need that if `𝑪 ≅ 𝑨 / θ ∈ 𝓚`, then also `𝑪 / ψ ≅ (𝑨 / θ) / ψ ∈ 𝓚`.

-- So, if we want `𝓚` to be closed under all quotients, we cannot determine in advance the universe levels of the algebras that belong to `𝓚`.

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
--     hom-closed 𝓚 = ∀ 𝑨 -> (algebras 𝓚) 𝑨 -- (𝓚 (𝑨 / (⟦𝟎⟧ 𝑨)))
--      -> ∀ (θ : Congruence 𝑨) -> (∃ 𝑪 : Algebra lsuc ℓ S)
--           ------------------------------
--      ->     (𝓚 𝑪) × ((𝑨 / θ) ≅ 𝑪)


--    module _  {S : Signature 𝓞 𝓥}  where
--     open AlgebraClass

--     data HomClo {ℓ : Level} (𝓚 : AlgebraClass) : Pred AlgebraClass _ where
--      hombase : {𝑨 : Algebra ℓ S} → 𝑨 ∈ (algebras 𝓚) ℓ  → 𝑨 ∈ HomClo 𝓚
--      homstep : {𝑨 : Algebra ℓ S} ->  𝑨 ∈ HomClo 𝓚
--        ->     (∃ θ : Congruence 𝑨)
--        ->     (𝑪 : Algebra (lsuc ℓ) S)
--              ------------------------------
--        ->     𝑪 ∈ (algebras (lsuc ℓ) 𝓚) × ((𝑨 / θ) ≅ 𝑪)


