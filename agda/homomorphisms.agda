-- File: homomorphisms.agda
-- Author: William DeMeo and Siva Somayyajula
-- Date: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra)
open import relations using (ker; ker-pred; Rel; 𝟎; con; _//_)

module homomorphisms {S : Signature 𝓞 𝓥} where

--intensional preservation of operations
op_interpreted-in_and_commutes-intensionally-with :
 (𝑓 : ∣ S ∣) (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
 (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-intensionally-with g =
 (λ 𝒂 → g (∥ 𝑨 ∥ 𝑓 𝒂) ) ≡ (λ 𝒂 → ∥ 𝑩 ∥ 𝑓 (g ∘ 𝒂) )

all-ops-in_and_commute-partially-intensionally-with :
 (𝑨 : Algebra 𝓤 S)(𝑩 : Algebra 𝓦 S)
 (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with g =
 ∀ (𝑓 : ∣ S ∣ )
  → op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-intensionally-with g

intensional-hom : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
 →                (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

intensional-hom 𝑨 𝑩 g =
 all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with g

Hom : Algebra 𝓦 S → Algebra 𝓤 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

Hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
   all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with g

-- intensional with respect to both 𝑓 and 𝒂)
preserves-ops : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
 →              (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

preserves-ops (A , 𝐹ᴬ)(B , 𝐹ᴮ) g =
 (λ (𝑓 : ∣ S ∣ ) (𝒂 : ∥ S ∥ 𝑓 → A) → g (𝐹ᴬ 𝑓 𝒂))
  ≡ (λ (𝑓 : ∣ S ∣ ) (𝒂 : ∥ S ∥ 𝑓 → A )  → 𝐹ᴮ 𝑓 (g ∘ 𝒂))

all-ops-in_and_commute-intensionally-with :
 (𝑨 : Algebra 𝓤 S)(𝑩 : Algebra 𝓦 S)
 (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in 𝑨 and 𝑩 commute-intensionally-with g =
 preserves-ops 𝑨 𝑩 g

--the type of (intensional) homomorphisms
HOM : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

HOM 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
           all-ops-in 𝑨 and 𝑩 commute-intensionally-with g

op_interpreted-in_and_commutes-extensionally-with :
   (𝑓 : ∣ S ∣) (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
   (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-extensionally-with g =
 ∀( 𝒂 : ∥ S ∥ 𝑓 → ∣ 𝑨 ∣ ) → g (∥ 𝑨 ∥ 𝑓 𝒂) ≡ ∥ 𝑩 ∥ 𝑓 (g ∘ 𝒂)

all-ops-in_and_commute-extensionally-with :
     (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
 →   (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in 𝑨 and 𝑩 commute-extensionally-with g = ∀ (𝑓 : ∣ S ∣)
  → op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-extensionally-with g

is-homomorphism : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
 →                (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

is-homomorphism 𝑨 𝑩 g =
 all-ops-in 𝑨 and 𝑩 commute-extensionally-with g

hom : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g

𝓲𝓭 :  (A : Algebra 𝓤 S) → hom A A
𝓲𝓭 _ = (λ x → x) , λ _ _ → refl _ 

HCompClosed : {𝑨 : Algebra 𝓤 S}
              {𝑩 : Algebra 𝓦 S}
              {𝑪 : Algebra 𝓣 S}
 →            hom 𝑨 𝑩   →   hom 𝑩 𝑪
             ------------------------
 →                   hom 𝑨 𝑪

HCompClosed {𝑨 = A , FA}{𝑩 = B , FB}{𝑪 = C , FC}
 (g , ghom) (h , hhom) = h ∘ g , γ
  where
   γ : ( 𝑓 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝑓  →  A )
    →  ( h ∘ g ) ( FA 𝑓 𝒂 ) ≡ FC 𝑓 ( h ∘ g ∘ 𝒂 )

   γ 𝑓 𝒂 = (h ∘ g) (FA 𝑓 𝒂) ≡⟨ ap h ( ghom 𝑓 𝒂 ) ⟩
          h (FB 𝑓 (g ∘ 𝒂)) ≡⟨ hhom 𝑓 ( g ∘ 𝒂 ) ⟩
          FC 𝑓 (h ∘ g ∘ 𝒂) ∎

--Alternative notation for hom composition
module _ {A : Algebra 𝓤 S}
         {B : Algebra 𝓦 S}
         {C : Algebra 𝓣 S} where

  _>>>_ : hom A B  → hom B C → hom A C

  (g , ghom) >>> (h , hhom) = h ∘ g , γ
    where
      γ :      (𝑓 : ∣ S ∣ ) → (𝒂 : ∥ S ∥ 𝑓 → ∣ A ∣)
           -------------------------------------------
       →    (h ∘ g) (∥ A ∥ 𝑓 𝒂)  ≡  ∥ C ∥ 𝑓 (h ∘ g ∘ 𝒂)

      γ 𝑓 𝒂 =
       (h ∘ g) (∥ A ∥ 𝑓 𝒂) ≡⟨ ap (λ - → h -) (ghom 𝑓 𝒂) ⟩
       h (∥ B ∥ 𝑓 (g ∘ 𝒂)) ≡⟨ hhom 𝑓 (g ∘ 𝒂) ⟩
       ∥ C ∥ 𝑓 (h ∘ g ∘ 𝒂) ∎

homFactor : funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 S}
            (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
 →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣  →   Epic ∣ h ∣
           ---------------------------------------------
 →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

homFactor fe {𝑨 = A , FA}{𝑩 = B , FB}{𝑪 = C , FC}
 (g , ghom) (h , hhom) Kh⊆Kg hEpic = (ϕ , ϕIsHomCB) , g≡ϕ∘h
  where
   hInv : C → A
   hInv = λ c → (EpicInv h hEpic) c

   ϕ : C → B
   ϕ = λ c → g ( hInv c )

   ξ : (x : A) → ker-pred h (x , hInv (h x))
   ξ x =  ( cong-app (EInvIsRInv fe h hEpic) ( h x ) )⁻¹

   g≡ϕ∘h : g ≡ ϕ ∘ h
   g≡ϕ∘h = fe  λ x → Kh⊆Kg (ξ x)

   ζ : (𝑓 : ∣ S ∣)(𝒄 : ∥ S ∥ 𝑓 → C)(x : ∥ S ∥ 𝑓)
    →  𝒄 x ≡ (h ∘ hInv)(𝒄 x)

   ζ 𝑓 𝒄 x = (cong-app (EInvIsRInv fe h hEpic) (𝒄 x))⁻¹

   ι : (𝑓 : ∣ S ∣)(𝒄 : ∥ S ∥ 𝑓 → C)
    →  (λ x → 𝒄 x) ≡ (λ x → h (hInv (𝒄 x)))

   ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄)(EInvIsRInv fe h hEpic)⁻¹

   useker : (𝑓 : ∣ S ∣)  (𝒄 : ∥ S ∥ 𝑓 → C)
    → g (hInv (h (FA 𝑓 (hInv ∘ 𝒄)))) ≡ g(FA 𝑓 (hInv ∘ 𝒄))

   useker = λ 𝑓 𝒄
    → Kh⊆Kg (cong-app
             (EInvIsRInv fe h hEpic)
             (h(FA 𝑓(hInv ∘ 𝒄)))
            )

   ϕIsHomCB : (𝑓 : ∣ S ∣)(𝒂 : ∥ S ∥ 𝑓 → C)
    →         ϕ (FC 𝑓 𝒂)  ≡  FB 𝑓 (ϕ ∘ 𝒂)

   ϕIsHomCB 𝑓 𝒄 =
    g (hInv (FC 𝑓 𝒄))                ≡⟨ i   ⟩
    g (hInv (FC 𝑓 (h ∘ (hInv ∘ 𝒄)))) ≡⟨ ii  ⟩
    g (hInv (h (FA 𝑓 (hInv ∘ 𝒄))))   ≡⟨ iii ⟩
    g (FA 𝑓 (hInv ∘ 𝒄))              ≡⟨ iv  ⟩
    FB 𝑓 (λ x → g (hInv (𝒄 x)))      ∎
    where
     i   = ap (g ∘ hInv) (ap (FC 𝑓) (ι 𝑓 𝒄))
     ii  = ap (λ - → g (hInv -)) (hhom 𝑓 (hInv ∘ 𝒄))⁻¹
     iii = useker 𝑓 𝒄
     iv  = ghom 𝑓 (hInv ∘ 𝒄)

_is-hom-image-of_ : (𝑩 : Algebra (𝓤 ⁺) S)
 →                  (𝑨 : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

𝑩 is-hom-image-of 𝑨 = Σ θ ꞉ (Rel ∣ 𝑨 ∣ _) ,
                        con 𝑨 θ  × ((∣ 𝑨 ∣ // θ) ≡ ∣ 𝑩 ∣)

HomImagesOf : (Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
HomImagesOf 𝑨 = Σ 𝑩 ꞉ (Algebra _ S) , 𝑩 is-hom-image-of 𝑨

HomImagesOf-pred : (Algebra 𝓤 S)
 →                 Pred (Algebra ( 𝓤 ⁺ ) S) (𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))

HomImagesOf-pred 𝑨 = λ 𝑩 → 𝑩 is-hom-image-of 𝑨

_is-hom-image-of-class_ : {𝓤 : Universe} → (Algebra (𝓤 ⁺) S)
 →                        (Pred (Algebra 𝓤 S) (𝓤 ⁺))
 →                        𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

𝑩 is-hom-image-of-class 𝓚 = Σ 𝑨 ꞉ (Algebra _ S) ,
                               (𝑨 ∈ 𝓚) × (𝑩 is-hom-image-of 𝑨)

HomImagesOfClass : {𝓤 : Universe}
 →                 Pred (Algebra 𝓤 S) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ S) ,
                        (𝑩 is-hom-image-of-class 𝓚)

𝑯 : {𝓤 : Universe} → Pred (Algebra 𝓤 S) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
𝑯 𝓚 = HomImagesOfClass 𝓚

-- Here 𝓛𝓚 represents a (universe-indexed) collection of classes.
𝑯-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
 →         (𝓤 : Universe) → (Algebra (𝓤 ⁺) S)
 →          𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

𝑯-closed 𝓛𝓚 =
 λ 𝓤 𝑩 → (𝑩 is-hom-image-of-class (𝓛𝓚 𝓤)) → (𝑩 ∈ (𝓛𝓚 (𝓤 ⁺)))

_≅_ : (A B : Algebra 𝓤 S) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
A ≅ B =  Σ f ꞉ (hom A B) , Σ g ꞉ (hom B A) ,
          (∣ f ∣ ∘ ∣ g ∣ ≡ ∣ 𝓲𝓭 B ∣) × (∣ g ∣ ∘ ∣ f ∣ ≡ ∣ 𝓲𝓭 A ∣)

is-algebra-iso : {A B : Algebra 𝓤 S} (f : hom A B) → 𝓤 ⁺ ̇
is-algebra-iso {𝓤}{A} f = ker ∣ f ∣ ≡ 𝟎 {𝓤}{∣ A ∣}

AlgebraIsos : (A B : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
AlgebraIsos {𝓤} A B = Σ f ꞉ (hom A B) ,
                        is-algebra-iso {𝓤} {A} {B} f

_≈_ : Rel (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
A ≈ B = is-singleton (AlgebraIsos A B)

