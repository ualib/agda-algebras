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
 (f : ∣ S ∣) (A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
 (g : ∣ A ∣  → ∣ B ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

op f interpreted-in A and B commutes-intensionally-with g =
 (λ a → g (∥ A ∥ f a) ) ≡ (λ a → ∥ B ∥ f (g ∘ a) )

all-ops-in_and_commute-partially-intensionally-with :
 (A : Algebra 𝓤 S)(B : Algebra 𝓦 S)
 (g : ∣ A ∣  → ∣ B ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in A and B commute-partially-intensionally-with g =
 ∀ (f : ∣ S ∣ )
  → op f interpreted-in A and B commutes-intensionally-with g

intensional-hom : (A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
 →                (∣ A ∣ → ∣ B ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

intensional-hom A B g =
 all-ops-in A and B commute-partially-intensionally-with g

Hom : Algebra 𝓦 S → Algebra 𝓤 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

Hom A B = Σ g ꞉ (∣ A ∣ → ∣ B ∣) ,
   all-ops-in A and B commute-partially-intensionally-with g

-- intensional with respect to both f and a)
preserves-ops : (A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
 →              (∣ A ∣  → ∣ B ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

preserves-ops (A , 𝐹ᴬ)(B , 𝐹ᴮ) g =
 (λ (f : ∣ S ∣ ) (a : ∥ S ∥ f → A) → g (𝐹ᴬ f a))
  ≡ (λ (f : ∣ S ∣ ) (a : ∥ S ∥ f → A )  → 𝐹ᴮ f (g ∘ a))

all-ops-in_and_commute-intensionally-with :
 (A : Algebra 𝓤 S)(B : Algebra 𝓦 S)
 (g : ∣ A ∣  → ∣ B ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in A and B commute-intensionally-with g =
 preserves-ops A B g

--the type of (intensional) homomorphisms
HOM : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

HOM A B = Σ g ꞉ (∣ A ∣ → ∣ B ∣) ,
           all-ops-in A and B commute-intensionally-with g

op_interpreted-in_and_commutes-extensionally-with :
   (f : ∣ S ∣) (A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
   (g : ∣ A ∣  → ∣ B ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

op f interpreted-in A and B commutes-extensionally-with g =
 ∀( a : ∥ S ∥ f → ∣ A ∣ ) → g (∥ A ∥ f a) ≡ ∥ B ∥ f (g ∘ a)

all-ops-in_and_commute-extensionally-with :
     (A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
 →   (∣ A ∣  → ∣ B ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in A and B commute-extensionally-with g = ∀ (f : ∣ S ∣)
  → op f interpreted-in A and B commutes-extensionally-with g

is-homomorphism : (A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
 →                (∣ A ∣ → ∣ B ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

is-homomorphism A B g =
 all-ops-in A and B commute-extensionally-with g

hom : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
hom A B = Σ g ꞉ (∣ A ∣ → ∣ B ∣ ) , is-homomorphism A B g

𝓲𝓭 :  (A : Algebra 𝓤 S) → hom A A
𝓲𝓭 _ = (λ x → x) , λ _ _ → refl _ 

HCompClosed : {A : Algebra 𝓤 S}
              {B : Algebra 𝓦 S}
              {C : Algebra 𝓣 S}
 →            hom A B   →   hom B C
             ------------------------
 →                   hom A C

HCompClosed {A = A , FA}{B = B , FB}{C = C , FC}
 (g , ghom) (h , hhom) = h ∘ g , γ
  where
   γ : ( f : ∣ S ∣ ) ( a : ∥ S ∥ f  →  A )
    →  ( h ∘ g ) ( FA f a ) ≡ FC f ( h ∘ g ∘ a )

   γ f a = (h ∘ g) (FA f a) ≡⟨ ap h ( ghom f a ) ⟩
          h (FB f (g ∘ a)) ≡⟨ hhom f ( g ∘ a ) ⟩
          FC f (h ∘ g ∘ a) ∎

--Alternative notation for hom composition
module _ {A : Algebra 𝓤 S}
         {B : Algebra 𝓦 S}
         {C : Algebra 𝓣 S} where

  _>>>_ : hom A B  → hom B C → hom A C

  (g , ghom) >>> (h , hhom) = h ∘ g , γ
    where
      γ :      (f : ∣ S ∣ ) → (a : ∥ S ∥ f → ∣ A ∣)
           -------------------------------------------
       →    (h ∘ g) (∥ A ∥ f a)  ≡  ∥ C ∥ f (h ∘ g ∘ a)

      γ f a =
       (h ∘ g) (∥ A ∥ f a) ≡⟨ ap (λ - → h -) (ghom f a) ⟩
       h (∥ B ∥ f (g ∘ a)) ≡⟨ hhom f (g ∘ a) ⟩
       ∥ C ∥ f (h ∘ g ∘ a) ∎

homFactor : funext 𝓤 𝓤 → {A B C : Algebra 𝓤 S}
            (g : hom A B) (h : hom A C)
 →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣  →   Epic ∣ h ∣
           ---------------------------------------------
 →           Σ ϕ ꞉ (hom C B) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

homFactor fe {A = A , FA}{B = B , FB}{C = C , FC}
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

   ζ : (f : ∣ S ∣)(c : ∥ S ∥ f → C)(x : ∥ S ∥ f)
    →  c x ≡ (h ∘ hInv)(c x)

   ζ f c x = (cong-app (EInvIsRInv fe h hEpic) (c x))⁻¹

   ι : (f : ∣ S ∣)(c : ∥ S ∥ f → C)
    →  (λ x → c x) ≡ (λ x → h (hInv (c x)))

   ι f c = ap (λ - → - ∘ c)(EInvIsRInv fe h hEpic)⁻¹

   useker : (f : ∣ S ∣)  (c : ∥ S ∥ f → C)
    → g (hInv (h (FA f (hInv ∘ c)))) ≡ g(FA f (hInv ∘ c))

   useker = λ f c
    → Kh⊆Kg (cong-app
             (EInvIsRInv fe h hEpic)
             (h(FA f(hInv ∘ c)))
            )

   ϕIsHomCB : (f : ∣ S ∣)(a : ∥ S ∥ f → C)
    →         ϕ (FC f a)  ≡  FB f (ϕ ∘ a)

   ϕIsHomCB f c =
    g (hInv (FC f c))                ≡⟨ i   ⟩
    g (hInv (FC f (h ∘ (hInv ∘ c)))) ≡⟨ ii  ⟩
    g (hInv (h (FA f (hInv ∘ c))))   ≡⟨ iii ⟩
    g (FA f (hInv ∘ c))              ≡⟨ iv  ⟩
    FB f (λ x → g (hInv (c x)))      ∎
    where
     i   = ap (g ∘ hInv) (ap (FC f) (ι f c))
     ii  = ap (λ - → g (hInv -)) (hhom f (hInv ∘ c))⁻¹
     iii = useker f c
     iv  = ghom f (hInv ∘ c)

_is-hom-image-of_ : (B : Algebra (𝓤 ⁺) S)
 →                  (A : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

B is-hom-image-of A = Σ θ ꞉ (Rel ∣ A ∣ _) ,
                        con A θ  × ((∣ A ∣ // θ) ≡ ∣ B ∣)

HomImagesOf : (Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
HomImagesOf A = Σ B ꞉ (Algebra _ S) , B is-hom-image-of A

HomImagesOf-pred : (Algebra 𝓤 S)
 →                 Pred (Algebra ( 𝓤 ⁺ ) S) (𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))

HomImagesOf-pred A = λ B → B is-hom-image-of A

_is-hom-image-of-class_ : {𝓤 : Universe} → (Algebra (𝓤 ⁺) S)
 →                        (Pred (Algebra 𝓤 S) (𝓤 ⁺))
 →                        𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

B is-hom-image-of-class 𝒦 = Σ A ꞉ (Algebra _ S) ,
                               (A ∈ 𝒦) × (B is-hom-image-of A)

HomImagesOfClass : {𝓤 : Universe}
 →                 Pred (Algebra 𝓤 S) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

HomImagesOfClass 𝒦 = Σ B ꞉ (Algebra _ S) ,
                        (B is-hom-image-of-class 𝒦)

H : {𝓤 : Universe} → Pred (Algebra 𝓤 S) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
H 𝒦 = HomImagesOfClass 𝒦

-- Here ℒ𝒦 represents a (universe-indexed) collection of classes.
H-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
 →         (𝓤 : Universe) → (Algebra (𝓤 ⁺) S)
 →          𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

H-closed ℒ𝒦 =
 λ 𝓤 B → (B is-hom-image-of-class (ℒ𝒦 𝓤)) → (B ∈ (ℒ𝒦 (𝓤 ⁺)))

_≅_ : (A B : Algebra 𝓤 S) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
A ≅ B =  Σ ϕ ꞉ (hom A B) , Σ ψ ꞉ (hom B A) ,
          (∣ ϕ ∣ ∘ ∣ ψ ∣ ≡ ∣ 𝓲𝓭 B ∣) × (∣ ψ ∣ ∘ ∣ ϕ ∣ ≡ ∣ 𝓲𝓭 A ∣)

is-algebra-iso : {A B : Algebra 𝓤 S} (ϕ : hom A B) → 𝓤 ⁺ ̇
is-algebra-iso {𝓤}{A} ϕ = ker ∣ ϕ ∣ ≡ 𝟎 {𝓤}{∣ A ∣}

AlgebraIsos : (A B : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
AlgebraIsos {𝓤} A B = Σ ϕ ꞉ (hom A B) ,
                        is-algebra-iso {𝓤} {A} {B} ϕ

_≈_ : Rel (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
A ≈ B = is-singleton (AlgebraIsos A B)

