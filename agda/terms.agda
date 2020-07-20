-- FILE: terms.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π'; Op; _̂_)
open import homomorphisms using (HOM; Hom; hom)
open import relations using (Con; compatible-fun)
module terms {S : Signature 𝓞 𝓥} where

data Term {X : 𝓧 ̇}  :  𝓞 ⊔ 𝓥 ⊔ 𝓧 ̇  where
  generator : X → Term {X = X}
  node : (f : ∣ S ∣) → (t : ∥ S ∥ f → Term {X = X}) → Term

open Term

--The term algebra 𝑻(X).
𝑻 : 𝓧 ̇ → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓧) S
𝑻 X = Term{X = X} , node

module _ {A : Algebra 𝓤 S} {X : 𝓧 ̇ } where

 --1.a. Every map (X → A) lifts.
 free-lift : (h : X → ∣ A ∣)  →   ∣ 𝑻 X ∣ → ∣ A ∣
 free-lift h (generator x) = h x
 free-lift h (node f args) = ∥ A ∥ f λ i → free-lift h (args i)

 --1.b. The lift is (extensionally) a hom
 lift-hom : (h : X → ∣ A ∣) →  hom (𝑻 X) A
 lift-hom h = free-lift h , λ f a → ap (∥ A ∥ _) (refl _)

 --2. The lift to (free → A) is (extensionally) unique.
 free-unique : funext 𝓥 𝓤 → (g h : hom (𝑻 X) A)
  →            (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
  →            (t : Term )
              ---------------------------
  →            ∣ g ∣ t ≡ ∣ h ∣ t

 free-unique fe g h p (generator x) = p x
 free-unique fe g h p (node f args) =
    ∣ g ∣ (node f args)            ≡⟨ ∥ g ∥ f args ⟩
    ∥ A ∥ f (λ i → ∣ g ∣ (args i))  ≡⟨ ap (∥ A ∥ _) γ ⟩
    ∥ A ∥ f (λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ f args)⁻¹ ⟩
    ∣ h ∣ (node f args)             ∎
    where γ = fe λ i → free-unique fe g h p (args i)

 --1.b. that free-lift is (intensionally) a hom.
 lift-HOM : (h : X → ∣ A ∣) →  HOM (𝑻 X) A
 lift-HOM  h = free-lift h , refl _

 --2. The lift to  (free → A)  is (intensionally) unique.
 free-intensionally-unique : funext 𝓥 𝓤
  →             (g h : HOM (𝑻 X) A)
  →             (∣ g ∣ ∘ generator) ≡ (∣ h ∣ ∘ generator)
  →             (t : Term)
               --------------------------------
  →              ∣ g ∣ t ≡ ∣ h ∣ t

 free-intensionally-unique fe g h p (generator x) =
  intensionality p x

 free-intensionally-unique fe g h p (node f args) =
  ∣ g ∣ (node f args)   ≡⟨ ap (λ - → - f args) ∥ g ∥ ⟩
  ∥ A ∥ f(∣ g ∣ ∘ args) ≡⟨ ap (∥ A ∥ _) γ ⟩
  ∥ A ∥ f(∣ h ∣ ∘ args) ≡⟨ (ap (λ - → - f args) ∥ h ∥ ) ⁻¹ ⟩
  ∣ h ∣ (node f args)  ∎
   where
    γ = fe λ i → free-intensionally-unique fe g h p (args i)


_̇_ : {X : 𝓧 ̇ } → Term{X = X}
 →   (A : Algebra 𝓤 S) → (X → ∣ A ∣) → ∣ A ∣

((generator x)̇ A) a = a x

((node f args)̇ A) a = (f ̂ A) λ{x → (args x ̇ A) a}

interp-prod : funext 𝓥 𝓤
 →            {X : 𝓧 ̇}{I : 𝓤 ̇}(p : Term{X = X})
              (𝒜 : I → Algebra 𝓤 S)
              (x : X → ∀ i → ∣ (𝒜 i) ∣)
 →            (p ̇ (Π' 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

interp-prod fe (generator x₁) 𝒜 x = refl _

interp-prod fe (node f t) 𝒜 x =
 let IH = λ x₁ → interp-prod fe (t x₁) 𝒜 x in
  ∥ Π' 𝒜 ∥ f (λ x₁ → (t x₁ ̇ Π' 𝒜) x)
      ≡⟨ ap (∥ Π' 𝒜 ∥ f ) (fe IH) ⟩
  ∥ Π' 𝒜 ∥ f (λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
      ≡⟨ refl _ ⟩
  (λ i₁ → ∥ 𝒜 i₁ ∥ f (λ x₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
      ∎

interp-prod2 : global-dfunext
 →             {X : 𝓧 ̇ }{I : 𝓤 ̇ }
               (p : Term{X = X}) (A : I → Algebra 𝓤 S)
     -----------------------------------------------------------
 → (p ̇ Π' A) ≡ λ(args : X → ∣ Π' A ∣)
                   → (λ i → (p ̇ A i)(λ x → args x i))

interp-prod2 fe (generator x₁) A = refl _

interp-prod2 fe {X = X} (node f t) A =
  fe λ (tup : X → ∣ Π' A ∣) →
   let IH = λ x → interp-prod fe (t x) A  in
   let tA = λ z → t z ̇ Π' A in
    (f ̂ Π' A) (λ s → tA s tup)
      ≡⟨ refl _ ⟩
    ∥ Π' A ∥ f (λ s →  tA s tup)
      ≡⟨ ap ( ∥ Π' A ∥ f ) (fe  λ x → IH x tup) ⟩
    ∥ Π' A ∥ f (λ s → (λ j → (t s ̇ A j)(λ ℓ → tup ℓ j)))
      ≡⟨ refl _ ⟩
    (λ i → (f ̂ A i)(λ s → (t s ̇ A i)(λ ℓ → tup ℓ i)))
      ∎

-- Proof of 1. (homomorphisms commute with terms).
comm-hom-term : global-dfunext --  𝓥 𝓤
 →               {X : 𝓧 ̇}(A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
 →               (h : hom A B) (t : Term{X = X}) (a : X → ∣ A ∣)
               --------------------------------------------
 →               ∣ h ∣ ((t ̇ A) a) ≡ (t ̇ B) (∣ h ∣ ∘ a)

comm-hom-term fe A B h (generator x) a = refl _

comm-hom-term fe A B h (node f args) a =
 ∣ h ∣ ((f ̂ A)  (λ i₁ → (args i₁ ̇ A) a))
   ≡⟨ ∥ h ∥ f ( λ r → (args r ̇ A) a ) ⟩
 (f ̂ B) (λ i₁ →  ∣ h ∣ ((args i₁ ̇ A) a))
   ≡⟨ ap (_ ̂ B)(fe (λ i₁ → comm-hom-term fe A B h (args i₁) a))⟩
 (f ̂ B) (λ r → (args r ̇ B) (∣ h ∣ ∘ a))
   ∎

-- Proof of 2. (If t : Term, θ : Con A, then a θ b → t(a) θ t(b))
compatible-term : {X : 𝓧 ̇}
           (A : Algebra 𝓤 S) (t : Term{X = X}) (θ : Con A)
           --------------------------------------------------
 →                   compatible-fun (t ̇ A) ∣ θ ∣

compatible-term A (generator x) θ p = p x

compatible-term A (node f args) θ p =
 pr₂( ∥ θ ∥ ) f λ{x → (compatible-term A (args x) θ) p}

-- Proof of 1. ("intensional" version)
comm-hom-term' : global-dfunext
 →              {X : 𝓧 ̇}(A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
                (h : HOM A B) (t : Term{X = X})
               ---------------------------------------------
 →              ∣ h ∣ ∘ (t ̇ A) ≡ (t ̇ B) ∘ (λ a → ∣ h ∣ ∘ a )

comm-hom-term' gfe A B h (generator x) = refl _

comm-hom-term' gfe {X = X}A B h (node f args) = γ
 where
  γ : ∣ h ∣ ∘ (λ a → (f ̂ A) (λ i → (args i ̇ A) a))
      ≡ (λ a → (f ̂ B)(λ i → (args i ̇ B) a)) ∘ _∘_ ∣ h ∣
  γ = ∣ h ∣ ∘ (λ a → (f ̂ A) (λ i → (args i ̇ A) a))
        ≡⟨ ap (λ - → (λ a → - f (λ i → (args i ̇ A) a))) ∥ h ∥ ⟩
      (λ a → (f ̂ B)(∣ h ∣ ∘ (λ i →  (args i ̇ A) a)))
        ≡⟨ refl _ ⟩
      (λ a → (f ̂ B)(λ i → ∣ h ∣ ((args i ̇ A) a)))
        ≡⟨ ap (λ - → (λ a → (f ̂ B)(- a))) ih ⟩
    (λ a → (f ̂ B)(λ i → (args i ̇ B) a)) ∘ _∘_ ∣ h ∣
        ∎
    where
     IH : (a : X → ∣ A ∣)(i : ∥ S ∥ f)
      →   (∣ h ∣ ∘ (args i ̇ A)) a ≡ ((args i ̇ B) ∘ _∘_ ∣ h ∣) a
     IH a i = intensionality (comm-hom-term' gfe A B h (args i)) a

     ih : (λ a → (λ i → ∣ h ∣ ((args i ̇ A) a)))
           ≡ (λ a → (λ i → ((args i ̇ B) ∘ _∘_ ∣ h ∣) a))
     ih = gfe λ a → gfe λ i → IH a i

compatible-term' : {X : 𝓧 ̇}(A : Algebra 𝓤 S)
                  ( t : Term{X = X} ) (θ : Con A)
                 ---------------------------------
 →                 compatible-fun (t ̇ A) ∣ θ ∣

compatible-term' A (generator x) θ p = p x
compatible-term' A (node f args) θ p =
 pr₂( ∥ θ ∥ ) f λ{x → (compatible-term' A (args x) θ) p}

-- Interpretation of terms in homomorphic images
-- (using subsingleton truncation)
-- module _
--  {𝓤 𝓥 : Universe}       -- {ua : Univalence}
--  (hfe : global-hfunext)
--  (gfe : global-dfunext)
--  (dfe : dfunext 𝓤 𝓤)
--  (pt  : subsingleton-truncations-exist)
--  (pe  : propext 𝓥)
--  (X : 𝓤 ̇ ) -- {X : 𝓧 ̇ }
--  (A B : Algebra 𝓤 S)
--  (ϕ : hom A B)
--  (wcem : wconstant-endomap ∣ A ∣)
--        -- (_≈_ : X → X → 𝓥 ̇ )
--        -- (≈p  : is-subsingleton-valued _≈_)
--        -- (≈r  : reflexive _≈_)
--        -- (≈s  : symmetric _≈_)
--        -- (≈t  : transitive _≈_)
--       where

--  open subsingleton-truncations-exist pt renaming (∥_∥ to ⌈_⌉; ∣_∣ to ⌞_⌟) public
--  open basic-truncation-development pt hfe renaming (∥_∥ to ⟦_⟧; ∣_∣ to ⟪_⟫) public
--  open exit-∥∥ pt hfe public

--  homimage : 𝓤 ̇
--  homimage = image ∣ ϕ ∣

--  ∥∥-elim : ⟦ ∣ A ∣ ⟧ → ∣ A ∣
--  ∥∥-elim = wconstant-endomap-gives-∥∥-choice-function wcem
--  -- wconstant-endomap-gives-∥∥-choice-function :
--  --  {X : 𝓤 ̇ } → wconstant-endomap X → (∥ X ∥ → X)
--  homimageAlgebra : Algebra 𝓤 S
--  homimageAlgebra = homimage , opsinterp
--   where
--    a' : {f : ∣ S ∣ }(x : ∥ S ∥ f → homimage)(y : ∥ S ∥ f) → -∃ ∣ A ∣ (λ x' → ∣ ϕ ∣ x' ≡ pr₁ (x y))
--    a' x y =
--     let ∣xy∣ = pr₁ (x y) in
--     let ∥xy∥ = pr₂ (x y) in ∥xy∥ -- ∥xy∥ -- restriction ∣ ϕ ∣ ( x y )

--    a : {f : ∣ S ∣ }(x : ∥ S ∥ f → homimage)(y : ∥ S ∥ f) → ∣ A ∣
--    -- a x y = Inv ∣ ϕ ∣  ∣ x y ∣ ∥ x y ∥
--    a x y =
--     let ∣xy∣ = pr₁ (x y) in 
--     let ∥xy∥ = pr₂ (x y) in {!pr₁ (∥∥-elim ∥xy∥)!} -- ∥xy∥ -- restriction ∣ ϕ ∣ ( x y )

--    opsinterp : (f : ∣ S ∣) → Op (∥ S ∥ f) homimage
--    opsinterp =
--     -- λ f x → (∣ ϕ ∣  (∥ A ∥ f (a x)) , im (∥ A ∥ f (a x)))
--     λ f x → (∣ ϕ ∣  (∥ A ∥ f (a x)) , ⟪ ( ∥ A ∥ f (a x) , refl (∣ ϕ ∣ _ )) ⟫ )

--  HIA : Algebra 𝓤 S
--  HIA = homimageAlgebra -- {A = A}{B = B} ϕ

--  preim : (b : X → Σ (Image_∋_ ∣ ϕ ∣))(x : X) → ∣ A ∣
--  preim = λ b x → (Inv ∣ ϕ ∣ (∣ b x ∣)(∥ b x ∥))

--  ζ : (b : X → Σ (Image_∋_ ∣ ϕ ∣))(x : X) → ∣ ϕ ∣ (preim b x) ≡ ∣ b x ∣
--  ζ b x = InvIsInv ∣ ϕ ∣ ∣ b x ∣ ∥ b x ∥

 -- hom-image-interp : (b : X → ∣ HIA ∣)(p : Term)
 --  → (p ̇ HIA ) b ≡ ( ∣ ϕ ∣ ((p ̇ A)(preim b)) , ∣ ((p ̇ A)(preim b)) , refl _ ∣ )

 -- hom-image-interp b (generator x) = to-subtype-≡ {!!} fstbx
 --  where
 --   fstbx : ∣ b x ∣ ≡ ∣ ϕ ∣ (preim b x)
 --   fstbx = ζ b x ⁻¹

 -- hom-image-interp b (node 𝓸 t) = ap (𝓸 ̂ HIA) (gfe φIH)
 --  where
 --   φIH : (x : ∥ S ∥ 𝓸)
 --    → (t x ̇ HIA) b  ≡ ∣ ϕ ∣ (( t x ̇ A )(preim b)) , im ((t x ̇ A)(preim b))
 --   φIH x = hom-image-interp b (t x)

