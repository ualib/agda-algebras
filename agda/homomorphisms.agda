-- File: homomorphisms.agda
-- Author: William DeMeo and Siva Somayyajula
-- Date: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences

module homomorphisms {𝑆 : Signature 𝓞 𝓥} where

open import prelude using (_∘_; _∈_; _⊆_; EpicInv; cong-app;
 EInvIsRInv; Image_∋_) public

--intensional preservation of operations
op_interpreted-in_and_commutes-intensionally-with :
 (f : ∣ 𝑆 ∣) (A : Algebra 𝓤 𝑆) (B : Algebra 𝓦 𝑆)
 (g : ∣ A ∣  → ∣ B ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

op f interpreted-in A and B commutes-intensionally-with g =
 (λ a → g (∥ A ∥ f a) ) ≡ (λ a → ∥ B ∥ f (g ∘ a) )

all-ops-in_and_commute-partially-intensionally-with :
 (A : Algebra 𝓤 𝑆)(B : Algebra 𝓦 𝑆)
 (g : ∣ A ∣  → ∣ B ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in A and B commute-partially-intensionally-with g =
 ∀ (f : ∣ 𝑆 ∣ )
  → op f interpreted-in A and B commutes-intensionally-with g

intensional-hom : (A : Algebra 𝓤 𝑆) (B : Algebra 𝓦 𝑆)
 →                (∣ A ∣ → ∣ B ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

intensional-hom A B g =
 all-ops-in A and B commute-partially-intensionally-with g

Hom : Algebra 𝓦 𝑆 → Algebra 𝓤 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

Hom A B = Σ g ꞉ (∣ A ∣ → ∣ B ∣) ,
   all-ops-in A and B commute-partially-intensionally-with g

-- intensional with respect to both f and a)
preserves-ops : (A : Algebra 𝓤 𝑆) (B : Algebra 𝓦 𝑆)
 →              (∣ A ∣  → ∣ B ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

preserves-ops (A , 𝐹ᴬ)(B , 𝐹ᴮ) g =
 (λ (f : ∣ 𝑆 ∣ ) (a : ∥ 𝑆 ∥ f → A) → g (𝐹ᴬ f a))
  ≡ (λ (f : ∣ 𝑆 ∣ ) (a : ∥ 𝑆 ∥ f → A )  → 𝐹ᴮ f (g ∘ a))

all-ops-in_and_commute-intensionally-with :
 (A : Algebra 𝓤 𝑆)(B : Algebra 𝓦 𝑆)
 (g : ∣ A ∣  → ∣ B ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in A and B commute-intensionally-with g =
 preserves-ops A B g

--the type of (intensional) homomorphisms
HOM : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

HOM A B = Σ g ꞉ (∣ A ∣ → ∣ B ∣) ,
           all-ops-in A and B commute-intensionally-with g

op_interpreted-in_and_commutes-extensionally-with :
   (f : ∣ 𝑆 ∣) (A : Algebra 𝓤 𝑆) (B : Algebra 𝓦 𝑆)
   (g : ∣ A ∣  → ∣ B ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

op f interpreted-in A and B commutes-extensionally-with g =
 ∀( a : ∥ 𝑆 ∥ f → ∣ A ∣ ) → g (∥ A ∥ f a) ≡ ∥ B ∥ f (g ∘ a)

all-ops-in_and_commute-extensionally-with :
     (A : Algebra 𝓤 𝑆) (B : Algebra 𝓦 𝑆)
 →   (∣ A ∣  → ∣ B ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in A and B commute-extensionally-with g = ∀ (f : ∣ 𝑆 ∣)
  → op f interpreted-in A and B commutes-extensionally-with g

is-homomorphism : (A : Algebra 𝓤 𝑆) (B : Algebra 𝓦 𝑆)
 →                (∣ A ∣ → ∣ B ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

is-homomorphism A B g =
 all-ops-in A and B commute-extensionally-with g

hom : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
hom A B = Σ g ꞉ (∣ A ∣ → ∣ B ∣ ) , is-homomorphism A B g

𝒾𝒹 :  (A : Algebra 𝓤 𝑆) → hom A A
𝒾𝒹 _ = (λ x → x) , λ _ _ → refl _ 

HCompClosed : {A : Algebra 𝓤 𝑆}
              {B : Algebra 𝓦 𝑆}
              {C : Algebra 𝓣 𝑆}
 →            hom A B   →   hom B C
             ------------------------
 →                   hom A C

HCompClosed {A = A , FA}{B = B , FB}{C = C , FC}
 (g , ghom) (h , hhom) = h ∘ g , γ
  where
   γ : ( f : ∣ 𝑆 ∣ ) ( a : ∥ 𝑆 ∥ f  →  A )
    →  ( h ∘ g ) ( FA f a ) ≡ FC f ( h ∘ g ∘ a )

   γ f a = (h ∘ g) (FA f a) ≡⟨ ap h ( ghom f a ) ⟩
          h (FB f (g ∘ a)) ≡⟨ hhom f ( g ∘ a ) ⟩
          FC f (h ∘ g ∘ a) ∎

--Alternative notation for hom composition
module _ {A : Algebra 𝓤 𝑆}
         {B : Algebra 𝓦 𝑆}
         {C : Algebra 𝓣 𝑆} where

  _>>>_ : hom A B  → hom B C → hom A C

  (g , ghom) >>> (h , hhom) = h ∘ g , γ
    where
      γ :      (f : ∣ 𝑆 ∣ ) → (a : ∥ 𝑆 ∥ f → ∣ A ∣)
           -------------------------------------------
       →    (h ∘ g) (∥ A ∥ f a)  ≡  ∥ C ∥ f (h ∘ g ∘ a)

      γ f a =
       (h ∘ g) (∥ A ∥ f a) ≡⟨ ap (λ - → h -) (ghom f a) ⟩
       h (∥ B ∥ f (g ∘ a)) ≡⟨ hhom f (g ∘ a) ⟩
       ∥ C ∥ f (h ∘ g ∘ a) ∎

homFactor : funext 𝓤 𝓤 → {A B C : Algebra 𝓤 𝑆}
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

   ζ : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)(x : ∥ 𝑆 ∥ f)
    →  c x ≡ (h ∘ hInv)(c x)

   ζ f c x = (cong-app (EInvIsRInv fe h hEpic) (c x))⁻¹

   ι : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)
    →  (λ x → c x) ≡ (λ x → h (hInv (c x)))

   ι f c = ap (λ - → - ∘ c)(EInvIsRInv fe h hEpic)⁻¹

   useker : (f : ∣ 𝑆 ∣)  (c : ∥ 𝑆 ∥ f → C)
    → g (hInv (h (FA f (hInv ∘ c)))) ≡ g(FA f (hInv ∘ c))

   useker = λ f c
    → Kh⊆Kg (cong-app
             (EInvIsRInv fe h hEpic)
             (h(FA f(hInv ∘ c)))
            )

   ϕIsHomCB : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → C)
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


--Isomorphism
--For algebras, isomorphisms are simply homs with 0 kernel.

-- module _ {𝓤 : Universe} where

_≅_ : (𝑨 𝑩 : Algebra 𝓤 𝑆) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
𝑨 ≅ 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) ,
            (∣ f ∣ ∘ ∣ g ∣ ≡ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≡ ∣ 𝒾𝒹 𝑨 ∣)

-- is-algebra-iso : {𝑨 𝑩 : Algebra 𝓤 𝑆} (f : hom 𝑨 𝑩) → 𝓤 ⁺ ̇
-- is-algebra-iso {𝑨} f = ker ∣ f ∣ ≡ 𝟎 {A = ∣ 𝑨 ∣}

-- AlgebraIsos : (𝑨 𝑩 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
-- AlgebraIsos 𝑨 𝑩 = Σ f ꞉ (hom 𝑨 𝑩) , is-algebra-iso {𝑨}{𝑩} f

-- _≈_ : Rel (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
-- 𝑨 ≈ 𝑩 = is-singleton (AlgebraIsos 𝑨 𝑩)


-- The following seems to be the most useful definition (for our
-- purposes) of the class of homomomrphic images of an algebra.
HomImage : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓤 𝑆)(ϕ : hom 𝑨 𝑩) → ∣ 𝑩 ∣ → 𝓤 ̇
HomImage 𝑩 ϕ = λ b → Image ∣ ϕ ∣ ∋ b

HomImagesOf : {𝓤 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
HomImagesOf {𝓤} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
                                 is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

_is-hom-image-of_ : (𝑩 : Algebra 𝓤 𝑆)
  →                (𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

𝑩 is-hom-image-of 𝑨 = Σ 𝑪ϕ ꞉ (HomImagesOf 𝑨) , 𝑩 ≅ ∣ 𝑪ϕ ∣

_is-hom-image-of-class_ : {𝓤 : Universe}
  →                       Algebra 𝓤 𝑆
  →                       Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)
  →                       𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

_is-hom-image-of-class_ {𝓤} 𝑩 𝓚 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) ,
                             (𝑨 ∈ 𝓚) × (𝑩 is-hom-image-of 𝑨)

HomImagesOfClass : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ 𝑆) ,
                     (𝑩 is-hom-image-of-class 𝓚)

H : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
H 𝓚 = HomImagesOfClass 𝓚

-- Here 𝓛𝓚 represents a (universe-indexed) collection of classes.
H-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺))
 →         (𝓤 : Universe) → Algebra 𝓤 𝑆
 →          𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

H-closed 𝓛𝓚 = λ 𝓤 𝑩 → _is-hom-image-of-class_ {𝓤 = 𝓤} 𝑩 (𝓛𝓚 𝓤) → 𝑩 ∈ (𝓛𝓚 𝓤)

--  homimage : 𝓤 ̇
--  homimage = image ∣ ϕ ∣

--  ∥∥-elim : ⟦ ∣ A ∣ ⟧ → ∣ A ∣
--  ∥∥-elim = wconstant-endomap-gives-∥∥-choice-function wcem
--  -- wconstant-endomap-gives-∥∥-choice-function :
--  --  {X : 𝓤 ̇ } → wconstant-endomap X → (∥ X ∥ → X)
--  homimageAlgebra : Algebra 𝓤 𝑆
--  homimageAlgebra = homimage , opsinterp
--   where
--    a' : {f : ∣ 𝑆 ∣ }(x : ∥ 𝑆 ∥ f → homimage)(y : ∥ 𝑆 ∥ f) → -∃ ∣ A ∣ (λ x' → ∣ ϕ ∣ x' ≡ pr₁ (x y))
--    a' x y =
--     let ∣xy∣ = pr₁ (x y) in
--     let ∥xy∥ = pr₂ (x y) in ∥xy∥ -- ∥xy∥ -- restriction ∣ ϕ ∣ ( x y )

--    a : {f : ∣ 𝑆 ∣ }(x : ∥ 𝑆 ∥ f → homimage)(y : ∥ 𝑆 ∥ f) → ∣ A ∣
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

-----------------------------------------------------------------------------------

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

--    hom-closed : (𝓚 : Pred (Algebra (𝓤 ⁺) S) l)
--     →           Pred (Algebra 𝓤 S) _
--     hom-closed 𝓚 = λ A → (𝓚 (A / (∥𝟎∥ A)))
--       →             (∃ θ : Congruence A)
--       →             (∃ 𝑪 : Algebra (𝓤 ⁺) S)
--       →             (𝓚 𝑪) × ((A / θ) ≅ 𝑪)

-- To get this to type check, we have an apparent problem, and we need a trick to resolve it. The class 𝓚 is a collection of algebras whose universes live at some level. (Above we use `𝓤 ⁺`.)

-- However, if `A` is an algebra with `∣ A ∣ : 𝓤 ̇`, then the quotient structure  (as it is now defined in Con.agda), has type `A / θ : 𝓤 ⁺ ̇`. So, in order for the class `𝓚` to contain both `A` and all its quotients `A / θ` (i.e. all its homomorphic images), we need to somehow define a class of algebras that have different universe levels.

-- Can we define a data type with such "universe level polymorphism"?

-- Without that, we use a trick to get around the problem. Instead of assuming that `A` itself belongs to `𝓚`, we could instead take the "quotient" `A / ∥𝟎∥` (which is isomorphic to `A`) as belonging to `𝓚`.

-- This is a hack and, worse, it won't do for us. We need something inductive because we will also need that if `𝑪 ≅ A / θ ∈ 𝓚`, then also `𝑪 / ψ ≅ (A / θ) / ψ ∈ 𝓚`.

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
--     hom-closed 𝓚 = ∀ A -> (algebras 𝓚) A -- (𝓚 (A / (⟦𝟎⟧ A)))
--      -> ∀ (θ : Congruence A) -> (∃ 𝑪 : Algebra lsuc ℓ S)
--           ------------------------------
--      ->     (𝓚 𝑪) × ((A / θ) ≅ 𝑪)


--    module _  {S : Signature 𝓞 𝓥}  where
--     open AlgebraClass

--     data HomClo {ℓ : Level} (𝓚 : AlgebraClass) : Pred AlgebraClass _ where
--      hombase : {A : Algebra ℓ S} → A ∈ (algebras 𝓚) ℓ  → A ∈ HomClo 𝓚
--      homstep : {A : Algebra ℓ S} ->  A ∈ HomClo 𝓚
--        ->     (∃ θ : Congruence A)
--        ->     (𝑪 : Algebra (lsuc ℓ) S)
--              ------------------------------
--        ->     𝑪 ∈ (algebras (lsuc ℓ) 𝓚) × ((A / θ) ≅ 𝑪)




-- ------------------
