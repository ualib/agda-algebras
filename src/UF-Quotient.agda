--FILE: UF-Quotient.agda
--DATE: 26 Apr 2020
--BLAME: williamdemeo@gmail.com
--REF: Based on Martin Escardo's course notes
--     cf.  https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#quotients
--          https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Quotient.html
--     In particular, comments appearing in quotes below, along with the code to which those comments refer, are due to Martin Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

{-"We now construct quotients using a technique proposed by Voevodsky, who assumed propositional resizing for that purpose, so that
   the quotient of a given type by a given equivalence relation would live in the same universe as the type. But the requirement that
   the quotient lives in the same universe is not needed to prove the universal property of the quotient.

   We construct the quotient using propositional truncations, assuming functional and propositional extensionality, *without assuming resizing*. -}

module UF-Quotient where

open import UF-Prelude using (Universe; 𝓤; 𝓥; 𝓦; _⁺; _̇;_⊔_; 𝓤ω; _∘_; _,_; Σ; -Σ; pr₁; pr₂; Π; -Π; domain; codomain; _×_; _+_; _≡_; refl; _∼_; _≡⟨_⟩_; _∎; ap; _⁻¹; _∙_)
open import UF-Singleton using (is-set; is-singleton; is-subsingleton; is-center)
open import UF-Univalence using (subsets-of-sets-are-sets; to-subtype-≡; Id→fun)
open import UF-Extensionality
  using (global-hfunext; propext; Ω; ∃!; -∃!; powersets-are-sets; dfunext-gives-hfunext; being-subsingleton-is-subsingleton; Π-is-set; happly)

open import UF-Truncation using (subsingleton-truncations-exist)

--"A binary relation `_≈_` on a type `X : 𝓤` with values in a universe `𝓥` (which can of course be `𝓤`) is called an *equivalence
-- relation* if it is subsingleton-valued, reflexive, symmetric and transitive. All these notions have the same type:
is-subsingleton-valued
 reflexive symmetric transitive
 is-equivalence-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
--"and are defined by:
is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)
reflexive                    _≈_ = ∀ x → x ≈ x
symmetric                  _≈_ = ∀ x y → x ≈ y → y ≈ x
transitive                   _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

is-equivalence-relation _≈_ = is-subsingleton-valued _≈_  × reflexive _≈_  × symmetric _≈_  × transitive _≈_

--"We now work with a submodule with parameters to quotient a given type `X` by a given equivalence relation `_≈_`.
-- We assume not only the existence of propositional truncations, but also functional and propositional extensionality. -}
module quotient
       {𝓤 𝓥 : Universe}
       (pt  : subsingleton-truncations-exist)
       (hfe : global-hfunext)
       (pe  : propext 𝓥)
       (X   : 𝓤 ̇ )
       (_≈_ : X → X → 𝓥 ̇ )
       (≈p  : is-subsingleton-valued _≈_)
       (≈r  : reflexive _≈_)
       (≈s  : symmetric _≈_)
       (≈t  : transitive _≈_)   where

  open UF-Truncation.basic-truncation-development pt hfe

  --"From the relation `_≈_ : X → X → 𝓥 ̇` we define a function `X → (X → Ω 𝓥)`, and we take the quotient `X/≈` to be
  -- the image of this function. It is for constructing the image that we need subsingleton truncations. Functional and propositional
  -- extensionality are then used to prove that the quotient is a set.
  equiv-rel : X → (X → Ω 𝓥)
  equiv-rel x y = (x ≈ y) , ≈p x y

  X/≈ : 𝓥 ⁺ ⊔ 𝓤 ̇
  X/≈ = image equiv-rel

  X/≈-is-set : is-set X/≈
  X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
                     (powersets-are-sets (dfunext-gives-hfunext hunapply) hunapply pe)
                      λ _ → ∃-is-subsingleton

  η : X → X/≈
  η = corestriction equiv-rel  --Recall, corestriction takes a function f : X → Y and restricts the codomain to be just the image of f,
                                      -- (which of course yields a surjective function).

  --"We show that `η` is the universal solution to the problem of transforming equivalence `_≈_` into equality `_≡_`.

  --"By construction, `η` is a surjection [as mentioned]:
  η-surjection : is-surjection η
  η-surjection = corestriction-surjection equiv-rel

  --"It is convenient to use the following induction principle for reasoning about the image `X/≈`.
  η-induction : (P : X/≈ → 𝓦 ̇ )
   →             ( ( x' : X/≈ ) → is-subsingleton (P x') )
   →             ( ( x : X ) → P (η x) )
   →             ( x' : X/≈ ) → P x'
  η-induction = surjection-induction η η-surjection

  --"The first part of the universal property of `η` says that equivalent points are mapped to identified points:
  η-equiv-equal : {x y : X} → x ≈ y → η x ≡ η y
  η-equiv-equal {x} {y} e = to-subtype-≡ (λ _ → ∃-is-subsingleton) γ
   where
    γ : equiv-rel x ≡ equiv-rel y
    γ = hunapply ζ
     where
      ζ : equiv-rel x ∼ equiv-rel y
      ζ z = to-subtype-≡ (λ _ → being-subsingleton-is-subsingleton hunapply)
                                  (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e))

  --"To prove the required universal property, we also need the fact that `η` reflects equality into equivalence:
  η-equal-equiv : {x y : X} → η x ≡ η y → x ≈ y
  η-equal-equiv {x} {y} p = equiv-rel-reflect (ap pr₁ p)
   where
    equiv-rel-reflect : equiv-rel x ≡ equiv-rel y → x ≈ y
    equiv-rel-reflect q = b (≈r y)
     where
      a : (y ≈ y) ≡ (x ≈ y)
      a = ap (λ - → pr₁ (- y) ) (q ⁻¹)
      b : y ≈ y → x ≈ y
      b = Id→fun a

  --"We are now ready to formulate and prove the required universal property of the quotient. What is noteworthy here,
  -- regarding universes, is that the universal property says that we can eliminate into any set `A` of any universe `𝓦`.
  universal-property : (A : 𝓦 ̇) → is-set A
   →                       (f : X → A) → ({x x' : X} → x ≈ x' → f x ≡ f x' )
   →                       ∃! f' ꞉ (X/≈ → A) , f' ∘ η ≡ f
  universal-property {𝓦} A Aset f τ = e
   where
    G : X/≈ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ̇
    G x' = Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x' ) × (f x ≡ a)

    φ : (x' : X/≈) → is-subsingleton (G x')
    φ = η-induction _ γ induction-step
     where
      induction-step : (y : X) → is-subsingleton (G (η y))
      induction-step x (a , d) (b , e) = to-subtype-≡ (λ _ → ∃-is-subsingleton) p
       where
        h : (Σ x' ꞉ X , (η x' ≡ η x) × (f x' ≡ a) ) → (Σ y' ꞉ X , (η y' ≡ η x) × (f y' ≡ b) ) → a ≡ b
        h ( x' , ηx'≡ηx , fx'≡a ) (y' , ηy'≡ηx , fy'≡b ) =
          a          ≡⟨ fx'≡a ⁻¹ ⟩
          f x'      ≡⟨ τ (η-equal-equiv (ηx'≡ηx ∙ ηy'≡ηx ⁻¹) ) ⟩
          f y'     ≡⟨ fy'≡b ⟩
          b     ∎
        p : a ≡ b
        p = ∥∥-recursion (Aset a b) (λ σ → ∥∥-recursion (Aset a b) (h σ) e ) d

      γ : (x' : X/≈) → is-subsingleton (is-subsingleton (G x'))
      γ x' = being-subsingleton-is-subsingleton hunapply

    k : (x' : X/≈) → G x'
    k = η-induction _ φ induction-step
     where
      induction-step : (y : X) → G (η y)
      induction-step x = f x , ∣ x , refl (η x) , refl (f x) ∣

    f' : X/≈ → A
    f' x' = pr₁ (k x')

    r : f' ∘ η ≡ f
    r = hunapply h
     where
      g :  (y : X) → ∃ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y) )
      g y = pr₂ (k (η y) )

      j : (y : X) → ( Σ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y) ) ) → f' (η y) ≡ f y
      j y (x , p , q) = f' (η y) ≡⟨ q ⁻¹ ⟩ f x ≡⟨ τ (η-equal-equiv p) ⟩ f y ∎

      h : (y : X) → f' (η y) ≡ f y -- f' ∘ η ∼ f
      h y = ∥∥-recursion (Aset (f' (η y) ) (f y) ) (j y) (g y)

    c : (σ : Σ f'' ꞉ (X/≈ → A) , f'' ∘ η ≡ f) → (f' , r) ≡ σ -- is-center (Σ (λ f'' → f'' ∘ η ≡ f)) (f' , r)
    c (f'' , s) = to-subtype-≡ (λ g → Π-is-set hfe (λ _ → Aset) (g ∘ η) f) t
     where
      w : (x : X) → f' (η x) ≡ f'' (η x)
      w = happly (f' ∘ η) (f'' ∘ η) (r ∙ s ⁻¹)
      t : f' ≡ f''
      t = hunapply (η-induction _ (λ x' → Aset (f' x') (f'' x') ) w)
    e : ∃! f' ꞉ (X/≈ → A) , f' ∘ η ≡ f
    e = (f' , r) , c

--"As mentioned above, if one so wishes, it is possible to resize down the quotient `X/≈` to the same universe as the given type
-- `X` lives by assuming propositional resizing. But we don't see any mathematical need or benefit to do so, as the constructed
-- quotient, regardless of the universe it inhabits, has a universal property that eliminates into any desired universe, lower, equal
-- or higher than the quotiented type."

