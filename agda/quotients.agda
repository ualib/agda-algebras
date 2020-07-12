{-# OPTIONS --without-K --exact-split --safe #-}

module quotients where

open import MGS-Unique-Existence        public
open import MGS-Subsingleton-Truncation public

--The value of the relation is in a universe 𝓥, where 𝓤 and 𝓥 are arbitrary.
--The function is-prop-valued and takes values in the lub of 𝓤 and 𝓥.

--We first give the type of five functions that we define below, where _≈_ is a variable:

is-subsingleton-valued
 reflexive
 symmetric
 transitive
 is-equivalence-relation : {X : 𝓤 ̇ }
  →                        (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

is-subsingleton-valued _≈_ = ∀ x y → is-subsingleton (x ≈ y)
-- This means if we have two proofs p, q : x ≈ y, then p ≡ q.

reflexive      _≈_ = ∀ x → x ≈ x
symmetric      _≈_ = ∀ x y → x ≈ y → y ≈ x
transitive     _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z
is-equivalence-relation _≈_ =
 is-subsingleton-valued _≈_ × reflexive _≈_ × symmetric _≈_ × transitive _≈_

FunExt : 𝓤ω
FunExt = (𝓤 𝓥 : Universe) → funext 𝓤 𝓥

module _
 {𝓤 𝓥 : Universe}

 -- Assume:
 (pt  : subsingleton-truncations-exist) -- truncations that stay in the same universe
 (fe  : FunExt)
 (gfe : global-dfunext)
 (hfe  : global-hfunext)
 (pe  : propext 𝓥)                      -- propositional truncation for the universe 𝓥
 (X   : 𝓤 ̇ )
 (_≈_ : X → X → 𝓥 ̇ )                   -- an equiv relation _≈_ with values in 𝓥 ̇.
 (≈p  : is-subsingleton-valued _≈_)
 (≈r  : reflexive _≈_)
 (≈s  : symmetric _≈_)
 (≈t  : transitive _≈_)
 where

 open basic-truncation-development pt hfe

 -- Ω 𝓥 is the type of subsingletons, or (univalent) propositions in 𝓥
 equiv-rel : X → (X → Ω 𝓥)
 equiv-rel x y = (x ≈ y) , ≈p x y

 -- From _≈_ : X → (X → 𝓥 ̇ ) define a relation X → (X → Ω 𝓥), formally a function.
 -- Then take the quotient X/≈ to be the image of this function.
 X/≈ : 𝓤 ⊔ (𝓥 ⁺) ̇
 X/≈ = image equiv-rel
 -- (It is for constructing the image that we need propositional truncations.)

 -- Recall,
 --   image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 --   image f = Σ y ꞉ codomain f , ∃ x ꞉ domain f , f x ≡ y
 -- so image equiv-rel = Σ g ꞉ (X → Ω 𝓥) , ∃ x ꞉ X , equiv-rel x ≡ g
 -- Given x : X, the function g : X → Ω 𝓥 is a predicate on X
 -- that represents the X/≈ equivalence class containing x.
 -- Here `≈p x y` says is-prop(x ≈ y). I think equiv-rel x y is not
 -- saying that x and y are in the same class, but rather it says
 -- what it means for x and y to be in the same class.
 -- And ≈p x y doesn't say that there is a proof of x ≈ y; it merely says,
 -- if there is a proof of x ≈ y, then it is unique.

 X/≈-is-set : is-set X/≈
 X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
              (powersets-are-sets hfe gfe pe)
              (λ _ → ∃-is-subsingleton) -- ∥∥-is-subsingleton -- ∥∥-is-prop
 -- Recall, is-set X = (x y : X) → is-subsingleton (x ≡ y)

 η : X → X/≈
 η = corestriction equiv-rel

 -- η is the universal solution to the problem of transforming the
 -- equivalence _≈_ into equality _≡_.

 -- By construction, η is a surjection.
 η-surjection : is-surjection η
 η-surjection = corestriction-surjection equiv-rel

 -- induction principle for reasoning about the image.
 η-induction : ∀ {𝓦} (P : X/≈ → 𝓦 ̇ )
  →            ((x' : X/≈) → is-subsingleton (P x'))
  →            ((x : X) → P(η x))
  →            (x' : X/≈) → P x'

 η-induction = surjection-induction η η-surjection
 -- Notice that the property we consider has values in any universe 𝓦.

 -- equivalent points are mapped to equal points:
 η-equiv-equal : {x y : X} → x ≈ y → η x ≡ η y
 η-equiv-equal {x} {y} e = to-Σ-≡ ( (fe 𝓤 (𝓥 ⁺))
  (λ z → to-Σ-≡ (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e) ,
    being-subsingleton-is-subsingleton gfe _ _)) , ∥∥-is-subsingleton _ _)

 -- η reflects equality into equivalence:
 η-equal-equiv : {x y : X} → η x ≡ η y → x ≈ y
 η-equal-equiv {x} {y} p = equiv-rel-reflect (ap pr₁ p)
  where
   equiv-rel-reflect : equiv-rel x ≡ equiv-rel y → x ≈ y
   equiv-rel-reflect q = b (≈r y)
    where
     a : (y ≈ y) ≡ (x ≈ y)
     a = ap (λ - → pr₁(- y)) (q ⁻¹)
     b : (y ≈ y) → (x ≈ y)
     b = Id→fun a

 -- The universal property of the quotient.
 -- Notice that we can eliminate into any set A of any universe 𝓦.
 --
 --      η
 -- X ------> X/≈
 --  \       .
 --   \     .
 --  f \   . f'
 --     \ .
 --      v
 --      A

 universal-property : ∀ {𝓦} (A : 𝓦 ̇ )
  →                   is-set A
  →                   (f : X → A)
  →                   ({x x' : X} → x ≈ x' → f x ≡ f x')
  →                   ∃! f' ꞉ (X/≈ → A) , f' ∘ η ≡ f

 universal-property {𝓦} A Aset f pr = ic
  where
   G : X/≈ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ̇
   G x' = Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x') × (f x ≡ a)

   φ : (x' : X/≈) → is-subsingleton (G x')
   φ = η-induction _ γ induction-step
    where
     induction-step : (y : X) → is-subsingleton (G (η y))
     induction-step x (a , d) (b , e) =
      to-Σ-≡ (p , ∥∥-is-subsingleton _ _)
       where
        h : (Σ x' ꞉ X , (η x' ≡ η x) × (f x' ≡ a))
         →  (Σ y' ꞉ X , (η y' ≡ η x) × (f y' ≡ b))
         →  a ≡ b

        h (x' , r , s) (y' , t , u) =
         s ⁻¹ ∙ pr (η-equal-equiv (r ∙ t ⁻¹)) ∙ u

        p : a ≡ b
        p = ∥∥-recursion (Aset a b) (λ σ → ∥∥-recursion (Aset a b) (h σ) e) d

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
     g : (y : X)
      → ∃ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y))

     g y = pr₂(k(η y))

     j : (y : X)
      →  (Σ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y)))
      →  f'(η y) ≡ f y

     j y (x , p , q) = q ⁻¹ ∙ pr (η-equal-equiv p)

     h : (y : X) → f'(η y) ≡ f y
     h y = ∥∥-recursion (Aset (f' (η y)) (f y)) (j y) (g y)

   c : (σ : Σ f'' ꞉ (X/≈ → A), f'' ∘ η ≡ f) → (f' , r) ≡ σ
   c (f'' , s) = to-subtype-≡ (λ g → Π-is-set hfe (λ _ → Aset) (g ∘ η) f) t
    where
     w : ∀ x → f'(η x) ≡ f''(η x)
     w = happly (f' ∘ η) (f'' ∘ η) (r ∙ s ⁻¹)

     t : f' ≡ f''
     t = hunapply (η-induction _ (λ x' → Aset (f' x') (f'' x')) w)

   ic : ∃! f' ꞉ (X/≈ → A), f' ∘ η ≡ f
   ic = (f' , r) , c
