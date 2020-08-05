--FILE: free.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 4 Aug 2020
--UPDATE: 4 Aug 2020
--REF: The quotient construction is based on Martin Escardo's quotient module
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#quotients
--      and https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Quotient.html
--     MHE explains the quotient construction as follows:
{-
  "We now construct quotients using a technique proposed by Voevodsky, who assumed propositional
  resizing for that purpose, so that the quotient of a given type by a given equivalence relation
  would live in the same universe as the type. But the requirement that the quotient lives in the
  same universe is not needed to prove the universal property of the quotient.

  We construct the quotient using propositional truncations, assuming functional and propositional
  extensionality, *without assuming resizing*."
-}

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (subsets-of-sets-are-sets; Ω; propext; global-dfunext; ∃!; -∃!;
 dfunext-gives-hfunext; powersets-are-sets; global-hfunext; dfunext; _∼_; Id→fun; happly;
 subsingleton-truncations-exist; to-subtype-≡; being-subsingleton-is-subsingleton;
 Π-is-set)

module free
 {𝑆 : Signature 𝓞 𝓥}
 {𝓤 : Universe}
 {X : 𝓤 ̇ }
 {𝕏 : {𝓤 : Universe}(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤} where

open import homomorphisms {𝑆 = 𝑆} public

open import subuniverses
 {𝑆 = 𝑆}
 {X = X}
 {𝕏 = 𝕏}
 {fe = gfe}

open import terms
 {𝑆 = 𝑆}
 {𝓤 = 𝓤}
 {X = X}
 {𝕏 = 𝕏}
 {gfe = gfe} renaming (generator to ℊ) public

{-
  "We now work with a submodule with parameters to quotient a given type `X` by a given
  equivalence relation `_≈_`. We assume not only the existence of propositional truncations,
  as discussed above, but also functional and propositional extensionality."
-}

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


 -- open prelude.basic-truncation-development pt hfe using (image; hunapply; ∃-is-subsingleton; corestriction; is-surjection; corestriction-surjection; surjection-induction; ∃; -∃; ∥∥-recursion) renaming (∥_∥ to ⟪_⟫; ∣_∣ to ⌞_⌟) public

 open prelude.basic-truncation-development pt hfe renaming (∥_∥ to ⟪_⟫; ∣_∣ to ⌞_⌟) public

 {-
   "From the given relation `_≈_ : X → X → 𝓥 ̇` we define a function `X → (X → Ω 𝓥)`, and we
   take the quotient `X/≈` to be the image of this function. It is for constructing the image
   that we need subsingleton truncations. Functional and propositional extensionality are then
   used to prove that the quotient is a set."
 -}

 equiv-rel : X → (X → Ω 𝓥)
 equiv-rel x y = (x ≈ y) , ≈p x y

 X/≈ : 𝓥 ⁺ ⊔ 𝓤 ̇
 X/≈ = image equiv-rel

 X/≈-is-set : is-set X/≈
 X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
                (powersets-are-sets (dfunext-gives-hfunext hunapply) hunapply pe)
                      λ _ → ∃-is-subsingleton

 η : X → X/≈
 η = corestriction equiv-rel
 --corestriction takes a function f : X → Y and restricts the codomain to be the image of f

{-
  "We show that `η` is the universal solution to the problem of transforming equivalence `_≈_`
  into equality `_≡_`."
-}

 η-surjection : is-surjection η
 η-surjection = corestriction-surjection equiv-rel

{-
  "It is convenient to use the following induction principle for reasoning about the image `X/≈`."
-}
 η-induction : (P : X/≈ → 𝓦 ̇)
  →            (( x' : X/≈) → is-subsingleton (P x'))
  →            (( x : X) → P (η x))
  →            (x' : X/≈ ) → P x'
 η-induction = surjection-induction η η-surjection

{-
  "The first part of the universal property of `η` says that equivalent points are mapped to identified points:"
-}
 η-equiv-equal : {x y : X} → x ≈ y → η x ≡ η y
 η-equiv-equal {x} {y} e = to-subtype-≡ (λ _ → ∃-is-subsingleton) γ
  where
   γ : equiv-rel x ≡ equiv-rel y
   γ = hunapply ζ
    where
     ζ : equiv-rel x ∼ equiv-rel y
     ζ z = to-subtype-≡ (λ _ → being-subsingleton-is-subsingleton hunapply)
                        (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e))

{-
  "To prove the required universal property, we also need the fact that `η` reflects equality into equivalence:
-}
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

{-
  "We are now ready to formulate and prove the required universal property of the quotient.
  What is noteworthy here, regarding universes, is that the universal property says that we
  can eliminate into any set `A` of any universe `𝓦`.
-}
 universal-property : (A : 𝓦 ̇)
  →                   is-set A
  →                   (f : X → A)
  →                   ({x x' : X} → x ≈ x' → f x ≡ f x' )
  →                   ∃! f' ꞉ (X/≈ → A) , (f' ∘ η ≡ f)
 universal-property {𝓦} A Aset f τ = e
  where
   G : X/≈ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ̇
   G x' = Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x' ) × (f x ≡ a)

   φ : (x' : X/≈) → is-subsingleton (G x')
   φ = η-induction _ γ induction-step
    where
     induction-step : (y : X) → is-subsingleton (G (η y))
     induction-step x (a , d) (b , e) =
             to-subtype-≡ (λ _ → ∃-is-subsingleton) p
      where
       h : (Σ x' ꞉ X , (η x' ≡ η x) × (f x' ≡ a))
        →  (Σ y' ꞉ X , (η y' ≡ η x) × (f y' ≡ b))
        →  a ≡ b

       h (x' , ηx'≡ηx , fx'≡a)(y' , ηy'≡ηx , fy'≡b) =
         a    ≡⟨ fx'≡a ⁻¹ ⟩
         f x' ≡⟨ τ(η-equal-equiv (ηx'≡ηx ∙ ηy'≡ηx ⁻¹)) ⟩
         f y' ≡⟨ fy'≡b ⟩
         b    ∎

       p : a ≡ b
       p = ∥∥-recursion (Aset a b) (λ σ → ∥∥-recursion (Aset a b) (h σ) e ) d

     γ : (x' : X/≈) → is-subsingleton (is-subsingleton (G x'))
     γ x' = being-subsingleton-is-subsingleton hunapply

   k : (x' : X/≈) → G x'
   k = η-induction _ φ induction-step
    where
     induction-step : (y : X) → G (η y)
     induction-step x = f x , ⌞ x , refl (η x) , refl (f x) ⌟

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

----------------------------------------------------------------------------
_⊧_≈_ : {𝓦 : Universe} → Algebra 𝓦 𝑆
 →      Term → Term → 𝓤 ⊔ 𝓦 ̇

𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : {𝓦 𝓣 : Universe} → Pred (Algebra 𝓦 𝑆) 𝓣
 →      Term → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ⁺ ̇

_⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

OVU+ : Universe
OVU+ = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺

OVU++ : Universe
OVU++ = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺

module prod-closure {𝔓 : Universe} where

 𝔓+ : Universe   -- notation: \MfP yields 𝔓
 𝔓+ = OVU+ ⊔ 𝔓

 𝔓++ : Universe
 𝔓++ = OVU++ ⊔ 𝔓 ⁺

 ----------------------------------------------------------------------
 --Closure under products
 data PClo (𝒦 : Pred (Algebra 𝔓+ 𝑆)(𝔓+ ⁺)) : Pred (Algebra 𝔓+ 𝑆) (𝔓++ ⁺) where
  pbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo 𝒦
  prod : {I : 𝔓 ̇ }{𝒜 : I → Algebra _ 𝑆}
   →     (∀ i → 𝒜 i ∈ PClo 𝒦)
   →     ⨅ 𝒜 ∈ PClo 𝒦

 P-closed : (ℒ𝒦 : (𝓣 : Universe) → Pred (Algebra 𝓣 𝑆) (𝓣 ⁺ ))
  →      (𝓘 : Universe)(I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓘 𝑆)
  →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓘 ) → 𝓘 ⁺ ̇
 P-closed ℒ𝒦 = λ 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  ⨅ 𝒜  ∈ (ℒ𝒦 𝓘)

module sub-closure {𝔖 : Universe} where

 𝔖+ : Universe   -- notation: \MfS yields 𝔖
 𝔖+ = OVU+ ⊔ 𝔖

 𝔖++ : Universe
 𝔖++ = OVU++ ⊔ 𝔖 ⁺

 ----------------------------------------------------------------------
 --Closure under subalgebras
 data SClo (𝒦 : Pred (Algebra 𝔖 𝑆)(𝔖 ⁺)) : Pred (Algebra 𝔖 𝑆) (𝔖+ ⁺) where
  sbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo 𝒦
  sub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ SClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ SClo 𝒦

 S-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺))
  →      (𝓤 : Universe) → (𝑩 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 S-closed ℒ𝒦 =
  λ 𝓤 B → (B is-subalgebra-of-class (ℒ𝒦 𝓤)) → (B ∈ ℒ𝒦 𝓤)


module hom-closure {ℌ : Universe} where

 ℌ+ : Universe    -- notation: \MfH yields ℌ
 ℌ+ = OVU+ ⊔ ℌ

 ℌ++ : Universe
 ℌ++ = OVU++ ⊔ ℌ ⁺

 ----------------------------------------------------------------------
 --Closure under hom images
 data HClo (𝒦 : Pred (Algebra ℌ+ 𝑆)(ℌ+ ⁺)) : Pred (Algebra ℌ+ 𝑆) (ℌ++ ⁺) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo 𝒦
  hhom : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ HClo 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo 𝒦


module var-closure {𝔙 : Universe} where

 𝔙+ : Universe    -- notation: \MfV yields 𝔙
 𝔙+ = OVU+ ⊔ 𝔙

 𝔙++ : Universe
 𝔙++ = OVU++ ⊔ 𝔙 ⁺

 data VClo (𝒦 : Pred (Algebra 𝔙+ 𝑆) 𝔙+) : Pred (Algebra 𝔙+ 𝑆) (𝔙+ ⁺) where
  vbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo 𝒦
  vprod : {I : 𝔙 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ VClo 𝒦) → ⨅ 𝒜 ∈ VClo 𝒦
  vsub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ VClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ VClo 𝒦
  vhom : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦

------------------------------------------------------------------------
-- Equational theories and classes
TH : Pred (Algebra 𝓤 𝑆) OVU++ → _ ̇
TH 𝒦 = Σ (p , q) ꞉ (Term × Term) , 𝒦 ⊧ p ≋ q

Th : {𝓦 𝓣 : Universe} → Pred (Algebra 𝓦 𝑆) 𝓣 → Pred (Term × Term) _
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

MOD : (ℰ : Pred (Term × Term) 𝓤) → OVU+ ̇
MOD ℰ = Σ A ꞉ (Algebra 𝓤 𝑆) , ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

Mod : Pred (Term × Term) OVU++ → Pred (Algebra 𝓤 𝑆) OVU++
Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

module relatively_free_algebra
 {𝔓 : Universe}
 {𝒦𝔓+ : Pred (Algebra (𝔓 ⁺) 𝑆) (𝔓 ⁺ ⁺)}
 {𝒦3 : Pred (Algebra ((OVU+ ⊔ 𝔓)) 𝑆) ((OVU+ ⊔ 𝔓))}
 {𝒦4 : Pred (Algebra ((OVU+ ⊔ 𝔓 ⁺) ⁺ ⁺) 𝑆) ((OVU+ ⊔ 𝔓 ⁺) ⁺ ⁺)}
 {𝒦5 : Pred (Algebra ((OVU+ ⊔ 𝔓 ⁺ ⁺) ⁺) 𝑆) ((OVU+ ⊔ 𝔓 ⁺ ⁺) ⁺ ⁺)}
 (pt  : subsingleton-truncations-exist)
 (hfe : global-hfunext)
 (pe  : propext (OVU+ ⁺ ⊔ 𝔓 ⁺ ⁺)) where

 𝔖 ℌ 𝔙 𝔉 : Universe
 𝔖 = 𝔓 ⁺
 ℌ = 𝔖 ⁺
 𝔙 = ℌ ⁺

 𝔉⁻⁻ = (OVU+ ⁺ ⊔ ℌ)
 𝔉⁻ = (OVU+ ⁺ ⊔ 𝔙)
 𝔉 = (OVU+ ⁺ ⁺ ⊔ 𝔙)

 open prod-closure {𝔓 = 𝔓}
 open sub-closure {𝔖 = 𝔖}
 open hom-closure {ℌ = ℌ}
 open var-closure {𝔙 = 𝔉}

 -- ==========================================================
 -- The free algebra in Agda
 -- ------------------------
 𝑻HI = HomImagesOf 𝑻

 𝑻img : _ ̇
 𝑻img = Σ 𝑨 ꞉ (Algebra 𝔖 𝑆) ,
           Σ ϕ ꞉ hom 𝑻 𝑨 , (𝑨 ∈ SClo 𝒦𝔓+) × Epic ∣ ϕ ∣

 𝑻𝑨 : (ti : 𝑻img) → Algebra _ 𝑆
 𝑻𝑨 ti = ∣ ti ∣

 𝑻𝑨∈SClo : (ti : 𝑻img) → (𝑻𝑨 ti) ∈ SClo 𝒦𝔓+
 𝑻𝑨∈SClo ti = ∣ pr₂ ∥ ti ∥ ∣

 𝑻ϕ : (ti : 𝑻img) → hom 𝑻 (𝑻𝑨 ti)
 𝑻ϕ ti = pr₁ ∥ ti ∥

 𝑻ϕE : (ti : 𝑻img) → Epic ∣ (𝑻ϕ ti) ∣
 𝑻ϕE ti = ∥ pr₂ ∥ ti ∥ ∥

 𝑻KER : _ ̇
 𝑻KER = Σ (p , q) ꞉ (∣ 𝑻 ∣ × ∣ 𝑻 ∣) ,
    ∀ ti → (p , q) ∈ KER-pred{B = ∣ (𝑻𝑨 ti) ∣} ∣ 𝑻ϕ ti ∣

 ΨPred : Pred (∣ 𝑻 ∣ × ∣ 𝑻 ∣) _
 ΨPred (p , q) =
  ∀ (ti : 𝑻img) → ∣ (𝑻ϕ ti) ∣ ∘ (p ̇ 𝑻) ≡ ∣ (𝑻ϕ ti) ∣ ∘ (q ̇ 𝑻)

 Θ : (OVU+ ⊔ 𝔓 ⁺) ⁺ ̇
 Θ = Σ tt ꞉ (∣ 𝑻 ∣ × ∣ 𝑻 ∣) ,
     ∀(ti : 𝑻img) → ∣ (𝑻ϕ ti) ∣ ∘ ((fst tt) ̇ 𝑻) ≡ ∣ (𝑻ϕ ti) ∣ ∘ ((snd tt) ̇ 𝑻)

 ΨPred-Θ-agreement : ∀(tt : Θ) → ΨPred (fst tt)
 ΨPred-Θ-agreement tt = snd tt

 ΨPred-Θ-agreement' : ∀(tt : ∣ 𝑻 ∣ × ∣ 𝑻 ∣) → ΨPred tt → Θ
 ΨPred-Θ-agreement' tt Ψtt = tt , Ψtt


 open prelude.basic-truncation-development pt hfe renaming (∥_∥ to ⟪_⟫; ∣_∣ to ⌞_⌟) public

 _≈_ : ∣ 𝑻 ∣ → ∣ 𝑻 ∣ → ((OVU+ ⊔ 𝔓 ⁺) ⁺) ̇
 p ≈ q = ∀ (ti : 𝑻img) → ∣ (𝑻ϕ ti) ∣ ∘ (p ̇ 𝑻) ≡ ∣ (𝑻ϕ ti) ∣ ∘ (q ̇ 𝑻)

 ≈p : is-subsingleton-valued _≈_
 ≈p = λ t₁ t₂ prf₁ prf₂ → {!!}

 Ψ : ∣ 𝑻 ∣ → (∣ 𝑻 ∣ → Ω ((OVU+ ⊔ 𝔓 ⁺) ⁺))
 Ψ p q = (p ≈ q) , ≈p p q

 -- This is the version we work with:
 -- Ψ : Rel ∣ 𝑻 ∣ (OVU+ ⊔ 𝔓 ⁺) ⁺
 -- Ψ p q = ∀ (ti : 𝑻img) → ∣ (𝑻ϕ ti) ∣ ∘ (p ̇ 𝑻) ≡ ∣ (𝑻ϕ ti) ∣ ∘ (q ̇ 𝑻)

 𝑻/Ψ : ((OVU+ ⊔ 𝔓 ⁺) ⁺) ⁺ ̇
 𝑻/Ψ = image Ψ

 -- Ψ-is-subsingleton-valued : is-subsingleton-valued Ψ
 -- Ψ-is-subsingleton-valued = λ t₁ t₂ prf₁ prf₂ → {!!}

 Ψ-is-rfl : reflexive _≈_
 Ψ-is-rfl = λ p ti → 𝓇ℯ𝒻𝓁

 Ψ-is-sym : symmetric _≈_
 Ψ-is-sym = λ p q p≡q ti → (p≡q ti)⁻¹

 Ψ-is-trans : transitive _≈_
 Ψ-is-trans = λ p q r p≡q q≡r ti → (p≡q ti) ∙ (q≡r ti)

 Ψ-IsEquivalence : IsEquivalence{𝓤 = 𝓞 ⊔ 𝓥 ⊔ 𝓤}{A = ∣ 𝑻 ∣} _≈_
 Ψ-IsEquivalence =
  record { rfl = Ψ-is-rfl ; sym = Ψ-is-sym ; trans = Ψ-is-trans }

 open quotient
  {𝓤 = 𝓞 ⊔ 𝓥 ⊔ 𝓤} {𝓥 = (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ⁺ ⊔ 𝔓 ⁺ ⁺}
  pt
  hfe
  pe
  ∣ 𝑻 ∣
  _≈_
  ≈p -- Ψ-is-subsingleton-valued
  Ψ-is-rfl
  Ψ-is-sym
  Ψ-is-trans

 𝑻compatible-op : ∣ 𝑆 ∣ → Rel ∣ 𝑻 ∣ ((OVU+ ⊔ 𝔓 ⁺) ⁺) → _ ̇
 𝑻compatible-op f R = (lift-rel R) =[ (f ̂ 𝑻) ]⇒ R

 𝑻compatible : Rel ∣ 𝑻 ∣ ((OVU+ ⊔ 𝔓 ⁺) ⁺) → _ ̇
 𝑻compatible R = ∀ f → 𝑻compatible-op f R

 record 𝑻Congruence : ((OVU+ ⊔ 𝔓 ⁺) ⁺) ⁺ ̇  where
  constructor mk𝑻con
  field
   ⟨_⟩ : Rel ∣ 𝑻 ∣ ((OVU+ ⊔ 𝔓 ⁺) ⁺)
   Compatible : 𝑻compatible ⟨_⟩
   IsEquiv : IsEquivalence ⟨_⟩
   IsSSValued : ∀ x y → is-subsingleton (⟨_⟩ x y)
 open 𝑻Congruence

 Ψ-𝑻compatible : 𝑻compatible _≈_
 Ψ-𝑻compatible f {𝒕}{𝒔} 𝒕𝒔∈Ψ ti = gfe λ x → γ x
  where
   𝑨 : Algebra 𝔖 𝑆
   𝑨 = 𝑻𝑨 ti

   ϕ : hom 𝑻 𝑨
   ϕ = 𝑻ϕ ti

   𝒕s 𝒔s : (i : ∥ 𝑆 ∥ f) → (X → ∣ 𝑻 ∣) → ∣ 𝑻 ∣
   𝒕s i = 𝒕 i ̇ 𝑻
   𝒔s i = 𝒔 i ̇ 𝑻

   𝒕≡𝒔 : (i : ∥ 𝑆 ∥ f) → ∣ ϕ ∣ ∘ (𝒕s i) ≡ ∣ ϕ ∣ ∘ (𝒔s i)
   𝒕≡𝒔 i = 𝒕𝒔∈Ψ i ti

   γ : ∀ x
    →  ∣ ϕ ∣((f ̂ 𝑻) (λ i → (𝒕 i ̇ 𝑻) x))
         ≡ ∣ ϕ ∣ ((f ̂ 𝑻)(λ i → (𝒔 i ̇ 𝑻) x))
   γ x =
    ∣ ϕ ∣ ((f ̂ 𝑻) (λ i → 𝒕s i x)) ≡⟨ ∥ ϕ ∥ f (λ i → 𝒕s i x) ⟩
    ((f ̂ 𝑨) (λ i → ∣ ϕ ∣ (𝒕s i x))) ≡⟨  ap (f ̂ 𝑨) (gfe λ i → intensionality (𝒕≡𝒔 i) x) ⟩
    ((f ̂ 𝑨) (λ i → ∣ ϕ ∣ (𝒔s i x))) ≡⟨  (∥ ϕ ∥ f (λ i → 𝒔s i x))⁻¹ ⟩
    ∣ ϕ ∣ ((f ̂ 𝑻) (λ i → (𝒔s i x))) ∎

 ConΨ : 𝑻Congruence
 ConΨ = mk𝑻con _≈_ Ψ-𝑻compatible Ψ-IsEquivalence ≈p -- Ψ-is-subsingleton-valued

 𝔽 : Algebra 𝔉 𝑆
 𝔽 = (
        -- carrier
        (  ∣ 𝑻 ∣ // ⟨ ConΨ ⟩  ) ,

        -- operations
        (  λ f args
            → ([ (f ̂ 𝑻) (λ i₁ → fst ∥ args i₁ ∥) ] ⟨ ConΨ ⟩) ,
                ((f ̂ 𝑻) (λ i₁ → fst ∥ args i₁ ∥) , 𝓇ℯ𝒻𝓁 )   )
      )


 --(N.B. the following did not require truncation.)
 𝔽-is-universal-for : (𝑨 : Algebra 𝓤 𝑆) → hom 𝔽 𝑨
 𝔽-is-universal-for 𝑨 = ϕ , ϕhom
  where
   h₀ : X → ∣ 𝑨 ∣
   h₀ = fst (𝕏 𝑨)

   hE : Epic h₀
   hE = snd (𝕏 𝑨)

   h : hom 𝑻 𝑨
   h = lift-hom{𝑨 = 𝑨} h₀
   -- Recall, _//_ :  (A : 𝓤 ̇ ) → Rel A 𝓡 → (𝓤 ⊔ 𝓡) ⁺ ̇
   --         A // ≈ = Σ C ꞉ _ ,  Σ a ꞉ A ,  C ≡ ( [ a ] ≈ )
   -- so if [a] : ∣ 𝑻 ∣ // ⟨ ConΨ ⟩, then fst ∥ [a] ∥ is a
   -- representative of the ConΨ-class [a].

   ϕ : ∣ 𝑻 ∣ // ⟨ ConΨ ⟩ → ∣ 𝑨 ∣
   ϕ = λ [a] → ∣ h ∣ (fst ∥ [a] ∥)

   ϕhom : is-homomorphism 𝔽 𝑨 ϕ
   ϕhom f a = γ
    where
     γ : ϕ ((f ̂ 𝔽) a) ≡ (f ̂ 𝑨) (λ x → ϕ (a x))
     γ = ϕ ((f ̂ 𝔽) a) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         ϕ (([ (f ̂ 𝑻) (λ i → fst ∥ a i ∥) ] ⟨ ConΨ ⟩) ,
           ((f ̂ 𝑻) (λ i → fst ∥ a i ∥) , refl _ ))
                        ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         ∣ h ∣ ((f ̂ 𝑻) (λ i → fst ∥ a i ∥))
                        ≡⟨ ∥ h ∥ f ((λ i → fst ∥ a i ∥)) ⟩
         (f ̂ 𝑨) (∣ h ∣ ∘ (λ i → fst ∥ a i ∥))
                        ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         (f ̂ 𝑨) (ϕ ∘ a) ∎



 𝔽-carrier-is-set : is-set (∣ 𝑻 ∣ // ⟨ ConΨ ⟩)
 𝔽-carrier-is-set = λ x y x₁ y₁ → {!!}
 -- subsets-of-sets-are-sets (∣ 𝑻 ∣ → 𝔉 ̇) _ -- (X → Ω 𝓥)
 --               (powersets-are-sets ? ) -- dfunext-gives-hfunext hunapply{X = ∣ 𝑻 ∣})
 --               hunapply{X = ∣ 𝑻 ∣} pe
 --               (λ _ → ∃-is-subsingleton)


--N.B. Ψ𝒦𝑻 is the kernel of 𝑻 → 𝔽(𝒦, 𝑻).  Therefore, to prove
--𝑨 is a hom image of 𝔽(𝒦, 𝑻), it suffices to show that the kernel of
--the lift h : 𝑻 → 𝑨 *contains* Ψ𝒦𝑻
--
--    𝑻---- g --->>𝔽  (ker g = Ψ𝒦𝑻)
--     \         .
--      \       .
--       h     ∃ϕ     (want: Ψ𝒦𝑻 ⊆ ker h)
--        \   .
--         \ .
--          V
--          𝑨

 -- To complete the proof of Birkhoff, it remains to show that 𝔽 belongs to SP(𝒦).
 -- Actually, it suffices to show 𝔽 belongs to VClo 𝒦.
 -- For if that is true, then we have an algebra (𝔽) that belongs to VClo 𝒦
 -- and such that ∃ hom ϕ : 𝔽 → 𝑨 for all 𝑨 ∈ Mod Th (VClo 𝒦).
 -- data VClo (𝒦 : Pred (Algebra 𝔙+ 𝑆) (𝔙+ ⁺)) : Pred (Algebra 𝔙+ 𝑆) (𝔙++ ⁺) where
 --  vbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo 𝒦
 --  vprod : {I : 𝔙 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ VClo 𝒦) → ⨅ 𝒜 ∈ VClo 𝒦
 --  vsub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ VClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ VClo 𝒦
 --  vhom : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦
 -- 𝔽∈VClo : 𝔽 ∈ VClo 𝒦4
 -- 𝔽∈VClo = γ
 --  where

 --   ΣP : Pred (Algebra 𝔉 𝑆) _ → _ ̇
 --   ΣP K = Σ 𝑨 ꞉ (Algebra _ 𝑆) , 𝑨 ∈ K

 --   ⨅P : Pred (Algebra 𝔉 𝑆) _ → Algebra _ 𝑆
 --   ⨅P K = ⨅ (λ (A : (ΣP K)) → ∣ A ∣ )

 --   ⨅𝒦 : Algebra (𝔉 ⁺) 𝑆
 --   ⨅𝒦 = ⨅P 𝒦4

 --   ⨅𝒦∈VClo : ⨅𝒦 ∈ (VClo 𝒦4)
 --   ⨅𝒦∈VClo = {!sprod {I = Pred (Algebra (OVU+ ⁺ ⁺) 𝑆) (OVU+ ⁺ ⁺ ⁺)}{𝒜 = ⨅P} ?!}

 --   h : ∣ 𝔽 ∣ → ∣ ⨅𝒦 ∣
 --   h = {!!}

 --   hembe : is-embedding h
 --   hembe = {!!}

 --   hhomo : is-homomorphism 𝔽 ⨅𝒦 h
 --   hhomo = {!!}

 --   𝔽sub : SubalgebrasOf ⨅𝒦
 --   𝔽sub = (𝔽 , h , (hembe , hhomo))

 --   γ : 𝔽 ∈ VClo 𝒦3
 --   γ = vsub ⨅𝒦∈VClo 𝔽sub



 -- To get the full universality of 𝔽, we should also prove that the hom described above
 -- (in the proof of 𝔽-is-universal-for) is actually unique.
 -- We'll postpone that for now, but here's a stub.
 -- 𝔽-hom-unique : {𝑨 : Algebra 𝓦 𝑆}(g h : hom 𝔽 𝑨)
 --  →              ∣ g ∣ ≡ ∣ h ∣
 -- 𝔽-hom-unique g h = gfe λ x → {!γ x!}
 --  where γ : ∀ x → ∣ g ∣ x ≡ ∣ h ∣ x
 --        γ = {!!}

--  SClo→𝑻img : {𝑪 : Algebra 𝔖 𝑆}
--   →          (𝑪 ∈ SClo 𝒦++) → 𝑻img
--  SClo→𝑻img {𝑪 = 𝑪} 𝑪∈SClo𝒦 =
--   𝑪 , (fst (𝑻hom-gen 𝑪)) , (𝑪∈SClo𝒦 , (snd (𝑻hom-gen 𝑪)))

--  Ψ⊆ThSClo : Ψ ⊆ Th (SClo 𝒦++)
--  Ψ⊆ThSClo {p , q} pΨq {𝑪} 𝑪∈SClo𝒦 = 𝑪⊧p≈q
--   where
--    ti : 𝑻img
--    ti = SClo→𝑻img {𝑪 = 𝑪} 𝑪∈SClo𝒦

--    ϕ : hom 𝑻 𝑪
--    ϕ = 𝑻ϕ ti

--    ϕE : Epic ∣ ϕ ∣
--    ϕE = 𝑻ϕE ti

--    ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
--    ϕsur 𝒄 x = ϕE (𝒄 x)

--    preim : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 ∣
--    preim 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

--    ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (preim 𝒄) ≡ 𝒄
--    ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

--    γ : ∣ ϕ ∣ ∘ (p ̇ 𝑻) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻)
--    γ = pΨq ti

--    𝑪⊧p≈q : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
--    𝑪⊧p≈q = gfe λ 𝒄 →
--     (p ̇ 𝑪) 𝒄               ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
--     (p ̇ 𝑪) (∣ ϕ ∣ ∘ (preim 𝒄)) ≡⟨ (comm-hom-term gfe 𝑻 𝑪 ϕ p (preim 𝒄))⁻¹ ⟩
--     ∣ ϕ ∣ ((p ̇ 𝑻)(preim 𝒄))     ≡⟨ (intensionality γ (preim 𝒄)) ⟩
--     ∣ ϕ ∣ ((q ̇ 𝑻)(preim 𝒄))     ≡⟨ comm-hom-term gfe 𝑻 𝑪 ϕ q (preim 𝒄) ⟩
--     (q ̇ 𝑪)(∣ ϕ ∣ ∘ (preim 𝒄))  ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
--     (q ̇ 𝑪) 𝒄 ∎


--  Ψ⊆Th : ∀ p q → (p , q) ∈ Ψ → 𝒦++ ⊧ p ≋ q
--  Ψ⊆Th p q pΨq {𝑨} KA = Ψ⊆ThSClo {p , q} pΨq (sbase KA)





--  data SPClo : Pred (Algebra (OVU+ ⁺ ⁺ ⁺) 𝑆) (OVU+ ⁺ ⁺ ⁺ ⁺) where
--   spbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦4 → 𝑨 ∈ SPClo
--   sprod : {I : _ ̇ }{𝒜 : I → Algebra _ 𝑆}
--    →     (∀ i → 𝒜 i ∈ SPClo) → ⨅ 𝒜 ∈ SPClo
--   ssub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ SPClo
--    →    (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ SPClo

--  -- claim: 𝔽 belongs to SPClo
--  -- {𝒦 : Pred (Algebra (OVU+ ⁺ ) 𝑆) (OVU+ ⁺ ⁺ )}
--  -- 𝔽 : Algebra (OVU+ ⁺ ⁺ ⁺) 𝑆
--  -- 𝔽∈SPClo : 𝔽 ∈ SClo{𝓢 = (OVU+ ⁺ ⁺)} PClo{𝓢 = (OVU+ ⁺)} 𝒦
-- -- SubalgebrasOf : {𝓢 : Universe} → Algebra 𝓢 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓢 ⁺ ̇
-- -- SubalgebrasOf {𝓢} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓢 𝑆) ,
-- --                 Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) ,
-- --                   is-embedding h × is-homomorphism 𝑩 𝑨 h

--  -- we will show 𝔽 is a subalgebra of ⨅ 𝒜 where
--  -- {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆}(∀ i → 𝒜 i ∈ SPClo)
--  𝔽∈SPClo : 𝔽 ∈ SPClo
--  𝔽∈SPClo = γ
--   where

--    ΣP : Pred (Algebra (OVU+ ⁺ ) 𝑆) (OVU+ ⁺ ⁺ ) → OVU+ ⁺ ⁺  ̇
--    ΣP 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , 𝑨 ∈ 𝒦

--    ⨅P : Pred (Algebra (OVU+ ⁺ ) 𝑆) (OVU+ ⁺ ⁺ ) → Algebra (OVU+ ⁺ ⁺ ) 𝑆
--    ⨅P 𝒦 = ⨅ (λ (A : (ΣP 𝒦)) → ∣ A ∣ )

--    ⨅𝒦 : Algebra (OVU+ ⁺ ⁺) 𝑆
--    ⨅𝒦 = ⨅P 𝒦++

--    ⨅𝒦∈SPClo : ⨅𝒦 ∈ SPClo
--    ⨅𝒦∈SPClo = {!sprod {I = Pred (Algebra (OVU+ ⁺ ⁺) 𝑆) (OVU+ ⁺ ⁺ ⁺)}{𝒜 = ⨅P} ?!}

--    h : ∣ 𝔽 ∣ → ∣ ⨅𝒦 ∣
--    h = {!!}

--    hembe : is-embedding h
--    hembe = {!!}

--    hhomo : is-homomorphism 𝔽 ⨅𝒦 h
--    hhomo = {!!}

--    𝔽sub : SubalgebrasOf ⨅𝒦
--    𝔽sub = (𝔽 , h , (hembe , hhomo))

--    γ : 𝔽 ∈ SPClo
--    γ = ssub ⨅𝒦∈SPClo 𝔽sub

--  open product-compatibility {𝓢 = OVU+}

--  pclo-id1 : ∀ {p q} → (𝒦+ ⊧ p ≋ q) → (PClo 𝒦+ ⊧ p ≋ q)
--  pclo-id1 {p} {q} α (pbase x) = α x
--  pclo-id1 {p} {q} α (prod{I}{𝒜} 𝒜-P𝒦 ) = γ
--   where
--    IH : (i : I)  → (p ̇ 𝒜 i) ≡ (q ̇ 𝒜 i)
--    IH = λ i → pclo-id1{p}{q} α  ( 𝒜-P𝒦  i )
--    γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
--    γ = products-preserve-identities p q I 𝒜 IH

--  pclo-id2 : ∀{p q} → ((PClo 𝒦+) ⊧ p ≋ q ) → (𝒦+ ⊧ p ≋ q)
--  pclo-id2 p A∈𝒦 = p (pbase A∈𝒦)

--  sclo-id1 : ∀{p q} → (𝒦+ ⊧ p ≋ q) → (SClo 𝒦+ ⊧ p ≋ q)
--  sclo-id1 {p} {q} 𝒦⊧p≋q (sbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
--  sclo-id1 {p} {q} 𝒦⊧p≋q (sub {𝑨 = 𝑨} A∈SClo𝒦 sa) = γ
--   where
--    A⊧p≈q : 𝑨 ⊧ p ≈ q
--    A⊧p≈q = sclo-id1{p}{q} 𝒦⊧p≋q A∈SClo𝒦

--    B : Algebra 𝔖 𝑆
--    B = ∣ sa ∣

--    h : ∣ B ∣ → ∣ 𝑨 ∣
--    h = pr₁ ∥ sa ∥

--    hem : is-embedding h
--    hem = ∣ pr₂ ∥ sa ∥ ∣

--    hhm : is-homomorphism B 𝑨 h
--    hhm = ∥ pr₂ ∥ sa ∥ ∥

--    ξ : (b : X → ∣ B ∣ ) → h ((p ̇ B) b) ≡ h ((q ̇ B) b)
--    ξ b =
--     h ((p ̇ B) b)  ≡⟨ comm-hom-term gfe B 𝑨 (h , hhm) p b ⟩
--     (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
--     (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe B 𝑨 (h , hhm) q b)⁻¹ ⟩
--     h ((q ̇ B) b)  ∎

--    hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
--    hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

--    γ : p ̇ B ≡ q ̇ B
--    γ = gfe λ b → hlc (ξ b)

--  sclo-id2 : ∀ {p q} → (SClo 𝒦+ ⊧ p ≋ q) → (𝒦+ ⊧ p ≋ q)
--  sclo-id2 p A∈𝒦 = p (sbase A∈𝒦)

--  hclo-id1 : ∀{p q} → (𝒦+ ⊧ p ≋ q) → (HClo 𝒦+ ⊧ p ≋ q)
--  hclo-id1 {p}{q} 𝒦⊧p≋q (hbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
--  hclo-id1 {p}{q} 𝒦⊧p≋q (hhom{𝑨} A∈HClo𝒦 𝑩ϕhE) = γ
--   where
--    A⊧p≈q : 𝑨 ⊧ p ≈ q
--    A⊧p≈q = (hclo-id1{p}{q} 𝒦⊧p≋q ) A∈HClo𝒦

--    𝑩 : Algebra ℌ 𝑆
--    𝑩 = ∣ 𝑩ϕhE ∣

--    ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
--    ϕ = ∣ ∥ 𝑩ϕhE ∥ ∣

--    ϕhom : is-homomorphism 𝑨 𝑩 ϕ
--    ϕhom = ∣ pr₂ ∥ 𝑩ϕhE ∥ ∣

--    ϕsur : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
--    ϕsur 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhE ∥ ∥ (𝒃 x)

--    preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
--    preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕsur 𝒃 x))

--    ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
--    ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕsur 𝒃 x)

--    γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
--    γ = gfe λ 𝒃 →
--     (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
--     (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) p (preim 𝒃))⁻¹ ⟩
--     ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality A⊧p≈q (preim 𝒃)) ⟩
--     ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
--     (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
--     (q ̇ 𝑩) 𝒃 ∎

--  hclo-id2 : ∀ {p q} → (HClo 𝒦+ ⊧ p ≋ q) → (𝒦+ ⊧ p ≋ q)
--  hclo-id2 p A∈𝒦 = p (hbase A∈𝒦)

--  vclo-id1 : ∀ {p q} → (𝒦+ ⊧ p ≋ q) → (VClo 𝒦+ ⊧ p ≋ q)
--  vclo-id1 {p} {q} α (vbase A∈𝒦) = α A∈𝒦
--  vclo-id1 {p} {q} α (vprod{I = I}{𝒜 = 𝒜} 𝒜∈VClo𝒦) = γ
--   where
--    IH : (i : I) → 𝒜 i ⊧ p ≈ q
--    IH i = vclo-id1{p}{q} α (𝒜∈VClo𝒦 i)

--    γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
--    γ = products-preserve-identities p q I 𝒜 IH

--  vclo-id1 {p} {q} α ( vsub {𝑨 = 𝑨} A∈VClo𝒦 sa ) = γ
--   where
--    A⊧p≈q : 𝑨 ⊧ p ≈ q
--    A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

--    𝑩 : Algebra 𝔙 𝑆
--    𝑩 = ∣ sa ∣

--    h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
--    h = pr₁ ∥ sa ∥

--    hem : is-embedding h
--    hem = ∣ pr₂ ∥ sa ∥ ∣

--    hhm : is-homomorphism 𝑩 𝑨 h
--    hhm = ∥ pr₂ ∥ sa ∥ ∥

--    ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
--    ξ b =
--     h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
--     (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
--     (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
--     h ((q ̇ 𝑩) b)  ∎

--    hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
--    hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

--    γ : p ̇ 𝑩 ≡ q ̇ 𝑩
--    γ = gfe λ b → hlc (ξ b)

--  vclo-id1 {p}{q} α (vhom{𝑨 = 𝑨} A∈VClo𝒦 𝑩ϕhE) = γ
--   where
--    A⊧p≈q : 𝑨 ⊧ p ≈ q
--    A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

--    𝑩 : Algebra 𝔙 𝑆
--    𝑩 = ∣ 𝑩ϕhE ∣

--    ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
--    ϕ = ∣ ∥ 𝑩ϕhE ∥ ∣

--    ϕh : is-homomorphism 𝑨 𝑩 ϕ
--    ϕh = ∣ pr₂ ∥ 𝑩ϕhE ∥ ∣

--    ϕE : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
--    ϕE 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhE ∥ ∥ (𝒃 x)

--    preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
--    preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕE 𝒃 x))

--    ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
--    ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕE 𝒃 x)

--    γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
--    γ = gfe λ 𝒃 →
--     (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
--     (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) p (preim 𝒃))⁻¹ ⟩
--     ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality A⊧p≈q (preim 𝒃)) ⟩
--     ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) q (preim 𝒃) ⟩
--     (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
--     (q ̇ 𝑩) 𝒃 ∎

--  vclo-id2 : ∀ {p q} → (VClo 𝒦+ ⊧ p ≋ q) → (𝒦+ ⊧ p ≋ q)
--  vclo-id2 p A∈𝒦 = p (vbase A∈𝒦)

--  -- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
--  ThHSP-axiomatizes : (p q : ∣ 𝑻 ∣)
--            -----------------------------------------
--   →         𝒦+ ⊧ p ≋ q  ⇔  ((p , q) ∈ Th (VClo 𝒦+))

--  ThHSP-axiomatizes p q =
--   (λ 𝒦⊧p≋q 𝑨∈VClo𝒦 → vclo-id1{p = p}{q = q} 𝒦⊧p≋q 𝑨∈VClo𝒦) ,
--   λ pq∈Th 𝑨∈𝒦 → pq∈Th (vbase 𝑨∈𝒦)

-- -----------------------------------------------------
-- -- Old, unused stuff

--  --Compatibility of identities with interpretation of terms
--  compatibility-of-interpretations : (p q : Term)
--   →        (𝒦 ⊧ p ≋ q)
--   →        ∀ 𝑨 (ka : 𝑨 ∈ 𝒦) (hh : hom 𝑻 𝑨)
--   →        ∣ hh ∣ ((∣ term-gen p ∣ ̇ 𝑻) ℊ)
--          ≡ ∣ hh ∣ ((∣ term-gen q ∣ ̇ 𝑻) ℊ)

--  compatibility-of-interpretations p q 𝒦⊧p≋q 𝑨 ka hh = γ
--   where
--    𝓅 𝓆 : ∣ 𝑻 ∣  -- Notation: 𝓅 = \Mcp
--    𝓅 = ∣ tg p ∣
--    𝓆 = ∣ tg q ∣

--    p≡𝓅 : p ≡ (𝓅 ̇ 𝑻) ℊ
--    p≡𝓅 = ∥ tg p ∥

--    q≡𝓆 : q ≡ (𝓆 ̇ 𝑻) ℊ
--    q≡𝓆 = ∥ tg q ∥

--    pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
--    pA≡qA = 𝒦⊧p≋q ka

--    γ : ∣ hh ∣ ((𝓅 ̇ 𝑻) ℊ) ≡ ∣ hh ∣ ((𝓆 ̇ 𝑻) ℊ)
--    γ =
--     ∣ hh ∣ ((𝓅 ̇ 𝑻) ℊ)  ≡⟨ (ap ∣ hh ∣ (term-gen-agreement p))⁻¹ ⟩
--     ∣ hh ∣ ((p ̇ 𝑻) ℊ)  ≡⟨ (comm-hom-term gfe 𝑻 𝑨 hh p ℊ) ⟩
--     (p ̇ 𝑨) (∣ hh ∣ ∘ ℊ)  ≡⟨ intensionality pA≡qA (∣ hh ∣ ∘ ℊ)  ⟩
--     (q ̇ 𝑨) (∣ hh ∣ ∘ ℊ)  ≡⟨ (comm-hom-term gfe 𝑻 𝑨 hh q ℊ)⁻¹ ⟩
--     ∣ hh ∣ ((q ̇ 𝑻) ℊ)  ≡⟨ ap ∣ hh ∣ (term-gen-agreement q) ⟩
--     ∣ hh ∣ ((𝓆 ̇ 𝑻) ℊ)  ∎












































 -- 𝑻img→𝑻⊧ : ∀ p q → (p , q) ∈ Ψ' → (ti : 𝑻img)
 --          ------------------------------------------------------
 --  →        ∣ (𝑻ϕ ti) ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ (𝑻ϕ ti) ∣ ((q ̇ 𝑻) ℊ)

 -- 𝑻img→𝑻⊧ p q pΨq ti = goal1
 --  where
 --   𝑪 : Algebra 𝓤 𝑆
 --   𝑪 = ∣ ti ∣

 --   ϕ : hom 𝑻 𝑪
 --   ϕ = 𝑻ϕ ti

 --   pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
 --   pCq = pΨq ti

 --   𝓅 𝓆 : ∣ 𝑻 ∣  -- Notation: 𝓅 = \Mcp
 --   𝓅 = ∣ tg{X = X}{gfe = gfe} p ∣
 --   𝓆 = ∣ tg{X = X}{gfe = gfe} q ∣

 --   p≡𝓅 : p ≡ (𝓅 ̇ 𝑻) ℊ
 --   p≡𝓅 = ∥ tg p ∥

 --   q≡𝓆 : q ≡ (𝓆 ̇ 𝑻) ℊ
 --   q≡𝓆 = ∥ tg q ∥

 --   ξ : ∣ ϕ ∣ ((𝓅 ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((𝓆 ̇ 𝑻) ℊ)
 --   ξ = (ap ∣ ϕ ∣ p≡𝓅)⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣ q≡𝓆)

 --   goal1 : ∣ ϕ ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)
 --   goal1 = (ap ∣ ϕ ∣ (term-gen-agreement p))
 --            ∙ ξ ∙ (ap ∣ ϕ ∣ (term-gen-agreement q))⁻¹

-- module _
--  {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓤 ⊔ 𝓦)} where

 -- 𝒦subset : (𝑩 : Algebra 𝓤 𝑆)
 --  →           𝑩 ∈ 𝒦  →  Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦
 -- 𝒦subset 𝑩 𝑩∈𝒦 = 𝑩 , 𝑩∈𝒦

 -- 𝒦supset : (BK : Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦) → ∣ BK ∣ ∈ 𝒦
 -- 𝒦supset BK = ∥ BK ∥

 -- 𝒦prod : (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆) → hom (𝔽) (⨅ 𝒜)
 -- 𝒦prod I 𝒜  = 𝔽-is-universal-for (⨅ 𝒜)

--  𝔽∈SP : hom 𝔽 ⨅

-- {𝒜 : I → Algebra _ 𝑆}
