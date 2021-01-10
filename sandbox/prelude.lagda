\begin{code}
-- FILE: prelude.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020
-- REF: Some parts of this file are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
-- SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ 
-- Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

module prelude where

open import Universes public

variable
  𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓞 𝓠 𝓡 𝓢 𝓧 : Universe

open import Identity-Type renaming (_≡_ to infix 0 _≡_ ;
 refl to 𝓇ℯ𝒻𝓁) public

pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}

open import Sigma-Type renaming (_,_ to infixr 50 _,_) public

open import MGS-MLTT using (_∘_; domain; codomain; transport; _≡⟨_⟩_; _∎; pr₁; pr₂; -Σ; -- 𝕁;
 Π; ¬; _×_; 𝑖𝑑; _∼_; _+_; 𝟘; 𝟙; 𝟚; _⇔_; lr-implication; rl-implication; id; _⁻¹; ap) public

open import MGS-Equivalences using (is-equiv; inverse; invertible) public

open import MGS-Subsingleton-Theorems using (funext; global-hfunext; dfunext; is-singleton;
 is-subsingleton; is-prop; Univalence; global-dfunext; univalence-gives-global-dfunext; _●_;
 _≃_; logically-equivalent-subsingletons-are-equivalent; Π-is-subsingleton; Σ-is-subsingleton) public

open import MGS-Powerset renaming (_∈_ to _∈₀_; _⊆_ to _⊆₀_; ∈-is-subsingleton to ∈₀-is-subsingleton)
 using (𝓟; equiv-to-subsingleton; powersets-are-sets'; subset-extensionality'; propext; _holds) public

open import MGS-Embeddings using (Nat; NatΠ; NatΠ-is-embedding; is-embedding; pr₁-embedding;
 is-set; _↪_; embedding-gives-ap-is-equiv; embeddings-are-lc; ×-is-subsingleton) public

open import MGS-Solved-Exercises using (to-subtype-≡) public

open import MGS-Unique-Existence using (∃!; -∃!) public

open import MGS-Subsingleton-Truncation hiding (refl; _∈_; _⊆_) public


module _  {𝓤 : Universe}{X : 𝓤 ̇ }  where
 ≡-rfl : (x : X) → x ≡ x
 ≡-rfl x = refl _

 ≡-sym : (x y : X) → x ≡ y → y ≡ x
 ≡-sym x y (refl _) = refl _

 ≡-trans : (x y z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-trans x y z (refl _) (refl _) = refl _

 ≡-Trans : (x : X){y : X}(z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-Trans x {y} z (refl _) (refl _) = refl _

∣_∣ fst : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇} → Σ Y → X
∣ x , y ∣ = x
fst (x , y) = x

∥_∥ snd : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
∥ x , y ∥ = y
snd (x , y) = y

ap-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          {f g : X → Y} {a b : X}
 →         f ≡ g   →   a ≡ b
         -----------------------
 →            f a ≡ g b

ap-cong (refl _) (refl _) = refl _

cong-app : {A : 𝓤 ̇ } {B : A → 𝓦 ̇ }
           {f g : (a : A) → B a}
 →          f ≡ g   →   (a : A)
          -----------------------
 →              f a ≡ g a

cong-app (refl _) a = refl _



------------------------------------------------------------------------------------------
-- PREDICATES: sets, elements, subsets, set union, set intersection, etc.

Pred : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
Pred A 𝓥 = A → 𝓥 ̇

Pred₀ : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
Pred₀ A 𝓥 = Σ P ꞉ (A → 𝓥 ̇) , ∀ x → is-subsingleton (P x)

infix 4 _∈_ _∉_
_∈_ : {A : 𝓤 ̇ } → A → Pred A 𝓦 → 𝓦 ̇
x ∈ P = P x

_∉_ : {A : 𝓤 ̇ } → A → Pred A 𝓦 → 𝓦 ̇
x ∉ P = ¬ (x ∈ P)

infix 4 _⊆_ _⊇_
_⊆_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

_⊇_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
P ⊇ Q = Q ⊆ P

_=̇_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
P =̇ Q = (P ⊆ Q) × (Q ⊆ P)

_∈∈_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A  →  B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
_∈∈_ f S = (x : _) → f x ∈ S

Pred-refl : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          P ≡ Q → (a : A) → a ∈ P → a ∈ Q
Pred-refl (refl _) _ = λ z → z

Pred-≡ : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          P ≡ Q → P =̇ Q
Pred-≡ (refl _) = (λ z → z) , λ z → z

Pred-≡→⊆ : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          P ≡ Q → (P ⊆ Q)
Pred-≡→⊆ (refl _) = (λ z → z)

Pred-≡→⊇ : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          P ≡ Q → (P ⊇ Q)
Pred-≡→⊇ (refl _) = (λ z → z)

Pred-=̇-≡ : {𝓤 𝓦 : Universe}
 →          propext 𝓦 → global-dfunext
 →          {A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          ((x : A) → is-subsingleton (P x))
 →          ((x : A) → is-subsingleton (Q x))
 →          P =̇ Q → P ≡ Q
Pred-=̇-≡ pe gfe {A}{P}{Q} ssP ssQ (pq , qp) = gfe γ
 where
  γ : (x : A) → P x ≡ Q x
  γ x = pe (ssP x) (ssQ x) pq qp

infixr 1 _⊎_

-- Disjoint Union.
data _⊎_ (A : 𝓤 ̇) (B : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

-- Union.
infixr 6 _∪_
_∪_ : {A : 𝓤 ̇} → Pred A 𝓥 → Pred A 𝓦 → Pred A _
P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q


-- The empty set.
∅ : {A : 𝓤 ̇} → Pred A 𝓤₀
∅ = λ _ → 𝟘

-- The singleton set.
-- ｛_｝ : {A : 𝓤 ̇} → A → Pred A _
-- ｛ x ｝ = x ≡_


Im_⊆_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
Im_⊆_ {A = A} f S = (x : A) → f x ∈ S

img : {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
      (f : X → Y) (P : Pred Y 𝓤)
 →    Im f ⊆ P →  X → Σ P
img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁


--Products of predicates and their meanings --
--The product `Π P` of a predicate `P : Pred X 𝓤` is inhabited iff  P x holds for all x : X.
ΠP-meaning : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{P : Pred X 𝓤}
 →            Π P  →  (x : X) → P x
ΠP-meaning f x = f x



module _ {𝓤 𝓦 : Universe} where
 ≡-elim-left : {A₁ A₂ : 𝓤 ̇ } {B₁ B₂ : 𝓦 ̇ }
  →            (A₁ , B₁) ≡ (A₂ , B₂)
               ----------------------
  →                   A₁ ≡ A₂
 ≡-elim-left e = ap pr₁ e

 ≡-elim-right : {A₁ A₂ : 𝓤 ̇ }{B₁ B₂ : 𝓦 ̇ }
  →             (A₁ , B₁) ≡ (A₂ , B₂)
               -----------------------
  →                    B₁ ≡ B₂
 ≡-elim-right e = ap pr₂ e

 ≡-×-intro : {A₁ A₂ : 𝓤 ̇ } {B₁ B₂ : 𝓦 ̇ }
  →           A₁ ≡ A₂  →  B₁ ≡ B₂
           ------------------------
  →          (A₁ , B₁) ≡ (A₂ , B₂)
 ≡-×-intro (refl _ ) (refl _ ) = (refl _ )


 cong-app-pred : {A : 𝓤 ̇ }{B₁ B₂ : Pred A 𝓦}
                 (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
                ------------------------------
  →                         x ∈ B₂
 cong-app-pred x x∈B₁ (refl _ ) = x∈B₁

 cong-pred : {A : 𝓤 ̇ }{B : Pred A 𝓦}
             (x y : A) →  x ∈ B  →  x ≡ y
             ----------------------------
  →                       y ∈ B
 cong-pred x .x x∈B (refl _ ) = x∈B

-- ≡-×-int : {𝓤 𝓦 : Universe}{A₁ A₂ : 𝓤 ̇ } {B₁ B₂ : 𝓦 ̇ }
--   →           A₁ ≡ A₂  →  B₁ ≡ B₂
--            ------------------------
--   →          (A₁ , B₁) ≡ (A₂ , B₂)
-- ≡-×-int (refl _ ) (refl _ ) = (refl _ )

≡-×-int : {𝓤 𝓦 : Universe}{A : 𝓤 ̇ } {B : 𝓦 ̇ }(a a' : A)(b b' : B)
  →           a ≡ a'  →  b ≡ b'
           ------------------------
  →          (a , b) ≡ (a' , b')
≡-×-int a a' b b' (refl _ ) (refl _ ) = (refl _ )

module _ {𝓤 𝓦 : Universe} where
 data Image_∋_ {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
   where
   im : (x : A) → Image f ∋ f x
   eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

 ImageIsImage : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                (f : A → B) (b : B) (a : A)
  →              b ≡ f a
               ----------------------------
  →              Image f ∋ b
 ImageIsImage {A = A}{B = B} f b a b≡fa = eq b a b≡fa

 Inv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)(b : B) → Image f ∋ b  →  A
 Inv f .(f a) (im a) = a
 Inv f b (eq b a b≡fa) = a

 InvIsInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
            (b : B) (b∈Imgf : Image f ∋ b)
           ---------------------------------
  →         f (Inv f b b∈Imgf) ≡ b
 InvIsInv f .(f a) (im a) = refl _
 InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹

 Epic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) →  𝓤 ⊔ 𝓦 ̇
 Epic g = ∀ y → Image g ∋ y


 EpicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → Epic f → B → A
 EpicInv f fEpi b = Inv f b (fEpi b)

 -- The (psudo-)inverse of an epic is the right inverse.
 EpicInvIsRightInv : funext 𝓦 𝓦 → {A : 𝓤 ̇ } {B : 𝓦 ̇ }
              (f : A → B)  (fEpi : Epic f)
             ---------------------------------
  →           f ∘ (EpicInv f fEpi) ≡ 𝑖𝑑 B
 EpicInvIsRightInv fe f fEpi = fe (λ x → InvIsInv f x (fEpi x))

 Monic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) → 𝓤 ⊔ 𝓦 ̇
 Monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂

 --The (pseudo-)inverse of a monic function
 MonicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → Monic f
  →           (b : B) → Image f ∋ b → A
 MonicInv f fmonic  = λ b Imf∋b → Inv f b Imf∋b

 --The (psudo-)inverse of a monic is the left inverse.
 MonicInvIsLeftInv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                     (f : A → B) (fmonic : Monic f)(x : A)
                    ----------------------------------------
   →                 (MonicInv f fmonic) (f x) (im x) ≡ x
 MonicInvIsLeftInv f fmonic x = refl _

 Bijective : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) → 𝓤 ⊔ 𝓦 ̇
 Bijective f = Epic f × Monic f

 Inverse : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
  →         Bijective f  →   B → A
 Inverse f fbi b = Inv f b (∣ fbi ∣ b)

 --The next three are from UF-Base.lagda and UF-Equiv.lagda (resp.) which, at one time,
 --were part of Matin Escsardo's UF Agda repository.
 refl-left-neutral : {𝓤 : Universe} {X : 𝓤 ̇ } {x y : X} (p : x ≡ y) → (refl _) ∙ p ≡ p
 refl-left-neutral (refl _) = refl _

 refl-right-neutral : {𝓤 : Universe}{X : 𝓤 ̇ } {x y : X} (p : x ≡ y) → p ≡ p ∙ (refl _)
 refl-right-neutral p = refl _

 identifications-in-fibers : {𝓤 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
  →                          (Σ γ ꞉ x ≡ x' , ap f γ ∙ p' ≡ p) → (x , p) ≡ (x' , p')
 identifications-in-fibers f .(f x) x .x 𝓇ℯ𝒻𝓁 p' (𝓇ℯ𝒻𝓁 , r) = g
  where
   g : x , 𝓇ℯ𝒻𝓁 ≡ x , p'
   g = ap (λ - → (x , -)) (r ⁻¹ ∙ refl-left-neutral _)

 monic-into-set-is-embedding : {A : 𝓤 ̇}{B : 𝓦 ̇} → is-set B
  →                            (f : A → B)  →  Monic f
                             ---------------------------
  →                             is-embedding f

 monic-into-set-is-embedding {A} Bset f fmon b (a , fa≡b) (a' , fa'≡b) = γ
  where
   faa' : f a ≡ f a'
   faa' = ≡-Trans (f a) (f a') fa≡b (fa'≡b ⁻¹)

   aa' : a ≡ a'
   aa' = fmon a a' faa'

   𝒜 : A → 𝓦 ̇
   𝒜 a = f a ≡ b

   arg1 : Σ p ꞉ (a ≡ a') , (transport 𝒜 p fa≡b) ≡ fa'≡b
   arg1 = aa' , Bset (f a') b (transport 𝒜 aa' fa≡b) fa'≡b

   γ : a , fa≡b ≡ a' , fa'≡b
   γ = to-Σ-≡ arg1

 -- bijections-are-invertible : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)
 --  →                          Bijective f   →   invertible f

 -- bijections-are-invertible {A}{B} f fbi = {!!} , {!!}

 invertibles-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓦 ̇ }(f : X → Y)
  →               invertible f → is-embedding f
 invertibles-are-embeddings f fi = equivs-are-embeddings f (invertibles-are-equivs f fi)


 -- Embedding elimination (makes it easier to apply is-embedding)
 embedding-elim : {X : 𝓤 ̇ } {Y : 𝓦 ̇ }{f : X → Y}
  →               is-embedding f
  →               (x x' : X)
  →               f x ≡ f x' → x ≡ x'
 embedding-elim {f = f} femb x x' fxfx' = γ
  where
   fibx : fiber f (f x)
   fibx = x , 𝓇ℯ𝒻𝓁
   fibx' : fiber f (f x)
   fibx' = x' , ((fxfx') ⁻¹)
   iss-fibffx : is-subsingleton (fiber f (f x))
   iss-fibffx = femb (f x)
   fibxfibx' : fibx ≡ fibx'
   fibxfibx' = iss-fibffx fibx fibx'
   γ : x ≡ x'
   γ = ap pr₁ fibxfibx'

epic : {A B : 𝓤₀ ̇ } (g : A → B) → 𝓤₀ ̇
epic = Epic {𝓤₀} {𝓤₀}

monic : {A B : 𝓤₀ ̇ } (g : A → B) → 𝓤₀ ̇
monic = Monic {𝓤₀}{𝓤₀}

bijective : {A B : 𝓤₀ ̇ }(g : A → B) → 𝓤₀ ̇
bijective g = epic g × monic g


--EXTENSIONALITY/INTENSIONALITY----------------------------------------------

--Ordinary function extensionality
extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ∼ g   →   f ≡ g

--Ordinary function intensionality (the opposite of function extensionality)
intensionality : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ≡ g  →  (x : A)
                  ------------------
 →                    f x ≡ g x

intensionality  (refl _ ) _  = refl _

--Dependent intensionality
dintensionality : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : A → 𝓦 ̇ } {f g : (x : A) → B x}
 →                f ≡ g  →  (x : A)
                  ------------------
 →                    f x ≡ g x

dintensionality  (refl _ ) _  = refl _


--Dependent intensionality
dep-intensionality : ∀ {𝓤 𝓦}{A : 𝓤 ̇ }{B : A → 𝓦 ̇ }
                     {f g : ∀(x : A) → B x}
 →                   f ≡ g  →  (x : A)
                    ------------------
 →                    f x ≡ g x

dep-intensionality (refl _ ) _ = refl _

--------------------------------------
--Dependent function extensionality
dep-extensionality : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
dep-extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : A → 𝓦 ̇ }
  {f g : ∀(x : A) → B x} →  f ∼ g  →  f ≡ g

∀-extensionality : 𝓤ω
∀-extensionality = ∀  {𝓤 𝓥} → extensionality 𝓤 𝓥

∀-dep-extensionality : 𝓤ω
∀-dep-extensionality = ∀ {𝓤 𝓥} → dep-extensionality 𝓤 𝓥

extensionality-lemma : ∀ {𝓤 𝓥 𝓣} →
                       {I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )
                       (args : X → (Π A))
 →                     p ≡ q
   -------------------------------------------------------------
 → (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q =
 ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

record Σω {X : 𝓤ω} (Y : X → 𝓤ω ) : 𝓤ω  where
  constructor
   _⸲_  -- notation: type \,3 for ⸲
  field
   π₁ : X
   π₂ : Y π₁

infixr 50 _⸲_

-Σω : (X : 𝓤ω) (Y : X → 𝓤ω ) → 𝓤ω
-Σω X Y = Σω Y

syntax -Σω X (λ x → y) = Σω x ꞉ X ⸲ y

_⨉_ : 𝓤ω → 𝓤ω → 𝓤ω
X ⨉ Y = Σω x ꞉ X ⸲ Y

---------------------------------
--Some tools for powersets

KER-𝓟 : {𝓤 𝓦 : Universe}{A : 𝓤 ̇} {B : 𝓦 ̇} → is-set B → (f : A → B) → A → A → Ω 𝓦
KER-𝓟 Bset f x y = (f x ≡ f y) , Bset (f x) (f y)

-- This says (f x) ≡ (f y) and is-singleton (f x) ≡ (f y)

ker-𝓟 : {𝓤 : Universe}{A B : 𝓤 ̇} → is-set B → (f : A → B) → A → 𝓟 A
ker-𝓟 {𝓤} = KER-𝓟 {𝓤}{𝓤}

module _ {𝓤 : Universe} where

 cong-app-𝓟 : ∀ { A : 𝓤 ̇ } { B C : 𝓟 A} (x : A)
  →             x ∈₀ B   →   B ≡ C
               -------------------------
  →                    x ∈₀ C

 cong-app-𝓟 {A}{B}{C} x Bx B≡C = B⊆C x Bx
  where
   B⊆C : B ⊆₀ C
   B⊆C = fst (⊆-refl-consequence B C B≡C)

 cong-𝓟 : {A : 𝓤 ̇ } {B : 𝓟 A} (x y : A)
  →            x ∈₀ B   →   x ≡ y
             -------------------------
  →                   y ∈₀ B
 cong-𝓟 {A}{B} x y Bx xy  = transport (λ - → B - holds) xy Bx

\end{code}






























 -- bijections-of-sets-are-embeddings : funext 𝓦 𝓦
 --  →                                  {A : 𝓤 ̇}{B : 𝓦 ̇} (f : A → B)
 --  →                                  is-set A → is-set B → Bijective f
 --                                    -----------------------------------
 --  →                                  is-embedding f

 -- bijections-of-sets-are-embeddings fe {A} f Aset Bset fbi = γ
 --  where
 --   mon : (a a' : A) → (f a ≡ f a') → (a ≡ a')
 --   mon a a' h₀ = ∥ fbi ∥ a a' h₀

 --   mon-inv : (a a' : A) → invertible (mon a a')
 --   mon-inv a a' = (ap f) , ((λ p → (Bset (f a) (f a')) (ap f (mon a a' p)) p) ,
 --                             λ p → (Aset a a' (mon a a' (ap f p)) p) )

 --   mon-equiv : (a a' : A) → is-equiv (mon a a')
 --   mon-equiv a a' = invertibles-are-equivs (mon a a') (mon-inv a a')

 --   ζ : (a a' : A) → (f a ≡ f a') ≃ (a ≡ a')
 --   ζ a a' = (mon a a') , (mon-equiv a a')

 --   γ : is-embedding f
 --   γ = embedding-criterion f ζ


-- pred-extensionality :  propext 𝓤 → dfunext 𝓤 𝓤 → dfunext 𝓤 (𝓤 ⁺)
--  →                     {X : 𝓤 ̇ } {A B : Pred X 𝓤}
--  →                     A ⊆ B → B ⊆ A → A ≡ B
-- pred-extensionality pe fe fe' {X} {A} {B} h k = fe' φ
--  where
--   φ : (x : X) → A x ≡ B x
--   φ x = {!!} 


