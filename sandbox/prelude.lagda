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
 _≃_; logically-equivalent-subsingletons-are-equivalent; Π-is-subsingleton) public

open import MGS-Powerset renaming (_∈_ to _∈₀_; _⊆_ to _⊆₀_) using (𝓟; ∈-is-subsingleton;
 equiv-to-subsingleton; powersets-are-sets'; subset-extensionality'; propext) public

open import MGS-Embeddings using (Nat; NatΠ; NatΠ-is-embedding; is-embedding; pr₁-embedding;
 is-set; _↪_; embedding-gives-ap-is-equiv; embeddings-are-lc; ×-is-subsingleton) public

open import MGS-Solved-Exercises using (to-subtype-≡) public

open import MGS-Unique-Existence using (∃!; -∃!) public

open import MGS-Subsingleton-Truncation hiding (refl; _∈_; _⊆_) public

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

_∈∈_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A  →  B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
_∈∈_ f S = (x : _) → f x ∈ S


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

cong-app-pred : ∀{A : 𝓤 ̇ }{B₁ B₂ : Pred A 𝓤}
                (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
               ------------------------------
 →                         x ∈ B₂
cong-app-pred x x∈B₁ (refl _ ) = x∈B₁

cong-pred : {A : 𝓤 ̇ }{B : Pred A 𝓤}
            (x y : A) →  x ∈ B  →  x ≡ y
            ----------------------------
 →                       y ∈ B
cong-pred x .x x∈B (refl _ ) = x∈B


data Image_∋_ {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
  where
  im : (x : A) → Image f ∋ f x
  eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

-- image_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → Pred B (𝓤 ⊔ 𝓦)
-- image f = λ b → ∃ λ a → b ≡ f a
-- image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
-- image f = Σ y ꞉ codomain f , ∃ x ꞉ domain f , f x ≡ y

ImageIsImage : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
               (f : A → B) (b : B) (a : A)
 →              b ≡ f a
              ----------------------------
 →              Image f ∋ b
ImageIsImage {A = A}{B = B} f b a b≡fa = eq b a b≡fa

Inv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)(b : B) → Image f ∋ b  →  A
Inv f .(f a) (im a) = a
Inv f b (eq b a b≡fa) = a

-- inv : {A B : 𝓤₀ ̇ }(f : A → B)(b : B) → image f → A
-- inv {A} {B} = Inv {𝓤₀}{𝓤₀}{A}{B}

InvIsInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
           (b : B) (b∈Imgf : Image f ∋ b)
          ---------------------------------
 →         f (Inv f b b∈Imgf) ≡ b
InvIsInv f .(f a) (im a) = refl _
InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹

Epic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) →  𝓤 ⊔ 𝓦 ̇
Epic g = ∀ y → Image g ∋ y

epic : {A B : 𝓤₀ ̇ } (g : A → B) → 𝓤₀ ̇
epic = Epic {𝓤₀} {𝓤₀}

EpicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → Epic f → B → A
EpicInv f fEpic b = Inv f b (fEpic b)

-- The (psudo-)inverse of an epic is the right inverse.
EInvIsRInv : funext 𝓦 𝓦 → {A : 𝓤 ̇ } {B : 𝓦 ̇ }
             (f : A → B)  (fEpic : Epic f)
            ---------------------------------
 →           f ∘ (EpicInv f fEpic) ≡ 𝑖𝑑 B
EInvIsRInv fe f fEpic = fe (λ x → InvIsInv f x (fEpic x))

monic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) → 𝓤 ⊔ 𝓦 ̇
monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂
monic₀ : {A B : 𝓤₀ ̇ } (g : A → B) → 𝓤₀ ̇
monic₀ = monic {𝓤₀}{𝓤₀}

--The (pseudo-)inverse of a monic function
monic-inv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → monic f
 →           (b : B) → Image f ∋ b → A
monic-inv f fmonic  = λ b Imf∋b → Inv f b Imf∋b

--The (psudo-)inverse of a monic is the left inverse.
monic-inv-is-linv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                    (f : A → B) (fmonic : monic f)(x : A)
                   ----------------------------------------
  →                 (monic-inv f fmonic) (f x) (im x) ≡ x
monic-inv-is-linv f fmonic x = refl _

bijective : {A B : 𝓤₀ ̇ }(g : A → B) → 𝓤₀ ̇
bijective g = epic g × monic g

Bijective : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(g : A → B) → 𝓤 ⊔ 𝓦 ̇
Bijective g = Epic g × monic g

-----------------------------------------------------------------------
-- Embedding elimination (makes it easier to apply is-embedding)
embedding-elim : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }{f : X → Y}
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


-------------------------------------------------------
--Function extensionality from univalence

--Ordinary function extensionality
extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ∼ g   →   f ≡ g

--Opposite of function extensionality
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

extensionality-lemma : {I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
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

\end{code}
