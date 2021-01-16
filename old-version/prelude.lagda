---
layout: default
title : prelude module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: prelude.lagda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATED: 12 Jan 2021
REF: Parts of this file are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
     Below, MHE = Martin Hötzel Escardo.
-->

## Agda Preliminaries

This chapter describes the [prelude module][] of the [agda-ualib][]. The source code for this module comprises the (literate) Agda_ program that was used to generate the html page displaying the sentence you are now reading. This source code inhabits the file [prelude.lagda][], which resides in the [git repository of the agda-ualib][].

**Notation**. Here are some acronyms that we use frequently.

  * MHE = [Martin Hötzel Escardo](https://www.cs.bham.ac.uk/~mhe/)
  * MLTT = [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)

----------------------------------------------------

### Options and imports
--------------------

All but the most trivial Agda programs begin by setting some options that effect how Agda behaves and importing from existing libraries (e.g., the [Agda Standard Library][] or, in our case, MHE's [Type Topology][] library). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, here's the start of the first Agda source file in our library, which we call [prelude.lagda][].

```agda
   {-# OPTIONS --without-K --exact-split --safe #-}
```

This specifies Agda `OPTIONS` that we will use throughout the library.

  * `without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

  * `exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* or *definitional* equalities.  MHE explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

  * `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must remove the `--safe` flag and insert the `--allow-unsolved-metas` flag, so we could use the following in such case:

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
```

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module prelude where

open import universes public

variable
  𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓞 𝓠 𝓡 𝓢 𝓧 : Universe

open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁) public

pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}

open import Sigma-Type renaming (_,_ to infixr 50 _,_) public

open import MGS-MLTT using (_∘_; domain; codomain; transport; _≡⟨_⟩_; _∎; pr₁; pr₂; -Σ; -- 𝕁;
 Π; ¬; _×_; 𝑖𝑑; _∼_; _+_; 𝟘; 𝟙; 𝟚; _⇔_; lr-implication; rl-implication; id; _⁻¹; ap) public

open import MGS-Equivalences using (is-equiv; inverse; invertible) public

open import MGS-Subsingleton-Theorems using (funext; global-hfunext; dfunext; is-singleton;
 is-subsingleton; is-prop; Univalence; global-dfunext; univalence-gives-global-dfunext; _●_;
 _≃_; logically-equivalent-subsingletons-are-equivalent; Π-is-subsingleton; Σ-is-subsingleton) public

open import MGS-Powerset renaming (_∈_ to _∈₀_; _⊆_ to _⊆₀_; ∈-is-subsingleton to ∈₀-is-subsingleton)
 using (𝓟; equiv-to-subsingleton; powersets-are-sets'; subset-extensionality'; propext; _holds; Ω) public

open import MGS-Embeddings using (Nat; NatΠ; NatΠ-is-embedding; is-embedding; pr₁-embedding; ∘-embedding;
 is-set; _↪_; embedding-gives-ap-is-equiv; embeddings-are-lc; ×-is-subsingleton; id-is-embedding) public

open import MGS-Solved-Exercises using (to-subtype-≡) public

open import MGS-Unique-Existence using (∃!; -∃!) public

open import MGS-Subsingleton-Truncation using (_∙_; to-Σ-≡; equivs-are-embeddings;
 invertibles-are-equivs; fiber; ⊆-refl-consequence; hfunext) public

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
\end{code}


### Predicates: sets, elements, subsets, set union, set intersection, etc.

\begin{code}
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
\end{code}

### Products of predicates and their meanings --

The product `Π P` of a predicate `P : Pred X 𝓤` is inhabited iff  P x holds for all x : X.
\begin{code}
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
\end{code}

### Extensionality and intensionality

#### Ordinary function extensionality

\begin{code}
extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ∼ g   →   f ≡ g
\end{code}

#### Ordinary function intensionality

This is the opposite of function extensionality)

\begin{code}
intensionality : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ≡ g  →  (x : A)
                  ------------------
 →                    f x ≡ g x

intensionality  (refl _ ) _  = refl _
\end{code}

#### Dependent intensionality


\begin{code}
dintensionality : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : A → 𝓦 ̇ } {f g : (x : A) → B x}
 →                f ≡ g  →  (x : A)
                  ------------------
 →                    f x ≡ g x

dintensionality  (refl _ ) _  = refl _

dep-intensionality : ∀ {𝓤 𝓦}{A : 𝓤 ̇ }{B : A → 𝓦 ̇ }
                     {f g : ∀(x : A) → B x}
 →                   f ≡ g  →  (x : A)
                    ------------------
 →                    f x ≡ g x

dep-intensionality (refl _ ) _ = refl _
\end{code}


#### Dependent function extensionality

\begin{code}
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
\end{code}

### Some tools for powersets

\begin{code}
KER-𝓟 : {𝓤 𝓦 : Universe}{A : 𝓤 ̇} {B : 𝓦 ̇} → is-set B → (f : A → B) → A → A → Ω 𝓦
KER-𝓟 Bset f x y = (f x ≡ f y) , Bset (f x) (f y)
\end{code}

This says `(f x) ≡ (f y)` and `is-singleton (f x) ≡ (f y)`.


\begin{code}
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







[2015 post by Floris van Doorn]: https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean/
[absolute value]: https://en.wikipedia.org/wiki/Absolute_value
[agda2-mode]: https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html
[agda-ualib]: https://gitlab.com/ualib/ualib.gitlab.io
[Agda]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Agda Language Reference]: https://agda.readthedocs.io/en/v2.6.1/language
[Agda Standard Library]: https://agda.github.io/agda-stdlib/
[Agda Tools]: https://agda.readthedocs.io/en/v2.6.1/tools/
[Agda Tutorial]: https://people.inf.elte.hu/pgj/agda/tutorial/Index.html
[Agda Universal Algebra Library]: https://github.com/UniversalAlgebra/agda-ualib/
[Agda User's Manual]: https://agda.readthedocs.io/en/v2.6.1/
[Agda Wiki]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Algebraic Effects and Handlers]: https://www.cs.uoregon.edu/research/summerschool/summer18/topics.php#Bauer
[Andrej Bauer]: http://www.andrej.com/index.html
[Axioms and Computation]: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#
[basic.lean]: https://gitlab.com/ualib/lean-ualib/tree/william/src/basic.lean
[birkhoff.lean]: https://gitlab.com/ualib/lean-ualib/tree/william/src/birkhoff.lean
[Category Theory in Context]: http://www.math.jhu.edu/~eriehl/context.pdf
[categorytheory.gitlab.io]: https://categorytheory.gitlab.io
[classes.lean]: https://github.com/leanprover/lean/blob/master/library/init/algebra/classes.lean
[classical.lean]: https://github.com/leanprover/lean/blob/master/library/init/classical.lean
[Clifford Bergman]: https://orion.math.iastate.edu/cbergman/
[Cliff Bergman]: https://orion.math.iastate.edu/cbergman/
[clone.lean]: https://gitlab.com/ualib/lean-ualib/tree/william/src/clone.lean
[Coercions using Type Classes]: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes
[constructive mathematics]: https://ncatlab.org/nlab/show/constructive+mathematics
[Coq]: http://coq.inria.fr
[core.lean]: https://github.com/leanprover/lean/blob/master/library/init/core.lean
[dependent types]: https://en.wikipedia.org/wiki/Dependent_type
[Emacs]: https://www.gnu.org/software/emacs/
[Equality Section]: https://leanprover.github.io/logic_and_proof/first_order_logic.html?highlight=equality#equality
[Formalization of Universal Algebra in Agda]: http://www.sciencedirect.com/science/article/pii/S1571066118300768
[free.lean]: https://gitlab.com/ualib/lean-ualib/tree/william/src/free.lean
[function extensionality]: https://ncatlab.org/nlab/show/function+extensionality
[function.lean]: https://github.com/leanprover/lean/blob/master/library/init/function.lean
[functions.lean]: https://github.com/leanprover/lean/blob/master/library/init/algebra/functions.lean
[HoTT]: https://homotopytypetheory.org/
[HoTT-UF-in-Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
[HSP Theorem]: https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff's_theorem
[Implicit Arguments]: https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html#implicit-arguments
[Inductive Types in Lean]: https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html
[inductive types]: https://en.wikipedia.org/wiki/Intuitionistic_type_theory#Inductive_types
[Jeremy Avigad]: http://www.andrew.cmu.edu/user/avigad/
[lattice.lean]: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/lattice.lean
[Lean]: https://leanprover.github.io/
[Lean 2]: https://github.com/leanprover/lean2
[Lean 4]: https://github.com/leanprover/lean4
[lean extension]: https://github.com/leanprover/vscode-lean
[Lean github repository]:  https://github.com/leanprover/lean/
[Lean Reference Manual]: https://leanprover.github.io/reference/
[Lean Standard Library]: https://github.com/leanprover/lean
[Lean Tutorial]: https://leanprover.github.io/tutorial/
[Lean Universal Algebra Library]: https://github.com/UniversalAlgebra/lean-ualib/
[Libor Barto]: http://www.karlin.mff.cuni.cz/~barto/
[`lean/library/init`]: https://github.com/leanprover/lean/tree/master/library/init
[`lean/library/init/algebra`]: https://github.com/leanprover/lean/blob/master/library/init/algebra
[`lean/library/init/data`]: https://github.com/leanprover/lean/tree/master/library/init/data
[lean_src]: https://github.com/leanprover/lean
[Logic and Proof]: https://leanprover.github.io/logic_and_proof/
[logic.lean]: https://github.com/leanprover/lean/blob/master/library/init/logic.lean
[master]: https://gitlab.com/ualib/lean-ualib/tree/master
[Mathlib]: https://github.com/leanprover-community/mathlib/
[Mathlib documentation]: https://leanprover-community.github.io/papers/mathlib-paper.pdf
[`mathlib/src/data/set/basic.lean`]: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/basic.lean
[Miklós Maróti]: http://www.math.u-szeged.hu/~mmaroti/
[More on Implicit Arguments]: https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html?highlight=implicit#more-on-implicit-arguments
[`nat/`]: https://github.com/leanprover/lean/blob/master/library/init/data/nat
[NuPRL]: http://www.nuprl.org/
[OPLSS 2018]: https://www.cs.uoregon.edu/research/summerschool/summer18/topics.php#Bauer
[order.lean]: https://github.com/leanprover/lean/blob/master/library/init/algebra/order.lean
[prod.lean]: https://github.com/leanprover/lean/blob/master/library/init/data/prod.lean
[Peter Mayr]: http://math.colorado.edu/~mayr/
[Programming Languages Foundations in Agda]: https://plfa.github.io/
[proof assistant]: https://en.wikipedia.org/wiki/Proof_assistant
[proof tactics]: https://en.wikipedia.org/wiki/Tactic_(proof_assistant)
[propext.lean]: https://github.com/leanprover/lean/blob/master/library/init/propext.lean
[quot.lean]: https://github.com/leanprover/lean/blob/master/library/init/data/quot.lean
[quotient.lean]: https://gitlab.com/ualib/lean-ualib/blob/william/src/quotient.lean
[Ralph Freese]: https://math.hawaii.edu/~ralph/
[reading material]: https://arxiv.org/abs/1807.05923
[set.lean]: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean
[setoid.lean]: https://github.com/leanprover/lean/blob/master/library/init/data/setoid.lean
[`sigma/`]: https://github.com/leanprover/lean/blob/master/library/init/data/sigma/
[`sigma/basic.lean`]: https://github.com/leanprover/lean/blob/master/library/init/data/sigma/basic.lean
[Siva Somayyajula]: http://www.cs.cmu.edu/~ssomayya/
[Theorem Proving in Lean]: https://leanprover.github.io/theorem_proving_in_lean/index.html
[this gist]: https://gist.github.com/andrejbauer/3cc438ab38646516e5e9278fdb22022c
[TPL]: https://leanprover.github.io/theorem_proving_in_lean/
[type theory]: https://en.wikipedia.org/wiki/Type_theory
[Type Theory and Formal Proof]: <https://www.cambridge.org/vi/academic/subjects/computer-science/programming-languages-and-applied-logic/type-theory-and-formal-proof-introduction>`_
[Type Topology]: <https://github.com/martinescardo/TypeTopology>`_
[Univalent Foundations with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#additionalexercisessol
[Venanzio Capretta]: https://www.duplavis.com/venanzio/
[vscode]: https://code.visualstudio.com/
[wf.lean]: https://github.com/leanprover/lean/blob/master/library/init/wf.lean
[william]: https://gitlab.com/ualib/lean-ualib/tree/william
[Introduction to Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html
[Computer Aided Formal Reasoning]: http://www.cs.nott.ac.uk/~psztxa/g53cfr/
[Dependent Types at Work]: http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf
[Dependently Typed Programming in Agda]: http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf
[Programming Language Foundations in Agda]: https://plfa.github.io/
[prelude module]: https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/prelude.lagda.rst
[basic module]: https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/basic.lagda.rst
[congruences module]: https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst
[homomorphisms module]: https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/homomorphisms.lagda.rst
[terms module]: https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/terms.lagda.rst
[subuniverses module]: https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/subuniverses.lagda.rst
[closure module]: https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst
[birkhoff module]: https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/birkhoff.lagda.rst
