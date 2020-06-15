--FILE: UF-Extensionality.agda
--DATE: 4 Apr 2020
--UPDATE: 23 May 2020
--BLAME: williamdemeo@gmail.com
--REF: Much of this file is based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua
--      https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#hfunext
--      In particular, the quoted comments below, along with sections of code to which those comments refer, are due to Martin Escardo.
--      Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Extensionality where

-- open import Data.Bool using (Bool; true; false)

open import UF-Prelude using (Universe; 𝓘; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; _⁺; _̇;_⊔_; 𝓤ω; 𝑖𝑑; id; ℕ; is-empty; 𝟘; !𝟘; ¬; zero; succ; _∘_; _,_; _×_; Σ; -Σ; pr₁; pr₂; Π; -Π; _+_; inl; inr; domain; codomain; _≡_; refl; ap;_≡⟨_⟩_;_∎;_∼_; transport; _⁻¹; _⇔_; Epic; EpicInv; InvIsInv; Id; 𝟙; 𝟚; ₀; ₁; ≡-elim-right; 𝟙-is-not-𝟘; ∣_∣; ∥_∥)

open import UF-Singleton using (is-center; is-set; is-singleton; is-subsingleton; center;centrality; singletons-are-subsingletons; pointed-subsingletons-are-singletons; EM; is-prop; 𝟙-is-singleton)

open import UF-Equality using (Nat; NatΣ; subsingletons-are-sets; _is-of-hlevel_; to-Σ-≡'; singletons-are-sets; wconstant; Hedberg; types-with-wconstant-≡-endomaps-are-sets; to-Σ-≡; singleton-types'-are-singletons; _◁_; retract-of-singleton; has-section; singleton-type; _≃_; fiber; is-equiv; invertible; id-is-equiv; invertibles-are-equivs; inv-elim-left; inv-elim-right; inverse; equivs-are-invertible; ≃-gives-▷; _●_; ≃-sym; Σ-≡-≃; Σ-cong; _≃⟨_⟩_; _■; Σ-flip; ∘-is-equiv; inversion-involutive; invertibility-gives-≃; inverses-are-sections; inverses-are-retractions)

open import UF-Univalence using (is-univalent; equivs-are-lc; ΠΣ-distr-≃; maps-of-singletons-are-equivs; NatΣ-equiv-gives-fiberwise-equiv; pr₁-equiv; Eq→Id; to-subtype-≡; Id→Eq; subsingleton-criterion'; equiv-to-subsingleton; has-retraction; joyal-equivs-are-invertible; is-joyal-equiv; ×-is-subsingleton'; Σ-assoc; Σ-is-subsingleton; logically-equivalent-subsingletons-are-equivalent; Id→fun; ×-is-subsingleton; 𝕁-equiv; is-hae; transport-ap-≃; haes-are-equivs; transport-map-along-≃)

--------------------------------------------------------------------------------------------

-- Function extensionality from univalence
funext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g
-- (N.B. funext is known to be independent of MLTT)

--"*Exercise*. Assuming `funext`, prove that if a function `f : X → Y` is an equivalence then so is the
-- precomposition map `_∘ f : (Y → Z) → (X → Z)`."
--SOLUTION.
module _ (feuw : funext 𝓤 𝓦) (fewu : funext 𝓦 𝓤) (feuv : funext 𝓤 𝓥)(fevw : funext 𝓥 𝓦)
  {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇} (f : X → Y) where

  _∘f : (g : Y → Z) → (X → Z)
  g ∘f = g ∘ f

  fequiv-implies-_∘fequiv : is-equiv f → is-equiv _∘f
  fequiv-implies-_∘fequiv  fequiv = invertibles-are-equivs _∘f postcomp-is-invertible
   where
    f⁻¹ : Y → X
    f⁻¹ = inverse f fequiv

    _∘finv : (X → Z) → (Y → Z)
    gf ∘finv = λ y → gf (f⁻¹ y)

    ∘f∼∘finv : ( _∘f ) ∘ ( _∘finv ) ∼ id
    ∘f∼∘finv gf = feuw (λ x → ap (λ - → gf -) (inv-elim-left f fequiv x) )

    ∘finv∼∘f : ( _∘finv ) ∘ ( _∘f ) ∼ id
    ∘finv∼∘f g = fevw λ y → ap (λ - → g -) ((inv-elim-right f fequiv y))

    postcomp-is-invertible : invertible _∘f
    postcomp-is-invertible = _∘finv , ∘finv∼∘f , ∘f∼∘finv


--"The crucial step in Voevodsky's proof (see: https://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf )
-- that univalence implies funext is to establish the conclusion of the above exer. assuming univalence instead."
--(the proof here is by equivalence induction on f)

precomp-is-equiv : is-univalent 𝓤
 →                 (X Y : 𝓤 ̇)   (f : X → Y)
 →                 is-equiv f  →  (Z : 𝓤 ̇ )
                  ---------------------------------
 →                 is-equiv (λ (g : Y → Z) → g ∘ f)
precomp-is-equiv {𝓤} ua =  𝕁-equiv ua
  ( λ X Y (f : X → Y) → (Z : 𝓤 ̇ ) → is-equiv (λ g → g ∘ f) )
  ( λ X Z → id-is-equiv (X → Z) )

--"With this we can prove the desired result as follows.
univalence-gives-funext : is-univalent 𝓤 → funext 𝓥 𝓤
univalence-gives-funext {𝓤} {𝓥} ua {X} {Y} {f₀} {f₁} = γ
 where
  Δ : 𝓤 ̇
  Δ = Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ≡ y₁

  δ : Y → Δ
  δ y = (y , y , refl y)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = invertibles-are-equivs δ (π₀ , η , ε)
   where
    η : (y : Y) → π₀ (δ y) ≡ y
    η y = refl y

    ε : (d : Δ) → δ (π₀ d) ≡ d
    ε (y , y , refl y) = refl (y , y , refl y)

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = precomp-is-equiv ua Y Δ δ δ-is-equiv Y

  p : φ π₀ ≡ φ π₁
  p = refl (𝑖𝑑 Y)

  q : π₀ ≡ π₁
  q = equivs-are-lc φ φ-is-equiv p

  γ : f₀ ∼ f₁ → f₀ ≡ f₁
  γ h = ap (λ π x → π (f₀ x , f₁ x , h x)) q

--"This definition of `γ` is probably too concise. Here are all the steps performed silently by Agda,
-- by expanding judgmental equalities, indicated with `refl` here:
  γ' : f₀ ∼ f₁ → f₀ ≡ f₁
  γ' h = f₀                        ≡⟨ refl _                               ⟩
    (λ x → f₀ x)                   ≡⟨ refl _                               ⟩
    (λ x → π₀ (f₀ x , f₁ x , h x)) ≡⟨ ap (λ - x → - (f₀ x , f₁ x , h x)) q ⟩
    (λ x → π₁ (f₀ x , f₁ x , h x)) ≡⟨ refl _                               ⟩
    (λ x → f₁ x)                   ≡⟨ refl _                               ⟩
    f₁                             ∎

--"So notice that this relies on the so-called η-rule for judgmental equality of functions, namely
-- `f = λ x → f x`. Without it, we would only get that `f₀ ∼ f₁ → (λ x → f₀ x) ≡ (λ x → f₁ x)` instead.

-----------------------------------------------------------------------
--Variations of function extensionality and their logical equivalence.

--"Dependent function extensionality:
dfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
dfunext 𝓤 𝓥 = {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g : Π A} → f ∼ g → f ≡ g

--"The above says that there is some map `f ~ g → f ≡ g`.  The following instead says that the
-- canonical map `happly` in the other direction is an equivalence:
happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → f ≡ g → f ∼ g
happly f g p x = ap (λ - → - x) p

hfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
hfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → is-equiv (happly f g)

hfunext-gives-dfunext : hfunext 𝓤 𝓥 → dfunext 𝓤 𝓥
hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)

--"Voevodsky showed that all these notions of function extensionality are logically equivalent to saying
-- that products of singletons are singletons:
vvfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
vvfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
 →              ((x : X) → is-singleton (A x))
                ------------------------------
 →                 is-singleton (Π A)

dfunext-gives-vvfunext : dfunext 𝓤 𝓥 → vvfunext 𝓤 𝓥
dfunext-gives-vvfunext fe {X} {A} Ax✦ = γ
 where
  f : Π A
  f x = center (A x) (Ax✦ x)

  c : (g : Π A) → f ≡ g
  c g = fe (λ (x : X) → centrality (A x) (Ax✦ x) (g x))

  γ : is-singleton (Π A)
  γ = f , c

--"We need some lemmas to get `hfunext` from `vvfunext`:
postcomp-invertible : {X : 𝓤 ̇}{Y : 𝓥 ̇}{A : 𝓦 ̇}
 →               funext 𝓦 𝓤   →   funext 𝓦 𝓥
 →               (f : X → Y)    →   invertible f
                  ---------------------------------
 →               invertible (λ (h : A → X) → f ∘ h)
postcomp-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = γ
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h

  g' : (A → Y) → (A → X)
  g' k = g ∘ k

  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = nfe (η ∘ h)

  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = nfe' (ε ∘ k)

  γ : invertible f'
  γ = (g' , η' , ε')

postcomp-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
 →                funext 𝓦 𝓤   →   funext 𝓦 𝓥
 →                (f : X → Y)    →   is-equiv f
                 ----------------------------------
 →                is-equiv (λ (h : A → X) → f ∘ h)

postcomp-is-equiv fe fe' f feq = invertibles-are-equivs  (λ h → f ∘ h)
  ( postcomp-invertible fe fe' f (equivs-are-invertible f feq) )

vvfunext-gives-hfunext : vvfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
vvfunext-gives-hfunext vfe {X} {Y} f = γ
 where
  a : (x : X) → is-singleton (Σ y ꞉ Y x , f x ≡ y)
  a x = singleton-types'-are-singletons (Y x) (f x)

  c : is-singleton (Π x ꞉ X , Σ y ꞉ Y x , f x ≡ y)
  c = vfe a

  ρ : (Σ g ꞉ Π Y , f ∼ g) ◁ (Π x ꞉ X , Σ y ꞉ Y x , f x ≡ y)
  ρ = ≃-gives-▷ ΠΣ-distr-≃

  d : is-singleton (Σ g ꞉ Π Y , f ∼ g)
  d = retract-of-singleton ρ c

  e : (Σ g ꞉ Π Y , f ≡ g) → (Σ g ꞉ Π Y , f ∼ g)
  e = NatΣ (happly f)

  i : is-equiv e
  i = maps-of-singletons-are-equivs e (singleton-types'-are-singletons (Π Y) f) d

  γ : (g : Π Y) → is-equiv (happly f g)
  γ = NatΣ-equiv-gives-fiberwise-equiv (happly f) i

--"And finally the seemingly rather weak, non-dependent version `funext` implies the seemingly
-- strongest version, which closes the circle of logical equivalences.
funext-gives-vvfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → vvfunext 𝓤 𝓥
funext-gives-vvfunext {𝓤} {𝓥} fe fe' {X} {A} φ = γ
 where
  f : Σ A → X
  f = pr₁

  f-is-equiv : is-equiv f
  f-is-equiv = pr₁-equiv φ

  g : (X → Σ A) → (X → X)
  g h = f ∘ h

  geq : is-equiv g
  geq = postcomp-is-equiv fe fe' f f-is-equiv

  ΣAx✦ : is-singleton (Σ h ꞉ (X → Σ A), f ∘ h ≡ 𝑖𝑑 X)
  ΣAx✦ = geq (𝑖𝑑 X)

  r : (Σ h ꞉ (X → Σ A), f ∘ h ≡ 𝑖𝑑 X) → Π A
  r (h , p) x = transport A (happly (f ∘ h) (𝑖𝑑 X) p x) (pr₂ (h x))

  s : Π A → (Σ h ꞉ (X → Σ A), f ∘ h ≡ 𝑖𝑑 X)
  s φ = (λ x → x , φ x) , refl (𝑖𝑑 X)

  η : ∀ φ → r (s φ) ≡ φ
  η φ = refl (r (s φ))

  γ : is-singleton (Π A)
  γ = retract-of-singleton (r , s , η) ΣAx✦

--"We have the following corollaries. We first formulate the types of some functions:
abstract
 funext-gives-hfunext       : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → hfunext 𝓤 𝓥
 dfunext-gives-hfunext      : dfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
 funext-gives-dfunext       : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → dfunext 𝓤 𝓥
 univalence-gives-dfunext'  : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
 univalence-gives-hfunext'  : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → hfunext 𝓤 𝓥
 univalence-gives-vvfunext' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → vvfunext 𝓤 𝓥
 univalence-gives-hfunext   : is-univalent 𝓤 → hfunext 𝓤 𝓤
 univalence-gives-dfunext   : is-univalent 𝓤 → dfunext 𝓤 𝓤
 univalence-gives-vvfunext  : is-univalent 𝓤 → vvfunext 𝓤 𝓤

--"And then we give their definitions (Agda makes sure there are no circularities):
 funext-gives-hfunext fe fe' = vvfunext-gives-hfunext (funext-gives-vvfunext fe fe')
 funext-gives-dfunext fe fe' = hfunext-gives-dfunext (funext-gives-hfunext fe fe')
 dfunext-gives-hfunext fe = vvfunext-gives-hfunext (dfunext-gives-vvfunext fe)
 univalence-gives-dfunext' 𝓤★ 𝓤𝓥★ = funext-gives-dfunext
    ( univalence-gives-funext 𝓤𝓥★ )  ( univalence-gives-funext 𝓤★ )
 univalence-gives-hfunext' 𝓤★ 𝓤𝓥★ = funext-gives-hfunext
    (univalence-gives-funext 𝓤𝓥★)  (univalence-gives-funext 𝓤★ )
 univalence-gives-vvfunext' 𝓤★ 𝓤𝓥★ = funext-gives-vvfunext
    (univalence-gives-funext 𝓤𝓥★)  (univalence-gives-funext 𝓤★ )
 univalence-gives-hfunext 𝓤★ = univalence-gives-hfunext' 𝓤★ 𝓤★
 univalence-gives-dfunext 𝓤★ = univalence-gives-dfunext' 𝓤★ 𝓤★
 univalence-gives-vvfunext 𝓤★ = univalence-gives-vvfunext' 𝓤★ 𝓤★

---------------------------------------------------------------------
--"Universes are map classifiers.
-- Under univalence, a universe `𝓤` becomes a map classifier, in the sense that maps from a type `X`
-- in `𝓤` into a type `Y` in `𝓤` are in canonical bijection with functions `Y → 𝓤`. Using the following
-- slice notation, this amounts to a bijection between `𝓤 / Y` and `Y → 𝓤`:
_/_ : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 / Y = Σ X ꞉ 𝓤 ̇ , (X → Y)

{-Recall, if 𝓤 is a category, and Y an object of 𝓤, then the slice category is denoted 𝓤 / Y; it has
   objects   : arrows f : X → Y and
   morphisms : functions g : X → X' such that f' ∘ g = f, where f' : X' → Y is an object of 𝓤 / Y.

      X --- g --> X'
       \         /
        f       f'
         \     /
          ↘   ↙
            Y                                              -}

--"We need the following lemma, which has other uses:
total-fiber-is-domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                        --------------------------------
 →                             Σ (fiber f) ≃ X
total-fiber-is-domain {𝓤}{𝓥}{X}{Y} f = invertibility-gives-≃ g ( h , h∼g , g∼h)
  where
    g : (Σ y ꞉ Y , Σ x ꞉ X , f x ≡ y) → X
    g (y , x , p) = x

    h : X → Σ y ꞉ Y , Σ x ꞉ X , f x ≡ y
    h x = f x , x , refl (f x)

    h∼g : ∀ t → h (g t) ≡ t
    h∼g (_ , x , refl _) = refl (f x , x , refl (f x))

    g∼h : (x : X) → g (h x) ≡ x
    g∼h = refl

--"The function `χ` gives the *characteristic function* of a map into `Y`:
χ : (Y : 𝓤 ̇) → 𝓤 / Y → (Y → 𝓤 ̇)
χ Y (X , f) = fiber f

--"We say that a universe is a *map classifier* if the above function is an equivalence for every `Y` in 𝓤 ̇
is-map-classifier : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-map-classifier 𝓤 = (Y : 𝓤 ̇) → is-equiv (χ Y)

--"Any `Y → 𝓤` is the characteristic function of some map into `Y` by taking its total space and the 1st proj:
𝕋 : (Y : 𝓤 ̇) → (Y → 𝓤 ̇) → 𝓤 / Y
𝕋 Y A = Σ A , pr₁

χη : is-univalent 𝓤
 →   (Y : 𝓤 ̇) (σ : 𝓤 / Y)
     -----------------------
 →    𝕋 Y (χ Y σ) ≡ σ

χη 𝓤★ Y (X , f) = r
  where
    e : Σ (fiber f) ≃ X
    e = total-fiber-is-domain f

    p : Σ (fiber f) ≡ X
    p = Eq→Id 𝓤★ ( Σ (fiber f) ) X e

    observation : ∣ ≃-sym e ∣ ≡ ( λ x → f x , x , refl (f x) )
    observation = refl _ -- (λ x → f x , x , refl (f x))

    q : transport (λ - → - → Y) p pr₁ ≡ f
    q = transport (λ - → - → Y) p pr₁  ≡⟨ transport-map-along-≃ 𝓤★ e pr₁ ⟩
          pr₁ ∘  ∣ ≃-sym e ∣                 ≡⟨ refl f ⟩
          f                                          ∎

    r : (Σ (fiber f) , pr₁) ≡ (X , f)
    r = to-Σ-≡ (p , q)

χε : is-univalent 𝓤
 →   dfunext 𝓤 (𝓤 ⁺)
 →   (Y : 𝓤 ̇) (A : Y → 𝓤 ̇)
     ------------------------
 →    χ Y (𝕋 Y A) ≡ A

χε 𝓤★ fe Y A = fe γ
  where
    f : ∀ y → fiber pr₁ y → A y
    f y ( (y , a) , refl p) = a

    g : ∀ y → A y → fiber pr₁ y
    g y a = (y , a) , refl y

    g∼f : ∀ y σ → g y (f y σ) ≡ σ
    g∼f y ( (y , a) , refl p) = refl ( (y , a) , refl p)

    f∼g : ∀ y a → f y (g y a) ≡ a
    f∼g y a = refl a

    γ : ∀ y → fiber pr₁ y ≡ A y
    γ y = Eq→Id 𝓤★ _ _ (invertibility-gives-≃ (f y) (g y , g∼f y , f∼g y) )

universes-are-map-classifiers : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                                ----------------------------------
 →                                    is-map-classifier 𝓤

universes-are-map-classifiers 𝓤★ fe Y = invertibles-are-equivs (χ Y) ( 𝕋 Y , χη 𝓤★ Y , χε 𝓤★ fe Y )

--"Therefore we have the following canonical equivalence:
map-classification : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺) → (Y : 𝓤 ̇)
                    ------------------------------------------------
 →                        𝓤 / Y   ≃   (Y → 𝓤 ̇)
map-classification 𝓤★ fe Y = χ Y , universes-are-map-classifiers 𝓤★ fe Y

-------------------------------------------------------------------------------------------------
--"The univalence axiom is a (sub) singleton.
-- If we use a type as an axiom, it should better have at most one element.)

--"We prove some generally useful lemmas first.
Π-is-subsingleton : dfunext 𝓤 𝓥
 →          {X : 𝓤 ̇} {A : X → 𝓥 ̇}
 →          ((x : X) → is-subsingleton (A x))
            ---------------------------------
 →           is-subsingleton (Π A)

Π-is-subsingleton fe Ax✧ f g = fe (λ x → Ax✧ x (f x) (g x))

being-singleton-is-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇} → is-subsingleton (is-singleton X)
being-singleton-is-subsingleton fe {X} (x , φ) (y , γ) = p
 where
 i : is-subsingleton X
 i = singletons-are-subsingletons X (y , γ)

 s : is-set X
 s = subsingletons-are-sets X i

 a : (z : X) → is-subsingleton ((t : X) → z ≡ t)
 a z = Π-is-subsingleton fe (s z)

 b : x ≡ y
 b = φ y

 p : (x , φ) ≡ (y , γ)
 p = to-subtype-≡ a b

being-equiv-is-subsingleton : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 →                            {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                              -----------------------------------
 →                              is-subsingleton (is-equiv f)
being-equiv-is-subsingleton fe fe' f =
  Π-is-subsingleton fe (λ x → being-singleton-is-subsingleton fe')


--"In passing, we fulfill a promise made above:
subsingletons-are-retracts-of-logically-equivalent-types :
           {X : 𝓤 ̇}{Y : 𝓥 ̇}
 →         is-subsingleton X
 →         (X ⇔ Y)
          --------------------
 →          X ◁ Y
subsingletons-are-retracts-of-logically-equivalent-types X✧ (f , g) =
 g , f , η
  where
   η : g ∘ f ∼ id
   η x = X✧ (g (f x)) x

equivalence-property-is-retract-of-invertibility-data :
      dfunext 𝓥 (𝓤 ⊔ 𝓥)  →  dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 →    {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
      --------------------------------
 →       is-equiv f ◁ invertible f

equivalence-property-is-retract-of-invertibility-data fe fe' f =
   subsingletons-are-retracts-of-logically-equivalent-types
     (being-equiv-is-subsingleton fe fe' f) (equivs-are-invertible f , invertibles-are-equivs f)

--"We now return to our main concern in this section.
univalence-is-subsingleton : is-univalent (𝓤 ⁺) → is-subsingleton (is-univalent 𝓤)
univalence-is-subsingleton {𝓤} 𝓤⁺★ = subsingleton-criterion' γ
 where
  γ : is-univalent 𝓤 → is-subsingleton (is-univalent 𝓤)
  γ 𝓤★ = goal
   where
    dfe₁ : dfunext 𝓤 (𝓤 ⁺)
    dfe₂ : dfunext (𝓤 ⁺) (𝓤 ⁺)

    dfe₁ = univalence-gives-dfunext' 𝓤★ 𝓤⁺★
    dfe₂ = univalence-gives-dfunext 𝓤⁺★

    goal : is-subsingleton (is-univalent 𝓤)
    goal  = Π-is-subsingleton dfe₂
                ( λ X → Π-is-subsingleton dfe₂
                  ( λ Y → being-equiv-is-subsingleton dfe₁ dfe₂ (Id→Eq X Y) ) )

{-"So if all universes are univalent then "being univalent" is a subsingleton, and hence a singleton.
   This hypothesis of global univalence cannot be expressed in our MLTT that only has `ω` many universes,
   because global univalence would have to live in the first universe after them. Agda does have such a
   universe `𝓤ω,` and so we can formulate it here. -}
Univalence : 𝓤ω
Univalence = ∀ 𝓤 → is-univalent 𝓤

univalence-is-subsingletonω : Univalence → is-subsingleton (is-univalent 𝓤)
univalence-is-subsingletonω {𝓤} 𝓤★ = univalence-is-subsingleton ( 𝓤★ (𝓤 ⁺) )

univalence-is-singleton : Univalence → is-singleton (is-univalent 𝓤)
univalence-is-singleton {𝓤} 𝓤★ =
  pointed-subsingletons-are-singletons (is-univalent 𝓤) (𝓤★ 𝓤) (univalence-is-subsingletonω 𝓤★)

--"It follows immediately from the above that global univalence gives global function extensionality.
global-dfunext : 𝓤ω
global-dfunext = ∀ {𝓤 𝓥} → dfunext 𝓤 𝓥

global-funext : 𝓤ω
global-funext = ∀ {𝓤 𝓥} → funext 𝓤 𝓥

univalence-gives-global-dfunext : Univalence → global-dfunext
univalence-gives-global-dfunext 𝓤★ {𝓤}{𝓥} = univalence-gives-dfunext' (𝓤★ 𝓤) ( 𝓤★ (𝓤 ⊔ 𝓥) )

global-hfunext : 𝓤ω
global-hfunext = ∀ {𝓤 𝓥} → hfunext 𝓤 𝓥

univalence-gives-global-hfunext : Univalence → global-hfunext
univalence-gives-global-hfunext 𝓤★ {𝓤}{𝓥} = univalence-gives-hfunext' (𝓤★ 𝓤) ( 𝓤★ (𝓤 ⊔ 𝓥) )

-----------------------------------------------------------------------------------
--Unique existence in univalent mathematics.
{-"Unique existence of `x : X` with `A x` in univalent mathematics, written `∃! x ꞉ X , A x` or simply
   `∃! A`, requires that not only the `x : X` but also the `a : A x` to be unique. More precisely, we
   require that there is a unique PAIR `(x , a) : Σ A`. This is particularly important in the formulation
   of universal properties involving types that are not necessarily sets, where it generalizes the
   categorical notion of uniqueness up to unique isomorphism.           -}

∃! : {X : 𝓤 ̇} → (X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
∃! A = is-singleton (Σ A)
infixr -1 ∃!

-∃! : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-∃! X Y = ∃! Y
infixr -1 -∃!
syntax -∃! A (λ x → b) = ∃! x ꞉ A , b

∃!-is-subsingleton : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → is-subsingleton (∃! A)
∃!-is-subsingleton A fe = being-singleton-is-subsingleton fe

unique-existence-gives-weak-unique-existence :
                {X : 𝓤 ̇}  (A : X → 𝓥 ̇)
 →              (∃! x ꞉ X , A x)
                ---------------------------------------------------
 →              (Σ x ꞉ X , A x) × ( (x y : X) → A x → A y → x ≡ y )
unique-existence-gives-weak-unique-existence A s = center (Σ A) s , u
 where
  u : ∀ x y → A x → A y → x ≡ y
  u x y a b = ap pr₁ (singletons-are-subsingletons (Σ A) s (x , a) (y , b))

--"The converse holds if each `A x` is a subsingleton:
weak-unique-existence-gives-unique-existence-sometimes :
        {X : 𝓤 ̇}  (A : X → 𝓥 ̇)
 →      ((x : X) → is-subsingleton (A x))
 →      (Σ x ꞉ X , A x) × ((x y : X) → A x → A y → x ≡ y)
       ----------------------------------------------------
 →      (∃! x ꞉ X , A x)

weak-unique-existence-gives-unique-existence-sometimes A Ax✧ ((x , a) , u) = (x , a) , φ
 where
  φ : (σ : Σ A) → x , a ≡ σ
  φ (y , b) = to-subtype-≡ Ax✧  (u x y a b)

--"*Exercise*. Find a counter-example in the absence of the requirement that all types `A x` are subsingletons.

--"Similarly, the existence of at most one `x : X` with `A x` should be understood as `is-subsingleton (Σ A)`, but we will not
-- introduce special notation for this concept, although it will occur often.

-------------------------------------------------------------------
-- Universal property of the natural numbers
-- -------------------------------------
-- (skipping for now)

---------------------------------------------------
-- More consequences of function extensionality
-- ---------------------------------------
being-subsingleton-is-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-subsingleton (is-subsingleton X)
being-subsingleton-is-subsingleton fe {X} X✧ X✧' = X✧≡X✧'
 where
  Xset : is-set X
  Xset = subsingletons-are-sets X X✧

  a : (x y : X) → X✧ x y ≡ X✧' x y
  a x y = Xset x y (X✧ x y) (X✧' x y)

  b : (x : X) → X✧ x ≡ X✧' x
  b x = fe (a x)

  X✧≡X✧' : X✧ ≡ X✧'
  X✧≡X✧' = fe b

being-center-is-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ } (c : X) → is-subsingleton (is-center X c)
being-center-is-subsingleton fe {X} c φ ψ = φ≡ψ
 where
  ζ : is-singleton X
  ζ = c , ψ

  ξ : (x : X) → is-subsingleton (c ≡ x)
  ξ x = singletons-are-sets X ζ c x

  φ≡ψ : φ ≡ ψ
  φ≡ψ = fe (λ x → ξ x (φ x) (ψ x))

--"Here the version `hfunext` of function extensionality is what is needed:
Π-is-set : hfunext 𝓤 𝓥  → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
             ----------------------------------------
 →              ( (x : X) → is-set (A x) ) → is-set (Π A)

Π-is-set hfe Ax-is-set f g = γ
 where
  f∼g✧ : is-subsingleton (f ∼ g)
  f∼g✧ p q = hfunext-gives-dfunext hfe (λ x → Ax-is-set x (f x) (g x) (p x) (q x))

  ξ : (f ≡ g) ≃ (f ∼ g)
  ξ = ( happly f g , hfe f g )

  γ : is-subsingleton (f ≡ g)
  γ = equiv-to-subsingleton ξ f∼g✧

being-set-is-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ }
                                 --------------------------
 →                                is-subsingleton (is-set X)

being-set-is-subsingleton fe = Π-is-subsingleton fe (λ x → Π-is-subsingleton fe (λ y → being-subsingleton-is-subsingleton fe) )

--"More generally:
hlevel-relation-is-subsingleton : dfunext 𝓤 𝓤 → (n : ℕ) (X : 𝓤 ̇ )
                                      -----------------------------------
 →                                      is-subsingleton (X is-of-hlevel n)

hlevel-relation-is-subsingleton {𝓤} fe zero X = being-singleton-is-subsingleton fe
hlevel-relation-is-subsingleton {𝓤} fe (succ n) X =
  Π-is-subsingleton fe  (λ x → Π-is-subsingleton fe
                                  ( λ x' → hlevel-relation-is-subsingleton fe n (x ≡ x') ) )

--"Composition of equivalences is associative:
●-assoc : dfunext 𝓣 (𝓤 ⊔ 𝓣) → dfunext (𝓤 ⊔ 𝓣) (𝓤 ⊔ 𝓣)
 →                    {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {T : 𝓣 ̇ }
                         (α : X ≃ Y) (β : Y ≃ Z) (γ : Z ≃ T)
                      ------------------------------------------
 →                       α ● (β ● γ) ≡ (α ● β) ● γ

●-assoc fe fe' (f , feq) (g , geq) (h , heq) = ap ( h ∘ g ∘ f ,_ ) q
 where
  ξ ζ : is-equiv (h ∘ g ∘ f)
  ξ = ∘-is-equiv (∘-is-equiv heq geq) feq
  ζ = ∘-is-equiv heq (∘-is-equiv geq feq)

  q : ξ ≡ ζ
  q = being-equiv-is-subsingleton fe fe' (h ∘ g ∘ f) _ _

≃-sym-involutive : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 →                    {X : 𝓤 ̇ }  {Y : 𝓥 ̇ }   (α : X ≃ Y)
                       --------------------------------
 →                     ≃-sym (≃-sym α) ≡ α

≃-sym-involutive fe fe' (f , a) =
  to-subtype-≡ (being-equiv-is-subsingleton fe fe') (inversion-involutive f a)

≃-sym-is-equiv : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 →                  {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    -------------------------------
 →                  is-equiv (≃-sym {𝓤} {𝓥} {X} {Y})

≃-sym-is-equiv fe₀ fe₁ fe₂ = invertibles-are-equivs ≃-sym
  (≃-sym ,  ≃-sym-involutive fe₀ fe₂ ,  ≃-sym-involutive fe₁ fe₂)

--"*Exercise*. The hlevels are closed under `Σ` and, using `hfunext`, also under `Π`. Univalence is not needed, but makes the proof easier.
-- (Without univalence, we need to show that the hlevels are closed under equivalence first.)

Π-cong : dfunext 𝓤 𝓥 → dfunext 𝓤 𝓦 → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Y' : X → 𝓦 ̇ }
 →        ( (x : X) → Y x ≃ Y' x )
           --------------------
 →             Π Y ≃ Π Y'

Π-cong fe fe' {X} {Y} {Y'} φ = invertibility-gives-≃ F (G , GF , FG)
 where
  f : (x : X) → Y x → Y' x
  f x = ∣ φ x ∣

  fxeq : (x : X) → is-equiv (f x)
  fxeq x = ∥ φ x ∥

  g : (x : X) → Y' x → Y x
  g x = inverse (f x) (fxeq x)

  fg : (x : X) (y' : Y' x) → f x (g x y') ≡ y'
  fg x = inverses-are-sections (f x) (fxeq x)

  gf : (x : X) (y : Y x) → g x (f x y) ≡ y
  gf x = inverses-are-retractions (f x) (fxeq x)

  F : ( (x : X) →  Y x ) → (x : X) → Y' x
  F φ x = f x (φ x)

  G : ( (x : X) →  Y' x ) → (x : X) → Y x
  G γ x = g x (γ x)

  FG : (γ : ( (x : X) → Y' x) ) → F (G γ) ≡ γ
  FG γ = fe' (λ x → fg x (γ x) )

  GF : (φ : ( (x : X) → Y x) ) → G (F φ) ≡ φ
  GF φ = fe (λ x → gf x (φ x) )

--"An application of `Π-cong` is `hfunext₂-≃`:
hfunext-≃ : hfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } ( f g : Π A )
              ----------------------------------------------------
 →                ( f ≡ g ) ≃ ( f ∼ g )

hfunext-≃ hfe f g = (happly f g , hfe f g)

hfunext₂-≃ : hfunext 𝓤 (𝓥 ⊔ 𝓦) → hfunext 𝓥 𝓦
 →              {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : (x : X) → Y x → 𝓦 ̇ }
                   ( f g : (x : X) (y : Y x) → A x y )
               -------------------------------------------------
 →              ( f ≡ g ) ≃ ( ∀ x y → f x y ≡ g x y )

hfunext₂-≃ fe fe' {X} f g =
  ( f ≡ g )                         ≃⟨ i ⟩
  ( ∀ x → f x ≡ g x )           ≃⟨ ii ⟩
  ( ∀ x y → f x y ≡ g x y )    ■   --  !!! CAUTION: ■ not ∎!!!
  where
   i = hfunext-≃ fe f g
   ii = Π-cong (hfunext-gives-dfunext fe) (hfunext-gives-dfunext fe)
           ( λ x → hfunext-≃ fe' (f x) (g x) )

precomp-invertible : dfunext 𝓥 𝓦 → dfunext 𝓤 𝓦 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                       (f : X → Y)    →     invertible f
                     ------------------------------
 →                  invertible (λ (h : Y → Z) → h ∘ f)

precomp-invertible fe fe' {X} {Y} {Z} f (g , g∼f , f∼g) = (g' , g'∼f' , f'∼g')
 where
  f' : (Y → Z) → (X → Z)
  f' h = h ∘ f

  g' : (X → Z) → (Y → Z)
  g' k = k ∘ g

  g'∼f' : (h : Y → Z) → g' (f' h) ≡ h
  g'∼f' h = fe ( λ y → ap h (f∼g y) )

  f'∼g' : (k : X → Z) → f' (g' k) ≡ k
  f'∼g' k = fe' (λ x → ap k (g∼f x) )

--"Recall that a function is a Joyal equivalence if it has a section and it has a retraction. We now show that this notion is a subsingleton.
-- For that purpose, we first show that if a function has a retraction then it has at most one section, and that if it has a section then it
-- has at most one retraction.
at-most-one-section : dfunext 𝓥 𝓤 → hfunext 𝓥 𝓥
 →                         {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 →                         has-retraction f
                           ----------------------------------
 →                         is-subsingleton (has-section f)

at-most-one-section {𝓥} {𝓤} fe hfe {X} {Y} f (g , g∼f) (h , f∼h) = d
 where
  fe' : dfunext 𝓥 𝓥
  fe' = hfunext-gives-dfunext hfe

  a : invertible f
  a = joyal-equivs-are-invertible f ( (h , f∼h) , g , g∼f )

  b : is-singleton (fiber (λ h →  f ∘ h) id)
  b = invertibles-are-equivs (λ h → f ∘ h) (postcomp-invertible fe fe' f a) id

  r : fiber (λ h →  f ∘ h) id → has-section f
  r (h , p) = (h , happly (f ∘ h) id p )

  s : has-section f → fiber (λ h → f ∘ h) id
  s (h , η) = h , fe' η

  rs : (σ : has-section f) → r (s σ) ≡ σ
  rs (h , η) = to-Σ-≡' q
   where
    q : happly (f ∘ h) id (inverse (happly (f ∘ h) id) (hfe (f ∘ h) id) η) ≡ η
    q = inverses-are-sections (happly (f ∘ h) id) (hfe (f ∘ h) id) η

  c : is-singleton (has-section f)
  c = retract-of-singleton (r , s , rs) b

  d : (σ : has-section f) → h , f∼h ≡ σ
  d = singletons-are-subsingletons (has-section f) c (h , f∼h)

at-most-one-retraction : hfunext 𝓤 𝓤 → dfunext 𝓥 𝓤
 →                             {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 →                             has-section f
                             --------------------------------------
 →                             is-subsingleton (has-retraction f)

at-most-one-retraction {𝓤} {𝓥} hfe fe' {X} {Y} f (g , f∼g) (h , h∼f) = d
 where
  fe : dfunext 𝓤 𝓤
  fe = hfunext-gives-dfunext hfe

  a : invertible f
  a = joyal-equivs-are-invertible f ( (g , f∼g) , (h , h∼f) )

  b : is-singleton (fiber (λ h →  h ∘ f) id)
  b = invertibles-are-equivs (λ h → h ∘ f) (precomp-invertible fe' fe f a) id

  r : fiber (λ h →  h ∘ f) id → has-retraction f
  r (h , p) = h , happly (h ∘ f) id p

  s : has-retraction f → fiber (λ h →  h ∘ f) id
  s (h , η) = h , fe η

  rs : (σ : has-retraction f) → r (s σ) ≡ σ
  rs (h , η) = to-Σ-≡' q
   where
    q : happly (h ∘ f) id (inverse (happly (h ∘ f) id) (hfe (h ∘ f) id) η) ≡ η
    q = inverses-are-sections (happly (h ∘ f) id) (hfe (h ∘ f) id) η

  c : is-singleton (has-retraction f)
  c = retract-of-singleton (r , s , rs) b

  d : (ρ : has-retraction f) → h , h∼f ≡ ρ
  d = singletons-are-subsingletons (has-retraction f) c (h , h∼f)
  --this also works:
  -- d = singletons-are-subsingletons (Σ (λ z → (x : X) → Identity.Id X (z (f x)) x)) c (h , h∼f)


being-joyal-equiv-is-subsingleton : hfunext 𝓤 𝓤 → hfunext 𝓥 𝓥 → dfunext 𝓥 𝓤
 →                                         {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 →                                         (f : X → Y)
                                             ---------------------------------------------
 →                                         is-subsingleton (is-joyal-equiv f)

being-joyal-equiv-is-subsingleton fe₀ fe₁ fe₂ f =
  ×-is-subsingleton' (at-most-one-section fe₂ fe₁ f , at-most-one-retraction fe₀ fe₂ f)

--"The fact that a function with a retraction has at most one section can also be used to prove that the notion of half adjoint equivalence is
-- property. This is because the type `is-hae f` is equivalent to the type `Σ (g , ε) ꞉ has-section f , ∀ x → (g (f x) , ε (f x)) ≡ (x , refl (f x))`,
-- where the equality is in the type `fiber f (f x)`.
being-hae-is-subsingleton : dfunext 𝓥 𝓤 → hfunext 𝓥 𝓥 → dfunext 𝓤 (𝓥 ⊔ 𝓤)
 →                                {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 →                                is-subsingleton (is-hae f)

being-hae-is-subsingleton fe₀ fe₁ fe₂ {X} {Y} f = subsingleton-criterion' γ
 where
  a = λ g ε x
    → ((g (f x) , ε (f x)) ≡ (x , refl (f x)))                                   ≃⟨ i  g ε x ⟩
      (Σ p ꞉ g (f x) ≡ x , transport (λ - → f - ≡ f x) p (ε (f x)) ≡ refl (f x)) ≃⟨ ii g ε x ⟩
      (Σ p ꞉ g (f x) ≡ x , ap f p ≡ ε (f x))                                     ■
   where
    i  = λ g ε x → Σ-≡-≃ (g (f x) , ε (f x)) (x , refl (f x))
    ii = λ g ε x → Σ-cong (λ p → transport-ap-≃ f p (ε (f x)))

  b = (Σ (g , ε) ꞉ has-section f , ∀ x → (g (f x) , ε (f x)) ≡ (x , refl (f x)))         ≃⟨ i   ⟩
      (Σ (g , ε) ꞉ has-section f , ∀ x → Σ  p ꞉ g (f x) ≡ x , ap f p ≡ ε (f x))          ≃⟨ ii  ⟩
      (Σ g ꞉ (Y → X) , Σ ε ꞉ f ∘ g ∼ id , ∀ x → Σ  p ꞉ g (f x) ≡ x , ap f p ≡ ε (f x))   ≃⟨ iii ⟩
      (Σ g ꞉ (Y → X) , Σ ε ꞉ f ∘ g ∼ id , Σ η ꞉ g ∘ f ∼ id , ∀ x → ap f (η x) ≡ ε (f x)) ≃⟨ iv  ⟩
      is-hae f                                                                           ■
   where
    i   = Σ-cong (λ (g , ε) → Π-cong fe₂ fe₂ (a g ε))
    ii  = Σ-assoc
    iii = Σ-cong (λ g → Σ-cong (λ ε → ΠΣ-distr-≃))
    iv  = Σ-cong (λ g → Σ-flip)

  γ : is-hae f → is-subsingleton (is-hae f)
  γ (g₀ , ε₀ , η₀ , τ₀) = is-hae-f✧
   where
    c : (x : X) → is-set (fiber f (f x))
    c x = singletons-are-sets ( fiber f (f x) ) (haes-are-equivs f (g₀ , ε₀ , η₀ , τ₀) (f x) )

    d : ((g , ε) : has-section f) → is-subsingleton (∀ x → (g (f x) , ε (f x)) ≡ (x , refl (f x)))
    d (g , ε) = Π-is-subsingleton fe₂ ( λ x → c x ( g (f x) , ε (f x) ) ( x , refl (f x) ) )

    e : is-subsingleton (Σ (g , ε) ꞉ has-section f , ∀ x → (g (f x) , ε (f x)) ≡ (x , refl (f x)))
    e = Σ-is-subsingleton (at-most-one-section fe₀ fe₁ f (g₀ , ε₀) ) d

    is-hae-f✧ : is-subsingleton (is-hae f)
    is-hae-f✧ = equiv-to-subsingleton (≃-sym b) e

--"Another consequence of function extensionality is that emptiness is a subsingleton:
emptiness-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇ )
                                  ----------------------------
 →                                is-subsingleton (is-empty X)

emptiness-is-subsingleton fe X f g = fe λ x → !𝟘 (f x ≡ g x) (f x)

--"If `P` is a subsingleton, then so is `P + ¬ P`.  More generally:
+-is-subsingleton : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
 →        is-subsingleton P   →    is-subsingleton Q   →   (P → Q → 𝟘)
           ----------------------------------------------------------
 →                         is-subsingleton (P + Q)

+-is-subsingleton {𝓤} {𝓥} {P} {Q} i j f = γ
 where
  γ : (x y : P + Q) → x ≡ y
  γ (inl p) (inl p') = ap inl (i p p')
  γ (inl p) (inr q)  = !𝟘 (inl p ≡ inr q) (f p q)
  γ (inr q) (inl p)  = !𝟘 (inr q ≡ inl p) (f p q)
  γ (inr q) (inr q') = ap inr (j q q')


+-is-subsingleton' : dfunext 𝓤 𝓤₀ → {P : 𝓤 ̇ } → is-subsingleton P
                         -------------------------------------------
 →                           is-subsingleton (P + ¬ P)

+-is-subsingleton' fe {P} P✧ = +-is-subsingleton P✧ (emptiness-is-subsingleton fe P) ff
 where
  ff : P → is-empty P → 𝟘
  ff p P→⊥  = P→⊥ p

EM-is-subsingleton : dfunext (𝓤 ⁺) 𝓤 → dfunext 𝓤 𝓤 → dfunext 𝓤 𝓤₀
                          ----------------------------------------------------
 →                                 is-subsingleton (EM 𝓤)

EM-is-subsingleton fe⁺ fe fe₀ = Π-is-subsingleton fe⁺ (λ P → Π-is-subsingleton fe (λ P✧ → +-is-subsingleton' fe₀ P✧) )

-----------------------------------------------------
-- Propositional extensionality and the powerset.
--"We have been using the mathematical terminology 'subsingleton,' but tradition in the formulation of the next notion demands the logical
-- terminology 'proposition.'  Propositional extensionality says that any two logically equivalent propositions are equal:
propext : ∀ 𝓤 → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇} → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

global-propext : 𝓤ω
global-propext = ∀ {𝓤} → propext 𝓤

--"This is directly implied by univalence:
univalence-gives-propext : is-univalent 𝓤 → propext 𝓤
univalence-gives-propext 𝓤★ {P} {Q} Pprop Qprop f g =
  Eq→Id 𝓤★ P Q ( logically-equivalent-subsingletons-are-equivalent P Q Pprop Qprop (f , g) )

--"Under the additional hypothesis of function extensionality, the converse of the above holds. We need a lemma for that.
subsingleton-univalence : propext 𝓤 → dfunext 𝓤 𝓤
 →                (P : 𝓤 ̇)       →     is-subsingleton P       → (X : 𝓤 ̇)
                   -------------------------------------------------
 →                                 is-equiv (Id→Eq P X)
--(proof will appear below, once we establish the needed lemma)

Id-from-subingleton : propext 𝓤 → dfunext 𝓤 𝓤
 →                 (P : 𝓤 ̇)       →     is-subsingleton P       → (X : 𝓤 ̇)
                   -------------------------------------------------
 →                                 is-subsingleton (P ≡ X)

Id-from-subingleton {𝓤} pe fe P P✧ = Hedberg P (λ X → h X , gfwconst X)
  where  --Recall, Hedberg says "a type is a set iff its identity types have designated `wconstant` endomaps:
    module _ (X : 𝓤 ̇) where   -- Hedberg : ... (u₀ : X) → ((u : X) → wconstant-endomap (u₀ ≡ u)) → (u : X) → is-subsingleton (u₀ ≡ u)
      f : P ≡ X → is-subsingleton X × (P ⇔ X)
      f p = transport is-subsingleton p P✧ , Id→fun p , (Id→fun (p ⁻¹))

      g : is-subsingleton X × (P ⇔ X) → P ≡ X
      g (X✧ , X→P , P→X) = pe P✧ X✧ X→P P→X

      h : P ≡ X → P ≡ X
      h = g ∘ f

      XP⇔X✧✧ : is-subsingleton (is-subsingleton X × (P ⇔ X) )
      XP⇔X✧✧ = ×-is-subsingleton'
         ( ( λ (_  : P ⇔ X) → being-subsingleton-is-subsingleton fe ) ,
             λ (X✧ : is-subsingleton X) → ×-is-subsingleton
                                (Π-is-subsingleton fe (λ p → X✧) )  --  instead of  λ u u' → fe (λ x → X✧ (u x) (u' x)) 
                                (Π-is-subsingleton fe (λ x → P✧) ) ) -- instead of  λ u u' → fe (λ x → P✧ (u x) (u' x)))

      gfwconst : wconstant (g ∘ f)
      gfwconst p q =  ap g ( XP⇔X✧✧ (f p) (f q) )

--[and now the promised proof of the converse]
subsingleton-univalence {𝓤} pe fe P P✧ X = γ
  where
    ℓ : P ≃ X → is-subsingleton X
    ℓ P≃X = equiv-to-subsingleton (≃-sym P≃X) P✧

    eqtoid : P ≃ X → P ≡ X
    eqtoid P≃X = pe P✧ ( equiv-to-subsingleton (≃-sym P≃X) P✧ ) ∣ P≃X ∣ ∣ ≃-sym P≃X ∣

    P≃X✧ : is-subsingleton (P ≃ X)
    P≃X✧ (f , feq) (f' , f'eq) = to-subtype-≡ (being-equiv-is-subsingleton fe fe) ( fe ( λ x → X✧ (f x) (f' x) ) )
      where
        X✧ : is-subsingleton X
        X✧ = equiv-to-subsingleton ( ≃-sym (f , feq) ) P✧

    ε : (eq : P ≃ X) → Id→Eq P X (eqtoid eq) ≡ eq    --  (λ x → Id→Eq P X (eqtoid x)) ∼ (λ x → x)
    ε eq = P≃X✧ (Id→Eq P X (eqtoid eq) ) eq

    η : (P≡X : P ≡ X)  →   eqtoid ( Id→Eq P X P≡X )   ≡   P≡X    --  (λ x → eqtoid (Id→Eq P X x)) ∼ (λ x → x)
    η P≡X = Id-from-subingleton pe fe P P✧ X ( eqtoid (Id→Eq P X P≡X) ) P≡X

    γ : is-equiv (Id→Eq P X)
    γ = invertibles-are-equivs (Id→Eq P X) (eqtoid , η , ε)


subsingleton-univalence-≃ : propext 𝓤 → dfunext 𝓤 𝓤
 →              (X P : 𝓤 ̇) → is-subsingleton P → (P ≡ X) ≃ (P ≃ X)

subsingleton-univalence-≃ pe fe X P P✧ = Id→Eq P X , subsingleton-univalence pe fe P P✧ X

--"We also need a version of propositional extensionality for the type `Ω 𝓤` of subsingletons in a given universe `𝓤`, which lives
-- in the next universe:
Ω : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω 𝓤 = Σ P ꞉ 𝓤 ̇ , is-subsingleton P

--So an element of Ω 𝓤 is a pair (P , P✧), where P✧ is a proof that P is a subsingleton.

_holds : Ω 𝓤 → 𝓤 ̇
_holds (P , P✧) = P

holds-is-subsingleton : (p : Ω 𝓤) → is-subsingleton (p holds)
holds-is-subsingleton (P , P✧) = P✧

Ω-ext : dfunext 𝓤 𝓤 → propext 𝓤 → {p q : Ω 𝓤}
 →            (p holds → q holds) → (q holds → p holds)
               ---------------------------------------
 →                                p ≡ q

Ω-ext {𝓤} fe pe {p} {q} f g = to-subtype-≡ (λ _ → being-subsingleton-is-subsingleton fe)
                                           (pe (holds-is-subsingleton p) (holds-is-subsingleton q) f g)

--"With this and Hedberg, we get that `Ω` is a set:
Ω-is-a-set : dfunext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-a-set {𝓤} fe pe = types-with-wconstant-≡-endomaps-are-sets (Ω 𝓤) c
  where
    A : (p q : Ω 𝓤) → 𝓤 ̇
    A p q =  (p holds → q holds) × (q holds → p holds)

    Apq✧ : (p q : Ω 𝓤) → is-subsingleton (A p q)
    Apq✧ p q = Σ-is-subsingleton
                       ( Π-is-subsingleton fe ( λ _ → holds-is-subsingleton q ) )
                       ( λ _ → Π-is-subsingleton fe ( λ _ → holds-is-subsingleton p) )

    g : (p q : Ω 𝓤) → p ≡ q → A p q 
    g p q p≡q = u , v
      where
        ph≡qh : p holds ≡ q holds
        ph≡qh = ap _holds p≡q

        u : p holds → q holds
        u = Id→fun ph≡qh

        v : q holds → p holds
        v = Id→fun (ph≡qh ⁻¹)


    h : (p q : Ω 𝓤) → A p q → p ≡ q
    h p q ( u , v ) = Ω-ext fe pe u v

    f : (p q : Ω 𝓤) → p ≡ q → p ≡ q
    f p q p≡q = h p q (g p q p≡q)

    wconstfpq : (p q : Ω 𝓤) (p≡q p≡'q : p ≡ q) → f p q p≡q   ≡  f p q p≡'q 
    wconstfpq p q p≡q p≡'q = ap (h p q) (Apq✧ p q (g p q p≡q) (g p q p≡'q))

    c : (p q : Ω 𝓤) → Σ f ꞉ (p ≡ q → p ≡ q) , wconstant f
    c p q = f p q , wconstfpq p q

--"Hence powersets, even of types that are not sets, are always sets.
powersets-are-sets : hfunext 𝓤 (𝓥 ⁺) → dfunext 𝓥 𝓥 → propext 𝓥 → {X : 𝓤 ̇}
 →                                   is-set (X → Ω 𝓥)
powersets-are-sets fe fe' pe = Π-is-set fe (λ x → Ω-is-a-set fe' pe)

--"The above considers `X : 𝓤` and `Ω 𝓥`.
-- When the two universes `𝓤` and `𝓥` are the same, we adopt the usual notation `𝓟 X` for the powerset `X → Ω 𝓤` of `X`.
𝓟 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = X → Ω 𝓤

powersets-are-sets' : Univalence → {X : 𝓤 ̇}
 →                         is-set (𝓟 X)
powersets-are-sets' {𝓤} 𝓤★ = powersets-are-sets
                                              ( univalence-gives-hfunext' (𝓤★ 𝓤) (𝓤★ (𝓤 ⁺) ) )
                                              ( univalence-gives-dfunext (𝓤★ 𝓤) )
                                              ( univalence-gives-propext (𝓤★ 𝓤) )

--"Both `Ω` and the powerset live in the next universe. [Later] with propositional resizing we get equivalent copies in the same universe.

--"Membership and containment for elements of the powerset are defined as follows:
_∈_ : {X : 𝓤 ̇} → X → 𝓟 X → 𝓤 ̇
x ∈ A = A x holds
infix  40 _∈_

_⊆_ : {X : 𝓤 ̇} → 𝓟 X → 𝓟 X → 𝓤 ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-is-subsingleton : {X : 𝓤 ̇} (A : 𝓟 X) (x : X) → is-subsingleton (x ∈ A)
∈-is-subsingleton A x = holds-is-subsingleton (A x)

⊆-is-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇} (A B : 𝓟 X)
                       -------------------------------------
 →                              is-subsingleton (A ⊆ B)
⊆-is-subsingleton fe A B = Π-is-subsingleton fe
                                    ( λ x → Π-is-subsingleton fe ( λ _ → ∈-is-subsingleton B x) )

⊆-refl : {X : 𝓤 ̇} (A : 𝓟 X) → A ⊆ A
⊆-refl A x = 𝑖𝑑 (x ∈ A)

⊆-refl-consequence : {X : 𝓤 ̇} (A B : 𝓟 X) → A ≡ B
                                    -----------------------
 →                                     (A ⊆ B) × (B ⊆ A)

⊆-refl-consequence {X} A A (refl A) = ⊆-refl A , ⊆-refl A

--"Although `𝓟 X` is a set even if `X` is not, the total space `Σ x ꞉ X , A x holds` of a member `A : 𝓟 X` of the powerset need not
-- be a set. For instance, if `A x holds = 𝟙` for all `x : X`, then the total space is equivalent to `X`, which may not be a set.

--"Propositional and functional extensionality give the usual extensionality condition for the powerset:
subset-extensionality : propext 𝓤 → dfunext 𝓤 𝓤 → dfunext 𝓤 (𝓤 ⁺) → {X : 𝓤 ̇} {A B : 𝓟 X}
 →                         A ⊆ B   →   B ⊆ A
                            ------------------
 →                                 A ≡ B

subset-extensionality pe fe fe' {X} {A} {B} A⊆B B⊆A = fe' φ
 where
  φ : (x : X) → A x ≡ B x
  φ x = to-subtype-≡ (λ _ → being-subsingleton-is-subsingleton fe)
                              (pe (holds-is-subsingleton (A x) ) ( holds-is-subsingleton (B x) ) (A⊆B x) (B⊆A x) )

--"And hence so does univalence:
subset-extensionality' : Univalence → {X : 𝓤 ̇} {A B : 𝓟 X}
 →                           A ⊆ B     →    B ⊆ A
                            ----------------------
 →                                     A ≡ B

subset-extensionality' {𝓤} 𝓤★ = subset-extensionality (univalence-gives-propext (𝓤★ 𝓤) )
                                                                          (univalence-gives-dfunext (𝓤★ 𝓤))
                                                                          (univalence-gives-dfunext' (𝓤★ 𝓤) ( 𝓤★ (𝓤 ⁺) ))

--"For set-level mathematics, function extensionality and propositional extensionality are often the only consequences of univalence that are
-- needed. A noteworthy exception is the theorem that the type of ordinals in a universe is an ordinal in the next universe, which requires
-- univalence for sets (see the HoTT book or https://www.cs.bham.ac.uk/~mhe/agda-new/OrdinalOfOrdinals.html ).


-- =========================================
-- Stuff from our old Preliminaries.agda file (moderately tweaked)
-- -----------------------------------------------------------
_∈∈𝓟_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} →  (A  →  B) →   𝓟 B → 𝓤 ⊔ 𝓥 ̇
_∈∈𝓟_  f S = (x : _) → f x ∈ S

Im_⊆𝓟_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } →  (A → B)  → 𝓟 B → 𝓤 ⊔ 𝓥 ̇
Im_⊆𝓟_ {A = A} f S = (x : A) → f x ∈ S

image : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
image f = Σ y ꞉ (codomain f) , ∃! x ꞉ (domain f) , f x ≡ y

restriction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → image f → Y
restriction f (y , _) = y

cong-app-𝓟 : ∀ { A : 𝓤 ̇ } { B₁ B₂ : 𝓟 A} (x : A)
 →          x ∈ B₁   →   B₁ ≡ B₂
            -------------------------
 →                    x ∈ B₂
cong-app-𝓟 {𝓤}{A}{B₁}{B₂} x x∈B₁ B₁≡B₂ = B₁⊆B₂ x x∈B₁
 where
  B₁⊆B₂ : B₁ ⊆ B₂
  B₁⊆B₂ = pr₁ (⊆-refl-consequence B₁ B₂ B₁≡B₂)

cong-𝓟 : {A : 𝓤 ̇ } {B : 𝓟 A} (x y : A)
 →            x ∈ B   →   x ≡ y
            -------------------------
 →                   y ∈ B
cong-𝓟 {A = A}{B = B} x y x∈B x≡y  = transport (λ - → B - holds) x≡y x∈B

KER-𝓟 :  {A : 𝓤 ̇} {B : 𝓦 ̇} → is-set B → (f : A → B) → A → A → Ω 𝓦
KER-𝓟 Bset f x y = (f x ≡ f y) , Bset (f x) (f y)

ker-𝓟 :  {A B : 𝓤 ̇} → is-set B → (f : A → B) → A → A → Ω 𝓤
ker-𝓟 {𝓤} = KER-𝓟 {𝓤}{𝓤}

-- The (psudo-)inverse of an epic is the right inverse.
EInvIsRInv : funext 𝓦 𝓦 → {A : 𝓤 ̇} {B : 𝓦 ̇} (f : A → B)  (fEpic : Epic f)
 →            f ∘ (EpicInv f fEpic) ≡ 𝑖𝑑 B
EInvIsRInv fe f fEpic = fe (λ x → InvIsInv f x (fEpic x))

-------------------------------------------------------
-- Function extensionality from univalence
--"Function extensionality says that any two pointwise equal functions are equal. This is known to be not provable or disprovable in MLTT.
--Ordinary function extensionality
extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ∼ g   →   f ≡ g

-- Opposite of function extensionality
intensionality : ∀ {𝓤 𝓦} {A : 𝓤 ̇} {B : 𝓦 ̇ } {f g : A → B}
 →                f ≡ g  →  (x : A)
                  ------------------
 →                    f x ≡ g x

intensionality (refl _) _ = refl _

-- dependent intensionality
dep-intensionality : ∀ {𝓤 𝓦} {A : 𝓤 ̇} {B : A → 𝓦 ̇ } {f g : ∀(x : A) → B x}
 →                f ≡ g  →  (x : A)
                    ------------------
 →                    f x ≡ g x

dep-intensionality (refl _) _ = refl _

--------------------------------------
--Dependent function extensionality
dep-extensionality : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
dep-extensionality 𝓤 𝓦 = {A : 𝓤 ̇} {B : A → 𝓦 ̇} {f g : ∀(x : A) → B x}
 →                      f ∼ g    →   f ≡ g

∀-extensionality : 𝓤ω
∀-extensionality = ∀  {𝓤 𝓥} → extensionality 𝓤 𝓥

∀-dep-extensionality : 𝓤ω
∀-dep-extensionality = ∀ {𝓤 𝓥} → dep-extensionality 𝓤 𝓥

extensionality-lemma : {I : 𝓘 ̇}{X : 𝓤 ̇} {A : I → 𝓥 ̇}( p q : (i : I) → (X → A i) → 𝓣 ̇ ) ( args : X → (Π A) )
 →       p ≡ q
 →  ( λ i → (p i ) ( λ x → args x i ) ) ≡ ( λ i → (q i ) ( λ x → args x i ) )
extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

module _  {I : 𝓘 ̇}  {X : 𝓤 ̇} {A : I → 𝓥 ̇} (fe : global-dfunext)  where

  ext-lemma :  ( p q : (i : I) → (X → A i) → A i )
   →           ( (i : I) (args : X → A i) →  Id ( A i ) (p i args) (q i args) )
   →            p ≡ q
  ext-lemma p q H = fe λ x → fe (H x)

-----------------

-- scratch work:

-- I suspect the following is false, unless we assume the types are subsingletons (i.e., sets).
-- sigma-elim : {fe : global-funext} {X : 𝓤 ̇}
--                 ( A B : X → 𝓥 ̇ )   →   Σ A  ≡  Σ B
--                ---------------------------------
--  →                            A  ≡  B
-- sigma-elim {𝓤} {𝓥} {fe} {X} A B eqv = γ
--  where
--   SA SB : 𝓤 ⊔ 𝓥 ̇
--   SA = Σ x ꞉ X , A x
--   SB = Σ x ꞉ X , B x
--
--   SA≡SB : SA ≡ SB
--   SA≡SB = eqv
--
--   SAx : (x : X) (p : A x) → SA
--   SAx x p = x , p
--
--   xAx≡xBx : (x : X) → (x , A x) ≡ (x , B x)
--   xAx≡xBx x = {!SA≡SB x!}
--
--   γ : A ≡ B
--   γ = fe λ x →
--     A x             ≡⟨ refl _ ⟩
--     pr₂ (x , A x)  ≡⟨  {!!}   ⟩
--     pr₂ (x , B x)  ≡⟨ refl _ ⟩
--     B x             ∎

-- I suspect the following is false. 
-- sigma-intensionality : ∀{𝓤 𝓦} {X : 𝓤 ̇} { A B : X → 𝓦 ̇ }
--  →                         Σ A  ≡  Σ B  →   (x : X)
--                           --------------------------
--  →                            (x , A x)  ≡  (x , B x)
-- sigma-intensionality eqv x = {!!}

-- Indeed, it is false, and Siva provided a counterexample.
module siva's-counterexample (ua : is-univalent 𝓤₀) where
  B₁ B₂ : 𝟚 → 𝓤₀ ̇
  B₁ = λ{₀ → 𝟘; ₁ → 𝟙}
  B₂ = λ{₀ → 𝟙; ₁ → 𝟘}

  counterex : ( Σ B₁ ≡ Σ B₂ )  ×  ¬ ( Σ x ꞉ 𝟚 , (x , B₁ x) ≡ (x , B₂ x) )
  counterex = ( Eq→Id ua (Σ B₁) (Σ B₂) ξ  ,  ζ )
   where
    ζ : ¬ ( Σ x ꞉ 𝟚 , (x , B₁ x) ≡ (x , B₂ x) )
    ζ (₀ , p) = 𝟙-is-not-𝟘 ((ap pr₂ p)⁻¹)
    ζ (₁ , p) = 𝟙-is-not-𝟘 (ap pr₂ p)

    f : Σ B₁ → Σ B₂
    f (₀ , p) = ₁ , p
    f (₁ , p) = ₀ , p

    g : Σ B₂ → Σ B₁
    g (₀ , p) = ₁ , p
    g (₁ , p) = ₀ , p

    f∼g :  f ∘ g ∼ id
    f∼g (₀ , p) = refl (₀ , p)
    f∼g (₁ , y) = refl (₁ , y)

    g∼f :  g ∘ f ∼ id
    g∼f (₀ , p) = refl (₀ , p)
    g∼f (₁ , y) = refl (₁ , y)

    f-is-invertible : invertible f
    f-is-invertible = g , g∼f , f∼g

    f-is-equiv : is-equiv f
    f-is-equiv = invertibles-are-equivs f f-is-invertible

    ξ : Σ B₁ ≃ Σ B₂
    ξ = f , f-is-equiv

