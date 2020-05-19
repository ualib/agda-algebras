--FILE: UF-Univalence.agda
--DATE: 29 Mar 2020
--BLAME: <williamdemeo@gmail.com>
--REF: Based on Martin Escardo's course notes
--SEE:  https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#univalence

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Univalence where

open import UF-Prelude using (Universe; 𝓤; 𝓤₀;𝓥; 𝓦; _⁺; _̇;_⊔_; ¬; id; 𝑖𝑑; 𝟚; _×_; _+_; inl; inr; _∘_; ₀; ₁; _,_; Σ; -Σ; domain; codomain; pr₁; pr₂; Π; -Π; _≡_; refl; ap; _≡⟨_⟩_; _∎; _∼_; _⁻¹; transport; Id→Fun; _≢_; _⇔_; ₁-is-not-₀; Σ-induction)

open import UF-Singleton using (is-set; is-singleton; is-subsingleton; singletons-are-subsingletons; pointed-subsingletons-are-singletons; center; centrality)

open import UF-Equality using (subsingletons-are-sets; Nat; NatΣ;  to-Σ-≡; ⁻¹-involutive; wconstant-≡-endomaps; types-with-wconstant-≡-endomaps-are-sets; _◁_; has-section; singleton-type; singleton-type'; retract-of-singleton; singleton-types'-are-singletons;_≃_; ⌜_⌝; id-≃; is-equiv; ∘-is-equiv; ⌜⌝-is-equiv; ≃-gives-▷; equiv-to-singleton; ≃-sym; fiber; inverse; inverse-of-∘; invertible; equivs-are-invertible;  to-×-≡;  inv-elim-right; inv-elim-left; invertibles-are-equivs; invertibility-gives-≃; Σ-cong; inverses-are-equivs; inverses-are-retractions; inverses-are-sections; fiber-point; fiber-identification; transport-ap; apd; transport-is-retraction)

-----------------------------------------------------------------------------
-- Voevodsky's univalence axiom
-- -------------------------------
{-"There is a canonical transformation `(X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y` that sends the identity identification `refl X : X ≡ X` to the identity
   equivalence `id-≃ X : X ≃ X`. The univalence axiom, for the universe `𝓤`, says that this canonical map is itself an equivalence. -}

Id→Eq : (X Y : 𝓤 ̇) → X ≡ Y → X ≃ Y
Id→Eq X X (refl X) = id-≃ X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇) → is-equiv (Id→Eq X Y)

--"Thus, the univalence of the universe `𝓤` says that identifications `X ≡ Y` of types in `𝓤` are in canonical
-- bijection with equivalences `X ≃ Y`, if by bijection we mean equivalence, where the canonical bijection is
-- `Id→Eq`.

--"We emphasize that this doesn't posit that univalence holds. It says what univalence is (like the type
-- that says what the twin-prime conjecture is).
univalence-≃ : is-univalent 𝓤 → (X Y : 𝓤 ̇) → (X ≡ Y) ≃ (X ≃ Y)
univalence-≃ ua X Y = Id→Eq X Y , ua X Y

Eq→Id : is-univalent 𝓤 → (X Y : 𝓤 ̇) → X ≃ Y → X ≡ Y
Eq→Id ua X Y = inverse (Id→Eq X Y) (ua X Y)

--[Recall,
--  "To show that the type `𝟙` is not equal to the type `𝟘`, we use that `transport id` gives
--   `𝟙 ≡ 𝟘 → id 𝟙 → id 𝟘` where `id` is the identity function of the universe `𝓤₀`. More
--   generally, we have the following conversion of type identifications into functions:
--     Id→Fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
--     Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇ ))
--  "Here the identity function is that of the universe `𝓤` where the types `X` and `Y` live.
--   An equivalent definition is the following, where this time the identity function is that
--   of the type `X`:
--     Id→Fun' : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
--     Id→Fun' (refl X) = 𝑖𝑑 X
--
--     Id→Funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y) → Id→Fun p ≡ Id→Fun' p
--     Id→Funs-agree (refl X) = refl (𝑖𝑑 X)
--
--  "So if we have a hypothetical identification `p : 𝟙 ≡ 𝟘`, then we get a function `𝟙 → 𝟘`.
--   We apply this function to `⋆ : 𝟙` to conclude the proof.
--]

--"Here is a third way to convert a type identification into a function:

Id→fun : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Id→fun {𝓤}{X}{Y} p = ⌜ Id→Eq X Y p ⌝

Id→funs-agree : {X Y : 𝓤 ̇}(p : X ≡ Y)
 →              Id→fun p ≡ Id→Fun p
Id→funs-agree (refl X) = refl (𝑖𝑑 X)

--"What characterizes univalent mathematics is not the univalence axiom. We have defined and studied
-- the main concepts of univalent mathematics in a pure, spartan MLTT. It is the concepts of hlevel,
-- including singleton, subsingleton and set, and the notion of equivalence that are at the heart of
-- univalent mathematics. Univalence *is* a fundamental ingredient, but first we need the correct
-- notion of equivalence to be able to formulate it.

--"*Remark*. If we formulate univalence with invertible maps instead of equivalences, we get a statement
-- that is provably false in MLTT, and this is one of the reasons why Voevodsky's notion of equivalence is
-- important. (This is Exercise 4.6 of the HoTT book.) There is a solution in Coq by Mike Shulman
-- (see https://github.com/HoTT/HoTT/blob/master/contrib/HoTTBookExercises.v)"

------------------------------------------------------------------------------
-- Example of a type that is not a set under univalence
-- ----------------------------------------------------

--"We have two automorphisms of `𝟚`, namely the identity function and the map that swaps ₀ and ₁:

swap₂ : 𝟚 → 𝟚
swap₂ ₀ = ₁
swap₂ ₁ = ₀

swap₂-involutive : (n : 𝟚) → swap₂ (swap₂ n) ≡ n
swap₂-involutive ₀ = refl ₀
swap₂-involutive ₁ = refl ₁

--"That is, `swap₂` is its own inverse and hence is an equivalence:
swap₂-is-equiv : is-equiv swap₂
swap₂-is-equiv = invertibles-are-equivs swap₂ (swap₂ , swap₂-involutive , swap₂-involutive )

--"We now use a local module to assume univalence of the first universe in the construction of our example:

module example-of-a-nonset (ua : is-univalent 𝓤₀) where

  -- The above gives two distinct equivalences:
  e₀ : 𝟚 ≃ 𝟚
  e₀ = id-≃ 𝟚

  e₁ : 𝟚 ≃ 𝟚
  e₁ = swap₂ , swap₂-is-equiv

  e₀-is-not-e₁ : e₀ ≢ e₁
  e₀-is-not-e₁ p = ₁-is-not-₀ r
   where
    q : id ≡ swap₂
    q = ap ⌜_⌝ p  -- so q is ⌜ e₀ ⌝ ≡ ⌜ e₁ ⌝

    r : ₁ ≡ ₀
    r = ap (λ - → - ₁) q

  -- Using univalence, we get two different identifications of the type `𝟚` with itself:

  p₀ : 𝟚 ≡ 𝟚
  p₀ = Eq→Id ua 𝟚 𝟚 e₀

  p₁ : 𝟚 ≡ 𝟚
  p₁ = Eq→Id ua 𝟚 𝟚 e₁

  --If `𝓤₀` is a set, then the ids `p₀` and `p₁` would be equal... but...
  p₀-is-not-p₁ : p₀ ≢ p₁
  p₀-is-not-p₁ q = e₀-is-not-e₁ r
   where
    r = e₀             ≡⟨ (inv-elim-right (Id→Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₀)⁻¹ ⟩
        Id→Eq 𝟚 𝟚 p₀  ≡⟨ ap (Id→Eq 𝟚 𝟚) q ⟩
        Id→Eq 𝟚 𝟚 p₁ ≡⟨ inv-elim-right (Id→Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₁ ⟩
        e₁             ∎
  -- ...so,
  𝓤₀-is-not-a-set : ¬(is-set (𝓤₀ ̇))
  𝓤₀-is-not-a-set set𝓤₀ = p₀-is-not-p₁ q
   where q : p₀ ≡ p₁
         q = set𝓤₀ 𝟚 𝟚 p₀ p₁

-- For more examples, see Kraus and Sattler (https://arxiv.org/abs/1311.4002).

--------------------------------------------------------------------------
-- Exercises
-- ---------

-- Here are some facts whose proofs are left to the reader but that we will need from the next section
-- onwards. Sample solutions are given below.

-- --------------------
-- Formulations
-- --------------------

-- Define functions for the following type declarations. As a matter of procedure, we suggest to import
-- this file in a solutions file and add another declaration with the same type and new name e.g.
-- `sections-are-lc-solution`, because we already have solutions in this file. It is important not to
-- forget to include the option `--without-K` in the solutions file that imports (the Agda version of)
-- this file.

subsingleton-criterion : {X : 𝓤 ̇ } → (X → is-singleton X)
                            ---------------------------------
 →                                is-subsingleton X
subsingleton-criterion f x = singletons-are-subsingletons (domain f) (f x) x

subsingleton-criterion-first-try : {X : 𝓤 ̇ } → (X → is-singleton X) → is-subsingleton X
subsingleton-criterion-first-try f x = λ y → x  ≡⟨ (cent x)⁻¹ ⟩ c ≡⟨ cent y ⟩ y ∎
 where
  c = pr₁ (f x)
  cent = pr₂ (f x)

subsingleton-criterion' : {X : 𝓤 ̇ } → (X → is-subsingleton X) → is-subsingleton X
subsingleton-criterion' f x y = f x x y

retract-of-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 →               Y ◁ X  →  is-subsingleton X
                  -----------------------------
 →                       is-subsingleton Y
retract-of-subsingleton (g , f , η) X✧ =
 subsingleton-criterion λ x → retract-of-singleton (g , f , η)
  ( pointed-subsingletons-are-singletons (codomain f) (f x) X✧ )

retract-of-subsingleton-first-try : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y ◁ X → is-subsingleton X → is-subsingleton Y
retract-of-subsingleton-first-try (g , f , η) X✧ = λ v₀ v₁ →
  v₀ ≡⟨ (η v₀)⁻¹ ⟩ g (f v₀) ≡⟨ ap g (X✧ (f v₀) (f v₁)) ⟩ g (f v₁) ≡⟨ η v₁ ⟩  v₁ ∎

left-cancellable one-to-one : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = {u u' : domain f} → f u ≡ f u' → u ≡ u'
one-to-one = left-cancellable --alias.

lc-maps-reflect-subsingletons : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         (f : X → Y)    →    left-cancellable f    →    is-subsingleton Y
      ----------------------------------------------------------------
 →                            is-subsingleton X
lc-maps-reflect-subsingletons f lcf Y✧ u u' = lcf (Y✧ (f u) (f u'))

has-retraction has-left-inv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction s = Σ r ꞉ (codomain s → domain s), r ∘ s ∼ id
has-left-inv = has-retraction -- alias

sections-are-lc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A) →  has-retraction s → left-cancellable s
sections-are-lc s (r , s-is-right-inv-to-r) {u}{u'} su≡su' =
 u ≡⟨ (s-is-right-inv-to-r u)⁻¹ ⟩ r (s u)  ≡⟨ ap r su≡su' ⟩ r (s u')  ≡⟨ s-is-right-inv-to-r u' ⟩ u' ∎

equivs-have-retractions : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-retraction f
equivs-have-retractions f feq = inverse f feq , inv-elim-left f feq

equivs-have-sections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-section f
equivs-have-sections f feq = inverse f feq , inv-elim-right f feq

equivs-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → left-cancellable f
equivs-are-lc f feq = sections-are-lc f (equivs-have-retractions f feq)

equiv-to-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → is-subsingleton Y → is-subsingleton X
equiv-to-subsingleton (f , feq) = lc-maps-reflect-subsingletons f (equivs-are-lc f feq)

comp-inverses : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }  (f : X → Y) (g : Y → Z)
                               (feq : is-equiv f)  (geq : is-equiv g)  (f⁻ : Y → X) (g⁻ : Z → Y)
 →                           f⁻ ∼ inverse f feq      →      g⁻ ∼ inverse g geq
                               --------------------------------------------
 →                           f⁻ ∘ g⁻ ∼ inverse (g ∘ f) (∘-is-equiv geq feq)
comp-inverses f g feq geq f⁻ g⁻ finv ginv w =
 let f⁻¹ = inverse f feq in
 let g⁻¹ = inverse g geq in
  f⁻ (g⁻ w)           ≡⟨ finv (g⁻ w) ⟩
  f⁻¹ (g⁻ w)         ≡⟨ ap f⁻¹ (ginv w) ⟩
  f⁻¹ (g⁻¹ w)        ≡⟨ inverse-of-∘ f g feq geq w ⟩
  inverse (g ∘ f) (∘-is-equiv geq feq) w  ∎

{---------------------------------------------------------------------------------------------------
    Let us review Hedberg's Theorem, which is what we need in order to prove `subtypes-of-sets-are-sets`.
    Hedberg says that a type is a set iff its identity types have designated `wconstant` endomaps:
       `Hedberg' : {X : 𝓤 ̇} (x : X) → ((y : X) → wconstant-endomap (x ≡ y)) → (y : X) → is-subsingleton (x ≡ y)`
    Recall, the notion of constant map: `wconstant f = (x x' : domain f) -> f x ≡ f x'`  and the types whose
    identity types have `wconstant` endomaps: `wconstant-endomap X = Σ f ꞉ (X -> X) , wconstant f`
    Recall, `wconstant-≡-endomaps X = (x y : X) → wconstant-endomap (x ≡ y)`. We also had the following
    (which is immediate from the definitions and recalling that `is-set X = (x y : X) -> is-subsingleton (x ≡ y)`)
     `sets-have-wconstant-≡-endomaps : (X : 𝓤 ̇) -> is-set X -> wconstant-≡-endomaps X`
    HEDBERG'S THEOREM is the converse of the preceding result.
     `types-with-wconstant-≡-endomaps-are-sets : (X : 𝓤 ̇) → wconstant-≡-endomaps X → is-set X`
------------------------------------------------------------------------------------------------------}
subtypes-of-sets-are-sets : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
 →               left-cancellable m  →  is-set Y
                 --------------------------------
 →                           is-set X

subtypes-of-sets-are-sets {X = X} m mlc Yset = types-with-wconstant-≡-endomaps-are-sets X wconst≡endoX 
  where
   f : {u v : X} → u ≡ v → u ≡ v
   f p = mlc (ap m p)

   κ : (u v : X) → (p q : u ≡ v) → f p ≡ f q
   κ u v p q = ap mlc (Yset (m u) (m v) (ap m p) (ap m q) )

   wconst≡endoX : wconstant-≡-endomaps X
   wconst≡endoX u v = (f , κ u v)

equiv-to-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 →           X ≃ Y  →  is-set Y
              --------------------
 →                 is-set X

equiv-to-set X≃Y = subtypes-of-sets-are-sets ⌜ X≃Y ⌝ (equivs-are-lc ⌜ X≃Y ⌝ (⌜⌝-is-equiv X≃Y))

sections-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
 →                    has-retraction f   →  g ∼ f
                      -----------------------------
 →                          has-retraction g         --Recall, has-retraction s = Σ r ꞉ (codomain s → domain s), r ∘ s ∼ id;
                                                            -- intuition: `has-retraction s`  ⇔   "s has a left inverse"

sections-closed-under-∼ f g (⁻f , flinv) g∼f = (⁻f , glinv)
 where
  glinv : ⁻f ∘ g ∼ id
  glinv = λ x → ⁻f (g x) ≡⟨ ap ⁻f (g∼f x) ⟩ ⁻f (f x) ≡⟨ flinv x ⟩ x ∎

retractions-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
 →           has-section f  →   g ∼ f
               ------------------------
 →            has-section g                  --Recall, has-section s = Σ r ꞉ (codomain s → domain s), s ∘ r ∼ id
                                                   -- (intuition: s has a right inverse)
retractions-closed-under-∼ f g (f⁻ , frinv) g∼f = (f⁻ , grinv)
 where
  grinv : g ∘ f⁻ ∼ id
  grinv = λ y → g (f⁻ y) ≡⟨ g∼f (f⁻ y) ⟩ f (f⁻ y) ≡⟨ frinv y ⟩ y ∎

--"An alternative notion of equivalence, equivalent to Voevodsky's, has been given by André Joyal:
is-joyal-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-joyal-equiv f = has-section f × has-retraction f  -- i.e., `has-right-inv f × has-left-inv f`

--"Provide definitions for the following type declarations:"
one-inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇}  (f : X → Y) (⁻f f⁻ : Y → X)
 →               (⁻f ∘ f ∼ id)     →      (f ∘ f⁻ ∼ id)
                -------------------------------------
 →                               ⁻f ∼ f⁻
one-inverse f ⁻f f⁻ flinv frinv x = ⁻f x ≡⟨ ap ⁻f ((frinv x)⁻¹) ⟩ ⁻f (f (f⁻ x)) ≡⟨ flinv (f⁻ x) ⟩ f⁻ x ∎

joyal-equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              (f : X → Y)     →      is-joyal-equiv f
           ---------------------------------------
 →                      invertible f       -- i.e.,   Σ g ꞉ (codomain f -> domain f) , (g ∘ f ∼ id) × (f ∘ g ∼ id)
joyal-equivs-are-invertible f ( (f⁻ , frinv) , (⁻f , flinv) ) = ( f⁻ , (rinv-is-linv , frinv) )
 where
   ⁻f∼f⁻ : ⁻f ∼ f⁻
   ⁻f∼f⁻ = one-inverse f ⁻f f⁻ flinv frinv

   rinv-is-linv : (f⁻ ∘ f ∼ id)
   rinv-is-linv = λ x → f⁻ (f x) ≡⟨ ( ⁻f∼f⁻ (f x) )⁻¹  ⟩ ⁻f (f x) ≡⟨ flinv x ⟩ x ∎

joyal-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            (f : X → Y)    →    is-joyal-equiv f
         ------------------------------------
 →                  is-equiv f
joyal-equivs-are-equivs f jf = invertibles-are-equivs f (joyal-equivs-are-invertible f jf)

invertibles-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
           (f : X → Y)     →     invertible f
         ---------------------------------
 →                  is-joyal-equiv f

invertibles-are-joyal-equivs f ( g , (gf∼id , fg∼id) ) = ( (g , fg∼id) , (g , gf∼id) )

equivs-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            (f : X → Y)     →      is-equiv f
         ---------------------------------
 →                is-joyal-equiv f
equivs-are-joyal-equivs f 𝓔f = invertibles-are-joyal-equivs f (equivs-are-invertible f 𝓔f)

equivs-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y}
 →         is-equiv f       →       g ∼ f
            ------------------------------
 →                    is-equiv g
equivs-closed-under-∼ {f = f} {g = g} 𝓔f g∼f = joyal-equivs-are-equivs g jg
 where
  hsf = equivs-have-sections f 𝓔f
  hrf = equivs-have-retractions f 𝓔f

  jg : is-joyal-equiv g
  jg = (retractions-closed-under-∼ f g hsf g∼f , sections-closed-under-∼ f g hrf g∼f)

equiv-to-singleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 →               X ≃ Y     →     is-singleton X
                --------------------------------
 →                     is-singleton Y 
equiv-to-singleton' X≃Y = equiv-to-singleton (≃-sym X≃Y)  -- alt proof:   = retract-of-singleton (≃-gives-▷ X≃Y)
  -- Recall,   retract-of-singleton : ... Y ◁ X  →  is-singleton X → is-singleton Y, and,  ≃-gives-▷ : ... X ≃ Y -> Y ◁ X

pr₁-lc : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ }   →   ( (x : X) → is-subsingleton (F x) )
                                                   -------------------------------------
 →                                                 left-cancellable ( λ (t : Σ F) → pr₁ t )
pr₁-lc Fx✧ prx≡prx' = to-Σ-≡ (prx≡prx' , Fx✧ _ _ _)

subsets-of-sets-are-sets : (X : 𝓤 ̇) (F : X → 𝓥 ̇ )
 →                 is-set X    →    ( (x : X) → is-subsingleton (F x) )
                    -------------------------------------------
 →                 is-set (Σ x ꞉ X , F x)
subsets-of-sets-are-sets X F Xset Fx✧ = subtypes-of-sets-are-sets pr₁ (pr₁-lc Fx✧) Xset
--Recall, subtypes-of-sets-are-sets : ... (m : X → Y) → left-cancellable m  →  is-set Y → is-set X
--Here, we have `m = pr₁` and `pr₁-lc Fx✧` says `pr₁` is `lc`. 

to-subtype-≡ : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ } {x x' : X} {v : F x} {v' : F x'}
 →       ( (x : X) → is-subsingleton (F x) )      →      x ≡ x'
           -----------------------------------------------
 →                             (x , v) ≡ (x' , v')
to-subtype-≡ {𝓤}{𝓥} {X} {F} {x}{x'} {v} {v'} Fx✧ x≡x' = to-Σ-≡ (x≡x' , goal)
 --Recall, to-Σ-≡ : ... {(σ₁ , σ₂) (τ₁ , τ₂) : Σ F}  → Σ p ꞉ σ₁ ≡ τ₁ , transport F p σ₂ ≡  τ₂  → σ ≡ τ
 where
  Fx'✧ : is-subsingleton (F x')   --Recall, is-subsingleton (F x') = (v v' : F x') -> v ≡ v'
  Fx'✧ = Fx✧ x'

  vᵗ : F x'
  vᵗ = transport F   x≡x'   v  --  Recall, transport : (F : X → 𝓥 ̇) →  x ≡ x'  →  F x → F x'

  goal : vᵗ ≡ v'
  goal = Fx'✧ vᵗ v'

--Before considering the next theorem, recall that if `F : X → 𝓥 ̇` , then an inhabitant `t` of the dependent pair
-- type `Σ F` has the form t = (x, F x), with `pr₁ t = x : X` and `pr₂ t = F x : 𝓥 ̇`. Now, if `𝓕 : Σ F → X`
--is defined by `𝓕 t = pr₁ t = pr₁ (x , F x) = x`, and if `x₁ : X ̇`, then we can consider `fiber 𝓕 x₁` which is the
--collection of all `(x , F x) ∈ domain 𝓕 ( = Σ F)` such that `x ≡ x₁`.

--The next theorem will establish that if `F x` is a singleton for every `x`, then such fibers are also singletons:
--i.e., the following implication holds:: `( (x : X) → is-singleton (F x) ) → is-equiv (λ (t : Σ F) → pr₁ t)` where, recall,
--`is-equiv (λ (t : Σ F) → pr₁ t) :  ( v : codomain (λ (t : Σ F) → pr₁ t) ) → is-singleton (fiber  (λ (t : Σ F) → pr₁ t) v)`

pr₁-equiv : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ } →  ( (x : X) → is-singleton (F x) )
               ----------------------------------------------------
 →                    is-equiv (λ (t : Σ F) → pr₁ t)
pr₁-equiv {𝓤} {𝓥} {X}{F} Fx✦ = invertibles-are-equivs pr₁ (g , η , ε)
 --To use `invertibles-are-equivs` we must show that pr₁ is invertible, and recall the definition
 --    `invertible f = Σ g ꞉ (codomain f → domain f) , (g ∘ f ∼ id) × (f ∘ g ∼ id)`
 --So to prove `f = pr₁` is invertible we must provide `g` and a proof `(η , ε)` that `g` is an inverse.
 where
  g : X → Σ F
  g x = x , pr₁ (Fx✦ x)

  ε : pr₁ ∘ g ∼ id -- (the identity on X)
  ε x = refl (pr₁ (g x))

  η : g ∘ pr₁ ∼ id  -- (the identity on Σ F)
  η (x , v) = to-subtype-≡ ( λ x → singletons-are-subsingletons (F x) (Fx✦ x) ) (ε x)
  --Recall, to-subtype-≡ : ... ( (x : X) → is-subsingleton (F x) )  →  x ≡ x'  → (x , v) ≡ (x' , v')

pr₁-≃ : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ }  → ( (x : X) → is-singleton (F x) )  →  Σ F ≃ X
pr₁-≃ Fx✦ = pr₁ , pr₁-equiv Fx✦

ΠΣ-distr-≃ : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ } {P : (x : X) → F x → 𝓦 ̇ }
 →          (Π x ꞉ X , Σ v ꞉ F x , P x v) ≃ (Σ f ꞉ Π F , Π x ꞉ X , P x (f x))
ΠΣ-distr-≃ {𝓤} {𝓥} {𝓦} {X} {F} {P} = invertibility-gives-≃ φ ( ψ , refl , refl )
 where   --ε : φ ∘ ψ ∼ id ;    ε = refl  ;   η : ψ ∘ φ ∼ id  ;  η = refl
  φ : ( Π x ꞉ X , Σ v ꞉ F x , P x v ) → Σ f ꞉ Π F , Π x ꞉ X , P x (f x)
  φ g = ( λ x → pr₁ (g x) ) ,  λ x → pr₂ (g x)

  ψ : ( Σ f ꞉ Π F , Π x ꞉ X , P x (f x) ) →  Π x ꞉ X , Σ v ꞉ F x , P x v
  ψ (f , φ) x = f x , φ x

Σ-assoc : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ } {𝓕 : Σ F → 𝓦 ̇ }
 →          Σ 𝓕 ≃ (Σ u ꞉ X , Σ v ꞉ F u , 𝓕 (u , v))
Σ-assoc {𝓤} {𝓥} {𝓦} {X} {F} {𝓕} = invertibility-gives-≃ f ( g , refl , refl )
 where
  f : Σ 𝓕 →  Σ u ꞉ X , Σ v ꞉ F u , 𝓕 (u , v)
  f ((u , v) , w) = u , (v , w)

  g : ( Σ u ꞉ X , Σ v ꞉ F u , 𝓕 (u , v) ) →  Σ 𝓕
  g ( u , (v , w) ) = (u , v) , w

⁻¹-is-equiv : {X : 𝓤 ̇} (u u' : X) → is-equiv (λ (p : u ≡ u') → p ⁻¹)
⁻¹-is-equiv u u' = invertibles-are-equivs _⁻¹ (_⁻¹ , ⁻¹-involutive , ⁻¹-involutive)

⁻¹-≃ : {X : 𝓤 ̇ } (u u' : X) → (u ≡ u') ≃ (u' ≡ u)
⁻¹-≃ u u' = _⁻¹ , ⁻¹-is-equiv u u'

singleton-types-≃ : {X : 𝓤 ̇ } (u : X) → singleton-type' u ≃ singleton-type u
singleton-types-≃ u = Σ-cong λ u' → ⁻¹-≃ u u'
--Recall, `singleton-type {𝓤}{X} u₀ = Σ u ꞉ X , u ≡ u₀
--   and, `singleton-type' {𝓤}{X} u₀ = Σ u ꞉ X , u₀ ≡ u
--Recall,
-- Σ-cong : {X : 𝓤 ̇} {A : X → 𝓥 ̇}{B : X → 𝓦 ̇} → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B

singletons-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }  → is-singleton X    →    is-singleton Y
                                                ---------------------------------
 →                                                               X ≃ Y
singletons-≃ {𝓤} {𝓥} {X} {Y} X⋆ Y⋆ = invertibility-gives-≃ f (g , η , ε)
 where
 f : X → Y
 f x = center Y Y⋆

 g : Y → X
 g y = center X X⋆

 η : g ∘ f ∼ id
 η = centrality X X⋆

 ε : f ∘ g ∼ id
 ε = centrality Y Y⋆ -- or pr₂ Y⋆

maps-of-singletons-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 →                is-singleton X    →      is-singleton Y
                 ------------------------------------------
 →                               is-equiv f
maps-of-singletons-are-equivs {𝓤} {𝓥} {X} {Y} f X⋆ Y⋆ = invertibles-are-equivs f (g , η , ε)
 where
 g : Y → X
 g y = center X X⋆

 η : g ∘ f ∼ id
 η = centrality X X⋆

 ε : f ∘ g ∼ id
 ε y = Y-is-subsingleton (f (g y)) y      -- recall, `is-subsingleton X = (x y : X) → x ≡ y`
  where
   Y-is-subsingleton : is-subsingleton Y
   Y-is-subsingleton = singletons-are-subsingletons Y Y⋆

logically-equivalent-subsingletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
 →            is-subsingleton X    →    is-subsingleton Y   →    X ⇔ Y
             ----------------------------------------------------------
 →                                            X ≃ Y

logically-equivalent-subsingletons-are-equivalent X Y Xss Yss ( f , g ) =
 invertibility-gives-≃ f ( g , (λ x → Xss (g (f x)) x) , λ x → Yss (f (g x)) x )

singletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
 →                    is-singleton X    →      is-singleton Y
                     ------------------------------------------
 →                                        X ≃ Y
singletons-are-equivalent {𝓤} {𝓥} X Y = singletons-≃ {𝓤}{𝓥}{X}{Y}

--Before proving the next theorem, let's review the type `Nat` (natural transformations) and their naturality. Recall,
--if F G : 𝓒 → 𝓓  are functors, a nat tran from F to G is an indexed family {αₛ : s ∈ 𝓒₀} of arrows of 𝓓
--satisfying the following naturality condition:  If s t : 𝓒ₒ,  f : Hom(s, t), then the following diagram commutes:
--      s        F s ---- αₛ ----> G s
--      |           |                       |
--    f |       Ff |                       | Gf
--      ↓         ↓                      ↓
--      t        F t ---- αₜ  ----> G t
--
-- In the MLTT setup we have developed, the naturality of the Nat type is automatic.
--    Nats-are-natural : {X : 𝓤 ̇} (F : X → 𝓥 ̇) (G : X → 𝓦 ̇) (α : Nat F G) {s t : X}  (p : s ≡ t) →
--         α s ∘ transport F p ≡ transport G p ∘ α t
--
-- NatΣ : {X : 𝓤 ̇}{F : X → 𝓥 ̇}{G : X → 𝓦 ̇} → Nat F G → Σ F → Σ G
-- NatΣ α (s , v) = s , α s v
--Recall, if F : X → 𝓥 ̇, then Σ F is the dependent pair type whose inhabitants have the form (x , F x).

-- transport-ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : Y → 𝓦 ̇)
-- (f : X → Y)    {x x' : X}
-- (p : x ≡ x')    (a : A (f x))
-- ---------------------------------------------------
-- →        transport (A ∘ f) p a ≡ transport A (ap f p) a
-- transport-ap A f (refl x) a = refl a

NatΣ-fiber-equiv : {X : 𝓤 ̇ } (F : X → 𝓥 ̇ )   (G : X → 𝓦 ̇ )
                   (α : Nat F G)   (s : X)   (w : G s)
           --------------------------------------------------------------
 →            fiber (α s) w ≃ fiber (NatΣ α) (s , w)
NatΣ-fiber-equiv F G α s w = invertibility-gives-≃ f (g , ε , η)
 where
  f : fiber (α s) w → fiber (NatΣ α) (s , w)
  f (a , refl _) = (s , a) , refl (s , α s a)

  g : fiber (NatΣ α) (s , w) → fiber (α s) w
  g ((s , a) , refl _) = a , refl (α s a)

  ε : g ∘ f ∼ id  -- (λ x₁ → g (f x₁)) ∼ (λ x₁ → x₁)
  ε (a , refl _) = refl (a , refl (α s a)) 

  η : f ∘ g ∼ id   -- (λ x₁ → f (g x₁)) ∼ (λ x₁ → x₁)
  η ((x , a) , refl _) = refl (( x , a) , refl (NatΣ α (x , a) ))

NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ } {G : X → 𝓦 ̇ }
                       (α : Nat F G)    →   is-equiv (NatΣ α)
                   --------------------------------------
 →                         ( (x : X) → is-equiv (α x) )
NatΣ-equiv-gives-fiberwise-equiv {𝓤} {𝓥} {𝓦} {X} {F} {G} α eqα x w = γ
 where
  d : fiber (α x) w ≃ fiber (NatΣ α) (x , w)
  d = NatΣ-fiber-equiv F G α x w
  
  s : is-singleton (fiber (NatΣ α) (x , w))
  s = eqα (x , w)

  γ : is-singleton (fiber (α x) w)
  γ = equiv-to-singleton d s

Σ-is-subsingleton : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ }
 →                is-subsingleton X   →  ( (u : X) → is-subsingleton (F u) )
                 -----------------------------------------------------
 →                                is-subsingleton (Σ F)
Σ-is-subsingleton X✧ Fu✧ (u , Fu) (u' , Fu') = to-subtype-≡ Fu✧ (X✧ u u')

×-is-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } →  is-singleton X    →    is-singleton Y
                                                 --------------------------------------
 →                                                       is-singleton (X × Y)
×-is-singleton (u , u-is-center) (v , v-is-center) = (u , v) , uv-is-center
 where
  uv-is-center :  ∀ p → (u , v) ≡ p
  uv-is-center (u' , v') = to-×-≡ (u-is-center u' , v-is-center v')

×-is-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-subsingleton X     →    is-subsingleton Y
                                                       -----------------------------------------
 →                                                              is-subsingleton (X × Y)
×-is-subsingleton X✧ Y✧ = Σ-is-subsingleton X✧ (λ _ → Y✧)

×-is-subsingleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 →          ( (Y → is-subsingleton X) × (X → is-subsingleton Y) )
              ---------------------------------------------------
 →                           is-subsingleton (X × Y)
×-is-subsingleton'  {𝓤} {𝓥} {X} {Y} (Gv✧ , Fu✧) (u , v) (u' , v') = to-×-≡ (Gv✧ v u u' , Fu✧ u v v')

×-is-subsingleton'-back : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }  →  is-subsingleton (X × Y)
                               ---------------------------------------------------
 →                            (Y → is-subsingleton X) × (X → is-subsingleton Y)
×-is-subsingleton'-back  {𝓤} {𝓥} {X} {Y} XY✧ = Gv✧ , Fu✧
 where
  Gv✧ : Y → is-subsingleton X
  Gv✧ v u u' = ap pr₁ (XY✧ (u , v) (u' , v))

  Fu✧ : X → is-subsingleton Y
  Fu✧ u v v' = ap pr₂ (XY✧ (u , v) (u , v'))

ap₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {u u' : X} {v v' : Y}
 →                u ≡ u'     →     v ≡ v'
                --------------------------
 →                     f u v ≡ f u' v'
ap₂ f (refl u) ( refl v) = refl (f u v)


---------------------------------------------------------------------------
-- A characterization of univalence
-- ----------------------------------

-- We begin with two general results, which will be placed in a more general context later.
equiv-singleton-lemma : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ }
          (u₀ : X)    ( f : (u : X) → u₀ ≡ u → F u )
 →      ( (u : X) → is-equiv (f u) )
        -------------------------------------------
 →             is-singleton (Σ F)
equiv-singleton-lemma {𝓤}{𝓥} {X}{F} u₀ f fueq = γ
 where
  abstract
   e : (u : X) → (u₀ ≡ u) ≃ F u
   e u = f u , fueq u

   d : singleton-type' u₀ ≃ Σ F
   d = Σ-cong e              -- Recall,  Σ-cong : ...  (A x ≃ B x) → Σ A ≃ Σ B

   γ : is-singleton (Σ F)
   γ = equiv-to-singleton (≃-sym d) (singleton-types'-are-singletons X u₀)

singleton-equiv-lemma : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ }
         (u₀ : X)  ( f : (u : X) → u₀ ≡ u → F u )       →      is-singleton (Σ F)
       ------------------------------------------------------------------
 →                (u : X) → is-equiv (f u)
singleton-equiv-lemma {𝓤} {𝓥} {X} {F} u₀ f ΣF✦ = γ
 where
  abstract
   g : singleton-type' u₀ → Σ F
   g = NatΣ f

   e : is-equiv g
   e = maps-of-singletons-are-equivs g  (singleton-types'-are-singletons X u₀) ΣF✦

   γ : (u : X) → is-equiv (f u)
   γ = NatΣ-equiv-gives-fiberwise-equiv f e

--"With this we can characterize univalence as follows:
univalence⇒ : is-univalent 𝓤 → (X₀ : 𝓤 ̇) → is-singleton (Σ X ꞉ 𝓤 ̇ , X₀ ≃ X)
univalence⇒ 𝓤★ X₀ = equiv-singleton-lemma X₀ (Id→Eq X₀) (𝓤★ X₀)

⇒univalence : ( (X₀ : 𝓤 ̇) → is-singleton (Σ X ꞉ 𝓤 ̇ , X₀ ≃ X) ) → is-univalent 𝓤
⇒univalence ΣX✦ X₀ = singleton-equiv-lemma X₀ (Id→Eq X₀) (ΣX✦ X₀)

--"(Of course, this doesn't say that there is only one type `X` equivalent to `X₀`, or only one equivalence from `X₀` to `X`,
-- because equality of `Σ` types is given by transport in the second component along an identification in the first component.)
-- We can replace *singleton* by *subsingleton* and still have a logical equivalence, and we sometimes need the characterization in this form:
univalence→ : is-univalent 𝓤 → (X₀ : 𝓤 ̇) → is-subsingleton (Σ X ꞉ 𝓤 ̇ , X₀ ≃ X)
univalence→ 𝓤★ X₀ = singletons-are-subsingletons (Σ (X₀ ≃_) ) (univalence⇒ 𝓤★ X₀)

→univalence : ( (X₀ : 𝓤 ̇) → is-subsingleton (Σ X ꞉ 𝓤 ̇ , X₀ ≃ X)) → is-univalent 𝓤
→univalence ΣX✧ = ⇒univalence ( λ X → pointed-subsingletons-are-singletons (Σ (X ≃_) ) ( X , id-≃ X ) (ΣX✧ X) )

--------------------------------------------------------------------------------------------------------------
-- EQUIVALENCE INDUCTION.

--FILE: EquivalenceInduction.agda
--DATE: 3 Apr 2020
--BLAME: <williamdemeo@gmail.com>
--REF: Based on Martin Escardo's course notes
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#equivalenceinduction


{- "Under univalence, we get induction principles for type equivalences, corresponding to the induction principles `ℍ` and `𝕁`
    for identifications.  To prove a property of equivalences, it is enough to prove it for the identity equivalence `id-≃ X` for all `X`.

    Our objective is to get the induction principles `ℍ-≃` and `𝕁-≃` below and their corresponding equations. As above, it is easy to
    define `𝕁-≃` from `ℍ-≃`, and it is harder to define `ℍ-≃` directly, and it is much harder to prove the desired equation for
    `ℍ-≃` directly. In order to make this easy, we define an auxiliary induction principle `𝔾-≃`, from which we trivially derive `ℍ-≃`,
    and whose equation is easy to prove.

    The reason the induction principle `𝔾-≃` and its equation are easy to construct and prove is that the type `Σ Y ꞉ 𝓤 ̇ , X ≃ Y`
    is a singleton by univalence, which considerably simplifies reasoning about transport. For `ℍ-≃` we consider `Y : 𝓤` and `e : X ≃ Y`
    separately, whereas for `G-≃` we treat them as a pair `(Y , e)`. The point is that the type of such pairs is a singleton by univalence."
-}

𝔾-≃ : is-univalent 𝓤
 →      (X : 𝓤 ̇)     ( A : (Σ Y ꞉ 𝓤 ̇ , X ≃ Y) → 𝓥 ̇ )
 →      A (X , id-≃ X)   →     (Y : 𝓤 ̇)   (X≃Y : X ≃ Y)
         ----------------------------------------------
 →                    A (Y , X≃Y)
𝔾-≃ {𝓤} 𝓤★ X A v Y X≃Y = transport A p v
 where
    t : Σ Y ꞉ 𝓤 ̇ , X ≃ Y
    t =  (X , id-≃ X)

    p : t ≡ ( Y , X≃Y )
    p = univalence→ {𝓤} 𝓤★ X t (Y , X≃Y)

𝔾-≃-equation : (𝓤★ : is-univalent 𝓤)
 →       (X : 𝓤 ̇)     ( A : (Σ Y ꞉ 𝓤 ̇ , X ≃ Y) → 𝓥 ̇ )     ( v : A ( X , id-≃ X) )
          --------------------------------------------------------------------
 →                        𝔾-≃ 𝓤★ X A v X (id-≃ X) ≡ v
𝔾-≃-equation {𝓤} {𝓥} 𝓤★ X A v =
  𝔾-≃ 𝓤★ X A v X (id-≃ X)    ≡⟨ refl _ ⟩
  transport A p v                     ≡⟨ ap (λ - → transport A - v) q ⟩
  transport A (refl t) v              ≡⟨ refl _ ⟩
  v                                         ∎
  where
    t : Σ Y ꞉ 𝓤 ̇ , X ≃ Y
    t = X , id-≃ X

    p : t ≡ t
    p = univalence→ {𝓤} 𝓤★ X t t

    q : p ≡ refl t
    q = subsingletons-are-sets (Σ Y ꞉ 𝓤 ̇ , X ≃ Y) (univalence→ {𝓤} 𝓤★ X) t t p (refl t)

ℍ-≃ : is-univalent 𝓤
 →     (X : 𝓤 ̇)          ( A : (Y : 𝓤 ̇) → X ≃ Y → 𝓥 ̇ )
 →     A X (id-≃ X)       →      (Y : 𝓤 ̇)   (X≃Y : X ≃ Y)
        -------------------------------------------------
 →                     A Y  X≃Y
ℍ-≃ 𝓤★ X A = 𝔾-≃ 𝓤★ X (Σ-induction A)

ℍ-≃-equation : (𝓤★ : is-univalent 𝓤)
 →          (X : 𝓤 ̇)     ( A : (Y : 𝓤 ̇) → X ≃ Y → 𝓥 ̇ )     ( v : A X (id-≃ X) )
             --------------------------------------------------------------------
 →                             ℍ-≃ 𝓤★ X A v X (id-≃ X) ≡ v
ℍ-≃-equation 𝓤★ X A = 𝔾-≃-equation 𝓤★ X (Σ-induction A)

--"The induction principle `ℍ-≃` keeps `X` fixed and lets `Y` vary, while the induction principle `𝕁-≃` lets both vary:
𝕁-≃ : is-univalent 𝓤
 →       ( A : (X Y : 𝓤 ̇) → X ≃ Y → 𝓥 ̇ )
 →       ( (X : 𝓤 ̇) → A X X (id-≃ X) )
 →       (X Y : 𝓤 ̇)       (X≃Y : X ≃ Y)
          ---------------------------------
 →          A X Y  X≃Y
𝕁-≃ 𝓤★ A φ X = ℍ-≃ 𝓤★ X (A X) (φ X)

𝕁-≃-equation : (𝓤★ : is-univalent 𝓤)
 →             ( A : (X Y : 𝓤 ̇) → X ≃ Y → 𝓥 ̇ )
 →             ( φ : (X  : 𝓤 ̇)  → A X X (id-≃ X) )
 →             (X : 𝓤 ̇)
               -------------------------------------------
 →             𝕁-≃ 𝓤★ A φ X X (id-≃ X) ≡ φ X
𝕁-≃-equation 𝓤★ A φ X = ℍ-≃-equation 𝓤★ X (A X) (φ X)

--"A second set of equivalence induction principles refer to `is-equiv` rather than `≃` and are proved by reduction to the first version `ℍ-≃`:
ℍ-equiv : is-univalent 𝓤
 →       (X : 𝓤 ̇)   ( A : (Y : 𝓤 ̇) → (X → Y) → 𝓥 ̇ )    →   A X (𝑖𝑑 X)
 →       (Y : 𝓤 ̇)    (f : X → Y)    →    is-equiv f
           -------------------------------------------------------------
 →          A Y f
ℍ-equiv {𝓤} {𝓥} 𝓤★ X A v Y f feq = γ (f , feq)
 where
  B : (Y : 𝓤 ̇) → X ≃ Y → 𝓥 ̇
  B Y (f , feq) = A Y f

  b : B X (id-≃ X)
  b = v

  γ : (X≃Y : X ≃ Y) → B Y X≃Y
  γ = ℍ-≃ 𝓤★ X B b Y

--"The above and the following say that to prove a property of *functions* holds for all equivalences, it is enough to prove it for all identity functions:
𝕁-equiv : is-univalent 𝓤
 →        ( A : (X Y : 𝓤 ̇) → (X → Y) → 𝓥 ̇ )   →   ( (X : 𝓤 ̇) → A X X (𝑖𝑑 X) )
 →        (X Y : 𝓤 ̇)   (f : X → Y)     →     is-equiv f
            --------------------------------------------------------------------
 →         A X Y f
𝕁-equiv 𝓤★ A φ X = ℍ-equiv 𝓤★ X (A X) (φ X)

--"And the following is an immediate consequence of the fact that invertible maps are equivalences:
𝕁-invertible :  is-univalent 𝓤
 →       ( A : (X Y : 𝓤 ̇) → (X → Y) → 𝓥 ̇ )  →    ( (X : 𝓤 ̇) → A X X (𝑖𝑑 X) )
 →       (X Y : 𝓤 ̇)   (f : X → Y)     →     invertible f
          --------------------------------------------------------
 →         A X Y f
𝕁-invertible 𝓤★ A φ X Y f finv = 𝕁-equiv 𝓤★ A φ X Y f (invertibles-are-equivs f finv)

--"For example, using `ℍ-equiv` we see that for any pair of functions `F : 𝓤 ̇ → 𝓤 ̇ `, `𝓕 : {X Y : 𝓤 ̇ } → (X → Y) → F X → F Y`,
-- if `𝓕` preserves identities then it automatically preserves composition of equivalences. More generally, it is enough that at least
-- one of the factors is an equivalence:
automatic-equiv-functoriality :
        (F : 𝓤 ̇ →  𝓤 ̇)
        ( 𝓕 : {X Y : 𝓤 ̇} → (X → Y) → F X → F Y )
        ( 𝓕-id : {X : 𝓤 ̇} → 𝓕 (𝑖𝑑 X) ≡ 𝑖𝑑 (F X) )
        {X Y Z : 𝓤 ̇}    (f : X → Y)    (g : Y → Z)
 →    is-univalent 𝓤     →    is-equiv f + is-equiv g
       --------------------------------------------------------
 →    𝓕 (g ∘ f)  ≡   𝓕 g ∘ 𝓕 f
automatic-equiv-functoriality {𝓤} F 𝓕 𝓕-id {X}{Y}{Z} f g 𝓤★ = γ
 where
  γ : is-equiv f + is-equiv g → 𝓕 (g ∘ f) ≡ 𝓕 g ∘ 𝓕 f
  γ (inl feq) = ℍ-equiv 𝓤★ X A a Y f feq g
   where
    A : (Y : 𝓤 ̇) → (X → Y) → 𝓤 ̇
    A Y f = (g : Y → Z) → 𝓕 (g ∘ f) ≡ 𝓕 g ∘ 𝓕 f

    a : (g : X → Z) → 𝓕 g ≡ 𝓕 g ∘ 𝓕 id
    a g = ap (𝓕 g ∘_) (𝓕-id ⁻¹)
  γ (inr geq) = ℍ-equiv 𝓤★ Y B b Z g geq f
   where
    B : (Z : 𝓤 ̇) → (Y → Z) → 𝓤 ̇
    B Z g = (f : X → Y) → 𝓕 (g ∘ f) ≡ 𝓕 g ∘ 𝓕 f

    b : (f : X → Y) → 𝓕 f ≡ 𝓕 (𝑖𝑑 Y) ∘ 𝓕 f
    b f = ap (_∘ 𝓕 f ) (𝓕-id ⁻¹)

--"Here is another example:
Σ-change-of-variable' : is-univalent 𝓤
 →      {X Y : 𝓤 ̇}    (A : X → 𝓥 ̇ )     (f : X → Y)    →    (feq : is-equiv f)
         ----------------------------------------------------------
 →       ( Σ x ꞉ X , A x ) ≡ ( Σ y ꞉ Y , A ( inverse f feq y ) )
Σ-change-of-variable' {𝓤}{𝓥} 𝓤★ {X}{Y} A f feq = ℍ-≃ 𝓤★ X B b Y (f , feq)
   where
    B : (Y : 𝓤 ̇) → X ≃ Y → (𝓤 ⊔ 𝓥) ⁺ ̇
    B Y (f , feq) = Σ A ≡ ( Σ (A ∘ inverse f feq) )

    b : B X (id-≃ X)
    b = refl (Σ A)

--"An unprimed version of this is given below, after we study half adjoint equivalences. The above version using the inverse of `f` can be
-- proved directly by induction, but the following version is perhaps more natural.
Σ-change-of-variable'' : is-univalent 𝓤
 →        {X Y : 𝓤 ̇}  (A : Y → 𝓥 ̇ )   (f : X → Y)
 →         is-equiv f
           ------------------------------------------------
 →         ( Σ y ꞉ Y , A y ) ≡ ( Σ x ꞉ X , A ( f x ) )
Σ-change-of-variable'' 𝓤★ A f  feq =
  Σ-change-of-variable' 𝓤★ A (inverse f feq) (inverses-are-equivs f feq)

--"This particular proof works only because inversion is involutive on the nose. As another example we have the following:
transport-map-along-≡ : {X Y Z : 𝓤 ̇}
                                   (X≡Y : X ≡ Y)    (g : X → Z)
 →                               transport (λ - → - → Z) X≡Y g  ≡   g ∘ Id→fun (X≡Y ⁻¹)
transport-map-along-≡ (refl X) = refl

transport-map-along-≃ : (𝓤★ : is-univalent 𝓤) {X Y Z : 𝓤 ̇}
                                   (X≃Y : X ≃ Y)    (g : X → Z)
 →                               transport (λ - → - → Z) (Eq→Id 𝓤★ X Y X≃Y) g  ≡   g ∘ ⌜ ≃-sym X≃Y ⌝
transport-map-along-≃ {𝓤} 𝓤★ {X}{Y}{Z} = 𝕁-≃ 𝓤★ A a X Y
 where
  A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓤 ̇
  A X Y e = (g : X → Z) → transport (λ - → - → Z) (Eq→Id 𝓤★ X Y e) g
                        ≡ g ∘ ⌜ ≃-sym e ⌝
  a : (X : 𝓤 ̇ ) → A X X (id-≃ X)
  a X g = transport (λ - → - → Z) (Eq→Id 𝓤★ X X (id-≃ X)) g ≡⟨ q      ⟩
          transport (λ - → - → Z) (refl X) g                ≡⟨ refl _ ⟩
          g                                                 ∎
    where
     p : Eq→Id 𝓤★ X X (id-≃ X) ≡ refl X
     p = inverses-are-retractions (Id→Eq X X) (𝓤★ X X) (refl X)

     q = ap (λ - → transport (λ - → - → Z) - g) p

---------------------------------------------------------------------------------------------------
-- Half adjoint equivalences
-- see: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#haes

--"An often useful alternative formulation of the notion of equivalence is that of half adjoint equivalence. If we have a function
-- `f : X → Y` with invertibility data `g : Y → X` , `η : g ∘ f ∼ id`, `ε : f ∘ g ∼ id`, then for any `x : X` we have that
-- `ap f (η x)` and `ε (f x)` are two identifications of type `f (g (f x)) ≡ f x`. The half adjoint condition says that these two identifications
-- are themselves identified. The addition of the constraint `τ x : ap f (η x) ≡ ε (f x)` turns invertibility, which is data in general,
-- into property of `f`
is-hae : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-hae f = Σ g ꞉ (codomain f → domain f) ,
                    Σ η ꞉ g ∘ f ∼ id , ( Σ ε ꞉ f ∘ g ∼ id , ( (x : domain f) → ap f (η x) ≡ ε (f x) ) )

--"The following just forgets the constraint `τ`:
haes-are-invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → is-hae f
                                                           -----------------------
 →                                                             invertible f
haes-are-invertible f ( g , η , ε , τ ) = g , η , ε

--LEFT OFF HERE-------------------------------------------

--"Hence half adjoint equivalences are equivalences, because invertible maps are equivalences. But it is also easy to prove this directly, avoiding
-- the detour via invertible maps. We begin with a construction which will be used a number of times in connection with half adjoint equivalences.
-- \begin{code}\end{code}

--"To recover the constraint for all equivalences, and hence for all invertible maps, under univalence, it is enough to give the constraint for
-- identity maps:
--\begin{code}\end{code}

--"The above can be proved without univalence as follows. This argument also allows us to have `X` and `Y` in different universes. An example
-- of an equivalence of types in different universes is `Id→Eq`, as stated by univalence.
--\begin{code}\end{code}

--"We wrote the above proof of `equivs-are-haes` in a deliberately verbose form to aid understanding. Here is the same proof in a
-- perversely reduced form:
--\begin{code}\end{code}

--"Notice that we have the following factorization, on the nose, of the construction of invertibility data from the equivalence property:
--\begin{code}\end{code}

--"Instead of working with the notion of half adjoint equivalence, we can just work with Voevodsky's notion of equivalence, and use the fact
-- that it satisfies the half adjoint condition:
--\begin{code}\end{code}

--"Here is an example, where, compared to `Σ-change-of-variable', we remove univalence from the hypothesis, generalize the universe of the
-- type `Y`, and weaken equality to equivalence in the conclusion. Notice that the proof starts as that of `Σ-reindexing-retract`
--\begin{code}\end{code}

--"For the sake of completeness, we also include the proof from the HoTT book that invertible maps are half adjoint equivalences, which uses a
-- standard argument coming from category theory. We first need some naturality lemmas:
--\begin{code}\end{code}

--The idea of the following proof is to improve `ε` to be able to give the required `τ`:
--\begin{code}\end{code}

--------------------------------

transport-ap-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                 {x x' : X} (a : x' ≡ x) (b : f x' ≡ f x)
               → (transport (λ - → f - ≡ f x) a b ≡ refl (f x)) ≃ (ap f a ≡ b)

transport-ap-≃ f (refl x) b = γ
 where
  γ : (b ≡ refl (f x)) ≃ (refl (f x) ≡ b)
  γ = ⁻¹-≃ b (refl (f x))

haes-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-hae f → is-equiv f
haes-are-equivs f (g , η , ε , τ) y = γ
 where
  c : (φ : fiber f y) → (g y , ε y) ≡ φ
  c (x , refl .(f x)) = q
   where
    p : transport (λ - → f - ≡ f x) (η x) (ε (f x)) ≡ refl (f x)
    p = ⌜ ≃-sym (transport-ap-≃ f (η x) (ε (f x))) ⌝ (τ x)

    q : (g (f x) , ε (f x)) ≡ (x , refl (f x))
    q = to-Σ-≡ (η x , p)

  γ : is-singleton (fiber f y)
  γ = (g y , ε y) , c

-- id-is-hae : (X : 𝓤 ̇ ) → is-hae (𝑖𝑑 X)
-- id-is-hae X = 𝑖𝑑 X , refl , refl , (λ x → refl (refl x))

-- ua-equivs-are-haes : is-univalent 𝓤
--                    → {X Y : 𝓤 ̇ } (f : X → Y)
--                    → is-equiv f → is-hae f

-- ua-equivs-are-haes ua {X} {Y} = 𝕁-equiv ua (λ X Y f → is-hae f) id-is-hae X Y

equivs-are-haes : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → is-equiv f → is-hae f

equivs-are-haes {𝓤} {𝓥} {X} {Y} f i = (g , η , ε , τ)
 where
  g : Y → X
  g = inverse f i

  η : g ∘ f ∼ id
  η = inverses-are-retractions f i

  ε : f ∘ g ∼ id
  ε = inverses-are-sections f i

  τ : (x : X) → ap f (η x) ≡ ε (f x)
  τ x = γ
   where
    φ : fiber f (f x)
    φ = center (fiber f (f x)) (i (f x))

    by-definition-of-g : g (f x) ≡ fiber-point φ
    by-definition-of-g = refl _

    p : φ ≡ (x , refl (f x))
    p = centrality (fiber f (f x)) (i (f x)) (x , refl (f x))

    a : g (f x) ≡ x
    a = ap fiber-point p

    b : f (g (f x)) ≡ f x
    b = fiber-identification φ

    by-definition-of-η : η x ≡ a
    by-definition-of-η = refl _

    by-definition-of-ε : ε (f x) ≡ b
    by-definition-of-ε = refl _

    q = transport (λ - → f - ≡ f x)       a          b         ≡⟨ refl _    ⟩
        transport (λ - → f - ≡ f x)       (ap pr₁ p) (pr₂ φ)   ≡⟨ t         ⟩
        transport (λ - → f (pr₁ -) ≡ f x) p          (pr₂ φ)   ≡⟨ apd pr₂ p ⟩
        refl (f x)                                             ∎
     where
      t = (transport-ap (λ - → f - ≡ f x) pr₁ p b)⁻¹

    γ : ap f (η x) ≡ ε (f x)
    γ = ⌜ transport-ap-≃ f a b ⌝ q

-- equivs-are-haes' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
--                  → is-equiv f → is-hae f

-- equivs-are-haes' f e = (inverse f e ,
--                         inverses-are-retractions f e ,
--                         inverses-are-sections f e ,
--                         τ)
--  where
--   τ : ∀ x → ap f (inverses-are-retractions f e x) ≡ inverses-are-sections f e (f x)
--   τ x = ⌜ transport-ap-≃ f (ap pr₁ p) (pr₂ φ) ⌝ q
--    where
--     φ : fiber f (f x)
--     φ = pr₁ (e (f x))

--     p : φ ≡ (x , refl (f x))
--     p = pr₂ (e (f x)) (x , refl (f x))

--     q : transport (λ - → f - ≡ f x) (ap pr₁ p) (pr₂ φ) ≡ refl (f x)
--     q = (transport-ap (λ - → f - ≡ f x) pr₁ p ( ( pr₂ φ ) ) )⁻¹ ⋆' apd pr₂ p  -- ∙




-- equiv-invertible-hae-factorization : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
--                                    → equivs-are-invertible f
--                                    ∼ haes-are-invertible f ∘ equivs-are-haes f

-- equiv-invertible-hae-factorization f e = refl (equivs-are-invertible f e)

half-adjoint-condition : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f) (x : X)
                       → ap f (inverses-are-retractions f e x) ≡ inverses-are-sections f e (f x)

half-adjoint-condition f e = pr₂ (pr₂ (pr₂ (equivs-are-haes f e)))

Σ-change-of-variable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                     → is-equiv f → (Σ y ꞉ Y , A y) ≃ (Σ x ꞉ X , A (f x))

Σ-change-of-variable {𝓤} {𝓥} {𝓦} {X} {Y} A f i = γ
 where
  g = inverse f i
  η = inverses-are-retractions f i
  ε = inverses-are-sections f i
  τ = half-adjoint-condition f i

  φ : Σ A → Σ (A ∘ f)
  φ (y , a) = (g y , transport A ((ε y)⁻¹) a)

  ψ : Σ (A ∘ f) → Σ A
  ψ (x , a) = (f x , a)

  ψφ : (z : Σ A) → ψ (φ z) ≡ z
  ψφ (y , a) = p
   where
    p : (f (g y) , transport A ((ε y)⁻¹) a) ≡ (y , a)
    p = to-Σ-≡ (ε y , transport-is-retraction A (ε y) a)

  φψ : (t : Σ (A ∘ f)) → φ (ψ t) ≡ t
  φψ (x , a) = p
   where
    a' : A (f (g (f x)))
    a' = transport A ((ε (f x))⁻¹) a

    q = transport (A ∘ f) (η x)  a' ≡⟨ transport-ap A f (η x) a'             ⟩
        transport A (ap f (η x)) a' ≡⟨ ap (λ - → transport A - a') (τ x)     ⟩
        transport A (ε (f x))    a' ≡⟨ transport-is-retraction A (ε (f x)) a ⟩
        a                          ∎

    p : (g (f x) , transport A ((ε (f x))⁻¹) a) ≡ (x , a)
    p = to-Σ-≡ (η x , q)

  γ : Σ A ≃ Σ (A ∘ f)
  γ = invertibility-gives-≃ φ (ψ , ψφ , φψ)

-- ~-naturality : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
--                (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
--                → H x · ap g p ≡ ap f p · H y   -- ∙  ∙

-- ~-naturality f g H {x} {_} {refl a} = refl-left ⁻¹

-- ~-naturality' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
--                 (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
--               → H x ∙ ap g p ∙ (H y)⁻¹ ≡ ap f p

-- ~-naturality' f g H {x} {x} {refl x} = ⁻¹-right∙ (H x)

-- ~-id-naturality : {X : 𝓤 ̇ }
--                   (h : X → X) (η : h ∼ id) {x : X}
--                 → η (h x) ≡ ap h (η x)

-- ~-id-naturality h η {x} =

--    η (h x)                         ≡⟨ refl _ ⟩
--    η (h x) ∙ refl (h x)            ≡⟨ i      ⟩
--    η (h x) ∙ (η x ∙ (η x)⁻¹)       ≡⟨ ii     ⟩
--    η (h x) ∙ η x ∙ (η x)⁻¹         ≡⟨ iii    ⟩
--    η (h x) ∙ ap id (η x) ∙ (η x)⁻¹ ≡⟨ iv     ⟩
--    ap h (η x)                      ∎

--  where
--   i   = ap (η(h x) ∙_) ((⁻¹-right∙ (η x))⁻¹)
--   ii  = (∙assoc (η (h x)) (η x) (η x ⁻¹))⁻¹
--   iii = ap (λ - → η (h x) ∙ - ∙ η x ⁻¹) ((ap-id (η x))⁻¹)
--   iv  = ~-naturality' h id η {h x} {x} {η x}

-- invertibles-are-haes : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
--                      → invertible f → is-hae f

-- invertibles-are-haes f (g , η , ε) = g , η , ε' , τ
--  where
--   ε' = λ y → f (g y)         ≡⟨ (ε (f (g y)))⁻¹ ⟩
--              f (g (f (g y))) ≡⟨ ap f (η (g y))  ⟩
--              f (g y)         ≡⟨ ε y ⟩
--              y               ∎

--   module _ (x : domain f) where

--    p = η (g (f x))       ≡⟨ ~-id-naturality (g ∘ f) η  ⟩
--        ap (g ∘ f) (η x)  ≡⟨ ap-∘ f g (η x)             ⟩
--        ap g (ap f (η x)) ∎

--    q = ap f (η (g (f x))) ∙ ε (f x)          ≡⟨ by-p            ⟩
--        ap f (ap g (ap f (η x))) ∙ ε (f x)    ≡⟨ by-ap-∘         ⟩
--        ap (f ∘ g) (ap f (η x))  ∙ ε (f x)    ≡⟨ by-~-naturality ⟩
--        ε (f (g (f x))) ∙ ap id (ap f (η x))  ≡⟨ by-ap-id        ⟩
--        ε (f (g (f x))) ∙ ap f (η x)          ∎
--     where
--      by-p            = ap (λ - → ap f - ∙ ε (f x)) p
--      by-ap-∘         = ap (_∙ ε (f x)) ((ap-∘ g f (ap f (η x)))⁻¹)
--      by-~-naturality = (~-naturality (f ∘ g) id ε {f (g (f x))} {f x} {ap f (η x)})⁻¹
--      by-ap-id        = ap (ε (f (g (f x))) ∙_) (ap-id (ap f (η x)))

--    τ = ap f (η x)                                           ≡⟨ refl-left ⁻¹ ⟩
--        refl (f (g (f x)))                     ∙ ap f (η x)  ≡⟨ by-⁻¹-left∙  ⟩
--        (ε (f (g (f x))))⁻¹ ∙  ε (f (g (f x))) ∙ ap f (η x)  ≡⟨ by-∙assoc    ⟩
--        (ε (f (g (f x))))⁻¹ ∙ (ε (f (g (f x))) ∙ ap f (η x)) ≡⟨ by-q         ⟩
--        (ε (f (g (f x))))⁻¹ ∙ (ap f (η (g (f x))) ∙ ε (f x)) ≡⟨ refl _       ⟩
--        ε' (f x)                                             ∎
--     where
--      by-⁻¹-left∙ = ap (_∙ ap f (η x)) ((⁻¹-left∙ (ε (f (g (f x)))))⁻¹)
--      by-∙assoc   = ∙assoc ((ε (f (g (f x))))⁻¹) (ε (f (g (f x)))) (ap f (η x))
--      by-q        = ap ((ε (f (g (f x))))⁻¹ ∙_) (q ⁻¹)

