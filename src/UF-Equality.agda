--FILE: UF-Equality.agda
--DATE: 19 Mar 2020
--UPDATE: 23 May 2020
--BLAME: williamdemeo@gmail.com
--REF: Much of this file is based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#identitytypeuf
--       In particular, the quoted comments below, along with sections of code to which those comments refer, are due to Martin Escardo.
--       Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Equality where

open import UF-Prelude using (𝓤₀; 𝓤; 𝓥; 𝓦; _̇; _⊔_; 𝑖𝑑; _∼_; codomain; id; ℕ; zero; succ; 𝟘; 𝟙; ¬; is-empty; !𝟘; _∘_; domain; Σ; -Σ; Σ-induction; curry; pr₁; pr₂; _,_; 𝟚; _×_; inl; inr; Id; _≡_; refl; _∙_; _⁻¹; ap; _≡⟨_⟩_;_∎; transport; decidable;has-decidable-equality;𝟚-has-decidable-equality; ℕ-has-decidable-equality; pred)

open import UF-Singleton using (center;is-set;is-singleton;is-subsingleton;singletons-are-subsingletons;𝟘-is-subsingleton;𝟙-is-subsingleton; centrality)

--open import Agda.Builtin.Nat public renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )

-----------------------------------------------------------------------------------------
-- The identity type in univalent mathematics
-- --------------------------------------------
--https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#identitytypeuf

--"We can view a type `X` as a sort of category with hom-types rather than hom-sets, with
-- the identifications between points as the arrows... `refl` provides a neutral element
-- for composition of identifications:
refl-left : {X : 𝓤 ̇} {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x}{refl x} = refl (refl x)
refl-right : {X : 𝓤 ̇} {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {p} = refl p
--"And composition (of identifications) is associative:
∙assoc : {X : 𝓤 ̇} {x y z t : X} (p : x ≡ y)(q : y ≡ z)(r : z ≡ t)
 →     (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙assoc p q (refl z) = refl (p ∙ q)
--(alt proof: ∙assoc{X = X}{x = x}x≡y y≡z (refl _) = refl (transport (Id X x) y≡z x≡y) )

--"If we wanted to prove the above without pattern matching, this time we would need the
-- dependent version `𝕁` of induction on `_≡_`.
-- *Exercise*. Try to do this with `𝕁` and with `ℍ`.
-- !!! come back to this exercise later !!!

--"[A]ll arrows, the identifications, are invertible.
-- ⁻¹-left∙ : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
--  →        p ⁻¹ ∙ p ≡ refl y            -- (id arrows are applied from right)
-- ⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-left∙ : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
 →        p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

-- Note the symbols ∙ ∙ are differenct (though they look identical in some fonts)

-- ⁻¹-right∙ : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
--  →         p ∙ p ⁻¹ ≡ refl x           -- (id arrows applied from right)
-- ⁻¹-right∙ (refl x) = refl (refl x)

⁻¹-right∙  : {X : 𝓤 ̇} {x y : X} (p : x ≡ y) →   p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

--"A category in which all arrows are invertible is called a groupoid. The above is
-- the basis for the Hofmann--Streicher groupoid model of type theory. But we actually
-- get higher groupoids, because given identifications `p q : x ≡ y` we can consider
-- the identity type `p ≡ q`, and given `u v : p ≡ q` we can consider the type `u ≡ v`,
-- and so on. See https://arxiv.org/abs/0812.0298 and https://lmcs.episciences.org/1062.

--"For some types, such as the natural numbers, we can prove that this process trivializes
-- after the first step, because the type `x ≡ y` has at most one element. Such types are
-- the *sets* as defined above. Voevodsky defined *hlevel* to measure how long it takes
-- for the process to trivialize. (see hlevel type below)

--"[M]ore constructions with identifications:
⁻¹-involutive : {X : 𝓤 ̇}{x y : X} (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)

--"The application operation on identifications is functorial, in the sense that it
-- preserves the neutral element and commutes with composition."

-- ap preserves neutral element, i.e. `ap f (refl x) ≡ refl (f x)`
ap-refl : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (x : X) → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

-- ap is compatible with composition, i.e. `ap f (p ∙ q) ≡ ap f p ∙ ap f q`
ap-∙ : {X : 𝓤 ̇} {Y : 𝓥 ̇}
       (f : X → Y)   {x y z : X}
       (p : x ≡ y)   (q : y ≡ z)
      -----------------------------------
 →    ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p (refl y) = refl (ap f p)

-- ap is compatible with inversion, i.e. `(ap f p)⁻¹ ≡ ap f (p ⁻¹)`
ap⁻¹ : {X : 𝓤 ̇} {Y : 𝓥 ̇}
       (f : X → Y) {x y : X}
       (p : x ≡ y)
      -----------------------------
 →    (ap f p)⁻¹ ≡ ap f (p ⁻¹)
ap⁻¹ f (refl x) = refl (refl (f x))

--"The above functions `ap-refl` and `ap-∙` constitute functoriality in the second argument.
-- We also have functoriality in the first argument.
ap-id : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)→ ap id p ≡ p
ap-id (refl x) = refl (refl x)

ap-∘ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
       (f : X → Y)  (g : Y → Z)  {x y : X}
       (p : x ≡ y)
      ----------------------------------------
 →    ap (g ∘ f) p ≡ (ap g ∘ ap f) p
ap-∘ f g (refl x) = refl (refl (g (f x)))

--"Transport is also functorial with respect to identification composition and function composition. By construction,
-- it maps the neutral element to the identity function. The apparent contravariance takes place because we have
-- defined function composition in the usual order, but identification composition in the diagramatic order.
transport∙ : {X : 𝓤 ̇}    (F : X → 𝓥 ̇)   {s t u : X}    (f : s ≡ t)    (g : t ≡ u)
           ------------------------------------------------------------
 →                  transport F (f ∙ g) ≡ transport F g ∘ transport F f
transport∙ F f (refl t) = refl (transport F f)

  --            F
  --     s -------------> Fs
  --      |                        /     \
  --   f  |   transport Ff /         \
  --      |                   ↙             |
  --     t --------> Ft              |  transport F (f ∘ g)
  --      |                    \            |
  --   g  |   transport Fg \        /
  --      |                         ↘  ↙
  --      u------------->  Fg

--"Functions of a type into a universe can be considered as generalized presheaves, which
-- we could perhaps call `∞`-presheaves. Their morphisms are natural transformations:
Nat : {X : 𝓤 ̇} → (X → 𝓥 ̇) → (X → 𝓦 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat F G = (s : domain F) → F s → G s

--[Before proceding, let's review the notion of natural transformation from category theory. Recall,
--if F G : 𝓒 → 𝓓 are functors, a natural transformation (α) from F to G (denoted α : F ⇒ G)  is an indexed
--family of arrows of 𝓓, indexed by the objects of 𝓒, satisfying the following naturality condition:
--   For each pair (s , t) of objects of 𝓒, and each f ∈ Hom(s, t), the following commutes:
--
--       s         F s   --- αₛ ---> G s
--       |            |                       |
--    f  |       Ff  |                       |  Gf    (the commutativity of this diagram 
--       ↓          ↓                      ↓          is referred to as "naturality")
--       t         F t  --- αₜ  ---> G t
--
--The Agda definition of `Nat` above is more general as F and G are not required to have the same codomains.
--On the other hand, it seems this development only concerns the categories of types where the objects (say, s t : X) are inhabitants
--of a given type X and the arrows (say, p : s ≡ t) are identifications of these objects.]

--"We don't need to specify the naturality condition, because it is automatic:
Nats-are-natural : {X : 𝓤 ̇} (F : X → 𝓥 ̇) (G : X → 𝓦 ̇)
                     (α : Nat F G)       {s t : X}          (p : s ≡ t)
                 ------------------------------------------------
 →                α t ∘ transport F p ≡ transport G p ∘ α s
Nats-are-natural F G α (refl s) = refl (α s)

--     s                         F s --- αₛ --->  G s
--     |                           |                         |
--   p : s ≡ t          transport F p           transport G p
--     ↓                         ↓                        ↓
--     t                        F t  --- αₜ  ---> G t

--"We will use the following constructions a number of times:
NatΣ : {X : 𝓤 ̇}{F : X → 𝓥 ̇}{G : X → 𝓦 ̇} → Nat F G   →    Σ F    →   Σ G
NatΣ α (s , v) = s , α s v

transport-ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} (G : Y → 𝓦 ̇)  (f : X → Y) {u₀ u : X} (p : u₀ ≡ u) ( w : G (f u₀) )
                ------ ---------------------------------------------------------------------
 →                             transport (G ∘ f) p w ≡ transport G (ap f p) w
transport-ap G f (refl u₀) w = refl w

------------------------------------------------------------------------------------
-- Identifications that depend on identifications
-- -----------------------------------------------
--"If we have an identification `p : A ≡ B` of two types `A` and `B`, and elements `a : A` and `b : B`, we cannot ask directly
-- whether `a ≡ b`, because although the types are identified by `p`, they are not necessarily the same, in the sense of
-- definitional equality. This is not merely a syntactical restriction of our formal system, but instead a fundamental fact that
-- reflects the philosophy of univalent mathematics. For instance, consider the type"
data Color : 𝓤₀ ̇ where
 Black White : Color

--"With univalence, we will have that `Color ≡ 𝟚` where `𝟚` is the two-point type `𝟙 + 𝟙` with elements `₀` and `₁`.
-- But there will be two identifications `p₀ p₁ : Color ≡ 𝟚`, one that identifies `Black` with `₀` and `White` with `₁`,
-- and another one that identifies `Black` with `₁` and `White` with `₀`. There is no preferred coding of binary colors as
-- bits. And, precisely because of that, even if univalence does give inhabitants of the type `Color ≡ 𝟚`, it doesn't make sense
-- to ask whether `Black ≡ ₀` holds without specifying one of the possible inhabitants `p₀` and `p₁`. What we will have is
-- that the functions `transport id p₀` and `transport id p₁` are the two possible bijections `Color → 𝟚` that identify
-- colors with bits. So, it is not enough to have `Color ≡ 𝟚` to be able to compare a color `c : Color` with a bit `b : 𝟚`. So
-- the meaningful comparison in the more general situation is `transport id p a ≡ b` for a specific `p : A ≡ B`, where `id`
-- is the identity function of the universe where the types `A` and `B` live, and hence `transport id : A ≡ B → (A → B)` is
-- the function that transforms identifications into functions.  More generally, we want to consider the situation in which we
-- replace the identity function `id` of the universe where `A` and `B` live by an arbitrary type family, which is what we do now.

--"If we have a type `X : 𝓤 ̇`, a type family `F : X → 𝓥 ̇`, points `u₀ u : X`, and an identification `p : u₀ ≡ u`, then we
-- get the identification `ap F p : F u₀ ≡ F u`.  However, if we have `v₀ : F u₀`, `v : F u`, we again cannot write down the
-- identity type ~~`v₀ ≡ v`~~ . This is again a non-sensical mathematical statement, because the types `F u₀` and `F u` are
-- not the same, but only identified, and in general there can be many identifications, not just `ap F p`, and so any identification
-- between elements of `F u₀` and `F u` has to be with respect to a specific identification, as in the above particular case.

--"This time, the meaningful comparison, given `p : u₀ ≡ u`, is `transport F p v₀ ≡ v`. For example, this idea applies when
-- comparing the values of a dependent function:
apd : {X : 𝓤 ̇} {F : X → 𝓥 ̇}    ( f : (u : X) → F u )   {u₀ u : X}    (p : u₀ ≡ u)  →  transport F p (f u₀) ≡ f u
apd f (refl u₀) = refl (f u₀)


------------------------------------------------------------------------------------------
-- Equality in Σ types
-- see: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality

--"With the above notion of dependent equality, we can characterize equality in `Σ` types as follows:
to-Σ-≡ : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ } {σ τ : Σ F}
 →      Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport F p (pr₂ σ) ≡ pr₂ τ
        -----------------------------------------------
 →                      σ ≡ τ
to-Σ-≡ (refl u , refl v) = refl (u , v)

from-Σ-≡ : {X : 𝓤 ̇ } {F : X → 𝓥 ̇ } {σ τ : Σ F}
 →                      σ ≡ τ
       ----------------------------------------------
 →      Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport F p (pr₂ σ) ≡ pr₂ τ
from-Σ-≡ (refl (u , v)) = (refl u , refl v)

--"The above gives the logical equivalence
--   `(σ ≡ τ) ⇔ Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport A p (pr₂ σ) ≡ pr₂ τ`.

--"But this is a very weak statement when the left- and right-hand identity types may have multiple elements, which is precisely
-- the point of univalent mathematics. What we want is the lhs and the rhs to be isomorphic, or more precisely, equivalent in the
-- sense of Voevodsky. Once we have defined the notion `_≃_` of type equivalence, this characterization will become an equivalence
--   `(σ ≡ τ) ≃ Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport A p pr₂ σ ≡ pr₂ τ`.
-- But even this is not sufficiently precise, because in general there are many equivalences between two types. For example, there
-- are precisely two equivalences `𝟙 + 𝟙 ≃ 𝟙 + 𝟙`, namely the identity function and the function that flips left and right.  What
-- we want to say is that a *specific map* is an equivalence. In our case, it is the function `from-Σ-≡` defined above.

--"Voevodsky came up with a definition of a type '`f` is an equivalence' which is always a subsingleton: a given function `f` can be
-- an equivalence in at most one way. In other words, being an equivalence is property of `f`, rather than data.
-- The following special case of `to-Σ-≡` is often useful:
to-Σ-≡' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {x : X} {a a' : A x}
 →               a ≡ a'
          ----------------------------
 →        Id (Σ A) (x , a) (x , a')
to-Σ-≡' {𝓤}{𝓥}{X}{A}{x} = ap (λ - → (x , -))

-- -----------------------------------------------------------------------------------
-- Voevodsky's notion of hlevel
-- see: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#hlevel

--"Voevodsky's hlevels `0,1,2,3,...` are shifted by `2` with respect to the `n`-groupoid numbering convention, and correspond
-- to `-2`-groupoids (singletons), `-1`-groupoids (subsingletons), `0`-groupoids (sets),... The `hlevel` relation is defined by
-- induction on `ℕ`, with the induction step working with the identity types of the elements of the type in question:
_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0 = is-singleton X
X is-of-hlevel succ n = (x x' : X) → ((x ≡ x') is-of-hlevel n)

--"It is often convenient in practice to have equivalent formulations of the types of hlevel `1` (as subsingletons) and `2` (as sets),
-- which we will develop soon.

-------------------------------------------------------------------
-- Hedberg's Theorem
-- ------------------
--"To characterize sets as the types of hlevel 2, we first need to show that subsingletons are sets, and this is not easy.
-- We use an argument due to Hedberg. This argument also shows that Voevodsky's hlevels are upper closed. We choose to
-- present an alternative formulation of Hedberg's Theorem, but we stress that the method of proof is essentially the same.
-- We first define a notion of constant map:
wconstant : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = (x x' : domain f) → f x ≡ f x'

--"The prefix "`w`" officially stands for "weakly". Perhaps *incoherently constant* or *wildly constant* would be better terminologies,
-- with *coherence* understood in the `∞`-categorical sense.

--"the type of constant endomaps of a given type:
wconstant-endomap : 𝓤 ̇ → 𝓤 ̇
wconstant-endomap X = Σ f ꞉ (X → X) , wconstant f

wcmap : (X : 𝓤 ̇) → wconstant-endomap X → (X → X)
wcmap X (f , w) = f

wcmap-constancy : (X : 𝓤 ̇) (c : wconstant-endomap X) → wconstant (wcmap X c)
wcmap-constancy X (f , w) = w

--"a type is a set iff its identity types have designated `wconstant` endomaps:
Hedberg : {X : 𝓤 ̇} (u₀ : X)  →  ( (u : X) → wconstant-endomap (u₀ ≡ u) ) 
          ---------------------------------------------------------
 →                    (u : X)   → is-subsingleton (u₀ ≡ u)
Hedberg {𝓤} {X} u₀ fwce u p q =
 p                        ≡⟨ a u p ⟩
 (f u₀ (refl u₀))⁻¹ ∙ f u p ≡⟨ ap (λ - → ( f u₀ (refl u₀) )⁻¹ ∙ - )  (κ u p q) ⟩
 (f u₀ (refl u₀))⁻¹ ∙ f u q ≡⟨ (a u q)⁻¹ ⟩
 q                        ∎
 where
  f : (u : X) → u₀ ≡ u → u₀ ≡ u
  f u = wcmap (u₀ ≡ u) (fwce u)

  κ : (u : X) (p q : u₀ ≡ u) → f u p ≡ f u q
  κ u = wcmap-constancy (u₀ ≡ u) (fwce u)

  a : (u : X) (p : u₀ ≡ u) → p ≡ ( f u₀ (refl u₀) )⁻¹ ∙ f u p
  a u₀ (refl u₀) = (  ⁻¹-left∙ (  ( f u₀ (refl u₀) )  )   )⁻¹  --  <-- I don't get it... (return to it later)

--------------------------------------------------------------------
-- A characterization of sets
-- --------------------------
--"We consider types whose identity types all have designated `wconstant` endomaps:
wconstant-≡-endomaps : 𝓤 ̇ → 𝓤 ̇
wconstant-≡-endomaps X = (x y : X) → wconstant-endomap (x ≡ y)

--"The following is immediate from the definitions." [Recall, `is-set X = (x y : X) → is-subsingleton (x ≡ y)`]
sets-have-wconstant-≡-endomaps : (X : 𝓤 ̇) → is-set X → wconstant-≡-endomaps X
sets-have-wconstant-≡-endomaps X Xset x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = p

  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = Xset x y p q

--"the converse is the content of Hedberg's Theorem.
types-with-wconstant-≡-endomaps-are-sets : (X : 𝓤 ̇)
 →                wconstant-≡-endomaps X
                 ---------------------------
 →                        is-set X
types-with-wconstant-≡-endomaps-are-sets X c x =
 Hedberg x (λ y → wcmap (x ≡ y) (c x y) , wcmap-constancy (x ≡ y) (c x y))

-----------------------------------------------------------------------
-- Subsingletons are sets
-- -----------------------
--"In the following definition of the auxiliary function `f`, we ignore the argument
-- `p`, using the fact that `X` is a subsingleton instead, to get a `wconstant` function:
subsingletons-have-wconstant-≡-endomaps : (X : 𝓤 ̇)
 →                                      is-subsingleton X
                                       ---------------------------
 →                                      wconstant-≡-endomaps X
subsingletons-have-wconstant-≡-endomaps X Xss x x' = (f , κ)
 where
  f : x ≡ x' → x ≡ x'
  f _ = Xss x x'

  κ : (p q : x ≡ x') → f p ≡ f q
  κ p q = refl (Xss x x')

--"And the corollary is that (sub)singleton types are sets.
subsingletons-are-sets : (X : 𝓤 ̇) → is-subsingleton X → is-set X
subsingletons-are-sets X s =
 types-with-wconstant-≡-endomaps-are-sets X (subsingletons-have-wconstant-≡-endomaps X s)

singletons-are-sets : (X : 𝓤 ̇) → is-singleton X → is-set X
singletons-are-sets X = subsingletons-are-sets X ∘ singletons-are-subsingletons X

--"In particular, the types `𝟘` and `𝟙` are sets.
𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingletons-are-sets 𝟘 𝟘-is-subsingleton

𝟙-is-set : is-set 𝟙
𝟙-is-set = subsingletons-are-sets 𝟙 𝟙-is-subsingleton

-----------------------------------------------------------------------
-- The types of hlevel 1 are the subsingletons
-- -------------------------------------------
--"with the above we get our desired characterization of the types of hlevel `1`
subsingletons-are-of-hlevel-1 : (X : 𝓤 ̇) → is-subsingleton X
                              ----------------------------
 →                             X is-of-hlevel 1
subsingletons-are-of-hlevel-1 X t x y = t x y , subsingletons-are-sets X t x y (t x y)

types-of-hlevel-1-are-subsingletons : (X : 𝓤 ̇)
 →                                   X is-of-hlevel 1
                                    ----------------------
 →                                   is-subsingleton X
types-of-hlevel-1-are-subsingletons X s x y = center (x ≡ y) (s x y)

--"This is an "iff" characterization, but, under univalence, it becomes an equality
-- because the types under consideration are subsingletons."

------------------------------------------------------------------------
-- The types of hlevel 2 are the sets
-- -------------------------------------
--"The same comments as for the previous section apply.
sets-are-of-hlevel-2 : (X : 𝓤 ̇) → is-set X → X is-of-hlevel 2
sets-are-of-hlevel-2 X t x y = subsingletons-are-of-hlevel-1 (x ≡ y) (t x y)
types-of-hlevel-2-are-sets : (X : 𝓤 ̇) → X is-of-hlevel 2 → is-set X
types-of-hlevel-2-are-sets X s x y = types-of-hlevel-1-are-subsingletons (x ≡ y) (s x y)

------------------------------------------------------------------------
-- The hlevels are upper closed
-- -----------------------------

--"A singleton is a subsingleton, a subsingleton is a set, ... , a type of hlevel `n` is
-- of hlevel `n+1` too, ... Again we can conclude this almost immediately from the above

hlevel-upper : (X : 𝓤 ̇) (n : ℕ) → X is-of-hlevel n → X is-of-hlevel (succ n)
hlevel-upper X zero = γ
 where
  γ : is-singleton X → (x y : X) → is-singleton (x ≡ y)
  γ h x y = p , subsingletons-are-sets X k x y p
   where
    k : is-subsingleton X
    k = singletons-are-subsingletons X h

    p : x ≡ y
    p = k x y
hlevel-upper X (succ n) = λ h x y → hlevel-upper (x ≡ y) n (h x y)

--"To be consistent with the above terminology, we have to stipulate that all types have
-- hlevel `∞`. We don't need a definition for this notion. But what may happen (and it does
-- with univalence) is that there are types which don't have any finite hlevel. We can say
-- that such types then have minimal hlevel `∞`.

_has-minimal-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X has-minimal-hlevel zero = X is-of-hlevel 0
X has-minimal-hlevel succ n = (X is-of-hlevel (succ n)) × ¬ (X is-of-hlevel n)

_has-minimal-hlevel-∞ : 𝓤 ̇ → 𝓤 ̇
X has-minimal-hlevel-∞ = (n : ℕ) → ¬(X is-of-hlevel n)


--"The type `𝟘` has minimal hlevel `1`, the type `ℕ` has minimal hlevel `2`. The solution
-- to the fact that `ℕ` has hlevel 2 is given in the next section.

--"*Exercise*. Formulate and prove... the type `𝟙` has minimal hlevel `0`. More ambitiously,
-- after univalence is available, show that the type of monoids has minimal hlevel `3`."
--
-- SOLUTION (incomplete... !!!come back to this later!!!)
𝟙-is-of-hlevel-2 : 𝟙 is-of-hlevel 2
𝟙-is-of-hlevel-2 = sets-are-of-hlevel-2 𝟙 𝟙-is-set

----------------------------------------------------------------------
-- `ℕ` and `𝟚` are sets
-- ----------------------
--"If a type has decidable equality we can define a `wconstant` function `x ≡ y → x ≡ y` and
-- hence conclude that it is a set. This argument is due to Hedberg.

pointed-types-have-wconstant-endomap : {X : 𝓤 ̇} → X → wconstant-endomap X
pointed-types-have-wconstant-endomap x = ( (λ y → x) , λ y z → refl x )

empty-types-have-wconstant-endomap : {X : 𝓤 ̇} → is-empty X → wconstant-endomap X
empty-types-have-wconstant-endomap e = ( id , λ x x' → !𝟘 (x ≡ x') (e x) )

decidable-has-wconstant-endomap : {X : 𝓤 ̇} → decidable X → wconstant-endomap X
decidable-has-wconstant-endomap (inl x) = pointed-types-have-wconstant-endomap x
decidable-has-wconstant-endomap (inr e) = empty-types-have-wconstant-endomap e

hedberg-lemma : {X : 𝓤 ̇} → has-decidable-equality X → wconstant-≡-endomaps X
hedberg-lemma {𝓤}{X} d x y = decidable-has-wconstant-endomap (d x y)

hedberg : {X : 𝓤 ̇} → has-decidable-equality X → is-set X
hedberg {𝓤}{X} d = types-with-wconstant-≡-endomaps-are-sets X (hedberg-lemma d)

ℕ-is-set : is-set ℕ
ℕ-is-set = hedberg ℕ-has-decidable-equality

𝟚-is-set : is-set 𝟚
𝟚-is-set = hedberg 𝟚-has-decidable-equality

--"Notice that excluded middle implies directly that all sets have decidable equality,
-- so that in its presence a type is a set iff it has decidable equality."



-------------------------------------------------------------------------------------------------
{-RETRACTS
   ----------
   As MHE explains (see https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#retracts )
   retract are used as a mathematical technique to transfer properties between types.

  "For instance, retracts of singletons are singletons. Showing that a particular type `X` is a singleton may be difficult to do directly...
   but it may be easy to show that `X` is a retract of `Y` for a type `Y` that is already known to be a singleton.... a major application
   will be to get a simple proof of the fact that invertible maps are equivalences in the sense of Voevodsky." -}

--A *section* of a function g : Y → X is a right inverse (i.e., f : X → Y such that g ∘ f = id)
has-section has-right-inv is-surjective : {X : 𝓤 ̇}{Y : 𝓥 ̇} → (Y → X) → 𝓤 ⊔ 𝓥 ̇
has-section g = Σ f ꞉ (codomain g → domain g), g ∘ f ∼ id         --i.e., ∀ (x : X) , (g ∘ f) x ≡ id x ≡ x
has-right-inv = has-section -- alias
is-surjective = has-section  -- alias (recall, surjective functions are those with sections)

--A *retraction* of a function f : X → Y is a left inverse (i.e., g : Y → X such that g ∘ f = id)
has-retraction has-left-inv is-injective : {X : 𝓤 ̇}{Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction r = Σ s ꞉ (codomain r → domain r),  s ∘ r ∼ id        --i.e., ∀ (x : X) , (s ∘ r) x ≡ id x ≡ x
has-left-inv = has-retraction  -- alias
is-injective = has-retraction    -- alias  (recall, injective functions are those with retractions)

--X is a retract of Y, written X ◁ Y, iff ∃ function g : Y → X that has a section (right-inverse).
_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇              -- NOTATION: type ◁ with `\lhd`
X ◁ Y = Σ g ꞉ (Y → X), has-section g
infix  10 _◁_
--An inhabitant `𝓻 : X ◁ Y` of a retraction type is a triple `𝓻 = (g , f , η)` where g : Y → X  is a surjective function with section
--`(f , η) : has-section g`, so f : X → Y and `η : g ∘ f ~ id`.


--X embeds in Y, written X ↪ Y, iff ∃ function f : X → Y that has a retraction (left-inverse).
_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇              -- NOTATION: type ↪ with `\hookrightarrow`
X ↪ Y = Σ f ꞉ (X → Y), has-retraction f
infix  10 _↪_
--An inhabitant `𝓮 : X ↪ Y` of an embedding type is a triple `𝓮 = (f , g , ε)` where `f : X → Y`  is an injective function (the embedding map)
--with retraction (g , ε) : has-retraction f so g : Y → X and ε : g ∘ f ~ id.

--"A function that has a section is called a retraction. We use this... also for the function that projects out the retraction:
retraction : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ◁ Y → Y → X
retraction (r , s , η) = r

section : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ◁ Y → X → Y
section (r , s , η) = s

retract-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }  (ρ : X ◁ Y) → (retraction ρ ∘ section ρ) ∼ (𝑖𝑑 X)
retract-equation (r , s , η) = η

retraction-has-section : {X : 𝓤 ̇} {Y : 𝓥 ̇} (ρ : X ◁ Y) → has-section (retraction ρ)
retraction-has-section (r , h) = h

--Similarly, for embeddings and their left inverses (which we call "extractions"):
extraction left-inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ↪ Y → Y → X
extraction (f , g , ε) = g
left-inverse = extraction -- alias

embedding right-inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ↪ Y → X → Y
embedding (f , g , ε) = f
right-inverse = embedding -- alias

--The name "extraction" seems suitable since embedding followed by extraction is identity:
embedding-equation : {X : 𝓤 ̇} {Y : 𝓥 ̇}  (𝓮 : X ↪ Y)
 →                 (extraction 𝓮 ∘ embedding 𝓮) ∼ (𝑖𝑑 X)
embedding-equation (f , g , ε) = ε
--(The name enforces the order---you only can't extract something that isn't first embedded.)

--An identity retraction
id-◁ : (X : 𝓤 ̇) → X ◁ X
id-◁ X = 𝑖𝑑 X , 𝑖𝑑 X , refl

--"*Exercise*. The identity retraction is by no means the only retraction of a type onto itself in general, of course.
-- Prove that we have (that is, produce an element of the type) `ℕ ◁ ℕ` with the function `pred : ℕ → ℕ` defined
-- above as the retraction. Try to produce more inhabitants of this type.
--
--SOLUTION.
--example 1.
ℕ-◁-ℕ-id : ℕ ◁ ℕ
ℕ-◁-ℕ-id = id-◁ ℕ
--example 2.
ℕ-◁-ℕ-pred : ℕ ◁ ℕ
ℕ-◁-ℕ-pred = pred , succ , refl
--example 3.
ℕ-◁-ℕ-add-two : ℕ ◁ ℕ 
ℕ-◁-ℕ-add-two = sub-two , add-two , refl
 where
  add-two : ℕ → ℕ
  add-two n = succ (succ n)

  sub-two : ℕ → ℕ
  sub-two 0 = 0
  sub-two (succ 0) = succ 0
  sub-two (succ (succ n)) = n

--"We can define the composition of two retractions as follows:
_◁∘_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ◁ Y → Y ◁ Z → X ◁ Z
(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
 where  -- Goal: (λ x → r (r' (s' (s x)))) ∼ (λ x → x)
  η'' = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
                         r (s x) ≡⟨ η x ⟩
                               x ∎

--"For notational convenience we also define composition with an implicit argument made explicit, and introduce postfix notation
-- for the identity retraction.
_◁⟨_⟩_ : (X : 𝓤 ̇) {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ
infixr  0 _◁⟨_⟩_        -- NOTATION. Type ◁⟨_⟩ with `\lhd\<_\>

_◀ : (X : 𝓤 ̇) → X ◁ X
X ◀ = id-◁ X
infix   1 _◀    -- NOTATION. Type ◀ with `\T` or `\T1`

{-"We conclude this section with some facts about retracts of `Σ` types. The following are technical tools for dealing with
   equivalences in the sense of Voevosky in comparison with invertible maps." -}

--"A pointwise retraction gives a retraction of the total spaces:
Σ-retract : {X : 𝓤 ̇}{A : X → 𝓥 ̇}{B : X → 𝓦 ̇}
 →             ( (x : X) → A x ◁ B x )
               ------------------------------
 →               Σ A ◁ Σ B
Σ-retract {𝓤}{𝓥}{𝓦}{X}{A}{B} ρ = NatΣ r , NatΣ s , η'
 where
  r : (x : X) → B x → A x
  r x = retraction (ρ x)

  s : (x : X) → A x → B x
  s x = section (ρ x)

  η : (x : X) (a : A x) → r x (s x a ) ≡ a
  η x = retract-equation (ρ x)

  η' : (σ : Σ A) → NatΣ r (NatΣ s σ) ≡ σ
  η' (x , a) = x , r x (s x a) ≡⟨ to-Σ-≡' (η x a) ⟩ x , a ∎

--"We have that `transport A (p ⁻¹)` is a two-sided inverse of `transport A p` using the functoriality of `transport A`, or
-- directly by induction on `p`:
transport-is-retraction : {X : 𝓤 ̇}
           (A : X → 𝓥 ̇)   {x y : X}   (p : x ≡ y)
        -- ------------------------------------
 →     transport A p ∘ transport A (p ⁻¹) ∼ 𝑖𝑑 (A y)

transport-is-retraction A (refl x) = refl

transport-is-section : {X : 𝓤 ̇}
           (A : X → 𝓥 ̇)    {x y : X}      (p : x ≡ y)
         ---------------------------------------
 →      transport A (p ⁻¹) ∘ transport A p ∼ 𝑖𝑑 (A x)
transport-is-section A (refl x) = refl

--"Using this, we have the following reindexing retraction of `Σ` types:"
Σ-reindexing-retract : {X : 𝓤 ̇} {Y : 𝓥 ̇}{A : X → 𝓦 ̇}
              (r : Y → X)    →        has-section r
            ------------------------------------
 →          ( Σ x ꞉ X , A x ) ◁ ( Σ y ꞉ Y , A (r y) )

Σ-reindexing-retract {𝓤}{𝓥}{𝓦}{X}{Y}{A} r (s , η) = γ , φ , γφ
 where
  γ : Σ (A ∘ r) → Σ A
  γ (y , a) = (r y , a)

  φ : Σ A → Σ (A ∘ r)
  φ (x , a) = s x , transport A ((η x)⁻¹) a

  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = p
   where
    p : (r (s x) , transport A ((η x)⁻¹) a) ≡ (x , a)
    p = to-Σ-≡ (η x , transport-is-retraction A (η x) a)

--"We have defined the property of a type being a singleton. The singleton type `Σ y ꞉ X , x ≡ y` induced by a point `x : X` of a type
-- `X` is denoted by `singleton-type x`. The terminology is justified by the fact that it is indeed a singleton in the sense defined above.
singleton-type : {X : 𝓤 ̇} → X → 𝓤 ̇
singleton-type {𝓤}{X} u₀ = Σ u ꞉ X , u ≡ u₀

singleton-type-center : {X : 𝓤 ̇} (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

singleton-type-centered : {X : 𝓤 ̇} (x : X) (σ : singleton-type x) → singleton-type-center x ≡ σ
singleton-type-centered x (x , refl x) = refl (x , refl x)

singleton-types-are-singletons : (X : 𝓤 ̇) (x : X) → is-singleton (singleton-type x)
singleton-types-are-singletons X x = singleton-type-center x ,  singleton-type-centered x

--"The following gives a technique for showing that some types are singletons:
retract-of-singleton : {X : 𝓤 ̇}{Y : 𝓥 ̇}
 →                    Y ◁ X  →  is-singleton X
                      -------------------------
 →                        is-singleton Y
retract-of-singleton (r , s , η) (✦ , φ) = r ✦ , γ
 where  γ = λ y → r ✦ ≡⟨ ap r (φ  (s y)) ⟩ r (s y) ≡⟨ η y ⟩  y ∎

--"Sometimes we need the following symmetric versions of the above.
singleton-type' : {X : 𝓤 ̇} → X → 𝓤 ̇
singleton-type' {𝓤}{X} u₀ = Σ u ꞉ X , u₀ ≡ u

singleton-type'-center : {X : 𝓤 ̇}(u : X) → singleton-type' u
singleton-type'-center u = (u , refl u)

singleton-type'-centered : {X : 𝓤 ̇} (u : X) (σ : singleton-type' u) → singleton-type'-center u ≡ σ
singleton-type'-centered u (u , refl u) = refl (u , refl u)

singleton-types'-are-singletons : (X : 𝓤 ̇) (u : X) → is-singleton (singleton-type' u)
singleton-types'-are-singletons X u = singleton-type'-center u , singleton-type'-centered u


------------------------------------------------------------------------------------------
--EQUIVALENCE.
--REF: Based on Martin Escardo's course notes
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#fibersandequivalences
--NOTE: formerly this content was in the file UF-Equivalence.agda, which was since merged into this file

-----------------------------------------------------------------------
-- Voevodsky's notion of type equivalence
-- ---------------------------------------
--(Paraphrazing Escardo) the main notions of univalent mathematics conceived of by Voevodsky are
--  * `singleton` types (called "contractible" types by Voevodsky),
--  * `hlevel` (including the notions of `subsingleton` and `set`), and
--  * type equivalence.
--In this section "type equivalence" is defined.

--"We begin with... *invertible function*, whose only difference from "equivalence" is that it is data rather than property.
invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
invertible f = Σ g ꞉ (codomain f → domain f) , (g ∘ f ∼ id) × (f ∘ g ∼ id)

--"...we will have a logical equivalence between *data* establishing invertibility of a function, and the *property* of the function being an equivalence."

--"Mathematically, what happens is that the type `is-equiv f` is a retract of the type `invertible f`. This retraction property is not easy to
-- show, and there are many approaches. We discuss an approach we [i.e., MHE] came up with while developing these lecture notes, which is
-- intended to be relatively simple and direct, but the reader should consult other approaches, such
-- as that of the HoTT book, which has a well-established categorical pedigree.

--"The problem with the notion of invertibility of `f` is that, while we have that the inverse `g`
-- is unique when it exists, we cannot in general prove the identification data `g ∘ f ∼ id`
-- and `f ∘ g ∼ id` are also unique, and, indeed, they are not in general
-- (see: https://github.com/HoTT/HoTT/blob/master/contrib/HoTTBookExercises.v).

--"The following is Voevodsky's proposed formulation of the notion of equivalence in MLTT,
-- which relies on the concept of `fiber`:

fiber : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ x ꞉ domain f , f x ≡ y
--[`fiber f y` is a pair `(x , p)` where `x : X` is such that `p : f x ≡ y`]
--[INTUITION. if f x ≡ y, then `fiber f y` is the f-kernel class containing x; in other terms,
--            `fiber f y` is the f-kernel class x ∈ f⁻¹{y}.)

fiber-point : {X : 𝓤 ̇}{Y : 𝓥 ̇}{f : X → Y}{y : Y} → fiber f y → X
fiber-point (x , p) = x

fiber-identification : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y} {y : Y} → (w : fiber f y) → f (fiber-point w) ≡ y
fiber-identification (x , p) = p

--"Voevodsky's insight is that a general notion of equivalence can be formulated in MLTT by requiring fibers to be singletons.
-- It is important here that not only the `x : X` with `f x ≡ y` is unique, but also that the identification datum `p : f x ≡ y` is unique.
-- This is similar to, or even a generalization of, the categorical notion of 'uniqueness up to a unique isomorphism'.
is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-equiv f = (y : codomain f) → is-singleton (fiber f y)

--[INTUTION. A map f : X → Y establishes an equivalence betwee X and Y provided it is one-to-one and onto;
--                  i.e., ∀ (y : Y), ∃! x : X, f x ≡ y`;
-- here (in MLTT) the uniqueness refers not only to x but also to the proof `η : f x ≡ y`.
-- In other terms, f : X → Y is an equivalence iff for each y : Y, the type `f⁻¹{y}` has preciely one inhabitant (i.e., is a singleton)
-- AND for each x the type `f x ≡ y` has preciely one inhabitant (i.e., proof); i.e., is a singleton.

--Obviously such an equivalence is invertible.
inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-equiv f → (Y → X)
inverse f e y = fiber-point (center (fiber f y) (e y))

inverses-are-sections : {X : 𝓤 ̇} {Y : 𝓥 ̇}
                             (f : X → Y) (e : is-equiv f)
                          --------------------------
 →                          f ∘ inverse f e ∼ id

inverses-are-sections f e y = fiber-identification (center ((fiber f y)) (e y))

--ALIAS. section ↔ right-inverse
inv-elim-right : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y)(e : is-equiv f) → f ∘ inverse f e ∼ id
inv-elim-right = inverses-are-sections

--[This says `inverse f e` is a *right* inverse of f. We can also show `inverse f e` is a *left* inverse of f, but this takes a bit more work.]
inverse-centrality : {X : 𝓤 ̇}{Y : 𝓥 ̇} (f : X → Y)(e : is-equiv f)(y : Y) (t : fiber f y)
 →                  (inverse f e y , inverses-are-sections f e y) ≡ t
inverse-centrality f e y = centrality (fiber f y) (e y)

inverses-are-retractions : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y)(e : is-equiv f)
 →                        inverse f e ∘ f ∼ id
inverses-are-retractions f e x = ap fiber-point p
 where p : inverse f e (f x) , inverses-are-sections f e (f x) ≡ x , refl (f x)
       p = inverse-centrality f e (f x) (x , (refl (f x)))

--ALIAS. retraction ↔ left-inverse
inv-elim-left : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y)(e : is-equiv f) → inverse f e ∘ f ∼ id
inv-elim-left = inverses-are-retractions

equivs-are-invertible : {X : 𝓤 ̇}{Y : 𝓥 ̇} (f : X → Y) → is-equiv f → invertible f
equivs-are-invertible f e = f⁻ , f⁻∘f∼id , f∘f⁻∼id
 where f⁻ = inverse f e
       f⁻∘f∼id = inv-elim-left f e
       f∘f⁻∼id = inv-elim-right f e

--ALIAS
equiv-inv : {X : 𝓤 ̇}{Y : 𝓥 ̇} (f : X → Y) → is-equiv f → invertible f
equiv-inv = equivs-are-invertible

--EXERCISE.
--Given `f : X → Y` and `e : is-equiv f`, prove that the inverse of f, `inverse f e` is itself invertible.
--SOLUTION.
equiv-invertible-inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (e : is-equiv f) → invertible (inverse f e)
equiv-invertible-inverse f e = f , inverses-are-sections f e , inverses-are-retractions f e

--EXERCISE.
--Given f : X → Y and e : is-equiv f, prove that the inverse of f is unique by completing the following or, if it seems impossible, explain why.
-- inverse-is-inverse : {X : 𝓤 ̇}{Y : 𝓥 ̇} (f : X → Y)(e : is-equiv f)((g , η) : invertible f) → g ∼ inverse f e
-- inverse-is-inverse f e (g , η) = ?
--SOLUTION.
inverse-is-unique : {X : 𝓤 ̇}{Y : 𝓥 ̇} (f : X → Y)(e : is-equiv f)((g , η) : invertible f) → g ∼ inverse f e
inverse-is-unique {Y = Y} f e (g , η) = γ
  where
   ζ : (y : Y) → (f (pr₁ (pr₁ (e y)))) ≡ y
   ζ y = pr₂ (pr₁ (e y) )

   ξ : (y : Y) → g (f (pr₁ (pr₁ (e y)))) ≡ pr₁ (pr₁ (e y))
   ξ y = (pr₁ η) (pr₁ (pr₁ (e y)))

   τ : (y : Y) → pr₁ (pr₁ (e y)) ≡ inverse f e (f (pr₁ (pr₁ (e y))))
   τ y = ((inverses-are-retractions f e) (pr₁ (pr₁ (e y))))⁻¹

   γ : (y : Y) → g y ≡ inverse f e y
   γ y = let x = pr₁ (pr₁ (e y)) in
     g y                     ≡⟨ ap (λ - → g -) (ζ y)⁻¹ ⟩
     g (f x)                 ≡⟨ ξ y ⟩
     x                        ≡⟨ τ y ⟩
     (inverse f e) (f x)  ≡⟨ ap (λ - → inverse f e -) (ζ y) ⟩
     inverse f e y        ∎

--"The non-trivial direction derives the equivalence property from invertibility data, for which we use...retraction.
-- Suppose invertibility data for a map `f : X → Y` are given as follows:
--
--    `g : Y → X` , `η : (x : X) → g (f x) ≡ x` ,  `ε : (y : Y) → f (g y) ≡ y`
--
-- and a point `y₀` in `codomain f` is given. We  show the fiber `Σ x ꞉ X , f x ≡ y₀` of `y₀` is a singleton.
--
-- 1. use assumption `ε` to show the type `f (g y) ≡ y₀` is a retract  of the type `y ≡ y₀` for any given `y : Y`.
--
--   To get the section `s : f (g y) ≡ y₀ → y ≡ y₀`, we transport along the identification `ε y : f (g y) ≡ y` over the family
--   `A - = (- ≡ y₀)`, which can be abbreviated as `_≡ y₀`.
--
--   To get the retraction `r` in the opposite direction, we transport along the inverse of the identification `ε y` over the same family.
--   (We already know that this gives a section-retraction pair by `transport-is-section`.)
--
-- 2. the type `Σ x ꞉ X , f x ≡ y₀` is a retract of the type `Σ y ꞉ Y , f (g y) ≡ y₀`
--    (by `Σ-reindexing-retract` using the assumption that `η` exibits `g` as a section of `f`)
--    which in turn is a retract of the type `Σ y ꞉ Y , y ≡ y₀` by applying `Σ` to both sides of the retraction
--    `(f (g y) ≡ y₀) ◁ (y ≡ y₀)` of the previous step.
--
--    This amounts to saying the type `fiber f y₀` is a retract of `singleton-type y₀`.

-- 3. But then we are done, because singleton types are singletons and retractions of singletons are singletons.
--
--Summary: Recall, the reindexing retraction of `Σ` types:"
--
--  Σ-reindexing-retract : {X : 𝓤 ̇} {Y : 𝓥 ̇}{A : X → 𝓦 ̇}
--                         (r : Y → X)   →   has-section r
--                       ------------------------------
--   →                   (Σ x ꞉ X , A x) ◁ (Σ y ꞉ Y , A (r y))
--
--  So we apply this with r = g and A = λ x → (f x ≡ y₀), to get
--
--    Σ x ꞉ X , f x ≡ y₀   ◁   Σ y ꞉ Y , f (g y) ≡ y₀
--
--  Recall, `f (g y) ≡ y₀  ◁  y ≡ y₀` means `∃ r : (y ≡ y₀) → (f (g y) ≡ y₀),
--
--    ∀ p : (f (g y) ≡ y₀),    ∃! q : (y ≡ y₀) st r q = p`
--
--  Next, apply `Σ` to both sides of the retract  (f (g y) ≡ y₀)  ◁  (y ≡ y₀) to get
--
--    Σ y ꞉ Y , f (g y) ≡ y₀   ◁   Σ y ꞉ Y , y ≡ y₀.

invertibles-are-equivs : {X : 𝓤 ̇}{Y : 𝓥 ̇}
              (f : X → Y)    →    invertible f
           ---------------------------------
 →                      is-equiv f
invertibles-are-equivs {𝓤}{𝓥}{X}{Y} f (g , η , ε) y₀ = iii
 where
  i : (y : Y) → (f (g y) ≡ y₀) ◁ (y ≡ y₀)
  i y = r , s , transport-is-section (_≡ y₀) (ε y)
   where
    s : f (g y) ≡ y₀ → y ≡ y₀
    s = transport (_≡ y₀) (ε y)

    r : y ≡ y₀ → f (g y) ≡ y₀
    r = transport (_≡ y₀) ((ε y)⁻¹)

  ii : fiber f y₀ ◁ singleton-type y₀ -- Recall:
                                      -- singleton-type x = Σ y ꞉ X , y ≡ x
  ii = (Σ x ꞉ X , f x ≡ y₀)     ◁⟨ Σ-reindexing-retract g (f , η) ⟩
       (Σ y ꞉ Y , f (g y) ≡ y₀) ◁⟨ Σ-retract i                    ⟩
       (Σ y ꞉ Y , y ≡ y₀)       ◀

  iii : is-singleton (fiber f y₀)   -- Recall:
                                    --  is-singleton X = Σ c ꞉ X  , is-center X c
                                    --  is-center X c = (x : X) → c ≡ x
  iii = retract-of-singleton ii (singleton-types-are-singletons Y y₀)

--ALIAS
invertible-equiv : {X : 𝓤 ̇}{Y : 𝓥 ̇} (f : X → Y) → invertible f → is-equiv f
invertible-equiv = invertibles-are-equivs

--"An immediate consequence is that inverses of equivalences are themselves equivalences:
inverses-are-equivs : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y)(e : is-equiv f)
 →                   is-equiv (inverse f e)
inverses-are-equivs f e = invertibles-are-equivs (inverse f e)
                       (f , inverses-are-sections f e  , inverses-are-retractions f e )
--ALIAS
inv-equiv  : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y)(e : is-equiv f) → is-equiv (inverse f e)
inv-equiv = inverses-are-equivs

--"Notice that inversion is involutive on the nose:
inversion-involutive : {X : 𝓤 ̇}{Y : 𝓥 ̇} (f : X → Y)(e : is-equiv f)
 →                    inverse (inverse f e) (inv-equiv f e) ≡ f
inversion-involutive f e = refl f

--ALIAS
inverse-involution : {X : 𝓤 ̇}{Y : 𝓥 ̇} (f : X → Y)(e : is-equiv f) → inverse (inverse f e) (inv-equiv f e) ≡ f
inverse-involution = inversion-involutive

--"To see that the above procedures do exhibit the type "`f` is an equivalence" as a retract
-- of the type "`f` is invertible", it suffices to show that it is a subsingleton (see:
-- `subsingletons-are-retracts-of-logically-equivalent-types`, `being-equiv-is-subsingleton).

--"The identity function is invertible:
id-invertible : (X : 𝓤 ̇) → invertible (𝑖𝑑 X)
id-invertible X = 𝑖𝑑 X , refl , refl

--"We can compose invertible maps:
∘-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {f' : Y → Z}
             → invertible f' → invertible f → invertible (f' ∘ f)

∘-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {f'}
  (g' , g'f'∼id ,  f'g'∼id) (g , gf∼id , fg∼id) = g ∘ g' , η , ε
 where
  η = λ x → -- Goal: g (g' (f' (f x))) ≡ x
        g (g' (f' (f x))) ≡⟨ ap g (g'f'∼id (f x)) ⟩
        g (f x)           ≡⟨ gf∼id x             ⟩
        x                 ∎  

  ε = λ z →  -- Goal: (f' ∘ f) (g (g' z)) ≡ z
       (f' ∘ f) (g (g' z)) ≡⟨ ap f' (fg∼id (g' z)) ⟩
       f' (g' z)           ≡⟨ f'g'∼id z ⟩
       z                   ∎

--"There is an identity equivalence, and we get composition of equivalences by reduction
-- to invertible maps:
id-is-equiv : (X : 𝓤 ̇) → is-equiv (𝑖𝑑 X)
id-is-equiv = singleton-types-are-singletons

--"An `abstract` definition is not expanded during type checking. One possible use of this
-- is efficiency. In our case, it saves about half a minute in the checking of this file
-- for correctness in the uses of `∘-is-equiv`:
∘-is-equiv : {X : 𝓤 ̇}{Y : 𝓥 ̇}{Z : 𝓦 ̇}{f : X → Y}{g : Y → Z}
 →          is-equiv g → is-equiv f
            ---------------------------
 →             is-equiv (g ∘ f)
∘-is-equiv {𝓤}{𝓥}{𝓦}{X}{Y}{Z}{f}{g} g-is-equiv f-is-equiv = γ
 where
  abstract
   γ : is-equiv (g ∘ f)
   γ = invertible-equiv (g ∘ f)
    (∘-invertible (equiv-inv g g-is-equiv)
                  (equiv-inv f f-is-equiv))


--"Because we have made the above definition abstract, we don't have access to the given
-- construction when proving things involving `∘-is-equiv`, such as the contravariance of
-- inversion:
inverse-of-∘ : {X : 𝓤 ̇}{Y : 𝓥 ̇}{Z : 𝓦 ̇}(f : X → Y) (g : Y → Z)
               (𝓠f : is-equiv f) (𝓠g : is-equiv g)
              ------------------------------------------------------------------------
 →            inverse f 𝓠f ∘ inverse g 𝓠g ∼ inverse (g ∘ f) (∘-is-equiv 𝓠g 𝓠f)
inverse-of-∘ f g 𝓠f 𝓠g =  λ z →
  -- Goal: (inverse f 𝓠f ∘ inverse g 𝓠g) z ≡ inverse (g ∘ f) (∘-is-equiv 𝓠g 𝓠f) z
  -- ...but rewriting the goal in notation defined below,
  -- Goal: (f⁻ ∘ g⁻) z ≡ gf⁻ z
  f⁻¹ (g⁻¹ z)                ≡⟨ (ap (f⁻¹ ∘ g⁻¹) (s z))⁻¹ ⟩
  f⁻¹ (g⁻¹ (g (f (gf⁻¹ z)))) ≡⟨ ap f⁻¹ (inv-elim-left g 𝓠g (f (gf⁻¹ z))) ⟩
  f⁻¹ (f (gf⁻¹ z))           ≡⟨ inv-elim-left f 𝓠f ((gf⁻¹ z)) ⟩
  gf⁻¹ z                     ∎

  where
  f⁻¹ = inverse f 𝓠f
  g⁻¹ = inverse g 𝓠g
  gf⁻¹ = inverse (g ∘ f) (∘-is-equiv 𝓠g 𝓠f)

  s : g ∘ f ∘ gf⁻¹ ∼ id
  s = inv-elim-right (g ∘ f) (∘-is-equiv 𝓠g 𝓠f)

--EQUIVALENCES----------------------------

--"The type of equivalences is defined as follows:
_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ f ꞉ (X → Y) , is-equiv f
infix  10 _≃_


--"Notice that this doesn't just say that `X` and `Y` are equivalent: the type `X ≃ Y` collects all the ways in which the types `X` and `Y`
-- are equivalent. For example, the two-point type `𝟚` is equivalent to itself in two ways, by the identity map, and by the map that
-- interchanges its two points, and hence the type `𝟚 ≃ 𝟚` has two elements.

--"Again it is convenient to have special names for its first and second projections:
Eq→fun : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ≃ Y → X → Y
Eq→fun (f , f-eq) = f

--ALIAS. NOTATION. type ⌜ and ⌝ with `\c1` and `\c2`; type ≃ with `\∼-`; type → with `\r1`
⌜_⌝ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ≃ Y → X → Y
⌜_⌝ = Eq→fun 

Eq→fun-is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} (e : X ≃ Y) → is-equiv (⌜ e ⌝)
Eq→fun-is-equiv (f , f-eq) = f-eq

⌜⌝-is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} (e : X ≃ Y) → is-equiv (⌜ e ⌝)
⌜⌝-is-equiv = Eq→fun-is-equiv

invertibility-gives-≃ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → invertible f → X ≃ Y
invertibility-gives-≃ f invf = f , invertible-equiv f invf

--"Examples: (each of the next three have proofs startingt with `invertibility-gives-≃`)
Σ-induction-≃ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇}{A : Σ Y → 𝓦 ̇}
 →             ((x : X)(y : Y x) → A (x , y)) ≃ ((z : Σ Y) → A z)
Σ-induction-≃ = invertibility-gives-≃ Σ-induction ( curry , refl , refl )

Σ-flip : {X : 𝓤 ̇} {Y : 𝓥 ̇}{A : X → Y → 𝓦 ̇}
 →      (Σ x ꞉ X , Σ y ꞉ Y , A x y) ≃ (Σ y ꞉ Y , Σ x ꞉ X , A x y)
Σ-flip = invertibility-gives-≃ (λ (x , y , p) → (y , x , p))
          ((λ (y , x , p) → (x , y , p)) , refl , refl)

×-comm : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X × Y) ≃ (Y × X)
×-comm = invertibility-gives-≃ (λ (x , y) → (y , x))
          ((λ (y , x) → (x , y)) , refl , refl)

--"The identity equivalence and the composition of two equivalences:

id-≃ : (X : 𝓤 ̇) → X ≃ X
id-≃ X = 𝑖𝑑 X , id-is-equiv X

infixl 30 _●_  -- NOTATION. type ● with `\cib`

_●_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
 →   X ≃ Y   →   Y ≃ Z
     ------------------------
 →          X ≃ Z
(f , d) ● (f' , e) = f' ∘ f , ∘-is-equiv e d

≃-sym : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ≃ Y → Y ≃ X
≃-sym (f , e) = inverse f e , inverses-are-equivs f e

--"We can use the following notation for equational reasoning with equivalences:
infixr  0 _≃⟨_⟩_
_≃⟨_⟩_ : (X : 𝓤 ̇) {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

infix   1 _■  -- NOTATION. type ■ with `\sq1`
_■ : (X : 𝓤 ̇) → X ≃ X  
_■ = id-≃   

--"We conclude this section with some important examples.

--"The function `transport A p` is an equivalence.
transport-is-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇){x y : X} (p : x ≡ y)
 →                  is-equiv (transport A p)
transport-is-equiv A (refl x) = id-is-equiv (A x)

--"Alternatively, we could have used the fact that `transport A (p ⁻¹)` is an inverse of `transport A p`.

--"Here is the promised characterization of equality in `Σ` types:
Σ-≡-≃ : {X : 𝓤 ̇} {A : X → 𝓥 ̇}(σ τ : Σ A)
 →     (σ ≡ τ) ≃ (Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport A p (pr₂ σ) ≡ pr₂ τ)
Σ-≡-≃ {𝓤} {𝓥} {X}{A} σ τ = invertibility-gives-≃ from-Σ-≡ (to-Σ-≡ , η , ε)
 where
  η : (q : σ ≡ τ) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  η (refl σ) = refl (refl σ)

  ε : (w : Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport A p (pr₂ σ) ≡ pr₂ τ) → from-Σ-≡ (to-Σ-≡ w) ≡ w
  ε (refl p , refl q) = refl ( refl p , refl q )

--"Similarly we have:
to-×-≡ : {X : 𝓤 ̇} {Y : 𝓥 ̇}{z t : X × Y}
 →      (pr₁ z ≡ pr₁ t) ×  (pr₂ z ≡ pr₂ t)
        ------------------------------------
 →       z ≡ t
to-×-≡ (refl x , refl y) = refl (x , y)

from-×-≡ : {X : 𝓤 ̇} {Y : 𝓥 ̇}{z t : X × Y}
 →         z ≡ t
          ------------------------------------
 →        (pr₁ z ≡ pr₁ t) ×  (pr₂ z ≡ pr₂ t)
from-×-≡  {𝓤} {𝓥} {X}{Y} (refl (x , y)) = refl x , refl y

×-≡-≃ : {X : 𝓤 ̇} {Y : 𝓥 ̇}(z t : X × Y)
 →      (z ≡ t) ≃ (pr₁ z ≡ pr₁ t) ×  (pr₂ z ≡ pr₂ t)
×-≡-≃ {𝓤} {𝓥} {X} {Y} z t = invertibility-gives-≃ from-×-≡ (to-×-≡ , η , ε)
 where
  η : (p : z ≡ t) → to-×-≡ (from-×-≡ p) ≡ p
  η (refl z) = refl (refl z)

  ε : (q : (pr₁ z ≡ pr₁ t) × (pr₂ z ≡ pr₂ t)) → from-×-≡ (to-×-≡ q) ≡ q
  ε (refl x , refl y) = refl ( refl x , refl y )

--"The following are often useful:
ap-pr₁-to-×-≡ : {X : 𝓤 ̇} {Y : 𝓥 ̇}{z t : X × Y}
 →             (p₁ : pr₁ z ≡ pr₁ t) → (p₂ : pr₂ z ≡ pr₂ t)
               -----------------------------------------------
 →             ap pr₁ (to-×-≡ (p₁ , p₂)) ≡ p₁
ap-pr₁-to-×-≡ (refl x) (refl y) = refl (refl x)

ap-pr₂-to-×-≡ : {X : 𝓤 ̇} {Y : 𝓥 ̇}{z t : X × Y}
 →             (p₁ : pr₁ z ≡ pr₁ t) → (p₂ : pr₂ z ≡ pr₂ t)
               -----------------------------------------------
 →             ap pr₂ (to-×-≡ (p₁ , p₂)) ≡ p₂
ap-pr₂-to-×-≡ (refl x) (refl y) = refl (refl y)

Σ-cong : {X : 𝓤 ̇} {A : X → 𝓥 ̇}{B : X → 𝓦 ̇}
 →     ((x : X) → A x ≃ B x) → Σ A ≃ Σ B
Σ-cong {𝓤} {𝓥} {𝓦} {X}{A}{B} φ = invertibility-gives-≃ (NatΣ f) (NatΣ g , NatΣ-η , NatΣ-ε)
 where
  f : (x : X) → A x → B x
  f x = ⌜ φ x ⌝

  g : (x : X) → B x → A x
  g x = inverse (f x) (⌜⌝-is-equiv (φ x))

  η : (x : X) (a : A x) → g x (f x a) ≡ a
  η x = inv-elim-left (f x) (⌜⌝-is-equiv (φ x))

  ε : (x : X) (b : B x) → f x (g x b) ≡ b
  ε x = inv-elim-right (f x)  (⌜⌝-is-equiv (φ x))

  NatΣ-η : (w : Σ A) → NatΣ g (NatΣ f w) ≡ w
  NatΣ-η (x , a) = x , g x (f x a) ≡⟨ to-Σ-≡' (η x a) ⟩ x , a ∎

  NatΣ-ε : (t : Σ B) → NatΣ f (NatΣ g t) ≡ t
  NatΣ-ε (x , b) = x , f x (g x b) ≡⟨ to-Σ-≡' (ε x b) ⟩ x , b ∎

≃-gives-◁ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ≃ Y → X ◁ Y
≃-gives-◁ (f , e) =  (f⁻¹ , f , inv-elim-left f e)
 where f⁻¹ = inverse f e
 --Explanation: the goal is X ◁ Y, which means we must produce an element of type
 --             `Σ r ꞉ (Y → X), has-section r`, where `has-section r` is
--              `Σ s ꞉ (codomain r → domain r), r ∘ s ∼ id`
-- In the present application, we take `r = f⁻¹ = inverse f e` and the proof of
-- `has-section f⁻¹` is `(f , inv-elim-left f e)`, since `inv-elim-left f e` gives `f⁻¹ ∘ f ∼ id.

--NOTATION. type ▷ with `\rhd`
≃-gives-▷ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ≃ Y → Y ◁ X
≃-gives-▷ (f , e) = (f , inverse f e , inv-elim-right f e)

equiv-to-singleton : {X : 𝓤 ̇} {Y : 𝓥 ̇}
 →                  X ≃ Y  →  is-singleton Y
                    ----------------------------
 →                   is-singleton X
equiv-to-singleton e = retract-of-singleton (≃-gives-◁ e)



---------------------



-- wjd added -----------------
--[`(g , η) : invertible f`  ==>  `g : Y → X`  and  `pr₁ η : (g ∘ f ∼ id)`  and  `pr₂ η : (f ∘ g ∼ id)`]
-- Exercise. Complete the following definitions for extracting the inverse map and
--           left- (resp. right-) identity of an invertible function.
--inv-map : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y) → invertible f → Y → X
--inv-map f (g , η) = ?
--
--inv-ids : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y)((g , η) : invertible f) → (g ∘ f ∼ id) × (f ∘ g ∼ id)
--inv-ids f (g , η) = ?
--
--inv-id-left : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y){gη : invertible f} → (pr₁ gη) ∘ f ∼ id
--inv-id-left f  {gη} = ?
--
--inv-id-right : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y){gη : invertible f} → f ∘ (pr₁ gη) ∼ id
--inv-id-right f  {gη} = ?
-- 
--inv-invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇}(f : X → Y){gη : invertible f} → invertible (pr₁ gη)
--inv-invertible f {g , η} = ?
--SOLUTIONS.
-- inv-map : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y) → invertible f → Y → X
-- inv-map f (g , η) = g

-- inv-ids : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y)((g , η) : invertible f) → (g ∘ f ∼ id) × (f ∘ g ∼ id)
-- inv-ids f (g , η) = pr₁ η , pr₂ η

-- inv-id-left : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y){gη : invertible f} → (pr₁ gη) ∘ f ∼ id
-- inv-id-left f {gη} = pr₁ (inv-ids f gη)

-- inv-id-right : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y){gη : invertible f} → f ∘ (pr₁ gη) ∼ id
-- inv-id-right f {gη} = pr₂ (inv-ids f gη)

-- inv-invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇}(f : X → Y){gη : invertible f} → invertible (pr₁ gη)
-- inv-invertible f {g , η} = f , inv-ids g (f , pr₂ η , pr₁ η)
-- end wjd added -----------------







------------------------------------------------------------------------------------------------------------















