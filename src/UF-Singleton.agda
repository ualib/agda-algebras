--FILE: UF-Singleton.agda
--DATE: 18 Mar 2020
--BLAME: williamdemeo@gmail.com
--REF: Based on Martin Escardo's course notes
--     cf. https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#subsingletonsandsets
--         https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Subsingletons.html
--     In particular, comments appearing in quotes below, along with the code to which those comments refer, are due to Martin Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Singleton where

open import UF-Prelude using (𝓤; 𝓥; _̇; _⁺; 𝟘; !𝟘; 𝟙; ⋆; 𝟙-induction; ¬; is-empty; -Σ; Σ; _,_; _×_; _+_; inl; inr; _≡_; refl; _≡⟨_⟩_; _∎; _⁻¹; _⇔_; ¬¬)

{-------------------------------------------------------------------------------------------------
 "Our univalent type theory
  -----------------------
   * A spartan MLTT (as above)
   * Univalence axiom (as below).
   * Subsingleton (or truth-value or propositional) truncations (as below).
  But...rather than postulating univalence and truncation, we will use them as explicit assumptions each time they are needed.
  We emphasize that there are univalent type theories in which univalence and existence of truncations are theorems, for
  example cubical type theory, which has a version available in Agda, called cubical Agda.
  (see: https://homotopytypetheory.org/2018/12/06/cubical-agda/ ) -}

----------------------------------------------------------------------------------
--"Singleton (or contractible) types.
-- Voevodsky defined a notion of *contractible type*, which we refer to here as *singleton type*.
is-center : (X : 𝓤 ̇) → X → 𝓤 ̇
is-center X ✦ = (u : X) → ✦ ≡ u   -- (type ✦ with `\st2`)

is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ ✦ ꞉ X  , is-center X ✦    -- (type the colon  as `\:4`)

--"Such an element `✦` is called a center of contraction of `X`."
𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ u → ⋆ ≡ u) (refl ⋆)

--"Once we have defined the notion of type equivalence, we will have that a type is a singleton if and only if it is equivalent to `𝟙`.
-- Let's adopt the following notation:
--   `X✦ :  is-singleton X`    (type ✦ with `\st2`)
--   `X✧ :  is-subsingleton X`   (type ✧ with `\st3`)
-- When working with singleton types, it will be convenient to have distinguished names for the two projections:
center : (X : 𝓤 ̇) → is-singleton X → X
center X (✦ , _ ) = ✦

centrality : (X : 𝓤 ̇)(X✦ : is-singleton X) (u : X) → center X X✦ ≡ u
centrality X (✦ , ✦-is-center ) = ✦-is-center

------------------------------------------------------------------------
--"Subsingletons (or propositions or truth values).
-- A type is a subsingleton if it has at most one element, that is, any two of its elements are equal, or identified.
is-subsingleton : 𝓤 ̇ →  𝓤 ̇
is-subsingleton X = (u u' : X) → u ≡ u'

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton u u' = !𝟘 (u ≡ u') u

singletons-are-subsingletons : (X : 𝓤 ̇) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (✦ , ✦-is-center) u u' = u ≡⟨ (✦-is-center u)⁻¹ ⟩ ✦ ≡⟨ ✦-is-center u' ⟩ u' ∎

𝟙-is-subsingleton : is-subsingleton 𝟙 
𝟙-is-subsingleton = singletons-are-subsingletons 𝟙 𝟙-is-singleton

pointed-subsingletons-are-singletons : (X : 𝓤 ̇) →  X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X u X✧ = (u , X✧ u)

singleton-iff-pointed-and-subsingleton : {X : 𝓤 ̇} → is-singleton X ⇔ (X × is-subsingleton X)
singleton-iff-pointed-and-subsingleton {𝓤}{X} = firstly , secondly
 where
  firstly : is-singleton X → (X × is-subsingleton X)
  firstly (✦ , ✦-is-center) = ✦ , singletons-are-subsingletons X (✦ , ✦-is-center)

  secondly : (X × is-subsingleton X) → is-singleton X
  secondly (u , X✧) = pointed-subsingletons-are-singletons X u X✧

--"The terminology stands for *subtype of a singleton* and is justified by the fact that a type `X` is a subsingleton according
-- to the above definition iff the map `X → 𝟙` is an *embedding*, iff `X` is embedded into a singleton.
-- Under *univalent excluded middle*, the empty type `𝟘` and the singleton type `𝟙` are the only subsingletons, up to equivalence,
-- or up to identity if we further assume univalence.

--"Subsingletons are also called propositions or truth values:
is-prop : 𝓤 ̇ → 𝓤 ̇           -- alias
is-prop = is-subsingleton

is-truth-value : 𝓤 ̇ → 𝓤 ̇    -- alias
is-truth-value = is-subsingleton

--"The terminology `is-subsingleton` is more mathematical and avoids the clash with the slogan 'propositions as types' which is
-- based on the interpretation of mathematical statements as arbitrary types, rather than just subsingletons. In these notes we
-- prefer the term *subsingleton*, but we occasionally use the terms *proposition* and *truth value*. When we wish to emphasize
-- this notion of proposition adopted in univalent mathematics, as opposed to "propositions as (arbitrary) types", we may say
-- *univalent proposition*.

--"In some formal systems, for example set theory based on first-order logic, one can tell that something is a proposition by looking
-- at its syntactical form, e.g. "there are infinitely many prime numbers" is a proposition, by construction, in such a theory.
-- In univalent mathematics, however, propositions are mathematical, rather than meta-mathematical, objects, and the fact that a type
-- turns out to be a proposition requires mathematical proof. Moreover, such a proof may be subtle and not immediate and require
-- significant preparation. An example is the proof that the univalence axiom is a proposition, which relies on the fact that univalence
-- implies function extensionality, which in turn implies that the assertion 'a map is an equivalence' is a proposition. Another non-trivial
-- example, which again relies on univalence or at least function extensionality, is the proof that the statement
--    'the type X is a proposition'
-- is itself a proposition, which can be written as `is-prop (is-prop X)` [or as `is-subsingleton (is-subsingleton X)`]
--Singletons and subsingletons are also called *-2-groupoids* and *-1-groupoids* respectively.

--"Sets (or 0-groupoids).
-- A type is defined to be a set if there is at most one way for any two of its elements to be equal:
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (u v : X) → is-subsingleton (u ≡ v)

--"...with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."

------------------------------------------------------------------------------------------
--"Univalent excluded middle [em]
-- ...under em the only two subsingletons up to equivalence are `𝟘` and `𝟙`. In fact, em in univalent mathematics says precisely that."
EM em : ∀ 𝓤 → 𝓤 ⁺ ̇
EM 𝓤 = (X : 𝓤 ̇) → is-subsingleton X → X + ¬ X
em = EM -- alias

EM' em' : ∀ 𝓤 → 𝓤 ⁺ ̇
EM' 𝓤 = (X : 𝓤 ̇) → is-subsingleton X → is-singleton X + is-empty X
em' = EM' -- alias

--"Notice that the above don't assert excluded middle, but instead say what excluded middle is, in two logically equivalent versions:
EM→EM' : EM 𝓤 → EM' 𝓤
EM→EM'  emu X X✧ =  γ (emu X X✧)
 where
  γ : X + ¬ X → is-singleton X + is-empty X
  γ (inl ✦) = inl (✦ , X✧ ✦) -- Recall, `X✧ : is-subsingleton X` is a map of type `(u u' : X) → u ≡ u'` so `X✧ ✦`  is a map that takes
  γ (inr ✧) = inr ✧            --                                                    each `u' : X` to `✦ ≡ u'` (i.e., `X✧` u is a proof of `is-center ✦`)

EM'→EM : EM' 𝓤 → EM 𝓤
EM'→EM emu' X X✧ = γ (emu' X X✧)
 where
  γ : is-singleton X + is-empty X → X + ¬ X
  γ (inl ✦) = inl (center X ✦)
  γ (inr ✧) = inr ✧

--"We will not assume or deny excluded middle [em], which is an independent statement (it can't be proved or disproved). We will
-- deliberately keep it undecided, adopting a neutral approach to the constructive vs. non-constructive dichotomy. We will however
-- prove a couple of consequences of [em] in discussions of foundational issues such as size and existence of subsingleton truncations.
-- We will also prove that [em] is a consequence of the axiom of choice. It should be emphasized that the potential failure of [em]
-- doesn't say that there may be mysterious subsingletons that fail to be singletons and also fail to be empty. No such things occur
-- in mathematical nature:
no-unicorns : ¬(Σ X ꞉ 𝓤 ̇ , is-subsingleton X × ¬(is-singleton X) × ¬(is-empty X))
no-unicorns (X , X✧ , ¬𝟙 , ¬𝟘) = false
 where
  X0 : is-empty X
  X0 u = ¬𝟙 (pointed-subsingletons-are-singletons X u X✧)

  false : 𝟘
  false = ¬𝟘 X0

--"Given this, what does the potential failure of [em] *mean*? That there is...
--
-- !!! no general way to determine which of the two cases `is-singleton X` or `is-empty X` applies for a given subsingleton `X` !!!
--
-- This kind of phenomenon should be familiar even in classical, non-constructive mathematics: although we are entitled to believe
-- that the Goldbach conjecture either holds or fails, we still don't know which one is the case, despite efforts by the sharpest
-- mathematical minds. A hypothetical element of the type `EM` would, in particular, be able to solve the Goldbach conjecture.
-- There is nothing wrong or contradictory with assuming the existence of such a magic blackbox. There is only loss of the implicit
-- algorithmic character of our type theory, which most mathematicians will be perfectly happy to live with. In these notes we don't
-- advocate any particular philosophy for or against [em] and other non-constructive principles. We confine ourselves to discussing
-- mathematical facts.

--"*Exercise*. We also have that it is impossible for `is-singleton X + is-empty X` to fail for a given subsingleton `X`, which amounts
-- to saying that `¬¬(is-singleton X + is-empty X)` always holds. (Occasionaly one hears people asserting that this says that the
-- double negation of excluded middle holds. But this is incorrect.. The above statement, when written in full, is
-- `(X : 𝓤 ̇ ) → is-subsingleton X → ¬¬(is-singleton X + is-empty X)`.
-- [ The incorrect assertion is:     ¬¬(∀ P → P ∨ ¬P);
--   The correct assertion is:       ∀P → ¬¬(P ∨ ¬P).   ]

--SOLUTION.
em'-irrefutable : (X : 𝓤 ̇ ) → is-subsingleton X → ¬¬(is-singleton X + is-empty X)
em'-irrefutable X X✧ ¬𝟙v𝟘 = ¬𝟙v𝟘 (inr X-is-empty)
 where
  X-is-empty : is-empty X
  X-is-empty u =  ¬𝟙v𝟘 ( inl (u , X✧ u) )

em-irrefutable : (X : 𝓤 ̇ ) → is-subsingleton X → ¬¬ (X + ¬ X)
em-irrefutable X X✧ not-Xv¬X = not-Xv¬X (inr ¬X)
 where
  ¬X : ¬ X
  ¬X x =  not-Xv¬X ( inl x )


--"This is a theorem, which is quite different from the double negation of [em], which is not a theorem and [says]
--   `¬¬( (X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X )`.
-- Just as [em], this is an independent statement."

--"*Exercise*. ...For any type `R` (replacing the empty type in the above), ∃ function `((X + (X → R)) → R) → R`, so that the kind
-- of phenomenon illustrated in the previous exercise has little to do with the emptiness of the empty type.

--SOLUTION.
general-em-irrefutable : (X : 𝓤 ̇) → (R : 𝓥 ̇) → ( (X + (X → R)) → R ) → R
general-em-irrefutable X R X⋁𝓸ᴿ = X⋁𝓸ᴿ  ( inr λ x → X⋁𝓸ᴿ (inl x) )

--[the label 𝓸ᴿ alludes to the fact that `(X → R) → R` is the type of (X-ary) operations on R.]

