--FILE: UF-Singleton.agda
--DATE: 18 Mar 2020
--UPDATE: 13 Jun 2020
--BLAME: williamdemeo@gmail.com
--REF: Much of this file is based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#subsingletonsandsets
--     https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Subsingletons.html
--     In particular, the quoted comments below, along with sections of code to which those comments
--     refer, are due to Martin Escardo. Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Singleton where

open import UF-Prelude using (𝓤; 𝓥; _̇; _⁺; 𝟘; !𝟘; 𝟙; ⋆; 𝟙-induction; ¬; is-empty; -Σ; Σ; _,_; _×_; _+_; inl; inr; _≡_; refl; _≡⟨_⟩_; _∎; _⁻¹; _⇔_; ¬¬)

{-(paraphrasing MHE) The univalent type theory developed here comprises
    * A spartan MLTT (as above)
    * Univalence axiom (as below)
    * Subsingleton (or truth-value or propositional) truncations (as below)
  Rather than postulating univalence and truncation, we will use them as explicit assumptions each time they
  are needed. N.B. there are other univalent type theories in which univalence and existence of truncations
  are THEOREMS; e.g., https://homotopytypetheory.org/2018/12/06/cubical-agda/-}

--"Voevodsky defined a notion of *contractible type*, which we refer to here as *singleton type*.
is-center : (X : 𝓤 ̇) → X → 𝓤 ̇
is-center X c = (u : X) → c ≡ u              -- NOTATION: type ✦ with `\st2`

is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ c ꞉ X  , is-center X c    -- NOTATION: type the colon  as `\:4`

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ u → ⋆ ≡ u) (refl ⋆)

--(paraphrasing MHE) with type equivalence, a type is a singleton iff it is equivalent to `𝟙`."

--We adopt the following notation:
--   `X✦ :  is-singleton X`       NOTATION: type ✦ with `\st2`
--   `X✧ :  is-subsingleton X`   NOTATION: type ✧ with `\st3`

center : (X : 𝓤 ̇) → is-singleton X → X
center X (c , _ ) = c

centrality : (X : 𝓤 ̇) (X✦ : is-singleton X) (u : X) → center X X✦ ≡ u
centrality X (_ , c-is-center ) = c-is-center

--"Subsingletons. A type is a subsingleton if it has at most one element.
is-subsingleton : 𝓤 ̇ →  𝓤 ̇
is-subsingleton X = (u u' : X) → u ≡ u'

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton u u' = !𝟘 (u ≡ u') u

singletons-are-subsingletons : (X : 𝓤 ̇) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X X✦ u u' =
 u           ≡⟨ (centrality X X✦ u)⁻¹ ⟩
 center X X✦ ≡⟨ centrality X X✦ u' ⟩
 u'          ∎

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton = singletons-are-subsingletons 𝟙 𝟙-is-singleton

pointed-subsingletons-are-singletons : (X : 𝓤 ̇) →  X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X u X✧ = (u , X✧ u)

singleton-iff-pointed-and-subsingleton : {X : 𝓤 ̇} → is-singleton X ⇔ (X × is-subsingleton X)
singleton-iff-pointed-and-subsingleton {𝓤}{X} = firstly , secondly
 where
  firstly : is-singleton X → (X × is-subsingleton X)
  firstly X✦ = center X X✦ , singletons-are-subsingletons X X✦

  secondly : (X × is-subsingleton X) → is-singleton X
  secondly (u , X✧) = pointed-subsingletons-are-singletons X u X✧

--(paraphrasing MHE) A type `X` is a subsingleton iff the map `X → 𝟙` is an embedding.
--Under "univalent EM", 𝟘 and 𝟙 are the only subsingletons, up to equivalence (or up to id assuming univalence).

--"Subsingletons are also called propositions or truth values:
is-prop is-truth-value : 𝓤 ̇ → 𝓤 ̇
is-prop = is-subsingleton           -- alias
is-truth-value = is-subsingleton    -- alias

--(paraphrasing MHE) In UF, props are mathematical, rather than meta-mathematical, objects; the fact that a
--type turns out to be a prop requires proof.  Such a proof may be subtle and require significant preparation.
--An example is the proof that the univalence axiom is a proposition, which relies on the fact that univalence
--implies function extensionality, which in turn implies that the assertion "a map is an equivalence" is a
--proposition. Another example that relies on univalence (or at least funext) is the fact that the proof of
--"the type X is a proposition" is itself a prop, i.e., `is-prop (is-prop X)`. Singletons and subsingletons
--are also called -2-groupoids and -1-groupoids resp.

--Sets (or 0-groupoids).
--"A type is defined to be a set if there is at most one way for any two of its elements to be equal:
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (u v : X) → is-subsingleton (u ≡ v)

--"Univalent excluded middle [em] ....the only subsingletons up to equiv are `𝟘` and `𝟙`:
EM em : ∀ 𝓤 → 𝓤 ⁺ ̇
EM 𝓤 = (X : 𝓤 ̇) → is-subsingleton X → X + ¬ X
em = EM -- alias

EM' em' : ∀ 𝓤 → 𝓤 ⁺ ̇
EM' 𝓤 = (X : 𝓤 ̇) → is-subsingleton X → is-singleton X + is-empty X
em' = EM' -- alias

EM→EM' : EM 𝓤 → EM' 𝓤
EM→EM'  emu X X✧ =  γ (emu X X✧)
 where
  γ : X + ¬ X → is-singleton X + is-empty X
  γ (inl ✦) = inl (✦ , X✧ ✦) -- Recall, `X✧ : is-subsingleton X` is a map of type `(u u' : X) → u ≡ u'` so
  γ (inr ✧) = inr ✧           -- `X✧ ✦`  is a map that takes each `u' : X` to `✦ ≡ u'` (i.e., `X✧` u is a proof of `is-center ✦`)

EM'→EM : EM' 𝓤 → EM 𝓤
EM'→EM emu' X X✧ = γ (emu' X X✧)
 where
  γ : is-singleton X + is-empty X → X + ¬ X
  γ (inl ✦) = inl (center X ✦)
  γ (inr ✧) = inr ✧

--(paraphrasing MHE) The potential failure of em doesn't say that there may be subsingletons that fail to be
--singletons and fail to be empty.
no-unicorns : ¬(Σ X ꞉ 𝓤 ̇ , is-subsingleton X × ¬(is-singleton X) × ¬(is-empty X))
no-unicorns (X , X✧ , ¬𝟙 , ¬𝟘) = false
 where
  X0 : is-empty X
  X0 u = ¬𝟙 (pointed-subsingletons-are-singletons X u X✧)

  false : 𝟘
  false = ¬𝟘 X0

--If `X` is a subsingleton, then `is-singleton X + is-empty X` is irrefutable.
em'-irrefutable : (X : 𝓤 ̇ ) → is-subsingleton X → ¬¬(is-singleton X + is-empty X)
em'-irrefutable X X✧ ¬𝟙v𝟘 = ¬𝟙v𝟘 (inr X-is-empty)
 where
  X-is-empty : is-empty X
  X-is-empty u =  ¬𝟙v𝟘 ( inl (u , X✧ u) )

em-irrefutable : (X : 𝓤 ̇ ) → is-subsingleton X → ¬¬ (X + ¬ X)
em-irrefutable X X✧ notXv¬X = false
 where -- N.B. notXv¬X : ¬ (X + ¬ X)
  ¬X : ¬ X
  ¬X x =  notXv¬X ( inl x )
  false : 𝟘
  false = notXv¬X (inr ¬X)

--(paraphrasing MHE)
--For any type `R` (replacing the empty type in the above), ∃ f : ((X + (X → R)) → R) → R, so the kind
--of phenomenon illustrated in the previous exercise has little to do with the emptiness of the empty type.
general-em-irrefutable : (X : 𝓤 ̇) → (R : 𝓥 ̇) → ( (X + (X → R)) → R ) → R
general-em-irrefutable X R X⋁𝓸ᴿ = X⋁𝓸ᴿ  ( inr λ x → X⋁𝓸ᴿ (inl x) )
--(the label 𝓸ᴿ alludes to the fact that `(X → R) → R` is the type of X-ary operations on R)

