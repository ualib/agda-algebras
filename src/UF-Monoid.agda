--FILE: UF-Monoid.agda
--DATE: 18 Mar 2020
--BLAME: williamdemeo@gmail.com
--REF: Based on Martin Escardo's course notes
--      cf.  https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#magmasandmonoids

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Monoid where

open import UF-Prelude using (Universe;_⁺;_̇;𝓤; universe-of; id; 𝑖𝑑; Σ; -Σ; _,_; _×_; _∘_; _≡_; refl; _∼_; transport; _≡⟨_⟩_; _∎; ap; _⁻¹)
open import UF-Equality using (to-Σ-≡; _≃_; to-×-≡; is-equiv; inverse; invertibles-are-equivs; inv-elim-left; inv-elim-right; Σ-cong)
open import UF-Singleton using (is-set; is-subsingleton)
open import UF-Extensionality using (Univalence; global-dfunext; univalence-gives-global-dfunext; global-hfunext;
  univalence-gives-global-hfunext; Π-is-subsingleton;being-equiv-is-subsingleton)
open import UF-Univalence using (×-is-subsingleton; Eq→Id;  ap₂; logically-equivalent-subsingletons-are-equivalent)

--------------------------------------------------------------------
-- The types of magmas and monoids
-- ------------------------------- 

--"A *magma* is a *set* equipped with a binary operation subject to no laws.
-- We can define the type of magmas in a universe `𝓤` as follows:"

Magma : (𝓤 : Universe) -> 𝓤 ⁺ ̇
Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , is-set X × (X -> X -> X)

--"The type `Magma 𝓤` collects all magmas in a universe `𝓤`, and lives in the successor universe `𝓤 ⁺`. Thus, this doesn't
-- define what a magma is as a property. It defines the type of magmas. A magma is an element of this type, that is, a
-- triple `(X , i , _·_)` with `X : 𝓤` and `i : is-set X` and `_·_ : X → X → X`.

--"Given a magma `M = (X , i , _·_)` we denote by `⟨ M ⟩` its underlying set `X` and by `magma-operation M` its multiplication `_·_`:
⟨_⟩ : Magma 𝓤 → 𝓤 ̇
⟨ X , i , _·_ ⟩ = X

∣_∣ = ⟨_⟩ -- alias

magma-is-set : (𝑴 : Magma 𝓤) → is-set ∣ 𝑴 ∣
magma-is-set ( X , i , _·_ ) = i

magma-operation : (𝑴 : Magma 𝓤) → ∣ 𝑴 ∣ → ∣ 𝑴 ∣ → ∣ 𝑴 ∣
magma-operation ( X , i , _·_ ) = _·_

⟦_⟧ = magma-operation -- alias

--"The following syntax declaration allows us to write `x ·⟨ M ⟩ y` as an abbreviation
-- of `magma-operation M x y`:

syntax magma-operation 𝑴 x y = x ·⟨ 𝑴 ⟩ y

--"he point is that this time we need such a mechanism because in order to be able to mention
-- arbitrary `x` and `y`, we first need to know their types, which is `⟨ M ⟩` and hence
-- `M` has to occur before `x` and `y` in the definition of `magma-operation`. The syntax
-- declaration circumvents this.

-------------------------------------------------------------------------
-- Magma homs
-- ----------
is-magma-hom : (𝑴 𝑵 : Magma 𝓤) → (∣ 𝑴 ∣ → ∣ 𝑵 ∣ ) → 𝓤 ̇
is-magma-hom 𝑴 𝑵 f =  ( x y :  ∣ 𝑴 ∣ ) → f (x ·⟨ 𝑴 ⟩ y) ≡ f x ·⟨ 𝑵 ⟩ f y

id-is-magma-hom : (𝑴 : Magma 𝓤) → is-magma-hom 𝑴 𝑴  (𝑖𝑑 ∣ 𝑴 ∣ )
id-is-magma-hom 𝑴 = λ x y → refl (x ·⟨ 𝑴 ⟩ y)  --(NIP)
-- id-is-magma-hom : (𝑴 : Magma 𝓤) → is-magma-hom 𝑴 𝑴 (𝑖𝑑 ∣ 𝑴 ∣ )
-- id-is-magma-hom 𝑴 = λ x y → refl (x ·⟨ 𝑴 ⟩ y)  --(NIP)


is-magma-iso' : {𝑴 𝑵 : Magma 𝓤} → (∣ 𝑴 ∣ → ∣ 𝑵 ∣ ) → 𝓤 ̇
is-magma-iso' {𝑴 = 𝑴} {𝑵 = 𝑵} f =
 is-magma-hom 𝑴 𝑵 f × ( Σ g ꞉ ( ∣ 𝑵 ∣ → ∣ 𝑴 ∣ ) ,
  is-magma-hom 𝑵 𝑴 g × (g ∘ f ∼ 𝑖𝑑 ∣ 𝑴 ∣ ) × (f ∘ g ∼ 𝑖𝑑 ∣ 𝑵 ∣ ) )

is-magma-iso : (𝑴 𝑵 : Magma 𝓤) → (∣ 𝑴 ∣ → ∣ 𝑵 ∣ ) → 𝓤 ̇
is-magma-iso 𝑴 𝑵 f = is-magma-iso' {𝑴 = 𝑴} {𝑵 = 𝑵} f
-- so `is-magma-iso f` is a tuple `( fhom , g , ghom , g∼f , f∼g )`, where
--  `fhom   : is-magma-hom 𝑴 𝑵 f`
--  `g        ꞉  ∣ 𝑵 ∣ → ∣ 𝑴 ∣ `
--  `ghom   : is-magma-hom 𝑵 𝑴 g`
--  `g∼f     : g ∘ f ∼ 𝑖𝑑 ∣ 𝑴 ∣`
--  `f∼g     : f ∘ g ∼ 𝑖𝑑 ∣ 𝑵 ∣`

-- is-magma-iso' : {𝑴 𝑵 : Magma 𝓤} → (∣ 𝑴 ∣ → ∣ 𝑵 ∣ ) → 𝓤 ̇
-- is-magma-iso' {𝑴 = 𝑴} {𝑵 = 𝑵} = is-magma-iso 𝑴 𝑵

id-is-magma-iso : (𝑴 : Magma 𝓤) → is-magma-iso 𝑴 𝑴 (𝑖𝑑 ∣ 𝑴 ∣)
id-is-magma-iso 𝑴 = id-is-magma-hom 𝑴 , 𝑖𝑑 ∣ 𝑴 ∣ , id-is-magma-hom 𝑴 , refl , refl --(NIP)

--"Every identification of magmas gives rise to a magma isomorphism by transport:"

Id→iso : {𝑴 𝑵 : Magma 𝓤} → 𝑴 ≡ 𝑵 → ∣ 𝑴 ∣ → ∣ 𝑵 ∣
Id→iso 𝑴≡𝑵 = transport ∣_∣ 𝑴≡𝑵

Id→iso-is-iso : {𝑴 𝑵 : Magma 𝓤} → (𝑴≡𝑵 : 𝑴 ≡ 𝑵) → is-magma-iso 𝑴 𝑵 (Id→iso 𝑴≡𝑵)
Id→iso-is-iso (refl 𝑴) = id-is-magma-iso 𝑴 --(NIP)

--"The isomorphisms can be collected in a type:"

_≅ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
𝑴 ≅ₘ 𝑵 = Σ f ꞉ (∣ 𝑴 ∣ → ∣ 𝑵 ∣ ) , is-magma-iso 𝑴 𝑵 f

--"The following function will be a bijection in the presence of univalence, so that the
-- identifications of magmas are in one-to-one correspondence with the magma isomorphisms:

magma-Id→iso : {𝑴 𝑵 : Magma 𝓤} → 𝑴 ≡ 𝑵 → 𝑴 ≅ₘ 𝑵
magma-Id→iso 𝑴≡𝑵 = Id→iso 𝑴≡𝑵 , Id→iso-is-iso 𝑴≡𝑵

--"If we omit the sethood condition in the definition of the type of magmas, we get the type
-- of what we could call `∞`-magmas (then the type of magmas could be called `0-Magma`)."

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

--"A *monoid* is a set equipped with an associative binary operation and with a two-sided
-- neutral element, and so we get the type of monoids as follows.
--
--"We first define the three laws:

left-neutral : {X : 𝓤 ̇} → X → (X → X → X) → 𝓤 ̇
left-neutral e _·_ = ∀ x → e · x ≡ x

right-neutral : {X : 𝓤 ̇} → X → (X → X → X) → 𝓤 ̇
right-neutral e _·_ = ∀ x → x · e ≡ x

associative : {X : 𝓤 ̇} → (X → X → X) → 𝓤 ̇
associative _·_ = ∀ x y z → (x · y) · z ≡ x · (y · z) 

--"Then a monoid is a set equipped with such `e` and `_·_` satisfying these three laws:

Monoid : (𝓤 : Universe) → 𝓤 ⁺ ̇
Monoid 𝓤 = Σ X ꞉ 𝓤 ̇ ,
 is-set X × (Σ · ꞉ (X → X → X) , (Σ e ꞉ X , (left-neutral e ·)
                                           × (right-neutral  e ·)
                                           × (associative ·)))

--"*Remark.* People are more likely to use records in Agda rather than iterated `Σ`s as
-- above (recall that we defined `Σ` using a record). This is fine, because records amount
-- to iterated `Σ` types (recall that also `_×_` is a `Σ` type, by definition). Here, however,
-- we are being deliberately spartan. Once we have defined our Agda notation for MLTT, we
-- want to stick to it. This is for teaching purposes (of MLTT, encoded in Agda, not of Agda
-- itself in its full glory).

--"We could drop the `is-set X` condition, but then we wouldn't get `∞`-monoids in any
-- reasonable sense. We would instead get "wild `∞`-monoids" or "incoherent `∞`-monoids".
-- The reason is that in monoids (with sets as carriers) the neutrality and associativity
-- equations can hold in at most one way, by definition of set. But if we drop the sethood
-- requirement, then the equations can hold in multiple ways. And then one is forced to
-- consider equations between the identifications (all the way up in the ∞-case), which is
-- what "coherence data" means. The wildness or incoherence amounts to the absence of such
-- data.

--"Similarly to the situation with magmas, identifications of monoids are in bijection with
-- monoid isomorphisms, assuming univalence. For this to be the case, it is absolutely necessary
-- that the carrier of a monoid is a set rather than an arbitrary type, for otherwise the monoid
-- equations can hold in many possible ways, and we would need to consider a notion of monoid
-- isomorphism that in addition to preserving the neutral element and the multiplication,
-- preserves the associativity identifications.

--"*Exercise*. Define the type of groups (with sets as carriers)."
-- SOLUTION.
invleft : {X : 𝓤 ̇} → X → (X → X → X) → (X → X) → 𝓤 ̇
invleft e _·_ _⁻¹̇ = ∀ x → ((x ⁻¹̇) · x) ≡ e

invright : {X : 𝓤 ̇} → X → (X → X → X) → (X → X) → 𝓤 ̇
invright e _·_ _⁻¹̇ = ∀ x → (x · (x ⁻¹̇)) ≡ e

Group : (𝓤 : Universe) → 𝓤 ⁺ ̇
Group 𝓤 = Σ X ꞉ 𝓤 ̇ , is-set X
 × (Σ · ꞉ (X → X → X) ,
    (Σ e ꞉ X , (left-neutral e ·)
             × (right-neutral e ·)
             × (associative ·)
             × (Σ ⁻¹̇ ꞉ (X → X) ,
                invleft e · ⁻¹̇ × invright e · ⁻¹̇)
     )
    )
  
-- ∣_∣ : Group 𝓤 → 𝓤 ̇
-- ⟨ G , i , _·_ ⟩ = G

--"*Exercise*. Write down the various types of categories defined in the HoTT book in Agda."

--"*Exercise*. Try to define a type of topological spaces."

{----------------------------------------------------------------------------
 "Magma equivalences
  ------------------
  We now define magma equivalences and show that the type of magma equivalences is identified with the type of magma
   isomorphisms. In the next section, which proves a *structure identity principles*, we apply this to characterize magma
   equality and equality of other mathematical structures in terms of equivalences of underlying types. For simplicity we
   assume global univalence here." -}
module magma-equivalences (𝓤★ : Univalence) where

 dfe : global-dfunext
 dfe = univalence-gives-global-dfunext 𝓤★

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext 𝓤★

 --"The magma homomorphism and isomorphism conditions are subsingleton types by virtue of the fact that the underlying type
 -- of a magma is a set by definition.
 being-magma-hom-is-subsingleton : (M N : Magma 𝓤) ( f : ⟨ M ⟩ → ⟨ N ⟩ )
  →                     is-subsingleton ( is-magma-hom M N f )

 being-magma-hom-is-subsingleton M N f = Π-is-subsingleton dfe
  ( λ x → Π-is-subsingleton dfe ( λ y → magma-is-set N ( f ( x ·⟨ M ⟩ y ) ) ( f x ·⟨ N ⟩ f y ) ) )

 being-magma-hom-is-subsingleton' : {M N : Magma 𝓤} ( f : ⟨ M ⟩ → ⟨ N ⟩ ) → is-subsingleton ( is-magma-hom M N f )
 being-magma-hom-is-subsingleton' {M = M} {N = N} f = being-magma-hom-is-subsingleton M N f

 being-magma-iso-is-subsingleton : (M N : Magma 𝓤) ( f : ⟨ M ⟩ → ⟨ N ⟩ )
  →                     is-subsingleton ( is-magma-iso M N f )

 being-magma-iso-is-subsingleton M N f
  --(h , g , k , η , ε ) ( h' , g' , k' , η' , ε' ) = γ
  (fhom , g , ghom , g∼f , f∼g ) ( fhom' , g' , g'hom , g'∼f , f∼g' ) = γ
  where
    p : fhom ≡ fhom'
    p = being-magma-hom-is-subsingleton M N f fhom fhom'

    q : g ≡ g'
    q = dfe ( λ y → g y             ≡⟨ ( ap g (f∼g' y) )⁻¹ ⟩
                          g ( f ( g' y ) )  ≡⟨ g∼f (g' y) ⟩
                          g' y             ∎ )

    ×✧ : is-subsingleton ( is-magma-hom N M g' × (g' ∘ f ∼ id) × (f ∘ g' ∼ id) )
    ×✧ =  ×-is-subsingleton
              ( being-magma-hom-is-subsingleton N M g' )
              ( ×-is-subsingleton ( Π-is-subsingleton dfe ( λ x → magma-is-set M ( g' (f x) ) x ) )
                                       ( Π-is-subsingleton dfe ( λ y → magma-is-set N ( f (g' y) ) y ) ) )

    γ : fhom , g , ghom , g∼f , f∼g ≡ fhom' , g' , g'hom , g'∼f , f∼g'
    γ = to-×-≡ (p , to-Σ-≡ (q , ×✧ _ _))

 being-magma-iso-is-subsingleton' : {M N : Magma 𝓤} ( f : ⟨ M ⟩ → ⟨ N ⟩ ) → is-subsingleton ( is-magma-iso M N f )
 being-magma-iso-is-subsingleton' {M = M} {N = N} = being-magma-iso-is-subsingleton M N

 --"By a magma equivalence we mean an equivalence which is a magma homomorphism. This notion is again a subsingleton type.
 is-magma-equiv' : { M N : Magma 𝓤 } → ( ⟨ M ⟩ → ⟨ N ⟩ ) → 𝓤 ̇
 is-magma-equiv' {M = M} {N = N} f = is-equiv f × is-magma-hom M N f

 is-magma-equiv : ( M N : Magma 𝓤 ) → ( ⟨ M ⟩ → ⟨ N ⟩ ) → 𝓤 ̇
 is-magma-equiv M N = is-magma-equiv' {M = M} {N = N}

 being-magma-equiv-is-subsingleton : (M N : Magma 𝓤) ( f : ⟨ M ⟩ → ⟨ N ⟩ )
  →                     is-subsingleton ( is-magma-equiv M N f )

 being-magma-equiv-is-subsingleton M N f =
  ×-is-subsingleton (being-equiv-is-subsingleton dfe dfe f) (being-magma-hom-is-subsingleton M N f)

 being-magma-equiv-is-subsingleton' : {M N : Magma 𝓤} ( f : ⟨ M ⟩ → ⟨ N ⟩ ) → is-subsingleton ( is-magma-equiv M N f )
 being-magma-equiv-is-subsingleton' {M = M} {N = N} f = being-magma-equiv-is-subsingleton M N f

 --"A function is a magma isomorphism if and only if it is a magma equivalence.
 magma-isos-are-magma-equivs : ( M N : Magma 𝓤 )
               ( f : ⟨ M ⟩ → ⟨ N ⟩ )    →    is-magma-iso M N f
               ----------------------------------------------
  →                      is-magma-equiv M N f
 magma-isos-are-magma-equivs M N f (fhom , g , ghom , g∼f , f∼g) =  feq , fhom
  where
   feq : is-equiv f
   feq = invertibles-are-equivs f ( g , g∼f , f∼g )

 magma-isos-are-magma-equivs' : { M N : Magma 𝓤 } ( f : ⟨ M ⟩ → ⟨ N ⟩ ) → is-magma-iso M N f → is-magma-equiv M N f
 magma-isos-are-magma-equivs' {M = M} {N = N} = magma-isos-are-magma-equivs M N

 magma-equivs-are-magma-isos : ( M N : Magma 𝓤 )
               ( f : ⟨ M ⟩ → ⟨ N ⟩ )    →    is-magma-equiv M N f
               ----------------------------------------------
  →                      is-magma-iso M N f


 magma-equivs-are-magma-isos M N f ( feq , fhom ) = fhom , inverse f feq , finv-hom , finv∼f , f∼finv
  where
   finv∼f : (inverse f feq) ∘ f ∼ id
   finv∼f = inv-elim-left f feq

   f∼finv : f ∘ (inverse f feq) ∼ id
   f∼finv = inv-elim-right f feq

   finv-hom : is-magma-hom N M (inverse f feq)
   finv-hom a b =  -- recall, is-magma-hom 𝑴 𝑵 f = (x y : ∣ 𝑴 ∣ ) → f (x ·⟨ 𝑴 ⟩ y) ≡ f x ·⟨ 𝑵 ⟩ f y
    let finv = inverse f feq in
      finv (a ·⟨ N ⟩ b)                       ≡⟨  ap₂ ( λ a b → finv ( a ·⟨ N ⟩ b) ) ( (f∼finv a)⁻¹ ) ( (f∼finv b)⁻¹ ) ⟩
      finv ( f (finv a) ·⟨ N ⟩ f (finv b) )    ≡⟨ ap finv  ((fhom (finv a) (finv b) )⁻¹) ⟩
      finv ( f ( (finv a) ·⟨ M ⟩ (finv b) ) )  ≡⟨ finv∼f ( finv a ·⟨ M ⟩ finv b ) ⟩
      ( (finv a) ·⟨ M ⟩ (finv b) )             ∎

 magma-equivs-are-magma-isos' : {M N : Magma 𝓤} (f : ⟨ M ⟩ → ⟨ N ⟩) → is-magma-equiv M N f → is-magma-iso M N f
 magma-equivs-are-magma-isos' {M = M} {N = N} = magma-equivs-are-magma-isos M N

 --"Because these two notions are subsingleton types, we conclude that they are equivalent.
 magma-iso-charac : ( M N : Magma 𝓤 ) ( f : ⟨ M ⟩ → ⟨ N ⟩ )
  →               is-magma-iso M N f ≃ is-magma-equiv M N f
 magma-iso-charac M N f  = logically-equivalent-subsingletons-are-equivalent
  (is-magma-iso M N f) (is-magma-equiv M N f)
  (being-magma-iso-is-subsingleton M N f) (being-magma-equiv-is-subsingleton M N f)
  (magma-isos-are-magma-equivs M N f , magma-equivs-are-magma-isos M N f)
 -- magma-iso-charac : ( M N : Magma 𝓤 ) ( f : ⟨ M ⟩ → ⟨ N ⟩ )
 --  →               is-magma-iso M N f ≃ is-magma-equiv M N f
 -- magma-iso-charac M N f  = logically-equivalent-subsingletons-are-equivalent
 --  (is-magma-iso M N f) (is-magma-equiv M N f)
 --  (being-magma-iso-is-subsingleton' f) (being-magma-equiv-is-subsingleton' f)
 --  (magma-isos-are-magma-equivs' f , magma-equivs-are-magma-isos' f)
 -- recall, logically-equivalent-subsingletons-are-equivalent ...  is-subsingleton X → is-subsingleton Y → X ⇔ Y → X ≃ Y

 --"And hence they are equal by univalence.
 magma-iso-charac' : ( M N : Magma 𝓤 ) ( f : ⟨ M ⟩ → ⟨ N ⟩ )
  →               is-magma-iso M N f ≡ is-magma-equiv M N f
 magma-iso-charac' M N f  = Eq→Id ( 𝓤★ ( universe-of ⟨ M ⟩ ) )
   ( is-magma-iso M N f ) ( is-magma-equiv M N f ) ( magma-iso-charac M N f )

 --"And by function extensionality the *properties* of being a magma isomorphism and a magma equivalence are the same:
 magma-iso-charac'' : ( M N : Magma 𝓤 )
  →               is-magma-iso M N ≡ is-magma-equiv M N
 magma-iso-charac'' M N = dfe ( magma-iso-charac' M N )

 --"Hence the type of magma equivalences is equivalent, and therefore equal, to the type of magma isomorphisms.
 _≃ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
 M ≃ₘ N = Σ f ꞉ ( ⟨ M ⟩ → ⟨ N ⟩ ) , is-magma-equiv M N f

 ≅ₘ-charac : ( M N : Magma 𝓤 )  → ( M ≅ₘ N ) ≃ ( M ≃ₘ N )
 ≅ₘ-charac M N = Σ-cong (magma-iso-charac M N)

 ≅ₘ-charac' : ( M N : Magma 𝓤 )  → ( M ≅ₘ N ) ≡ ( M ≃ₘ N )
 ≅ₘ-charac' M N = ap Σ (magma-iso-charac'' M N)

--"It follows from the results of this and the next section that magma equality amounts to magma isomorphism.

------------------------------------------------------------------------------
-- Equality of mathematical structures
-- -------------------------------
{-"Independent of any choice of foundation, we regard two groups to be the same, for all mathematical purposes, if they
   are isomorphic. Likewise, we consider two topological spaces to be the same if they are homeomorphic, two metric
   spaces to be the same if they are isometric, two categories to be the same if they are equivalent, and so on.

  "With Voevodsky's univalence axiom, we can *prove* that these notions of sameness are automatically captured by
   Martin-Löf's identity type. In particular, properties of groups are automatically invariant under isomorphism, properties
   of topological spaces are automatically invariant under homeomorphism, properties of metric spaces are automatically
   invariant under isometry, properties of categories are automatically invariant under equivalence, and so on, simply because,
   by design, properties are invariant under the notion of equality given by the identity type. In other foundations, the lack
   of such automatic invariance creates practical difficulties; see
   https://mathoverflow.net/questions/336191/cauchy-reals-and-dedekind-reals-satisfy-the-same-mathematical-theorems/.

  "A *structure identity principle* describes the identity type of types of mathematical structures in terms of equivalences
   of underlying types, relying on univalence.  The first published structure identity principle, for a large class of algebraic
   structures, is Coquand and Danielsson (https://www.sciencedirect.com/science/article/pii/S0019357713000694). The HoTT
   book (section 9.8) has a categorical version, whose formulation is attributed to Peter Aczel.

  "Here we formulate and prove a variation for types equipped with structure. We consider several versions:

   1. One for raw structures subject to no axioms, such as ∞-magmas and pointed types.

   2. One that adds axioms to a structure, so as to e.g. get an automatic characterization of magma identifications
      from a characterization of ∞-magma identifications.

   3. One that joins two kinds of structure, so as to e.g. get an automatic characterization of identifications of
      pointed ∞-magmas from characterizations of identifications for pointed types and for ∞-magmas.

   4. In particular, adding axioms to pointed ∞-magmas we get monoids with an automatic characterization of their
      identifications.

   5. And then adding an axiom to monoids we get groups, again with an automatic characterization of their identitifications.

   6. We also show that while two groups are equal precisely when they are isomorphic, two *subgroups* of a group are equal
      precisely when they have the same elements, if we define a subgroup to be a subset closed under the group operations.

  "We also apply theses ideas to characterize identifications of metric spaces, topological spaces, graphs, partially
   ordered sets, categories and more.-}

