--FILE: UF-Embedding.agda
--DATE: 22 Apr 2020
--UPDATE: 23 May 2020
--BLAME: williamdemeo@gmail.com
--REF: Much of this file is based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#equivconstructions
--      https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#yoneda
--      In particular, the quoted comments below, along with sections of code to which those comments refer, are due to Martin Escardo.
--      Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Embedding where

open import UF-Prelude using (Universe; 𝓤₀; 𝓤; 𝓥; 𝓦; 𝓣;  _̇; _⊔_; _⁺; id; 𝑖𝑑; _∘_; ₀; ₁; _,_; Σ; -Σ; pr₁; pr₂; Π; -Π; domain; codomain; _×_; Id; _≡_; ≡-sym; refl; 𝕁; _∼_; _∙_; ap; _⁻¹; transport; _≡⟨_⟩_; _∎; _⋆'_; type-of; 𝟙; ∣_∣; ∥_∥)

open import UF-Singleton using (is-set; is-singleton; is-subsingleton; pointed-subsingletons-are-singletons; singletons-are-subsingletons; 𝟙-is-singleton; center)

open import UF-Equality using (Nat; Nats-are-natural; NatΣ; _◁_;  Σ-retract; singleton-type';retract-of-singleton;singleton-types'-are-singletons; has-section; retraction; retraction-has-section; singleton-type; singleton-types-are-singletons; _≃_;  id-≃; is-equiv; invertibles-are-equivs; ≃-gives-▷; fiber; ≃-sym; _≃⟨_⟩_; _■; Σ-cong; equiv-to-singleton; _●_; inverse; inverses-are-sections; inverses-are-retractions; invertible; invertibility-gives-≃; id-is-equiv)

open import UF-Univalence using (is-univalent; Id→Eq; NatΣ-equiv-gives-fiberwise-equiv; maps-of-singletons-are-equivs; ΠΣ-distr-≃; pr₁-≃; univalence-≃; equiv-to-subsingleton; to-subtype-≡; Σ-is-subsingleton; lc-maps-reflect-subsingletons; sections-are-lc; ⁻¹-≃; singleton-equiv-lemma; left-cancellable; Σ-assoc; Σ-change-of-variable; equiv-to-set)

open import UF-Extensionality using (_/_; is-map-classifier; ∃!; -∃!; ∃!-is-subsingleton; funext; dfunext; happly; hfunext; global-dfunext; Univalence; global-hfunext; Π-is-subsingleton; being-equiv-is-subsingleton; univalence-gives-global-hfunext; univalence-gives-global-dfunext; Π-cong; ≃-sym-is-equiv; ●-assoc; being-subsingleton-is-subsingleton; univalence-gives-dfunext; χ; universes-are-map-classifiers; Ω; univalence-gives-dfunext'; powersets-are-sets'; propext; being-singleton-is-subsingleton; univalence-gives-vvfunext'; univalence-gives-propext)

-----------------------------------------------
-- Some constructions with types of equivalences
--"We first prove some properties of equivalence symmetrization and composition."

id-≃-left : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)      --[Recall, `_●_ : ... → X ≃ Y → Y ≃ Z → X ≃ Z`
 →           {X : 𝓤 ̇}    {Y : 𝓥 ̇}    (α : X ≃ Y)                                    --          `(f , d) ● (f' , e) = f' ∘ f , ∘-is-equiv e d`   ]
              --------------------------------
 →                     id-≃ X ● α ≡ α
id-≃-left fe fe' α =  to-subtype-≡ (being-equiv-is-subsingleton fe fe') (refl _)

≃-sym-left-inverse : dfunext 𝓥 𝓥 → {X : 𝓤 ̇}  {Y : 𝓥 ̇} (α : X ≃ Y)
 →                       ≃-sym α ● α   ≡   id-≃ Y
≃-sym-left-inverse fe (f , e) = to-subtype-≡ (being-equiv-is-subsingleton fe fe) ff⁻
 where
  ff⁻ : f ∘ inverse f e ≡ id
  ff⁻ = fe (inverses-are-sections f e)

≃-sym-right-inverse : dfunext 𝓤 𝓤
 →                         {X : 𝓤 ̇}   {Y : 𝓥 ̇}   (α : X ≃ Y)
                           --------------------------------
 →                           α ● ≃-sym α   ≡   id-≃ X
≃-sym-right-inverse fe (f , e) = to-subtype-≡ (being-equiv-is-subsingleton fe fe) f⁻f
 where
  f⁻f : (inverse f e) ∘ f ≡ id
  f⁻f = fe (inverses-are-retractions f e)

--"We then transfer the above to equivalence types:
≃-Sym : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 →       {X : 𝓤 ̇}  {Y : 𝓥 ̇}    →     (X ≃ Y)   ≃   (Y ≃ X)

≃-Sym fe₀ fe₁ fe₂ = ≃-sym , ≃-sym-is-equiv fe₀ fe₁ fe₂

≃-Comp : dfunext 𝓦 (𝓥 ⊔ 𝓦) → dfunext (𝓥 ⊔ 𝓦)  (𝓥 ⊔ 𝓦) → dfunext 𝓥 𝓥
 →         dfunext 𝓦 (𝓤 ⊔ 𝓦) → dfunext (𝓤 ⊔ 𝓦)  (𝓤 ⊔ 𝓦) → dfunext 𝓤 𝓤
 →         {X : 𝓤 ̇} {Y : 𝓥 ̇} (Z : 𝓦 ̇)
 →                  X ≃ Y
             -------------------
 →          (Y ≃ Z)   ≃   (X ≃ Z)
≃-Comp fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ Z X≃Y = invertibility-gives-≃ (X≃Y ●_) inv-X≃Y-●
  where
   inv-X≃Y-● : invertible (X≃Y ●_)
   inv-X≃Y-● = ( (≃-sym X≃Y ●_) , ζ , ξ )
    where
      ζ : ( λ β → ≃-sym X≃Y ● ( X≃Y ● β ) ) ∼ id
      ζ =  λ β → ≃-sym X≃Y ● ( X≃Y ● β)    ≡⟨ ●-assoc fe₀ fe₁ (≃-sym X≃Y) X≃Y β ⟩
                       ( ≃-sym X≃Y ● X≃Y ) ● β    ≡⟨ ap (_● β) (≃-sym-left-inverse fe₂ X≃Y ) ⟩
                        id-≃ _ ● β                        ≡⟨ id-≃-left fe₀ fe₁ _ ⟩
                        β                                      ∎
      ξ : ( λ δ → X≃Y ● (≃-sym X≃Y ● δ) ) ∼ id
      ξ = λ δ → X≃Y ● (≃-sym X≃Y ● δ)  ≡⟨ ●-assoc fe₃ fe₄ X≃Y (≃-sym X≃Y) δ ⟩
                       (X≃Y ● ≃-sym X≃Y) ● δ  ≡⟨ ap (_● δ) (≃-sym-right-inverse fe₅ X≃Y ) ⟩
                        id-≃ _ ● δ                    ≡⟨ id-≃-left fe₃ fe₄ _ ⟩
                        δ                                   ∎

--Using this MHE gives the following self-congruence property of equivalences:
Eq-Eq-cong' : dfunext 𝓥 (𝓤 ⊔ 𝓥) →  dfunext (𝓤 ⊔ 𝓥)  (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓤
 →               dfunext 𝓥 (𝓥 ⊔ 𝓦) → dfunext (𝓥 ⊔ 𝓦)  (𝓥 ⊔ 𝓦) → dfunext 𝓦 𝓦
 →               dfunext 𝓦 (𝓥 ⊔ 𝓦) →  dfunext 𝓥 𝓥 → dfunext 𝓦 (𝓦 ⊔ 𝓣)
 →               dfunext (𝓦 ⊔ 𝓣) (𝓦 ⊔ 𝓣) → dfunext 𝓣 𝓣 → dfunext 𝓣 (𝓦 ⊔ 𝓣)
 →               {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} {B : 𝓣 ̇}
                  --------------------------------------------
 →                X ≃ A   →   Y ≃ B   →    (X ≃ Y)   ≃   (A ≃ B)
Eq-Eq-cong' fevuv feuvuv feuu fevvw fevwvw feww fewvw fevv fewwt fewtwt fett fetwt {X} {Y} {A} {B} X≃A Y≃B =
   X ≃ Y     ≃⟨ ≃-Comp fevuv feuvuv feuu fevvw fevwvw feww Y (≃-sym X≃A) ⟩
   A ≃ Y     ≃⟨ ≃-Sym fevvw fewvw fevwvw ⟩
   Y ≃ A     ≃⟨ ≃-Comp fewvw fevwvw fevv fewwt fewtwt fett A (≃-sym Y≃B) ⟩
   B ≃ A     ≃⟨ ≃-Sym fewwt fetwt fewtwt ⟩
   A ≃ B     ■

--"The above shows why global function extensionality would be a better assumption in practice."
--[N.B. We can't simply delete `Eq-Eq-cong'` and adopt the following simpler version because the
-- former is used below.]
Eq-Eq-cong : (fe : global-dfunext) {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} {B : 𝓣 ̇}
 →               X ≃ A      →      Y ≃ B
                 ------------------------
 →                (X ≃ Y)   ≃   (A ≃ B)
Eq-Eq-cong fe = Eq-Eq-cong' fe fe fe fe fe fe fe fe fe fe fe fe

-----------------------------------------------------------------------------------------
--Type embeddings.
--"A function is called an embedding if its fibers are all subsingletons. In particular, equivalences
-- are embeddings. However, sections of types more general than sets don't need to be embeddings
-- (see: https://lmcs.episciences.org/2027 ).
is-embedding : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = (y : codomain f) → is-subsingleton (fiber f y)

being-embedding-is-subsingleton : global-dfunext → {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
 →                                is-subsingleton (is-embedding f)

being-embedding-is-subsingleton fe f =
 Π-is-subsingleton fe (λ x → being-subsingleton-is-subsingleton fe )

--"For example, if `A` is a subsingleton, then the second projection `A × X → X` is an embedding:
pr₂-embedding : (A : 𝓤 ̇) (X : 𝓥 ̇)
 →              is-subsingleton A
               -------------------------------------
 →              is-embedding (λ (z : A × X) → pr₂ z)
pr₂-embedding A X A✧ x ((a , x) , refl x) ((a' , x) , refl x) = p
 where
  p : (a , x) , refl x ≡ (a' , x) , refl x
  p = ap (λ - → ( ( - , x ) , refl x ) ) (A✧ a a')

--"*Exercise*. Show that the converse of `pr₂-embedding` holds.

--"More generally, with the arguments swapped, the projection `Σ A → X` is an embedding if `A x`
-- is a subsingleton for every `x : X`:
pr₁-embedding :  {X : 𝓤 ̇} {A : X → 𝓥 ̇}
 →               ((x : X) → is-subsingleton (A x))
                -----------------------------------
 →               is-embedding (λ (σ : Σ A) → pr₁ σ)
pr₁-embedding Ax✧ x ( (x , a) , refl x ) ( (x , a') , refl x ) = ap (λ - → (x , -) , refl x) (Ax✧ x a a')

--"*Exercise*. Show that the converse of `pr₁-embedding` holds.

equivs-are-embeddings : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y) → is-equiv f → is-embedding f
equivs-are-embeddings f feq y = singletons-are-subsingletons (fiber f y) (feq y)

id-is-embedding : {X : 𝓤 ̇} → is-embedding (𝑖𝑑 X)
id-is-embedding {𝓤}{X} = equivs-are-embeddings id (id-is-equiv X)

∘-embedding : {X : 𝓤 ̇}{Y : 𝓥 ̇}{Z : 𝓦 ̇}
              {f : X → Y}{g : Y → Z}
 →            is-embedding g   →   is-embedding f
              -------------------------------------
 →                   is-embedding (g ∘ f)

∘-embedding {𝓤}{𝓥}{𝓦}{X}{Y}{Z}{f}{g} gem fem = hem
 where
  hem : (z : Z) → is-subsingleton (fiber (g ∘ f) z)
  hem z = lc-maps-reflect-subsingletons (φ z)
           (sections-are-lc (φ z) (γ z , η z)) (Az✧ z)
   where
    A : (z : Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
    A z = Σ (y , p) ꞉ fiber g z , fiber f y

    Az✧ : (z : Z) → is-subsingleton (A z)
    Az✧ z = Σ-is-subsingleton (gem z) (λ w → fem (pr₁ w))

    φ : (z : Z) → fiber (g ∘ f) z → A z
    φ z (x , gfx≡z) = (f x , gfx≡z) , x , refl (f x)

    γ :  (z : Z) → A z →  fiber (g ∘ f) z
    γ z  ( (_ , p) , x , refl _) = x , p

    η :  (z : Z) (t : fiber (g ∘ f) z) → γ z (φ z t) ≡ t
    η _ (x , refl _) = refl (x , refl (g (f x)))


--"We can use the following criterion to prove that some maps are embeddings:
embedding-lemma :  {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y)
 →                 ((x : X) → is-singleton (fiber f (f x)))
                   -----------------------------------------
 →                           is-embedding f
embedding-lemma f fibff✧ = γ
 where
  γ : (y : codomain f) (u v : fiber f y) → u ≡ v
  γ y (x , fx≡y) fibfy =
   singletons-are-subsingletons (fiber f y) fibfy✧ (x , fx≡y) fibfy
   where
    fibffx≡fibfy : fiber f (f x) ≡ fiber f y
    fibffx≡fibfy = ap (fiber f) fx≡y
    fibfy✧ : is-singleton (fiber f y)
    fibfy✧ = transport is-singleton fibffx≡fibfy (fibff✧ x)

embedding-criterion : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
 →                    ((x x' : X) → (f x ≡ f x') ≃ (x ≡ x'))
                      ---------------------------------------
 →                           is-embedding f
embedding-criterion f feq = embedding-lemma f b
 where
  X = domain f

  a : (x : X) → (Σ x' ꞉ X , f x' ≡ f x) ≃ (Σ x' ꞉ X , x' ≡ x)
  a x = Σ-cong (λ x' → feq x' x)

  a' : (x : X) → fiber f (f x) ≃ singleton-type x
  a' = a

  b : (x : X) → is-singleton ( fiber f (f x) )
  b x = equiv-to-singleton (a' x) (singleton-types-are-singletons X x)

--"An equivalent formulation of `f` being an embedding is that the map
-- `ap f {x} {x'} : x ≡ x' → f x ≡ f x'` is an equivalence for all `x x' : X`.
ap-is-equiv-gives-embedding : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
 →                 ((x x' : X) → is-equiv (ap f {x} {x'}))
                   -----------------------------------
 →                           is-embedding f
ap-is-equiv-gives-embedding f apeq =
 embedding-criterion f (λ x' x → ≃-sym (ap f {x'} {x} , apeq x' x))

embedding-gives-ap-is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
 →                           is-embedding f
                   -----------------------------------
 →                 ((x x' : X) → is-equiv (ap f {x} {x'}))
embedding-gives-ap-is-equiv {𝓤}{𝓥} {X} f fem = γ
 where
  d : (x' : X) → ( Σ x ꞉ X , f x' ≡ f x ) ≃ ( Σ x ꞉ X , f x ≡ f x' )
  d x' = Σ-cong ( λ x → ⁻¹-≃ (f x') (f x) )

  s :  (x' : X) → is-subsingleton ( Σ x ꞉ X , f x' ≡ f x )
  s x' = equiv-to-subsingleton (d x') ( fem (f x') )

  γ : (x x' : X) → is-equiv ( ap f {x} {x'} )
  γ x = singleton-equiv-lemma x ( λ x' → ap f {x} {x'} )
            ( pointed-subsingletons-are-singletons
                ( Σ x' ꞉ X , f x ≡ f x' ) ( x , refl (f x) ) (s x) )

embedding-criterion-converse : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
 →                             is-embedding f
                     -------------------------------
 →                   ( (x x' : X) → (f x ≡ f x') ≃ (x ≡ x') )
embedding-criterion-converse f fem x' x =
 ≃-sym (ap f {x'} {x} , embedding-gives-ap-is-equiv f fem x' x )

--"Hence embeddings of arbitrary types are left cancellable, but the converse fails in general.

embeddings-are-lc :  {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-embedding f → left-cancellable f
embeddings-are-lc f fem {x} {y}  = ∣ embedding-criterion-converse f fem x y ∣

--"*Exercise*. Left cancellable maps into *sets* are always embeddings.

--"If an embedding has a section (right inverse), then it is an equivalence.
-- embedding-with-section-is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
--  →                  is-embedding f   →   has-section f
--                    -----------------------------------
--  →                           is-equiv f
-- embedding-with-section-is-equiv f fem (g , g∼f)  y = {!!}

-- --"Later we will see that a necessary and sufficient condition for an embedding to be an equivalence
-- is that it is as surjection.

-- --"If a type `Y` is embedded into `Z`, then the function type `X → Y` is embedded into `X → Z`. More generally, if `A x` is
-- -- embedded into `B x` for every `x : X`, then the dependent function type `Π A` is embedded into `Π B`.
-- NatΠ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} → Nat A B → Π A → Π B
-- NatΠ τ f x = τ x (f x)

-- --"(Notice that `NatΠ` is a dependently typed version of the combinator `S` from combinatory logic. Its logical interpretation, here,
-- -- is that if `A x` implies `B x` for all `x : X`, and `A x` holds for all `x : X`, then `B x` holds for all `x : X` too.)
-- NatΠ-is-embedding : hfunext 𝓤 𝓥 → hfunext 𝓤 𝓦
--  →             {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} (τ : Nat A B)
--  →             ((x : X) → is-embedding (τ x))
--                -----------------------------------------------
--  →               is-embedding (NatΠ τ)
-- NatΠ-is-embedding v w {X} {A} τ τxem = {!!}

-- --"We conclude this section by introducing notation for the type of embeddings.
_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ Y = Σ f ꞉ (X → Y) , is-embedding f

-- Emb→fun : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ↪ Y → X → Y
-- Emb→fun (f , _) = f

-- DO THESE NEXT:

--"The following justifies the terminology *subsingleton*:
--"*Exercise*. Show that `is-subsingleton X ⇔ (X ↪ 𝟙)`.
-- (see: HoTT-UF-Agda.html#the-subsingletons-are-the-subtypes-of-a-singleton ) 
--"*Exercise*. Hence assuming function extensionality and propositional extensionality, conclude
-- that `is-subsingleton X ≡ (X ↪ 𝟙)`.
-- (see: HoTT-UF-Agda.html#the-subsingletons-are-the-subtypes-of-a-singleton )

--"*Exercise*. Show that the map `Fin : ℕ → 𝓤₀` defined above is left-cancellable but not an embedding.

{---------------------------------------------------------------------------------------------
 "The Yoneda Lemma for types
  ---------------------------
  As we have seen (in the section on the identity type in univalent mathematics) a TYPE `X` can be seen
  as an ∞-groupoid and hence as an ∞-category, with identifications as the arrows. Likewise a UNIVERSE
  `𝓤` can be seen as the ∞-generalization of the category of sets, with functions as the arrows. Hence
  a TYPE FAMILY `A : X → 𝓤` can be seen as an ∞-presheaf, because groupoids are self-dual categories. -}

--"With this view, the identity type former `Id X : X → X → 𝓤` plays the role of the Yoneda embedding.
𝓨 : {X : 𝓤 ̇} → X → (X → 𝓤 ̇)
𝓨 {𝓤}{X} = Id X

--"Sometimes we want to make one of the parameters explicit:
𝑌 : (X : 𝓤 ̇) → X → (X → 𝓤 ̇)
𝑌 {𝓤} X  = 𝓨 {𝓤} {X}

{-"By our definition of `Nat`, for any `A : X → 𝓥 ̇` and `x : X` we have
   `Nat (𝓨 x) A = (y : X) → x ≡ y → A y`, and, by `Nats-are-natural`, we have that
   `Nat (𝓨 x) A` is the type of natural transformations from the presheaf `𝓨 x` to the presheaf `A`.
   The starting point of the Yoneda Lemma, in our context, is that every such natural transformation
   is a transport. -}
transport-lemma : {X : 𝓤 ̇}(A : X → 𝓥 ̇)(x : X)
                  (τ : Nat (𝓨 x) A)  (y : X)  (x≡y : x ≡ y)
                ----------------------------------------------
 →                τ y x≡y  ≡  transport A x≡y (τ x (refl x))
transport-lemma A x τ x (refl x) = refl ( τ x (refl x) )

--"We denote the point `τ x (refl x)` in the above lemma by `𝓔 A x τ` and refer to it as the
-- YONEDA ELEMENT of the transformation `τ`.
𝓔 : {X : 𝓤 ̇}(A : X → 𝓥 ̇)(x : X) → Nat (𝓨 x) A → A x
𝓔 A x τ = τ x (refl x)

--"The function `𝓔 A x : Nat (𝓨 x) A → A x` is an equivalence with inverse
-- `𝓝 A x : A x → Nat (𝓨 x) A`, the transport natural transformation induced by `A` and `x`:
𝓝 : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (x₀ : X) → A x₀ → Nat (𝓨 x₀) A
𝓝 A x₀ a x p = transport A p a

yoneda-η : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥 →  {X : 𝓤 ̇}
           (A : X → 𝓥 ̇)   (x : X)
           ------------------------
 →           𝓝 A x ∘ 𝓔 A x ∼ id

yoneda-η fe fe' A x = γ
 where
  γ : (τ : Nat (𝓨 x) A) → (λ y p → transport A p (τ x (refl x))) ≡ τ
  γ τ = fe (λ y → fe' (λ p → (transport-lemma A x τ y p)⁻¹ ))

yoneda-ε : {X : 𝓤 ̇}(A : X → 𝓥 ̇)(x : X)
           --------------------------------
 →              𝓔 A x ∘ 𝓝 A x ∼ id
yoneda-ε A x = γ
 where -- γ : 𝓝 A x ∘ 𝓔 A x ∼ id
    γ : (a : A x) → transport A (refl x) a ≡ a
    γ = refl

--"By a fiberwise equivalence we mean a natural transformation whose components are all equivalences:
is-fiberwise-equiv : {X : 𝓤 ̇}{A : X → 𝓥 ̇}{B : X → 𝓦 ̇} → Nat A B → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
is-fiberwise-equiv τ = ∀ x → is-equiv (τ x)

𝓔-is-equiv : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
 →           {X : 𝓤 ̇}  (A : X → 𝓥 ̇)
            ---------------------------
 →           is-fiberwise-equiv (𝓔 A)
𝓔-is-equiv fe fe' A x =
 invertibles-are-equivs (𝓔 A x) (𝓝 A x , yoneda-η fe fe' A x , yoneda-ε A x)

𝓝-is-equiv : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
 →            {X : 𝓤 ̇} (A : X → 𝓥 ̇)
             --------------------------
 →            is-fiberwise-equiv (𝓝 A)
𝓝-is-equiv fe fe' A x =
 invertibles-are-equivs (𝓝 A x) (𝓔 A x , yoneda-ε A x , yoneda-η fe fe' A x)

--"This gives the Yoneda Lemma for types
-- (see: https://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/),
-- which says that natural transformations from `𝓨 x` to `A` are in canonical bijection with
-- elements of `A x`:
Yoneda-Lemma : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
 →             {X : 𝓤 ̇} (A : X → 𝓥 ̇) (x : X)
               --------------------------------------
 →                  Nat (𝓨 x) A  ≃  A x
Yoneda-Lemma fe fe' A x = 𝓔 A x , 𝓔-is-equiv fe fe' A x

--"A universal element of a presheaf `A` corresponds in our context to an element of the type
-- `is-singleton (Σ A)`, which can also be written `∃! A`. If the transport transformation is a
-- fiberwise equivalence, then `A` has a universal element. More generally, we have the following:
retract-universal-lemma : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (x : X)
 →                        ((y : X) → A y ◁ (x ≡ y))
                         ------------------------------
 →                                  ∃! A
retract-universal-lemma A x ρ = A✦
 where
  σ : Σ A ◁ singleton-type' x
  σ = Σ-retract ρ

  A✦ : ∃! A
  A✦ = retract-of-singleton σ (singleton-types'-are-singletons (domain A) x)

fiberwise-equiv-universal : {X : 𝓤 ̇}(A : X → 𝓥 ̇)(x : X)
                            (τ : Nat (𝓨 x) A)  →  is-fiberwise-equiv τ
                           ---------------------------------------------
 →                                ∃! A

fiberwise-equiv-universal A x τ e = retract-universal-lemma A x ρ
 where
  ρ :  ∀ y → A y ◁ (x ≡ y)
  ρ y =  ≃-gives-▷ ( (τ  y) , e y)

--"Conversely:
universal-fiberwise-equiv :  {X : 𝓤 ̇}
       (A : X → 𝓥 ̇)  →  ∃! A  →  (x : X)  (τ : Nat (𝓨 x) A)
       -------------------------------------------------------
 →                 is-fiberwise-equiv τ
universal-fiberwise-equiv {𝓤} {𝓥} {X} A u x τ = γ
 where
  g : singleton-type' x → Σ A
  g = NatΣ τ

  e : is-equiv g
  e = maps-of-singletons-are-equivs g ( singleton-types'-are-singletons X x ) u

  γ : is-fiberwise-equiv τ
  γ = NatΣ-equiv-gives-fiberwise-equiv τ e

--"In particular, the induced transport transformation `τ = 𝓝 A x a` is a fiberwise equivalence if
-- and only if there is a unique `x : X` with `A x`, which we abbreviate as `∃! A`. A corollary is
-- the following characterization of function extensionality, similar to the above characterization
-- of univalence, by taking the transformation `τ = happly f`, because `hfe f` says that `τ` is a
-- fiberwise equivalence:
hfunext→ : hfunext 𝓤 𝓥 → ( (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (f : Π A) → ∃! g ꞉ Π A , f ∼ g )

hfunext→ hfe X A f = fiberwise-equiv-universal (f ∼_) f (happly f) (hfe f)

→hfunext : ( (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (f : Π A) → ∃! g ꞉ Π A , f ∼ g ) → hfunext 𝓤 𝓥

→hfunext φ {X} {A} f = universal-fiberwise-equiv (f ∼_) (φ X A f) f (happly f)

--"We also have the following general corollaries:

--"...if we have a fiberwise retraction, then any natural transformation is an equivalence.
fiberwise-equiv-criterion : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (x : X)
 →                          ((y : X) →  A y ◁ (x ≡ y))  →  (τ : Nat (𝓨 x) A)
                           ----------------------------------------------------
 →                                   is-fiberwise-equiv τ

fiberwise-equiv-criterion A x fibret τ =
  universal-fiberwise-equiv A (retract-universal-lemma A x fibret) x τ

--"...if we have a fiberwise equivalence, then any natural transformation is a fiberwise equivalence:
fiberwise-equiv-criterion' : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (x : X)
 →                           ((y : X)  →  (x ≡ y) ≃ A y)  →  (τ : Nat (𝓨 x) A)
                            ----------------------------------------------------
 →                                is-fiberwise-equiv τ

fiberwise-equiv-criterion' A x fibeq =
  fiberwise-equiv-criterion A x (λ y → ≃-gives-▷ (fibeq y) )

--"A presheaf (X → 𝓥 ̇) is called *representable* if it is pointwise equivalent to a presheaf of the form `𝓨 x`.

--[presheaf extensionality]
_≃̇_ : {X : 𝓤 ̇} → (X → 𝓥 ̇) → (X → 𝓦 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
A ≃̇ B = ∀ x → A x ≃ B x

is-representable : {X : 𝓤 ̇} → (X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
is-representable A = Σ x ꞉ domain A , 𝓨 x ≃̇ A

representable-universal : {X : 𝓤 ̇}
                          (A : X → 𝓥 ̇) → is-representable A
                         --------------------------------------
 →                           ∃! A
representable-universal A (x , 𝓨x≃̇A) = retract-universal-lemma A x ( λ x → ≃-gives-▷ (𝓨x≃̇A x) )

universal-representable : {X : 𝓤 ̇}
                          {A : X → 𝓥 ̇} → ∃! A
                         -------------------------
 →                          is-representable A
universal-representable {𝓤} {𝓥} {X} {A} ( (x , v) , xvcen ) = x , φ
 where
  𝓝Axv-fweq : is-fiberwise-equiv (𝓝 A x v)
  𝓝Axv-fweq = universal-fiberwise-equiv A ( (x , v) , xvcen ) x (𝓝 A x v)

  φ : (y : X) → (x ≡ y) ≃ A y
  φ y = (𝓝 A x v y , 𝓝Axv-fweq y)

--"Combining `retract-universal-lemma` and `universal-fiberwise-equiv` we get the following:
-- (see also: https://github.com/HoTT/book/issues/718#issuecomment-65378867 )
fiberwise-retractions-are-equivs : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (x : X)
                                   (τ : Nat (𝓨 x) A)
 →                                 ((y : X) → has-section (τ y))
                                  --------------------------------
 →                                    is-fiberwise-equiv τ

fiberwise-retractions-are-equivs {𝓤} {𝓥} {X}  A x τ s = γ
 where
  ρ : (y : X) → A y ◁ ( x ≡ y )
  ρ y = τ y , s y

  ∃!A : ∃! A
  ∃!A = retract-universal-lemma A x ρ

  γ : is-fiberwise-equiv τ
  γ = universal-fiberwise-equiv A ∃!A x τ

--"Perhaps the following formulation is more appealing:
fiberwise-◁-gives-≃ : (X : 𝓤 ̇) (A : X → 𝓥 ̇) (x : X)
 →                    ((y : X) → A y ◁ (x ≡ y))
 →                    ((y : X) → A y ≃ (x ≡ y))

fiberwise-◁-gives-≃ X A x ρ = γ
 where
  f : (y : X) → (x ≡ y) → A y
  f y = retraction (ρ y)

  ffweq : is-fiberwise-equiv f
  ffweq = fiberwise-retractions-are-equivs A x f (λ y → retraction-has-section (ρ y))

  γ : (y : X) → A y ≃ (x ≡ y)
  γ y = ≃-sym (f y , ffweq y)

--"We have the following corollary:
embedding-criterion' : {X : 𝓤 ̇} {Y : 𝓥 ̇}  (f : X → Y)
 →                     ((x x' : X) → (f x ≡ f x') ◁ (x ≡ x'))
                      ---------------------------------------
 →                                is-embedding f
embedding-criterion' f ρ = embedding-criterion f
  ( λ x → fiberwise-◁-gives-≃ (domain f) ( λ - → f x ≡ f - )  x (ρ x) )

--"*Exercise.* It also follows that `f` is an embedding if and only if the map `ap f {x} {x'}`
-- has a section.

-- To prove that  `𝓨 {𝓤} {X}` is an embedding (see: https://arxiv.org/abs/1903.01211 ) of `X`
-- into `X → 𝓤` for any type `X : 𝓤`, we need the following two lemmas, which are interesting in
-- their own right:
being-fiberwise-equiv-is-subsingleton : global-dfunext
 →                      {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇}
 →                      (τ : Nat A B)
                        --------------------------------------------
 →                      is-subsingleton (is-fiberwise-equiv τ)
being-fiberwise-equiv-is-subsingleton fe τ =
  Π-is-subsingleton fe (λ y → being-equiv-is-subsingleton fe fe (τ y) )

being-representable-is-subsingleton : global-dfunext
 →                 {X : 𝓤 ̇}(A : X → 𝓥 ̇)
 →                 is-subsingleton (is-representable A)
being-representable-is-subsingleton fe {X} A r₀ r₁ = r₀≡r₁
 where
  ∃!A : ∃! A
  ∃!A = representable-universal A r₀

  is-fweq✦ : (x : X) (τ : Nat (𝓨 x) A) → is-singleton (is-fiberwise-equiv τ)
  is-fweq✦ x τ = pointed-subsingletons-are-singletons
                       (is-fiberwise-equiv τ) (universal-fiberwise-equiv A ∃!A x τ)
                       (being-fiberwise-equiv-is-subsingleton fe τ)

  ε : (x : X) → (𝓨 x ≃̇ A) ≃ A x
  ε x = ((y : X) → 𝓨 x y ≃ A y)                    ≃⟨ ΠΣ-distr-≃ ⟩
        (Σ τ ꞉ Nat (𝓨 x) A , is-fiberwise-equiv τ) ≃⟨ pr₁-≃ (is-fweq✦ x) ⟩
        Nat (𝓨 x) A                                ≃⟨ Yoneda-Lemma fe fe A x ⟩
        A x                                         ■

  δ : is-representable A ≃ Σ A
  δ = Σ-cong ε

  is-repA✦ : is-singleton (is-representable A)
  is-repA✦ = equiv-to-singleton δ ∃!A

  r₀≡r₁ : r₀ ≡ r₁
  r₀≡r₁ = singletons-are-subsingletons (is-representable A) is-repA✦ r₀ r₁

--"With this it is almost immediate that the Yoneda map `𝑌 X` is an embedding of `X` into `X → 𝓤`:
𝓨-is-embedding : Univalence → (X : 𝓤 ̇) → is-embedding (𝑌 X)
𝓨-is-embedding {𝓤} 𝓤★ X A = fib𝓨A✧
 where
  hfe : global-hfunext
  hfe = univalence-gives-global-hfunext 𝓤★

  dfe : global-dfunext
  dfe = univalence-gives-global-dfunext 𝓤★

  p = λ x → (𝓨 x ≡ A)               ≃⟨ i x ⟩
            ((y : X) → 𝓨 x y ≡ A y) ≃⟨ ii x ⟩
            ((y : X) → 𝓨 x y ≃ A y) ■
    where
     i = λ x → (happly (𝓨 x) A , hfe (𝓨 x) A)
     ii = λ x → Π-cong dfe dfe (λ y → univalence-≃ (𝓤★ 𝓤) (𝓨 x y) (A y) )
  fibrep : fiber 𝓨 A ≃ is-representable A
  fibrep = Σ-cong p

  fib𝓨A✧ : is-subsingleton (fiber 𝓨 A)
  fib𝓨A✧ = equiv-to-subsingleton fibrep (being-representable-is-subsingleton dfe A)

--(next topic: "What is a function?")


----------------------------------------------------------------------------------------------
-- SUBTYPES.

--FILE: Subtype.agda
--DATE: 14 Apr 2020
--BLAME: <williamdemeo@gmail.com>
--REF: Based on Martin Escardo's course notes
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#universelifting


----------------------------------------------------------------------------------
--Universe lifting.
--"Universes are not cumulative on the nose in Agda, in the sense that from `X : 𝓤` we would get
-- that `X : 𝓤⁺` or that `X : 𝓤 ⊔ 𝓥`. Instead we work with embeddings of universes into larger
-- universes.

--"The following together with its induction principle should be considered as part of the universe
-- handling of our spartan Martin-Löf type theory:
record Lift {𝓤 : Universe} (𝓥 : Universe) (X : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 constructor lift
 field
  lower : X

open Lift public

--"The functions `Lift`, `lift` and `lower` have the following types:
type-of-Lift    :                   type-of ( Lift   {𝓤} 𝓥)          ≡   (𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
type-of-lift     : {X : 𝓤 ̇} → type-of ( lift    {𝓤} {𝓥} {X} )   ≡   ( X  →  Lift 𝓥 X )
type-of-lower : {X : 𝓤 ̇} → type-of ( lower {𝓤} {𝓥} {X} )   ≡   ( Lift 𝓥 X  →  X )

type-of-Lift = refl _
type-of-lift = refl _
type-of-lower = refl _

--"The induction and recursion principles are as follows:
Lift-induction : ∀ {𝓤} 𝓥 (X : 𝓤 ̇) (A : Lift 𝓥 X → 𝓦 ̇)
 →                 ( (x : X) → A (lift x) )
 →                 (ℓ : Lift 𝓥 X) → A ℓ
Lift-induction 𝓥 X A φ (lift x) = φ x

Lift-recursion : ∀ {𝓤} 𝓥 {X : 𝓤 ̇} {B : 𝓦 ̇}
 →                  (X → B)  →  Lift 𝓥 X → B
Lift-recursion 𝓥 {X} {B} = Lift-induction 𝓥 X λ _ → B

--"This gives an equivalence `lift : X → Lift 𝓥 X` and hence an embedding `Lift 𝓥 : 𝓤 ̇ → 𝓤 ⊔ 𝓥`.
-- The following two constructions can be performed with induction, but actually hold on the nose by
-- the so-called `η` rule for records.
-- (see https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion )
lower-lift : {X : 𝓤 ̇} (x : X) → lower {𝓤} {𝓥} (lift x) ≡ x
lower-lift = refl

lift-lower : {X : 𝓤 ̇} (ℓ : Lift 𝓥 X) → lift (lower ℓ) ≡ ℓ
lift-lower = refl

Lift-≃ : (X : 𝓤 ̇) → Lift 𝓥 X ≃ X
Lift-≃ {𝓤} {𝓥} X = invertibility-gives-≃ lower ( lift , lift-lower , lower-lift {𝓤} {𝓥} )

≃-Lift : (X : 𝓤 ̇) → X ≃ Lift 𝓥 X
≃-Lift {𝓤} {𝓥} X = invertibility-gives-≃ lift ( lower , lower-lift {𝓤} {𝓥} , lift-lower )

--"With universe lifting, we can generalize equivalence induction as follows, in several steps.

--"Firstly, function extensionality for a pair of universes gives function extensionality for any
-- pair of lower universes:
lower-dfunext : ∀ 𝓦 𝓣 𝓤 𝓥 → dfunext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → dfunext 𝓤 𝓥
lower-dfunext 𝓦 𝓣 𝓤 𝓥 fe {X} {A} {f} {g} h = f≡g
 where
  A' : Lift 𝓦 X → 𝓥 ⊔ 𝓣 ̇
  A' y = Lift 𝓣 ( A (lower y) )

  f' g' : Π A'
  f' y = lift (f (lower y) )
  g' y = lift (g (lower y) )

  h' : f' ∼ g'
  h' y = ap lift (h (lower y) )

  f'≡g' : f' ≡ g'
  f'≡g' = fe h'

  f≡g : f ≡ g
  f≡g = ap (λ f' x → lower (f' (lift x) ) ) f'≡g'

--"Secondly, a function from a universe to a higher universe is an embedding provided it maps any type
-- to an equivalent type and the two universes are univalent:
universe-embedding-criterion : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥)
 →                             (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇)
 →                             ((X : 𝓤 ̇) → f X ≃ X)
                              ------------------------
 →                             is-embedding f

universe-embedding-criterion {𝓤} {𝓥} 𝓤★ 𝓤⊔𝓥★ f e = embedding-criterion f γ
 where
  fe : dfunext (𝓤 ⊔ 𝓥)  (𝓤 ⊔ 𝓥)
  fe = univalence-gives-dfunext 𝓤⊔𝓥★

  fe₀ : dfunext 𝓤 𝓤
  fe₀ = lower-dfunext 𝓥 𝓥 𝓤 𝓤 fe

  fe₁ : dfunext 𝓤 (𝓤 ⊔ 𝓥)
  fe₁ = lower-dfunext 𝓥 𝓥 𝓤 (𝓤 ⊔ 𝓥) fe

  γ : (X X' : 𝓤 ̇ ) → (f X ≡ f X') ≃ (X ≡ X')
  γ X X' =  (f X ≡ f X')  ≃⟨ i   ⟩
                (f X ≃ f X')  ≃⟨ ii  ⟩
                (X ≃ X')      ≃⟨ iii ⟩
                (X ≡ X')      ■
   where
    i   = univalence-≃ 𝓤⊔𝓥★ (f X) (f X')
    ii  = Eq-Eq-cong' fe fe fe fe fe fe₀ fe₁ fe fe₀ fe₀ fe₀ fe₀ (e X) (e X')
    iii = ≃-sym (univalence-≃ 𝓤★ X X')


--"In particular, the function `Lift` is an embedding:
Lift-is-embedding : is-univalent 𝓤
 →                  is-univalent (𝓤 ⊔ 𝓥)
 →                  is-embedding (Lift {𝓤} 𝓥 )
Lift-is-embedding {𝓤} {𝓥} 𝓤★ 𝓤⊔𝓥★ =
 universe-embedding-criterion {𝓤}{𝓥} 𝓤★ 𝓤⊔𝓥★ (Lift 𝓥) Lift-≃

--"Thirdly, we have a generalization of `univalence→` from a single universe to a pair of universes.
-- We work with two symmetrical versions, where the second is derived from the first. We use an
-- anonymous module to assume univalence in the following couple of construction:
module _ {𝓤 𝓥 : Universe} (𝓥★ : is-univalent 𝓥) (𝓤⊔𝓥★ : is-univalent (𝓤 ⊔ 𝓥) ) where
 private
  fe : dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  fe = univalence-gives-dfunext 𝓤⊔𝓥★
  fe₀ : dfunext 𝓥 (𝓤 ⊔ 𝓥)
  fe₀ = lower-dfunext 𝓤 𝓤 𝓥 (𝓤 ⊔ 𝓥) fe
  fe₁ : dfunext 𝓤 (𝓤 ⊔ 𝓥)
  fe₁ = lower-dfunext (𝓤 ⊔ 𝓥) 𝓤 𝓤 (𝓤 ⊔ 𝓥) fe
  fe₂ : dfunext 𝓥 𝓥
  fe₂ = lower-dfunext 𝓤 𝓤 𝓥 𝓥 fe
  fe₃ : dfunext 𝓤 𝓤
  fe₃ = lower-dfunext 𝓥 𝓥 𝓤 𝓤 fe

 univalence→' : (X : 𝓤 ̇) → is-subsingleton ( Σ Y ꞉ 𝓥 ̇ , X ≃ Y )
 univalence→' X = γ
  where
   abstract
    e : (Y : 𝓥 ̇) → (X ≃ Y) ≃ (Lift 𝓤 Y ≡ Lift 𝓥 X)
    e Y = (X ≃ Y)                       ≃⟨ i    ⟩
            (Y ≃ X)                        ≃⟨ ii ⟩
            (Lift 𝓤 Y ≃ Lift 𝓥 X)  ≃⟨ iii ⟩
            (Lift 𝓤 Y ≡ Lift 𝓥 X)  ■
      where
        i = ≃-Sym fe₀ fe₁ fe
        ii = Eq-Eq-cong' fe₁ fe fe₂ fe₁ fe fe fe fe₃ fe fe fe fe (≃-Lift Y) (≃-Lift X)
        iii = ≃-sym (univalence-≃ 𝓤⊔𝓥★ (Lift 𝓤 Y) (Lift 𝓥 X) )

    d : (Σ Y ꞉ 𝓥 ̇ , X ≃ Y) ≃ (Σ Y ꞉ 𝓥 ̇ , Lift 𝓤 Y ≡ Lift 𝓥 X)
    d = Σ-cong e
    ΣY✧ : is-subsingleton (Σ Y ꞉ 𝓥 ̇ , Lift 𝓤 Y ≡ Lift 𝓥 X)
    ΣY✧ =  Lift-is-embedding 𝓥★ 𝓤⊔𝓥★ (Lift 𝓥 X)
    γ : is-subsingleton ( Σ Y ꞉ 𝓥 ̇ , X ≃ Y )
    γ = equiv-to-subsingleton d ΣY✧

 univalence→'-dual : (Y : 𝓤 ̇) → is-subsingleton (Σ X ꞉ 𝓥 ̇ , X ≃ Y)
 univalence→'-dual Y = equiv-to-subsingleton eq ΣY≃X✧
  where
   eq : (Σ X ꞉ 𝓥 ̇ , X ≃ Y ) ≃  (Σ X ꞉ 𝓥 ̇ , Y ≃ X)
   eq = Σ-cong λ X → ≃-Sym fe₁ fe₀ fe
   ΣY≃X✧ : is-subsingleton (Σ X ꞉ 𝓥 ̇ , Y ≃ X)
   ΣY≃X✧ = univalence→' Y

--"This is the end of the anonymous module. We are interested in these corollaries:
--\begin{code}\end{code}

--"The first one is applied to get the following, where `Y` lives in a universe above that of `X`:
--\begin{code}\end{code}

--"*Exercise*. [Formulate and prove](HoTT-UF-Agda.html#someexercisessol) the equations for `G↑-≃` and `H↑-≃` corresponding to
-- those for `𝔾-≃` and `ℍ-≃`.

--"The difference with `ℍ-≃` is that here, to get the conclusion, we need to assume `A (Lift 𝓥 X) (≃-Lift X)` rather than
-- `A X (id-≃)`. And we have a similar development with a similar example:
--\begin{code}\end{code}

--"All invertible functions from a type in a universe `𝓤` to a type in a higher universe `𝓤 ⊔ 𝓥` satisfy a given property if (and only if)
-- the functions `lift {𝓤} {𝓥} {X} : X → Lift 𝓥 X` satisfy the property for all `X : 𝓤` (where we don't write the implicit arguments for `lift`):
-- \begin{code}\end{code}

--"Here is an example. First, `lift` is a half adjoint equivalence on the nose:
--\begin{code}\end{code}

--"Hence all invertible maps going up universe levels are half adjoint equivalences:
--\begin{code}\end{code}

--"We have a dual development with the universes going down, where we consider `lower` in place of `lift`:
--\begin{code}\end{code}

--"All invertible functions from a type in a universe `𝓤 ⊔ 𝓥` to a type in the lower universe `𝓤` satisfy a given property if (and only if)
-- the functions `lower {𝓤} {𝓥} {Y} : Lift 𝓥 Y → Y` satisfy the property for all `Y : 𝓤`:
--\begin{code}\end{code}

--"And we have similar examples:
--\begin{code}\end{code}

--"A crucial example of an equivalence "going down one universe" is `Id→Eq X Y`. This is because the identity type `X ≡ Y` lives in the
-- successor universe `𝓤 ⁺` if `X` and `Y` live in `𝓤`, whereas the equivalence type `X ≃ Y` lives in the same universe as `X` and
-- `Y`. Hence we can apply the above function `invertibles-are-haes↓` to `Id→Eq X Y` to conclude that it is a half adjoint equivalence:
--\begin{code}\end{code}

--"We can be parsimonious with the uses of univalence by instead using `invertibles-are-haes`, which doesn't require univalence. However, that
-- `Id→Eq` is invertible of course requires univalence.
--\begin{code} \end{code}

--"The remainder of this section is not used anywhere else.  Using the universe `𝓤ω` discussed above, we can consider global properties:
--\begin{code}\end{code}

{-"We have already considered a few global properties, in fact, such as `is-singleton`, `is-subsingleton`, `is-set` and `_is-of-hlevel n`.
   We may hope to have that if `A` is a global property of types, then, in the presence of univalence, for any `X : 𝓤` and `Y : 𝓥`, if `A X` holds
   then so does `A Y`.  However, because we have a type of universes, or universe levels, we may define e.g. `A {𝓤} X = (𝓤 ≡ 𝓤₀)`, which violates
   this hope. To get this conclusion, we need an assumption on `A`. We say that `A` is cumulative if it is preserved by the embedding `Lift` of
   universes into higher universes: -}
--\begin{code}\end{code}

--"We can prove the following:
--\begin{code}\end{code}

--"However, the above notion of global property is very restrictive. For example, `is-inhabited` defined below is a global property of
-- type `{𝓤 : Universe} → 𝓤 ̇ → 𝓤 ⁺ ̇ `.  Hence we prove something more general, where in this example we take `F 𝓤 = 𝓤 ⁺`.
--\begin{code}\end{code}

--"The first claim follows with `F = id`:
--\begin{code}\end{code}

-----------------------------------------------------------------------------------------
-- The subtype classifier and other classifiers.
--"A subtype of a type `Y` is a type `X` *together* with an embedding of `X` into `Y`:
Subtypes : 𝓤 ̇ → 𝓤 ⁺ ̇
Subtypes {𝓤} Y = Σ X ꞉ 𝓤 ̇ , X ↪ Y

--"The type `Ω 𝓤` of subsingletons in the universe `𝓤` is the subtype classifier of types in `𝓤`, in the sense that we have a canonical
-- equivalence `Subtypes Y ≃ (Y → Ω 𝓤)` for any type `Y : 𝓤`.

--"We will derive this from something more general.  We defined embeddings to be maps whose fibers are all subsingletons.
-- We can replace `is-subsingleton` by an arbitrary property `P` of--or even structure on--types.

--"The following generalizes the slice constructor `_/_`:
_/[_]_ : (𝓤 : Universe) → (𝓤 ̇ → 𝓥 ̇) → 𝓤 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 /[ P ] Y = Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , ( ( y : Y ) → P (fiber f y) )

--[Recall, under univalence `𝓤` becomes a map classifier, which amounts to a bijection between `𝓤 / Y` and `Y → 𝓤`:
-- Inhabitants of 𝓤 / Y (= Σ X ꞉ 𝓤 ̇ , (X → Y)) are pairs (X, f), where f : X → Y.]

χ-special : (P : 𝓤 ̇ → 𝓥 ̇) (Y : 𝓤 ̇) → 𝓤 /[ P ] Y → (Y → Σ P)
χ-special P Y (X , f , φ) y = fiber f y , φ y

is-special-map-classifier : (𝓤 ̇ → 𝓥 ̇) → 𝓤 ⁺ ⊔ 𝓥 ̇
is-special-map-classifier {𝓤} P = (Y : 𝓤 ̇) → is-equiv (χ-special P Y)

--"If a universe is a map classifier then `Σ P` is the classifier of maps with `P`-fibers, for any `P : 𝓤  → 𝓥`:
mc-gives-sc : is-map-classifier 𝓤  →  (P : 𝓤 ̇ → 𝓥 ̇)
                   --------------------------------------
 →                 is-special-map-classifier P
mc-gives-sc {𝓤} s P Y = γ
  where
    e :   (𝓤 /[ P ] Y)  ≃  (Y → Σ P)
    e = (𝓤 /[ P ] Y)                                                 ≃⟨ ≃-sym a ⟩
          (Σ σ ꞉ 𝓤 / Y , ( ( y : Y ) → P ( ( χ Y ) σ y ) ) )   ≃⟨ ≃-sym b ⟩
          (Σ A ꞉ (Y → 𝓤 ̇) , ( ( y : Y ) → P (A y) ) )         ≃⟨ ≃-sym c ⟩
          (Y → Σ P)                                                    ■
     where
       a = Σ-assoc
       b = Σ-change-of-variable (λ A → Π (P ∘ A) )  (χ Y)  (s Y)    -- N.B.  λ A → Π (P ∘ A) ≡ λ A → (x : Y) → P (A x)
       c = ΠΣ-distr-≃

    observation : χ-special P Y ≡ ∣ e ∣
    observation = refl _

    γ : is-equiv (χ-special P Y)
    γ = ∥ e ∥

--"Therefore we have the following canonical equivalence:
χ-special-is-equiv : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
 →                       (P : 𝓤 ̇ → 𝓥 ̇)      (Y : 𝓤 ̇)
                          --------------------------------
 →                       is-equiv (χ-special P Y)
χ-special-is-equiv {𝓤} 𝓤★ fe P Y = mc-gives-sc (universes-are-map-classifiers 𝓤★ fe) P Y

special-map-classifier : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺) → (P : 𝓤 ̇ → 𝓥 ̇)  (Y : 𝓤 ̇)
                                ----------------------------------------------------------
 →                                             𝓤 /[ P ] Y    ≃    (Y → Σ P)

special-map-classifier {𝓤} 𝓤★ fe P Y = χ-special P Y , χ-special-is-equiv 𝓤★ fe P Y

--"In particular, considering `P = is-subsingleton`, we get the promised fact that `Ω` is the subtype classifier:
Ω-is-subtype-classifier :      Univalence  →  (Y : 𝓤 ̇)
                                      ---------------------------
 →                                   Subtypes Y   ≃   (Y → Ω 𝓤)
Ω-is-subtype-classifier {𝓤} 𝓤★ = special-map-classifier (𝓤★ 𝓤) (univalence-gives-dfunext' (𝓤★ 𝓤) (𝓤★ (𝓤 ⁺) ) ) is-subsingleton

--"It follows that the type of subtypes of `Y` is always a set, even if `Y` is not a set:
subtypes-form-set :     Univalence  →  (Y : 𝓤 ̇)
                                -----------------------
 →                               is-set (Subtypes Y)
subtypes-form-set {𝓤} 𝓤★ Y = equiv-to-set (Ω-is-subtype-classifier 𝓤★ Y) (powersets-are-sets' 𝓤★ )

--"We now consider `P = is-singleton` and the type of singletons:
𝓢 : (𝓤 : Universe) → 𝓤 ⁺ ̇
𝓢 𝓤 = Σ S ꞉ 𝓤 ̇ , is-singleton S

equiv-classification :   Univalence → (Y : 𝓤 ̇)
 →                          ( Σ X ꞉ 𝓤 ̇ , X ≃ Y )    ≃    ( Y → 𝓢 𝓤 )

equiv-classification {𝓤} 𝓤★ = special-map-classifier (𝓤★ 𝓤) (univalence-gives-dfunext' (𝓤★ 𝓤) (𝓤★ (𝓤 ⁺) ) ) is-singleton

--"With this we can derive a fact we already know, as follows.  First the type of singletons (in a universe) is itself a singleton (in the next universe):
the-singletons-form-a-singleton : propext 𝓤 → dfunext 𝓤 𝓤 → is-singleton (𝓢 𝓤)
the-singletons-form-a-singleton {𝓤} pe fe = 𝓢𝓤 , 𝓢𝓤✦
 where
  Lift𝓤𝟙✦ : is-singleton (Lift 𝓤 𝟙)
  Lift𝓤𝟙✦  = equiv-to-singleton (Lift-≃ 𝟙) 𝟙-is-singleton

  𝓢𝓤 : 𝓢 𝓤
  𝓢𝓤 = Lift 𝓤 𝟙 , Lift𝓤𝟙✦

  𝓢𝓤✦ : (x : 𝓢 𝓤) → 𝓢𝓤 ≡ x
  𝓢𝓤✦ (S , s) = to-subtype-≡ (λ _ → being-singleton-is-subsingleton fe) p
   where
    p : Lift 𝓤 𝟙 ≡ S
    p = pe ( singletons-are-subsingletons (Lift 𝓤 𝟙) Lift𝓤𝟙✦ )
               ( singletons-are-subsingletons S s )
               ( λ _ → center S s) (λ _ → center (Lift 𝓤 𝟙) Lift𝓤𝟙✦ )


--"What we already knew is this:
univalence-→-again : Univalence → (Y : 𝓤 ̇)  →  is-singleton (Σ X ꞉ 𝓤 ̇ , X ≃ Y)
univalence-→-again {𝓤} 𝓤★ Y = equiv-to-singleton (equiv-classification 𝓤★ Y) Y𝓢𝓤✦
 where
  Y𝓢𝓤✦ : is-singleton (Y → 𝓢 𝓤)
  Y𝓢𝓤✦ = univalence-gives-vvfunext' (𝓤★ 𝓤) (𝓤★ (𝓤 ⁺) )
                   ( λ y → the-singletons-form-a-singleton (univalence-gives-propext (𝓤★ 𝓤) )
                                                                              (univalence-gives-dfunext (𝓤★ 𝓤) ) )

--"*Exercise*. [(1)](HoTT-UF-Agda.html#pointed-types) Show that the retractions into `Y` are classified by the type `Σ A ꞉ 𝓤 ̇ , A` of pointed types.
--                 [(2)](HoTT-UF-Agda.html#surjections-into) After we have defined propositional truncations and surjections, show that the surjections
--                      into `Y` are classified by the type `Σ A ꞉ 𝓤 ̇ , ∥ A ∥` of inhabited types.



-- Added later. See: https://www.cs.bham.ac.uk/~mhe/agda-new/UF-UniverseEmbedding.html#3032


-- prop-fiber-criterion : global-propext → global-funext → (𝓤 𝓥 : Universe)
--  →                          (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )     →    ((X : 𝓤 ̇ ) → f X ≃ X)
--  →                          (Q : 𝓤 ⊔ 𝓥 ̇ ) → is-prop Q → is-prop (fiber f Q)
-- prop-fiber-criterion pe fe 𝓤 𝓥 f i Q j (P , r) = d (P , r)
--  where
--   k : is-prop (f P)
--   k = back-transport is-prop r j
--   e :  (X : 𝓤 ̇ ) → (f X ≡ f P) ≃ (f X ≃ f P)
--   e X = subsingleton-univalence-≃ ( pe (𝓤 ⊔ 𝓥) )  ( fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) ) (f X) (f P) k 
--   l : is-prop P
--   l = equiv-to-subsingleton (≃-sym (i P)) k
--   a : (X : 𝓤 ̇ ) → (f X ≡ f P) ≃ (X ≡ P)
--   a X = (f X ≡ f P)  ≃⟨ e X ⟩  --subsingleton-univalence-≃  
--       (f X ≃ f P)  ≃⟨ Eq-Eq-cong fe (i X) (i P) ⟩
--         (X ≃ P)      ≃⟨ {!!}  ⟩  -- ≃-sym (subsingleton-univalence-≃ (pe 𝓤) (fe 𝓤 𝓤) X P l)
--         (X ≡ P)      ■
--   b : (Σ X ꞉ 𝓤 ̇ , f X ≡ f P) ≃ (Σ X ꞉ 𝓤 ̇  , X ≡ P)
--   b = Σ-cong a
--   c : is-prop (Σ X ꞉ 𝓤 ̇ , f X ≡ f P)
--   c = equiv-to-subsingleton b {!!} -- (singleton-types'-are-singletons P)
--   d : is-prop (Σ X ꞉ 𝓤 ̇ , f X ≡ Q)
--   d = transport (λ - → is-prop (Σ X ꞉ 𝓤 ̇ , f X ≡ -)) r c

-- prop-fiber-lift : global-propext → global-dfunext → (Q : 𝓤 ⊔ 𝓥 ̇ ) → is-prop Q → is-prop (fiber (lift 𝓥) Q)
-- prop-fiber-lift {𝓤} {𝓥} pe fe = prop-fiber-criterion pe fe 𝓤 𝓥 (lift {𝓤} 𝓥) (Lift-≃ 𝓥)


