.. FILE: relations.lagda.rst
.. BLAME: William DeMeo and Siva Somayyajula
.. DATE: 23 Apr 2020
.. UPDATE: 16 Jun 2020
.. REF: Some of this file is simply a translation of the Agda standard library file Binary/Core.agda
   into our notation.

====================
Relations in Agda
====================

Here we describe the ``relations`` module of the `agda-ualib`_.

**N.B.** Some of the code described in this section was borrowed from similar code in the `Agda standard library`_ (in the file ``Binary/Core.agda``) and translated into our notation for consistency.

Preliminaries
---------------

::

   {-# OPTIONS --without-K --exact-split --safe #-}

   open import prelude
   open import basic using (Signature; Algebra)

   module relations where

--------------------------------------

Binary relations
------------------------

Heterogeneous binary relations.

::

   REL : 𝓤 ̇ → 𝓥 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓝 ⁺) ̇
   REL A B 𝓝 = A → B → 𝓝 ̇

Homogeneous binary relations.

::

   Rel : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
   Rel A 𝓝 = REL A A 𝓝

--------------------------------------

Kernels
---------

The kernel of a function can be defined in many ways. For example,

::

   KER : {A : 𝓤 ̇} {B : 𝓦 ̇} → (f : A → B) → 𝓤 ⊔ 𝓦 ̇
   KER {𝓤}{𝓦}{A} f = Σ x ꞉ A , Σ y ꞉ A , f x ≡ f y

   ker : {A B : 𝓤 ̇} → (f : A → B) → 𝓤 ̇
   ker {𝓤} = KER{𝓤}{𝓤}

or as a relation...

::

   KER-rel : {A : 𝓤 ̇} {B : 𝓦 ̇} → (f : A → B) → Rel A 𝓦
   KER-rel f x y = f x ≡ f y

   -- (in the special case 𝓦 ≡ 𝓤)
   ker-rel : {A B : 𝓤 ̇} → (f : A → B) → Rel A 𝓤
   ker-rel {𝓤} = KER-rel {𝓤} {𝓤}

or a binary predicate...

::

   KER-pred : {A : 𝓤 ̇}{B : 𝓦 ̇} (f : A → B) → Pred (A × A) 𝓦
   KER-pred f (x , y) = f x ≡ f y

   -- (in the special case 𝓦 ≡ 𝓤)
   ker-pred : {A : 𝓤 ̇}{B : 𝓤 ̇} (f : A → B) → Pred (A × A) 𝓤
   ker-pred {𝓤} = KER-pred {𝓤} {𝓤}

--------------------------------------

Implication
-----------------

We denote and define implication or containment (which could also be written _⊆_) as follows.

::

   _⇒_ : {A : 𝓤 ̇}  {B : 𝓥 ̇}  → REL A B 𝓡 → REL A B 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
   P ⇒ Q = ∀ {i j} → P i j → Q i j
   infixr 4 _⇒_

   _on_ : {A : 𝓤 ̇}  {B : 𝓥 ̇}  {C : 𝓦 ̇} → (B → B → C) → (A → B) → (A → A → C)
   _*_ on f = λ x y → f x * f y

Here is a more general version of implication 

::

   _=[_]⇒_ : {A : 𝓤 ̇}  {B : 𝓥 ̇} → Rel A 𝓡 → (A → B) → Rel B 𝓢 →  𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇
   P =[ f ]⇒ Q = P ⇒ (Q on f)
   infixr 4 _=[_]⇒_


Properties of binary relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Reflexivity of a binary relation (say, ``≈``) on ``X``, can be defined without an underlying equality as follows.

::

   reflexive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
   reflexive _≈_ = ∀ x → x ≈ x


Similarly, we have the usual notion of symmetric (resp., transitive) binary relation.

::

   symmetric : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
   symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

   transitive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
   transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

For a binary relation ≈ on A, denote a single ≈-class (containing a) by `[ a ] ≈`,

::

   [_]_ :  {A : 𝓤 ̇} →  (a : A) → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
   [ a ] _≈_ = Σ x ꞉ _ ,  a ≈ x

and denote the collection of all ≈-classes of A by `A // ≈`.

::

   _//_ :  (A : 𝓤 ̇ ) → Rel A 𝓡 → (𝓤 ⊔ 𝓡) ⁺ ̇
   A // ≈ = Σ C ꞉ _ ,   Σ a ꞉ A ,  C ≡ ( [ a ] ≈ )

   is-subsingleton-valued : {A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
   is-subsingleton-valued  _≈_ = ∀ x y → is-prop (x ≈ y)

The "trivial" or "diagonal" or "identity" relation is,

::

   𝟎 : {A : 𝓤 ̇} → 𝓤 ̇
   𝟎{𝓤} {A} = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

   𝟎-rel : {A : 𝓤 ̇} → Rel A 𝓤
   𝟎-rel a b = a ≡ b

or, in various other guises, 

::

   -- ...as a binary predicate:
   𝟎-pred : {A : 𝓤 ̇} → Pred (A × A) 𝓤
   𝟎-pred (a , a') = a ≡ a'

   --...as a binary predicate:
   𝟎'' : {A : 𝓤 ̇} → 𝓤 ̇
   𝟎'' {𝓤} {A} = Σ p ꞉ (A × A) , ∣ p ∣ ≡ ∥ p ∥

The "universal" or "total" or "all" relation.

::

   𝟏 : {A : 𝓤 ̇} → Rel A 𝓤₀
   𝟏 a b = 𝟙

Equivalence relations
----------------------

.. The preorders of the standard library are defined in terms of an underlying equivalence relation, and hence equivalence relations are not defined in terms of preorders.

Here are two ways to define an equivalence relation in Agda.

First, we use a record.

::

   record IsEquivalence {A : 𝓤 ̇} (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
     field
       rfl  : reflexive _≈_
       sym   : symmetric _≈_
       trans : transitive _≈_


Here's an alternative.

::

   is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
   is-equivalence-relation _≈_ =
    is-subsingleton-valued _≈_
     × reflexive _≈_ × symmetric _≈_ × transitive _≈_


Of course, `𝟎` is an equivalence relation, a fact we can prove as follows.

::

   𝟎-IsEquivalence : {A : 𝓤 ̇} → IsEquivalence {𝓤}{𝓤}{A} 𝟎-rel
   𝟎-IsEquivalence = record { rfl = ρ ; sym = σ ; trans = τ }
    where
     ρ : reflexive 𝟎-rel
     ρ x =  x ≡⟨ refl _ ⟩ x ∎

     σ : symmetric 𝟎-rel
     σ x y x≡y = x≡y ⁻¹

     τ : transitive 𝟎-rel
     τ x y z x≡y y≡z = x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎

We define the **lift** of a binary relation from pairs to pairs of tuples as follows:

::

   lift-rel :  {γ : 𝓥 ̇} {Z : 𝓤 ̇} → Rel Z 𝓦 → (γ → Z) → (γ → Z) → 𝓥 ⊔ 𝓦 ̇
   lift-rel R 𝒇 𝒈 = ∀ x → R (𝒇 x) (𝒈 x)


We define **compatibility** of a given function-relation pair as follows:

::

   compatible-fun : {γ : 𝓥 ̇} {Z : 𝓤 ̇} ( 𝒇 : (γ → Z) → Z )  (𝑹 : Rel Z 𝓦) →  𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   compatible-fun 𝒇 𝑹 = (lift-rel 𝑹) =[ 𝒇 ]⇒ 𝑹


Finally, we come to the definition of a congruence, which we define in a module (so that we can assume a particular signature ``S`` is present and available in the context).

::

   module _ {S : Signature 𝓞 𝓥}  where

     -- relation compatible with an operation
     compatible-op : {𝑨 : Algebra 𝓤 S} → ∣ S ∣ → Rel ∣ 𝑨 ∣ 𝓤 → 𝓥 ⊔ 𝓤 ̇
     compatible-op {𝓤} {𝑨} 𝓸 𝓻 = (lift-rel 𝓻) =[ (∥ 𝑨 ∥ 𝓸) ]⇒ 𝓻

     --The given relation is compatible with all ops of an algebra.
     compatible : (𝑨 : Algebra 𝓤 S) -> Rel ∣ 𝑨 ∣ 𝓤 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇
     compatible {𝓤} 𝑨 𝓻 = ∀ 𝓸 → compatible-op{𝓤}{𝑨} 𝓸 𝓻

     𝟎-compatible-op : funext 𝓥 𝓤
      →                {𝑨 : Algebra 𝓤 S} (𝓸 : ∣ S ∣)
      →                compatible-op {𝓤}{𝑨} 𝓸 𝟎-rel
     𝟎-compatible-op fe {𝑨 = 𝑨} 𝓸 ptws𝟎  = ap  (∥ 𝑨 ∥ 𝓸) (fe (λ x → ptws𝟎 x))
     -- 𝟎-rel : {A : 𝓤 ̇} → Rel A 𝓤
     -- 𝟎-rel a b = a ≡ b

     𝟎-compatible : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 S} → compatible 𝑨 𝟎-rel
     𝟎-compatible fe {𝑨} = λ 𝓸 args → 𝟎-compatible-op fe {𝑨} 𝓸 args

     -- Congruence relations
     Con : (𝑨 : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
     Con {𝓤} 𝑨 = Σ θ ꞉ ( Rel ∣ 𝑨 ∣ 𝓤 ) , IsEquivalence θ × compatible 𝑨 θ

     con : (𝑨 : Algebra 𝓤 S)  →  Pred (Rel ∣ 𝑨 ∣ 𝓤) _
     con 𝑨 = λ θ → IsEquivalence θ × compatible 𝑨 θ

     record Congruence (𝑨 : Algebra 𝓤 S) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
       constructor mkcon
       field
         ⟨_⟩ : Rel ∣ 𝑨 ∣ 𝓤
         Compatible : compatible 𝑨 ⟨_⟩
         IsEquiv : IsEquivalence ⟨_⟩
     open Congruence

We construct the "trivial" or "diagonal" or "identity" relation and prove it is a congruence as follows.

::

     Δ : funext 𝓥 𝓤 → (𝑨 : Algebra 𝓤 S) → Congruence 𝑨
     Δ fe 𝑨 = mkcon 𝟎-rel
                   ( 𝟎-compatible fe {𝑨} )
                   ( 𝟎-IsEquivalence )

     _╱_ : (𝑨 : Algebra 𝓤 S) → Congruence 𝑨
            ---------------------------------
      →     Algebra (𝓤 ⁺) S
     𝑨 ╱ θ = ( ( ∣ 𝑨 ∣ // ⟨ θ ⟩ ) , -- carrier
                ( λ 𝓸 args        -- operations
                    → ( [ ∥ 𝑨 ∥ 𝓸 (λ i₁ -> ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩ ) ,
                       ( ∥ 𝑨 ∥ 𝓸 (λ i₁ -> ∣ ∥ args i₁ ∥ ∣) , refl _ )
                )
              )





..
   Generalised connex: exactly one of the two relations holds.
      Connex : {A : 𝓤 ̇}  {B : 𝓥 ̇} → REL A B 𝓡 → REL B A 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
      Connex P Q = ∀ x y → P x y + Q y x
   Totality.
      Total : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
      Total _∼_ = Connex _∼_ _∼_
   Generalised trichotomy: exactly one of three types has a witness.
      data Tri (A : 𝓤 ̇) (B : 𝓥 ̇) (C : 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where
        tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
        tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
        tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C
   Trichotomy.
      Trichotomous : {A : 𝓤 ̇} → Rel A 𝓡 → Rel A 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇
      Trichotomous _≈_ _<_ = ∀ x y → Tri (x < y) (x ≈ y) (x > y)
        where _>_ = flip _<_
   Generalised maximum element.
      Max : {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → B → 𝓤 ⊔ 𝓡 ̇
      Max _≤_ T = ∀ x → x ≤ T
   Maximum element.
      Maximum : {A : 𝓤 ̇} → Rel A 𝓡 → A → 𝓤 ⊔ 𝓡 ̇
      Maximum = Max
   Generalised minimum element.
      Min : {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → A → 𝓥 ⊔ 𝓡 ̇
      Min R = Max (flip R)
   Minimum element.
      Minimum : {A : 𝓤 ̇} → Rel A 𝓡 → A → 𝓤 ⊔ 𝓡 ̇
      Minimum = Min
   Unary relations respecting a binary relation.
      _⟶_Respects_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → 𝓡 ̇) → (B → 𝓢 ̇) → REL A B 𝓣 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
      P ⟶ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x → Q y
   Unary relation respects a binary relation.
      _Respects_ :  {A : 𝓤 ̇} → (A → 𝓥 ̇) → Rel A 𝓡 → Set _
      P Respects _∼_ = P ⟶ P Respects _∼_
   Right respecting: relatedness is preserved on the right by equality.
      _Respectsʳ_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → Rel B 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
      _∼_ Respectsʳ _≈_ = ∀ {x} → (x ∼_) Respects _≈_
   Left respecting: relatedness is preserved on the left by equality.
      _Respectsˡ_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → Rel A 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
      P Respectsˡ _∼_ = ∀ {y} → (flip P y) Respects _∼_
   Respecting: relatedness is preserved on both sides by equality
      _Respects₂_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} → Rel A 𝓡 → Rel A 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇
      P Respects₂ _∼_ = (P Respectsʳ _∼_) × (P Respectsˡ _∼_)
   Substitutivity: any two related elements satisfy exactly the same set of unary relations.
      Substitutive :  {A : 𝓤 ̇} {B : 𝓥 ̇} → Rel A 𝓡 → (𝓢 : Universe) → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ⁺ ̇
      Substitutive {A = A} _∼_ 𝓢 = (P : A → 𝓢 ̇) → P Respects _∼_
   (Note that only the various derivatives of propositional equality can satisfy this property.)
   Decidable relations
   ------------------------
      data Dec {𝓤} (P : 𝓤 ̇) : 𝓤 ̇ where
        yes : ( p :   P) → Dec P
        no  : (¬p : ¬ P) → Dec P
   Decidability: it is possible to determine whether a given pair of elements are related.
      Decidable :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
      Decidable _∼_ = ∀ x y → Dec (x ∼ y)
   Weak decidability: it is sometimes possible to determine if a given pair of elements are related.
      data Maybe (A : 𝓤 ̇) : 𝓤 ̇ where
        just    : (x : A) → Maybe A
        nothing : Maybe A
      WeaklyDecidable :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
      WeaklyDecidable _∼_ = ∀ x y → Maybe (x ∼ y)
   Irrelevancy: all proofs that a given pair of elements are related are indistinguishable (analogous to subsingleton, or prop, or set).
      Irrelevant : {A : 𝓤 ̇} {B : 𝓥 ̇} →  REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
      Irrelevant _∼_ = ∀ {x y} (a b : x ∼ y) → a ≡ b
   Recomputability: we can rebuild a relevant proof given an irrelevant one.
      Recomputable :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
      Recomputable _∼_ = ∀ {x y} → .(x ∼ y) → x ∼ y
   Universal: all pairs of elements are related
      Universal :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
      Universal _∼_ = ∀ x y → x ∼ y
   Non-emptiness: at least one pair of elements are related.
      record NonEmpty  {A : 𝓤 ̇} {B : 𝓥 ̇} (T : REL A B 𝓡) : 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇ where
        constructor nonEmpty
        field
          {x}   : A
          {y}   : B
          proof : T x y
   Here's a more general definition of symmetry.  It pertains to relations from ``A`` to ``B`` (rather than from ``X`` to itself).
      Symmetric : {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → REL B A 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
      Symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x
      -- Sym P Q = P ⇒ flip Q
   Symmetry.
      Symmetric : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
      Symmetric _∼_ = Sym _∼_ _∼_
   Generalised transitivity.
      Trans : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇}
       →      REL A B 𝓡 → REL B C 𝓢 → REL A C 𝓣
       →      𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
      Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k
      flip : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : A → B → 𝓦 ̇}
       →     ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
      flip f = λ y x → f x y
   A flipped variant of generalised transitivity.
      TransFlip : {A : 𝓤 ̇}{B : 𝓥 ̇}{C : 𝓦 ̇}
       →          REL A B 𝓡 → REL B C 𝓢 → REL A C 𝓣
       →          𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
      TransFlip P Q R = ∀ {i j k} → Q j k → P i j → R i k
   Transitivity.
      Transitive : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
      Transitive _∼_ = Trans _∼_ _∼_ _∼_

   Generalised antisymmetry.
      Antisym : {A : 𝓤 ̇}  {B : 𝓥 ̇} → REL A B 𝓡 → REL B A 𝓢 → REL A B 𝓣 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
      Antisym R S E = ∀ {i j} → R i j → S j i → E i j
   Antisymmetry.
      Antisymmetric : {A : 𝓤 ̇} → Rel A 𝓡 → Rel A 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇
      Antisymmetric _≈_ _≤_ = Antisym _≤_ _≤_ _≈_
   Irreflexivity: this is defined terms of the underlying equality.
      Irreflexive : {A : 𝓤 ̇}  {B : 𝓥 ̇} → REL A B 𝓡 → REL A B 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
      Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬ (x < y)
   Asymmetry.
      Asymmetric : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
      Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)
