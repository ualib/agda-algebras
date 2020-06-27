.. FILE: prelude.lagda.rst
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 21 Apr 2020
.. UPDATE: 27 Jun 2020
.. REF: Some parts of this file are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
.. SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ 
.. Throughout, MHE = Martin Hötzel Escardo.

.. _agda preliminaries:

========================
Agda Preliminaries
========================

Options and imports
--------------------

All but the most trivial Agda programs begin by setting some options that effect how Agda behaves and importing from existing libraries (e.g., the `Agda Standard Library`_ or, in our case, Martin Escardo's `Type Topology`_ library). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, here's the start of the first Agda source file in our library, which we call ``prelude.lagda.rst``.

::

   {-# OPTIONS --without-K --exact-split --safe #-}

This specifies Agda ``OPTIONS`` that we will use throughout the library.  For example, the ``without-K`` option disables Streicher's K axiom, and ``exact-split`` makes Agda accept only those definitions with the equality sign "=" that behave like so-called *judgmental* or *definitional* equalities.

Universes
~~~~~~~~~~

We begin the first module of `agda-ualib`_, called ``prelude``, using the Agda directive ``module prelude where``.  We then immediately import the ``Universes`` module from Martin Hötzel Escardo's (MHE's) `Type Topology`_ library. 

::

   module prelude where

    open import Universes public

This ``Universes`` module provides, among other things, an elegant notation for type universes. (MHE has produced an outstanding set of notes on `HoTT-UF-in-Agda`_, which we highly recommend to those wanting more details than we provide here.)

Following MHE, we refer to universes using capitalized script letters 𝓤,𝓥,𝓦,𝓣 (type these in `agda2-mode` with ``\MCU``, ``\MCV``, etc).  We add a few more to Martin's list.

::

    variable
      𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓞 𝓠 𝓡 𝓢 𝓧 : Universe

In the ``Universes`` module, MHE defines the ̇ operator which maps a universe `𝓤` (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`, a.k.a. Type (𝓤 ⁺).  That is, `𝓤 ̇` is simply an alias for `Set 𝓤`, and we have `Set 𝓤 : Set (lsuc 𝓤)`. The level lzero is renamed 𝓤₀, so `𝓤₀ ̇` is an alias for Set lzero. (This corresponds to `Sort 0` in Lean.) Thus, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we denote by `𝓤₀ ⁺ ̇`

The following table translates between standard Agda syntax, MHE syntax and Lean syntax.

+----------------------+--------------------------+-----------------------------+
| Agda                 | MHE Notation             | Lean analog                 |
+======================+==========================+=============================+
| ``Level``            | ``Universe``             | ``universe``                |
|  ``lzero``           | ``𝓤₀``                   | ``0 : universe``            |
| ``Set lzero``        | ``𝓤₀ ̇`` ( = ``Type 𝓤₀``) | ``Sort 0``                  |
|  ``lsuc lzero``      | ``𝓤₀ ⁺``                 | ``1 : universe``            |
| ``Set (lsuc lzero)`` | ``𝓤₀ ⁺ ̇``                | ``Sort 1 = Type = Type 0``  |
+----------------------+--------------------------+-----------------------------+

Public imports
~~~~~~~~~~~~~~~

Next we import other parts of Martin's `Type Topology`_ library, using the Agda directive ``public``, which means these imports will be available wherever the ``prelude`` module in imported.  We describe some of these imports later, when making use of them, but we don't describe each one in detail. (The interested or confused reader should consult `HoTT-UF-in-Agda`_ to learn more.)

::

    open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓻ℯ𝓯𝓵) public
    pattern refl x = 𝓻ℯ𝓯𝓵 {x = x}
    open import Sigma-Type renaming (_,_ to infixr 50 _,_) public
    open import MGS-MLTT using (_∘_; domain; codomain; transport;
     _≡⟨_⟩_; _∎; pr₁; pr₂; -Σ; 𝕁; Π; ¬; _×_; 𝑖𝑑; _∼_; _+_; 𝟘; 𝟙; 𝟚;
     _⇔_; lr-implication; rl-implication; id; _⁻¹) public
    open import MGS-Equivalences using (is-equiv; inverse; invertible) public
    open import MGS-Subsingleton-Theorems using (funext; dfunext;
     is-singleton; is-subsingleton; is-prop; Univalence; global-dfunext;
     univalence-gives-global-dfunext; Π-is-subsingleton; _≃_;
     logically-equivalent-subsingletons-are-equivalent; _●_) public
    open import MGS-Powerset renaming (_∈_ to _∈₀_; _⊆_ to _⊆₀_) using (𝓟;
     ∈-is-subsingleton; equiv-to-subsingleton; powersets-are-sets';
     subset-extensionality') public
    open import MGS-Embeddings using (is-embedding; pr₁-embedding; is-set; _↪_;
     embedding-gives-ap-is-equiv; embeddings-are-lc; ×-is-subsingleton) public
    -- open import MGS-Quotient using (is-subsingleton-valued) public

.. MHE explains, "This says we are defining a binary operator `_,_` to construct the elements of this type as `x , y`. The definition says that an element of `Σ Y` has two `fields`, giving the types for them."

.. We don't have the space (or patience!) to describe each of the imports appearing in ``Preliminaries.agda``. Some of them will come up for discussion in due course. Until then, we refer the reader to the above mentioned documentation, as well as the brief :ref:`axiomk` in the appendix; the latter explains the ``--without-K`` option.

.. The full ``prelude.lagda.rst`` file, which defines other notation and objects we will use throughout the library, appears in the appendix :ref:`preliminaries.agda`. We will describe each of the objects defined therein as they come up in later sections.

Our preferred notations for the first and second projections of a product are ``∣_∣`` and ``∥_∥``, respectively; however, we will sometimes use the more standard ``pr₁`` and ``pr₂`` for compatibility with other libraries and sometimes for readability.

::

    ∣_∣ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → Σ Y → X
    ∣ x , y ∣ = x

    ∥_∥ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → (z : Σ Y) → Y (pr₁ z)
    ∥ x , y ∥ = y

For the :term:`dependent pair type`, we prefer the notation ``Σ x ꞉ X , y`` more than Agda's standard syntax (``Σ λ(x ꞉ X) → y``). `MHE`_ shows us how to define a version of Σ that makes the preferred notation available by making index type explicit.

.. code-block:: agda

    infixr -1 -Σ
    -Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
    -Σ X Y = Σ Y
    syntax -Σ X (λ x → y) = Σ x ꞉ X , y -- type `꞉` as `\:4`

**WARNING**. The symbol `꞉` in the above syntax definition is not the same as `:`, even though they may look very similar. When entering `Σ x ꞉ A , b`, we must type `\:4` in `agda2-mode` to obtain the `꞉` symbol.

MHE explains, Sigma induction as follows: "To prove that `A z` holds for all `z : Σ Y`, for a given property `A`, we just prove that we have `A (x , y)` for all `x : X` and `y : Y x`.  This is called `Σ` induction or `Σ` elimination (or `uncurry`).

.. code-block:: agda

    Σ-induction : {X : 𝓤 ̇}{Y : X → 𝓥 ̇}{A : Σ Y → 𝓦 ̇}
     →            ((x : X)(y : Y x) → A (x , y))
                  -------------------------------
     →            ((x , y) : Σ Y) → A (x , y)
    Σ-induction g (x , y) = g x y

    curry : {X : 𝓤 ̇}{Y : X → 𝓥 ̇}{A : Σ Y → 𝓦 ̇}
     →      (((x , y) : Σ Y ) → A (x , y))
           ---------------------------------
     →      ((x : X) (y : Y x) → A (x , y))
    curry f x y = f (x , y)
    -- Σ-inv = curry

Here's the special case in which the type `Y` doesn't depend on `X`.

.. code-block:: agda

    infixr 30 _×_
    _×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
    X × Y = Σ x ꞉ X , Y

The Pi type former
-------------------

MHE introduces the notation `Π` for them, similar to that for `Σ`.

.. code-block:: agda

    Π : {X : 𝓤 ̇} (A : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
    Π {𝓤} {𝓥} {X} A = (x : X) → A x

    -Π : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
    -Π X Y = Π Y
    infixr -1 -Π
    syntax -Π A (λ x → b) = Π x ꞉ A , b

..
   --              F
   --         s ------→ Fs
   --         ∥          ∥
   -- refl s  ∥          ∥ transport
   --         ⇓         ⇓
   --         t ------→ Ft
   --              F

.. The following is useful when we want to recover implicit arguments without mentioning them.
       lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
       lhs {𝓤}{X}{x}{y} p = x

       rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
       rhs {𝓤}{X}{x}{y} p = y

.. "Composition of identifications. Given two identifications `p : x ≡ y` and `q : y ≡ z`, we can compose them to get an identification `p ∙ q : x ≡ z`. This can also be seen as transitivity of equality.  Because the type of composition doesn't mention `p` and `q`, we can use the non-dependent version of `≡`-induction."
    _∙_ : {X : 𝓤 ̇}{s t u : X} → s ≡ t → t ≡ u → s ≡ u
    p ∙ q = transport ( lhs p ≡_ ) q p
    infixl 30 _∙_                    -- NOTATION: type ∙ using `\.`

    infix  40 _⁻¹
    _⁻¹ : {X : 𝓤 ̇} → {s t : X} → s ≡ t → t ≡ s
    p ⁻¹ = transport (_≡ lhs p) p (refl _) --  (lhs p))

An important tool that we use often in Agda proofs is application of a function to an identification `p : x ≡ x'`. We apply the ``ap`` operator to obtain the identification `ap f p : f x ≡ f x'` when given `p : x ≡ x'` and `f : X → Y`.

Since ``ap`` is already defined in MHE's `Type Topolgy` library, we don't redefine it here.  However, we do define some variations of ``ap`` that are sometimes useful.

::

    ap cong : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y){x x' : X} → x ≡ x' → f x ≡ f x'
    ap f {x} {x'} p = transport (λ - → f x ≡ f -) p (refl (f x))
    cong  = ap   -- alias    (NOTATION (cf. `cong` in `Relation/Binary/PropositionalEquality/Core.agda` )

    ap-cong : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f f' : X → Y}{x x' : X} → f ≡ f' → x ≡ x' → f x ≡ f' x'
    ap-cong {f = f}{x = x} (refl _) (refl _) = refl _

Here is a related tool that we borrow from the ``Relation/Binary/Core.agda`` module of the `Agda standard library`_.

::

    cong-app : ∀ {A : 𝓤 ̇} {B : A → 𝓦 ̇} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
    cong-app {f = f} (refl _) a = refl _

.. "Notice that we have so far used the recursion principle `transport` only. To reason about `transport`, `_∙_`, `_⁻¹` and `ap`, we will need to use the full induction principle `𝕁` (or equivalently pattern matching on `refl`)."

Function extensionality
------------------------

We will work with pointwise equality of functions, which MHE defines (in `Type Topology`_ ) as follows:

.. code-block:: agda

    _∼_ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
    f ∼ g = ∀ x → f x ≡ g x
    infix 0 _∼_

(The `_∼_` relation will be equivalent to equality of functions, once we have the principle of *univalence* at our disposal.)

.. Here are some more equations for transport, including a dependent version.

..  transport-× : {X : 𝓤 ̇ }(A : X → 𝓥 ̇ )(B : X → 𝓦 ̇)
                  {x y : X}(p : x ≡ y){c : A x × B x}
                 ---------------------------------------------------
     →            transport (λ x → A x × B x) p c
                   ≡ (transport A p (pr₁ c) , transport B p (pr₂ c))
    transport-× A B (refl _) {c} = refl _

    transportd : {X : 𝓤 ̇}
                 (A : X → 𝓥 ̇)(B : (x : X) → A x → 𝓦 ̇)
                 {x : X} (a : A x)
                 ((a' , b) : Σ a ꞉ A x , B x a)  {y : X}
                 (p : x ≡ y)  →   B x a'
                 --------------------------------
     →           B y (transport A p a')
    transportd A B a σ (refl _) = id

    transport-Σ : {X : 𝓤 ̇}
                  (A : X → 𝓥 ̇)(B : (x : X) → A x → 𝓦 ̇)
                  {x : X} (y : X) (p : x ≡ y) (a : A x)
                  {(a' , b) : Σ a ꞉ A x , B x a}
                 ---------------------------------------------------
     →            transport (λ x → Σ y ꞉ A x , B x y) p (a' , b)
                   ≡ transport A p a' , transportd A B a (a' , b) p b
    transport-Σ A B {x} x (refl _) a {σ} = refl _

.. The following was added later by MHE (see: https://www.cs.bham.ac.uk/~mhe/agda-new/Id.html#1449 )

    back-transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} → x ≡ y → A y → A x
    back-transport B p = transport B (p ⁻¹)


.. Negation
.. ---------
.. We first introduce notation for double and triple negation to avoid the use of brackets.
    ¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
    ¬¬ A = ¬(¬ A)
    ¬¬¬ A = ¬(¬¬ A)
   To prove `A → ¬¬ A`, start with a hypothetical element `a : A` and function `u : A → 𝟘` and get an element of `𝟘`."
    dni ¬¬-intro : (A : 𝓤 ̇) → A → ¬¬ A
    dni A a A→𝟘 = A→𝟘 a
    ¬¬-intro = dni -- alias

.. Paraphrasing MHE, there is no general way to implement the converse (i.e., from a function (A → 𝟘) → 𝟘, get a point of A). For truth values A, we can assume this as an axiom if we wish, because it is equivalent to em. But for arbitrary types `A`, this would be a form of global choice for type theory, and global choice is known to be inconsistent with univalence (see HoTT book, Thm 3.2.2), because there is no way to choose an element of every non-empty type in a way that is invariant under automorphisms. (However, the AoC is consistent with UF.)

.. In the next proof, we are given `f : A → B`, `v : B → 𝟘` and `a : A`, and we want an element of 𝟘 (easy, since `f a : B`, hence `v (f a) : 𝟘`).

..  contrapositive : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → (¬ B → ¬ A)
    contrapositive A→B B→𝟘 = λ a → B→𝟘 (A→B a)

.. Paraphrasing MHE, if we have a function `A → B` and `B` is empty, then `A` must be empty, too. From this we get that three negations imply one (we call it "triple negation reduction" or ¬¬¬-elim):
    tno ¬¬¬-elim : (A : 𝓤 ̇) → ¬¬¬ A → ¬ A
    tno A = contrapositive (dni A)
    ¬¬¬-elim = tno -- alias

.. Hence, using `dni` once again, we get that `¬¬¬ A` if and only if `¬ A`.

.. Logical equivalence
   --------------------
    _⇔_  _iff_  : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
    X ⇔ Y = (X → Y) × (Y → X)
    _iff_ = _⇔_ -- alias
    infix 10 _⇔_
    infix 10 _iff_

    lr-implication iff-elim-left : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X iff Y) → (X → Y)
    lr-implication = pr₁
    iff-elim-left = pr₁         -- alias

    rl-implication iff-elim-right : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X iff Y) → (Y → X)
    rl-implication = pr₂
    iff-elim-right = pr₂       -- alias

.. We now define a symbol for the negation of equality.
    _≢_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
    x₁ ≢ x₂ = ¬ (x₁ ≡ x₂)
    infix   0 _≢_

.. Here, we have `u≢v : u ≡ v → 𝟘` and we need `v≢u : v ≡ u → 𝟘`, so just compose `u≢v` with the function that inverts ids.
    ≢-sym : {X : 𝓤 ̇} {u v : X} → u ≢ v → v ≢ u
    ≢-sym {𝓤} {X} {u}{v} u≢v = u≢v ∘ (_⁻¹)

.. Paraphrasing MHE, to show the type `𝟙` is not the type `𝟘`, we use that `transport id` gives `𝟙 ≡ 𝟘 → id 𝟙 → id 𝟘` where `id` is the identity on the universe `𝓤₀`. More generally, we have the following conversion of type ids into functions:
    Id→Fun : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
    Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇))
.. Paraphrasing MHE, so given `p : 𝟙 ≡ 𝟘`, we get a function `𝟙 → 𝟘`. Applying this to `⋆ : 𝟙` we conclude the proof of 𝟙 ≢ 𝟘.
    𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
    𝟙-is-not-𝟘 𝟙≡𝟘 = Id→Fun 𝟙≡𝟘 ⋆
.. Paraphrasing MHE, to show that the inhabitants `₁` and `₀` of `𝟚` are not equal, we reduce to the above case. (recall, 𝟚 = 𝟙 + 𝟙 is the disjoint union of 𝟙 with a copy of itself; we named the points of 𝟚 using patterns `₀ = inl ⋆`, `₁ = inr ⋆`)
    ₁-is-not-₀ : ₁ ≢ ₀
    ₁-is-not-₀ ₁≡₀ = 𝟙-is-not-𝟘 𝟙≡𝟘
     where
      f : 𝟚 → 𝓤₀ ̇  -- 𝟚→𝓤₀̇
      f ₀ = 𝟘
      f ₁ = 𝟙

      𝟙≡𝟘 : 𝟙 ≡ 𝟘
      𝟙≡𝟘 = ap f ₁≡₀

.. Decidability
.. ---------------
    decidable : 𝓤 ̇ → 𝓤 ̇
    decidable A = A + ¬ A

    has-decidable-equality : (X : 𝓤 ̇) → 𝓤 ̇
    has-decidable-equality X = (x₁ x₂ : X) → decidable (x₁ ≡ x₂)

    𝟚-has-decidable-equality : has-decidable-equality 𝟚
    𝟚-has-decidable-equality ₀ ₀ = inl (refl _)
    𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
    𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
    𝟚-has-decidable-equality ₁ ₁ = inl (refl _)

    not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
    not-zero-is-one ₀ n≢₀ = !𝟘 (₀ ≡ ₁) (n≢₀ (refl _ ))
    not-zero-is-one ₁ _ = refl _

.. The following generalizes `₁-is-not-₀`... (so we could have formulated it first and used it to deduce `₁-is-not-₀`):
    inl-inr-disjoint-images : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x : X} {y : Y} → inl x ≢ inr y
    inl-inr-disjoint-images {𝓤}{𝓥}{X}{Y} inlx≡inry = 𝟙-is-not-𝟘 𝟙≡𝟘
     where
      f : X + Y → 𝓤₀ ̇
      f (inl x) = 𝟙
      f (inr y) = 𝟘

      𝟙≡𝟘 : 𝟙 ≡ 𝟘
      𝟙≡𝟘 = ap f inlx≡inry

    disjunctive-syllogism : {P : 𝓤 ̇} {Q : 𝓥 ̇} → P + Q → ¬ Q → P
    disjunctive-syllogism (inl p) _ = p
    disjunctive-syllogism (inr q) ¬Q = !𝟘 _ (¬Q q)

Predicates, Subsets
---------------------

We need a mechanism for implementing the notion of subsets in Agda.  A typical one is called ``Pred`` (for predicate). More generally, ``Pred A 𝓤`` can be viewed as the type of a property that elements of type ``A`` might satisfy. We write ``P : Pred A 𝓤`` (read "``P`` has type ``Pred A 𝓤``") to represent the subset of elements of ``A`` that satisfy property ``P``.

Here is the definition (which is similar to the one found in the ``Relation/Unary.agda`` file of `Agda standard library`_ ).

::

    Pred : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
    Pred A 𝓥 = A → 𝓥 ̇


The membership relation
~~~~~~~~~~~~~~~~~~~~~~~~~

We introduce notation so that we may indicate that ``x`` "belongs to" a "subset" ``P``, or that ``x`` "has property" ``P``, by writing either ``x ∈ P`` or ``P x`` (cf. ``Relation/Unary.agda`` in the `Agda standard library`_ ).

::

    infix 4 _∈_ _∉_
    _∈_ : {A : 𝓤 ̇} → A → Pred A 𝓦 → 𝓦 ̇
    x ∈ P = P x

    _∉_ : {A : 𝓤 ̇} → A → Pred A 𝓦 → 𝓦 ̇
    x ∉ P = ¬ (x ∈ P)

Subset relations
~~~~~~~~~~~~~~~~~~

The subset relation is then denoted, as usual, with the ``⊆`` symbol (cf. ``Relation/Unary.agda`` in the `Agda standard library`_ ).

::

    infix 4 _⊆_ _⊇_
    _⊆_ : {A : 𝓤 ̇} → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
    P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

    _⊇_ : {A : 𝓤 ̇} → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
    P ⊇ Q = Q ⊆ P

Miscellany
--------------

Finally, we include the following list of "utilities" that will come in handy later.  Most of these are self-explanatory, but we make a few remarks below when we feel there is something worth noting.

::

    _∈∈_ :  {A : 𝓤 ̇} {B : 𝓦 ̇} →  (A  →  B) →  Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
    _∈∈_  f S = (x : _) → f x ∈ S

    Im_⊆_ : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
    Im_⊆_ {A = A} f S = (x : A) → f x ∈ S

    img :  {X : 𝓤 ̇ } {Y : 𝓤 ̇} (f : X → Y) (P : Pred Y 𝓤) → Im f ⊆ P →  X → Σ P
    img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁

    ≡-elim-left : {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇ }
     →            (A₁ , B₁) ≡ (A₂ , B₂)
                  ----------------------
     →                   A₁ ≡ A₂
    ≡-elim-left e = ap pr₁ e

    ≡-elim-right : {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇}
     →             (A₁ , B₁) ≡ (A₂ , B₂)
                  -----------------------
     →                    B₁ ≡ B₂
    ≡-elim-right e = ap pr₂ e

    ≡-×-intro : {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇}
     →           A₁ ≡ A₂  →  B₁ ≡ B₂
              ------------------------
     →          (A₁ , B₁) ≡ (A₂ , B₂)
    ≡-×-intro (refl _ ) (refl _ ) = (refl _ )

    cong-app-pred : ∀{A : 𝓤 ̇}{B₁ B₂ : Pred A 𝓤}
                    (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
                   ------------------------------
     →                         x ∈ B₂
    cong-app-pred x x∈B₁ (refl _ ) = x∈B₁

    cong-pred : {A : 𝓤 ̇}{B : Pred A 𝓤}
                (x y : A) →  x ∈ B  →  x ≡ y
                ----------------------------
     →                       y ∈ B
    cong-pred x .x x∈B (refl _ ) = x∈B


    data Image_∋_ {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
      where
      im : (x : A) → Image f ∋ f x
      eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

    -- image_ : {A : 𝓤 ̇} {B : 𝓦 ̇} → (A → B) → Pred B (𝓤 ⊔ 𝓦)
    -- image f = λ b → ∃ λ a → b ≡ f a

    ImageIsImage : {A : 𝓤 ̇}{B : 𝓦 ̇}
                   (f : A → B) (b : B) (a : A)
     →              b ≡ f a
                  ----------------------------
     →              Image f ∋ b
    ImageIsImage {A = A}{B = B} f b a b≡fa = eq b a b≡fa

N.B. the assertion `Image f ∋ y` must come with a proof, which is of the form `∃a f a = y`, so we have a witness. Thus, the inverse can be "computed" in the following way:

::

    Inv : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B)(b : B) → Image f ∋ b  →  A
    Inv f .(f a) (im a) = a
    Inv f b (eq b a b≡fa) = a

The special case for Set (i.e., `𝓤₀ ̇`) is

::

    inv : {A B : 𝓤₀ ̇}(f : A → B)(b : B) → Image f ∋ b → A
    inv {A} {B} = Inv {𝓤₀}{𝓤₀}{A}{B}

    InvIsInv : {A : 𝓤 ̇} {B : 𝓦 ̇} (f : A → B)
               (b : B) (b∈Imgf : Image f ∋ b)
              ---------------------------------
     →         f (Inv f b b∈Imgf) ≡ b
    InvIsInv f .(f a) (im a) = refl _
    InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹

An epic (or surjective) function from 𝓤 ̇ to 𝓦 ̇ (and the special case for  `𝓤₀ ̇`) is defined as follows.

::

    Epic : {A : 𝓤 ̇} {B : 𝓦 ̇} (g : A → B) →  𝓤 ⊔ 𝓦 ̇
    Epic g = ∀ y → Image g ∋ y

    epic : {A B : 𝓤₀ ̇} (g : A → B) → 𝓤₀ ̇
    epic = Epic {𝓤₀} {𝓤₀}

The (pseudo-)inverse of an epic function is

::

    EpicInv : {A : 𝓤 ̇} {B : 𝓦 ̇ } (f : A → B) → Epic f → B → A
    EpicInv f fEpic b = Inv f b (fEpic b)


Monics (or injective) functions are defined this way (see also: `left-cancellable` aka `injective` in the `UF-Univalence` module).

::

    monic : {A : 𝓤 ̇} {B : 𝓦 ̇} (g : A → B) → 𝓤 ⊔ 𝓦 ̇
    monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂
    monic₀ : {A B : 𝓤₀ ̇} (g : A → B) → 𝓤₀ ̇
    monic₀ = monic {𝓤₀}{𝓤₀}

    --The (pseudo-)inverse of a monic function
    monic-inv : {A : 𝓤 ̇} {B : 𝓦 ̇} (f : A → B) → monic f
     →           (b : B) → Image f ∋ b → A
    monic-inv f fmonic  = λ b Imf∋b → Inv f b Imf∋b

    --The (psudo-)inverse of a monic is the left inverse.
    monic-inv-is-linv : {A : 𝓤 ̇}{B : 𝓦 ̇}
                        (f : A → B) (fmonic : monic f)(x : A)
                       ----------------------------------------
      →                 (monic-inv f fmonic) (f x) (im x) ≡ x
    monic-inv-is-linv f fmonic x = refl _

Finally, we define bijective functions as follows.

::

    bijective : {A B : 𝓤₀ ̇}(g : A → B) → 𝓤₀ ̇
    bijective g = epic g × monic g

    Bijective : {A : 𝓤 ̇}{B : 𝓦 ̇}(g : A → B) → 𝓤 ⊔ 𝓦 ̇
    Bijective g = Epic g × monic g


Extensionality
------------------

Extensional equality of functions, or :term:`function extensionality`, means that any two point-wise equal functions are equal.  As MHE explains, this is known to be not provable or disprovable in Martin-Löf Type Theory (MLTT).

::

    -- The (psudo-)inverse of an epic is the right inverse.
    EInvIsRInv : funext 𝓦 𝓦 → {A : 𝓤 ̇} {B : 𝓦 ̇} (f : A → B)  (fEpic : Epic f)
     →            f ∘ (EpicInv f fEpic) ≡ 𝑖𝑑 B
    EInvIsRInv fe f fEpic = fe (λ x → InvIsInv f x (fEpic x))


    -------------------------------------------------------
    -- Function extensionality from univalence
    --Ordinary function extensionality
    extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
    extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
     →                f ∼ g   →   f ≡ g

    -- Opposite of function extensionality
    intensionality : ∀ {𝓤 𝓦} {A : 𝓤 ̇} {B : 𝓦 ̇ } {f g : A → B}
     →                f ≡ g  →  (x : A)
                      ------------------
     →                    f x ≡ g x

    intensionality  (refl _ ) _  = refl _

    -- dependent intensionality
    dep-intensionality : ∀ {𝓤 𝓦} {A : 𝓤 ̇} {B : A → 𝓦 ̇ } {f g : ∀(x : A) → B x}
     →                f ≡ g  →  (x : A)
                        ------------------
     →                    f x ≡ g x

    dep-intensionality (refl _ ) _ = refl _

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

    -- module _  {I : 𝓘 ̇}  {X : 𝓤 ̇} {A : I → 𝓥 ̇} (fe : Fun-Ext)  where

    --   ext-lemma :  ( p q : (i : I) → (X → A i) → A i )
    --    →           ( (i : I) (args : X → A i) →  ID (A i) (p i args) (q i args) )
    --    →            p ≡ q
    --   ext-lemma p q H = fe λ x → fe (H x)

------------------

.. include:: hyperlink_references.rst





..
   -- .. -----------------------------------------------------------------------------------------
   --    N.B. The following variations of function extensionality are borrowed (with permission)
   --    from Martin Escardo's UF/HoTT MGS course notes.  We include them here because Martin has
   --    altered their definitions in his latest TypeTopology library, and the revised versions
   --    are not all backward compatible with code based on the versions below.

   --    Here is the definition of **dependent function extensionality**.
   --    ::

   --        dfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
   --        dfunext 𝓤 𝓥 = {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g : Π A} → f ∼ g → f ≡ g

   --    As MHE explains, the above definition says that there exists a map `f ~ g → f ≡ g`, whereas the following says that the canonical map `happly` in the other direction is an equivalence.

   --    ::
   --        happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → f ≡ g → f ∼ g
   --        happly f g p x = ap (λ - → - x) p

   --        hfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
   --        hfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → is-equiv (happly f g)

   --        hfunext-gives-dfunext : hfunext 𝓤 𝓥 → dfunext 𝓤 𝓥
   --        hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)

   --    As MHE explains, Voevodsky showed that all these notions of function extensionality are logically equivalent to saying that products of singletons are singletons.

   --    ::
   --        vvfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
   --        vvfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
   --         →              ((x : X) → is-singleton (A x))
   --                        ------------------------------
   --         →                 is-singleton (Π A)

   -- ::
   --     global-dfunext : 𝓤ω
   --     global-dfunext = ∀ {𝓤 𝓥} → DN-funext 𝓤 𝓥

