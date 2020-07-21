.. FILE: prelude.lagda.rst
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 21 Apr 2020
.. UPDATE: 8 Jul 2020
.. REF: Some parts of this file are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
.. SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ 
.. Throughout, MHE = Martin Hötzel Escardo.

.. _agda preliminaries:

========================
Agda Preliminaries
========================

**Notation**. Some acronyms we use frequently in this chapter are these.

  * :term:`MHE` = `Martin Hötzel Escardo <https://www.cs.bham.ac.uk/~mhe/>`_
  * :term:`MLTT` = `Martin-Löf Type Theory <https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory>`_

----------------------------------------------------

Options and imports
--------------------

All but the most trivial Agda programs begin by setting some options that effect how Agda behaves and importing from existing libraries (e.g., the `Agda Standard Library`_ or, in our case, :term:`MHE`'s `Type Topology`_ library). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, here's the start of the first Agda source file in our library, which we call ``prelude.lagda.rst``.

::

   {-# OPTIONS --without-K --exact-split --safe #-}

This specifies Agda ``OPTIONS`` that we will use throughout the library.

  * ``without-K`` disables `Streicher's K axiom <https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29>`_ ; see also the `section on axiom K <https://agda.readthedocs.io/en/v2.6.1/language/without-k.html>`_ in the `Agda Language Reference`_ manual.

  * ``exact-split`` makes Agda accept only those definitions that behave like so-called *judgmental* or *definitional* equalities.  :term:`MHE` explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the `Pattern matching and equality section <https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality>`_ of the `Agda Tools`_ documentation.

  * ``safe`` ensures that nothing is postulated outright---every non-:term:`MLTT` axiom has to be an explicit assumption (e.g., an argument to a function or module); see also `this section <https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe>`_ of the `Agda Tools`_ documentation and the `Safe Agda section <https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda>`_ of the `Agda Language Reference`_.

Universes
~~~~~~~~~~

We begin the first module of `agda-ualib`_, called ``prelude``, using the Agda directive ``module prelude where``.  We then immediately import the ``Universes`` module from :term:`MHE`'s `Type Topology`_ library.

::

   module prelude where

    open import Universes public

This ``Universes`` module provides, among other things, an elegant notation for type universes that we have fully adopted and we use MHE's notation throughout the agda-ualib_.

:term:`MHE` has authored an outstanding set of notes on `HoTT-UF-in-Agda`_ called `Introduction to Univalent Foundations of Mathematics with Agda`_ . We highly recommend these notes to anyone wanting more details than we provide here about :term:`MLTT` and the Univalent Foundations/HoTT extensions thereof.

Following :term:`MHE`, we refer to universes using capitalized script letters 𝓤,𝓥,𝓦,𝓣.  We add a few more to Martin's list.

::

    variable
      𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓞 𝓠 𝓡 𝓢 𝓧 : Universe

In the ``Universes`` module, :term:`MHE` defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to ``Set 𝓤``, and the latter has type ``Set (lsuc 𝓤)``.

The level ``lzero`` is renamed 𝓤₀, so 𝓤₀ ̇  is an alias for ``Set lzero`` (which, incidentally, corresponds to ``Sort 0`` in Lean_).

Although it is nice and short, we won't show all of the ``Universes`` module here.  Instead, we highlight the few lines of code from :term:`MHE`'s ``Universes.lagda`` file that makes available the notational devices that we just described and will adopt throughout the `agda-ualib`_.

.. proof:agda:: Universes.lagda excerpt

   .. code-block:: agda

      open import Agda.Primitive public
        using (_⊔_)
        renaming (lzero  to  𝓤₀
                ; lsuc   to  _⁺
                ; Level  to  Universe
                ; Setω   to  𝓤ω
                )

      _̇ : (𝓤 : Universe) → _
      𝓤 ̇ = Set 𝓤

      𝓤₁ = 𝓤₀ ⁺
      𝓤₂ = 𝓤₁ ⁺

      _⁺⁺ : Universe → Universe
      𝓤 ⁺⁺ = 𝓤 ⁺ ⁺


Thus, 𝓤 ̇ is simply an alias for ``Set 𝓤``, and we have ``Set 𝓤 : Set (lsuc 𝓤)``.

Finally, ``Set (lsuc lzero)`` is denoted by ``Set 𝓤₀ ⁺`` which (:term:`MHE` and) we denote by ``𝓤₀ ⁺ ̇``.

The following dictionary translates between standard Agda syntax and :term:`MHE`/agda-ualib_ notation.

.. code-block:: agda

   Agda              MHE/agda-ualib
   ====              ==============
   Level             Universe
   lzero             𝓤₀
   𝓤 : Level         𝓤 : Universe
   Set lzero         𝓤₀ ̇
   Set 𝓤             𝓤 ̇
   lsuc lzero        𝓤₀ ⁺
   lsuc 𝓤            𝓤 ⁺
   Set (lsuc lzero)  𝓤₀ ⁺ ̇
   Set (lsuc 𝓤)      𝓤 ⁺ ̇
   Setω              𝓤ω

.. +----------------------+--------------------------+-----------------------------+
   | Agda                 |  :term:`MHE` Notation    | Lean analog                 |
   +======================+==========================+=============================+
   | ``Level``            | ``Universe``             | ``universe``                |
   |  ``lzero``           | ``𝓤₀``                   | ``0 : universe``            |
   | ``Set lzero``        | ``𝓤₀ ̇`` ( = ``Type 𝓤₀``) | ``Sort 0``                  |
   |  ``lsuc lzero``      | ``𝓤₀ ⁺``                 | ``1 : universe``            |
   | ``Set (lsuc lzero)`` | ``𝓤₀ ⁺ ̇``                | ``Sort 1 = Type = Type 0``  |
   +----------------------+--------------------------+-----------------------------+

To justify the introduction of this somewhat nonstandard notation for universe levels, :term:`MHE` points out that the Agda library uses ``Level`` for universes (so what we write as 𝓤 ̇ is written ``Set 𝓤`` in standard Agda), but in univalent mathematics the types in 𝓤 ̇ need not be sets, so the standard Agda notation can be misleading. Furthermore, the standard notation places emphasis on levels rather than universes themselves.

There will be many occasions calling for a type living in the universe that is the least upper bound of two universes, say, 𝓤 ̇ and 𝓥 ̇ . The universe 𝓤 ⊔ 𝓥 ̇ denotes this least upper bound.  Here 𝓤 ⊔ 𝓥 is used to denote the universe level corresponding to the least upper bound of the levels 𝓤 and 𝓥, where the ``_⊔_`` is an Agda primitive designed for precisely this purpose.


Public imports
~~~~~~~~~~~~~~~

Next we import other parts of :term:`MHE`'s `Type Topology`_ library, using the Agda directive ``public``, which means these imports will be available wherever the ``prelude`` module in imported.  We describe some of these imports later, when making use of them, but we don't describe each one in detail. (The interested or confused reader should consult `HoTT-UF-in-Agda`_ to learn more.)

::

    open import Identity-Type renaming (_≡_ to infix 0 _≡_ ;
     refl to 𝓻ℯ𝓯𝓵) public

    pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}

    open import Sigma-Type renaming (_,_ to infixr 50 _,_) public

    open import MGS-MLTT using (_∘_; domain; codomain; transport;
     _≡⟨_⟩_; _∎; pr₁; pr₂; -Σ; 𝕁; Π; ¬; _×_; 𝑖𝑑; _∼_; _+_; 𝟘; 𝟙; 𝟚;
     _⇔_; lr-implication; rl-implication; id; _⁻¹; ap) public

    open import MGS-Equivalences using (is-equiv; inverse;
     invertible) public

    open import MGS-Subsingleton-Theorems using (funext;
     dfunext; is-singleton; is-subsingleton; is-prop; Univalence;
     global-dfunext; univalence-gives-global-dfunext; _●_; _≃_;
     logically-equivalent-subsingletons-are-equivalent;
     Π-is-subsingleton) public

    open import MGS-Powerset renaming (_∈_ to _∈₀_; _⊆_ to _⊆₀_)
     using (𝓟; ∈-is-subsingleton; equiv-to-subsingleton;
     powersets-are-sets'; subset-extensionality') public

    open import MGS-Embeddings using (is-embedding; pr₁-embedding;
     is-set; _↪_; embedding-gives-ap-is-equiv; embeddings-are-lc;
     ×-is-subsingleton) public

    open import MGS-Solved-Exercises using (to-subtype-≡) public


.. We don't have the space (or patience!) to describe each of the imports appearing in ``Preliminaries.agda``. Some of them will come up for discussion in due course. Until then, we refer the reader to the above mentioned documentation, as well as the brief :ref:`axiomk` in the appendix; the latter explains the ``--without-K`` option.

.. The full ``prelude.lagda.rst`` file, which defines other notation and objects we will use throughout the library, appears in the appendix :ref:`preliminaries.agda`. We will describe each of the objects defined therein as they come up in later sections.

----------------------------------------------

Dependent pair type
--------------------

Our preferred notations for the first and second projections of a product are ``∣_∣`` and ``∥_∥``, respectively; however, we will sometimes use the more standard ``pr₁`` and ``pr₂`` for compatibility with other libraries and sometimes for readability.

:Unicode Hints: In agda2-mode_ type ``\|`` and ``\||`` to produce ``∣`` and ``∥``; type ``pr\_1`` and ``pr\_2`` to produce ``pr₁`` and ``pr₂``.

::

    ∣_∣ : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇} → Σ Y → X
    ∣ x , y ∣ = x

    ∥_∥ : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
    ∥ x , y ∥ = y

For the :term:`dependent pair type`, we prefer the notation ``Σ x ꞉ X , y``, which is more pleasing (and more standard in the literature) than Agda's default syntax (``Σ λ(x ꞉ X) → y``), and :term:`MHE` has a useful trick that makes the preferred notation available by making index type explicit.

.. code-block:: agda

    infixr -1 -Σ
    -Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
    -Σ X Y = Σ Y
    syntax -Σ X (λ x → y) = Σ x ꞉ X , y -- type `꞉` as `\:4`

.. warning:: The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression ``Σ x ꞉ X , y`` above is obtained by typing ``\:4`` in agda2-mode_.

:term:`MHE` explains Sigma induction as follows: "To prove that ``A z`` holds for all ``z : Σ Y``, for a given property ``A``, we just prove that we have ``A (x , y)`` for all ``x : X`` and ``y : Y x``.  This is called ``Σ`` induction or ``Σ`` elimination (or ``uncurry``).

.. code-block:: agda

    Σ-induction : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ }{A : Σ Y → 𝓦 ̇ }
     →            ((x : X)(y : Y x) → A (x , y))
                  -------------------------------
     →            ((x , y) : Σ Y) → A (x , y)
    Σ-induction g (x , y) = g x y

    curry : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ }{A : Σ Y → 𝓦 ̇ }
     →      (((x , y) : Σ Y ) → A (x , y))
           ---------------------------------
     →      ((x : X) (y : Y x) → A (x , y))
    curry f x y = f (x , y)

The special case in which the type ``Y`` doesn't depend on ``X`` is of course the usual Cartesian product.

.. code-block:: agda

    infixr 30 _×_
    _×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
    X × Y = Σ x ꞉ X , Y

----------------------------------------

Dependent function type
---------------------------

To make the syntax for ``Π`` conform to the standard notation for "Pi types" (or :term:`dependent function type`), :term:`MHE` uses the same trick as the one used above for "Sigma types."

.. code-block:: agda

    Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
    Π {𝓤} {𝓥} {X} A = (x : X) → A x

    -Π : {𝓤 𝓥 : Universe}(X : 𝓤 ̇ )(Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
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

.. "Composition of identifications. Given two identifications ``p : x ≡ y`` and ``q : y ≡ z``, we can compose them to get an identification ``p ∙ q : x ≡ z``. This can also be seen as transitivity of equality.  Because the type of composition doesn't mention ``p`` and ``q``, we can use the non-dependent version of ``≡``-induction."
    _∙_ : {X : 𝓤 ̇}{s t u : X} → s ≡ t → t ≡ u → s ≡ u
    p ∙ q = transport ( lhs p ≡_ ) q p
    infixl 30 _∙_                    -- NOTATION: type ∙ using ``\.``

    infix  40 _⁻¹
    _⁻¹ : {X : 𝓤 ̇} → {s t : X} → s ≡ t → t ≡ s
    p ⁻¹ = transport (_≡ lhs p) p (refl _) --  (lhs p))

-------------------------------------------------------

Application
------------

An important tool that we use often in Agda proofs is application of a function to an identification ``p : x ≡ x'``. We apply the ``ap`` operator to obtain the identification ``ap f p : f x ≡ f x'`` when given ``p : x ≡ x'`` and ``f : X → Y``.

Since ``ap`` is already defined in :term:`MHE`'s `Type Topolgy` library, we don't redefine it here.  However, we do define some variations of ``ap`` that are sometimes useful.

::

    ap-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              {f g : X → Y} {a b : X}
     →         f ≡ g   →   a ≡ b
             -----------------------
     →            f a ≡ g b

    ap-cong (refl _) (refl _) = refl _

Here is a related tool that we borrow from the ``Relation/Binary/Core.agda`` module of the `Agda standard library`_.

::

    cong-app : {A : 𝓤 ̇ } {B : A → 𝓦 ̇ }
               {f g : (a : A) → B a}
     →          f ≡ g   →   (a : A)
              -----------------------
     →              f a ≡ g a

    cong-app (refl _) a = refl _

----------------------------------------

Function extensionality
------------------------

Extensional equality of functions, or :term:`function extensionality`, means that any two point-wise equal functions are equal.  As :term:`MHE` points out, this is known to be not provable or disprovable in Martin-Löf Type Theory (MLTT).

Nonetheless, we will mainly work with pointwise equality of functions, which :term:`MHE` defines (in `Type Topology`_ ) as follows:

.. code-block:: agda

    _∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇ 
    f ∼ g = ∀ x → f x ≡ g x
    infix 0 _∼_

(The ``_∼_`` relation will be equivalent to equality of functions, once we have the principle of *univalence* at our disposal.)

-------------------------------------------------------

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
    _∈_ : {A : 𝓤 ̇ } → A → Pred A 𝓦 → 𝓦 ̇
    x ∈ P = P x

    _∉_ : {A : 𝓤 ̇ } → A → Pred A 𝓦 → 𝓦 ̇
    x ∉ P = ¬ (x ∈ P)

Subset relations
~~~~~~~~~~~~~~~~~~

The subset relation is then denoted, as usual, with the ``⊆`` symbol (cf. ``Relation/Unary.agda`` in the `Agda standard library`_ ).

::

    infix 4 _⊆_ _⊇_
    _⊆_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
    P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

    _⊇_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
    P ⊇ Q = Q ⊆ P

-------------------------------------------------------

Miscellany
--------------

Finally, we include the following list of "utilities" that will come in handy later.  Most of these are self-explanatory, but we make a few remarks below when we feel there is something worth noting.

::

    _∈∈_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A  →  B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
    _∈∈_ f S = (x : _) → f x ∈ S

    Im_⊆_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
    Im_⊆_ {A = A} f S = (x : A) → f x ∈ S

    img : {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
          (f : X → Y) (P : Pred Y 𝓤)
     →    Im f ⊆ P →  X → Σ P
    img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁

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

    cong-app-pred : ∀{A : 𝓤 ̇ }{B₁ B₂ : Pred A 𝓤}
                    (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
                   ------------------------------
     →                         x ∈ B₂
    cong-app-pred x x∈B₁ (refl _ ) = x∈B₁

    cong-pred : {A : 𝓤 ̇ }{B : Pred A 𝓤}
                (x y : A) →  x ∈ B  →  x ≡ y
                ----------------------------
     →                       y ∈ B
    cong-pred x .x x∈B (refl _ ) = x∈B


    data Image_∋_ {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
      where
      im : (x : A) → Image f ∋ f x
      eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

    -- image_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → Pred B (𝓤 ⊔ 𝓦)
    -- image f = λ b → ∃ λ a → b ≡ f a

    ImageIsImage : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                   (f : A → B) (b : B) (a : A)
     →              b ≡ f a
                  ----------------------------
     →              Image f ∋ b
    ImageIsImage {A = A}{B = B} f b a b≡fa = eq b a b≡fa

N.B. the assertion ``Image f ∋ y`` must come with a proof, which is of the form ``∃a f a = y``, so we have a witness. Thus, the inverse can be "computed" in the following way:

::

    Inv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)(b : B) → Image f ∋ b  →  A
    Inv f .(f a) (im a) = a
    Inv f b (eq b a b≡fa) = a

The special case for Set (i.e., ``𝓤₀ ̇``) is

::

    inv : {A B : 𝓤₀ ̇ }(f : A → B)(b : B) → Image f ∋ b → A
    inv {A} {B} = Inv {𝓤₀}{𝓤₀}{A}{B}

    InvIsInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
               (b : B) (b∈Imgf : Image f ∋ b)
              ---------------------------------
     →         f (Inv f b b∈Imgf) ≡ b
    InvIsInv f .(f a) (im a) = refl _
    InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹

An epic (or surjective) function from 𝓤 ̇ to 𝓦 ̇ (and the special case for  ``𝓤₀ ̇``) is defined as follows.

::

    Epic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) →  𝓤 ⊔ 𝓦 ̇
    Epic g = ∀ y → Image g ∋ y

    epic : {A B : 𝓤₀ ̇ } (g : A → B) → 𝓤₀ ̇
    epic = Epic {𝓤₀} {𝓤₀}

The (pseudo-)inverse of an epic function is

::

    EpicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → Epic f → B → A
    EpicInv f fEpic b = Inv f b (fEpic b)


    -- The (psudo-)inverse of an epic is the right inverse.
    EInvIsRInv : funext 𝓦 𝓦 → {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                 (f : A → B)  (fEpic : Epic f)
                ---------------------------------
     →           f ∘ (EpicInv f fEpic) ≡ 𝑖𝑑 B
    EInvIsRInv fe f fEpic = fe (λ x → InvIsInv f x (fEpic x))



Monics (or injective) functions are defined this way.

::

    monic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) → 𝓤 ⊔ 𝓦 ̇
    monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂
    monic₀ : {A B : 𝓤₀ ̇ } (g : A → B) → 𝓤₀ ̇
    monic₀ = monic {𝓤₀}{𝓤₀}

    --The (pseudo-)inverse of a monic function
    monic-inv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → monic f
     →           (b : B) → Image f ∋ b → A
    monic-inv f fmonic  = λ b Imf∋b → Inv f b Imf∋b

    --The (psudo-)inverse of a monic is the left inverse.
    monic-inv-is-linv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                        (f : A → B) (fmonic : monic f)(x : A)
                       ----------------------------------------
      →                 (monic-inv f fmonic) (f x) (im x) ≡ x
    monic-inv-is-linv f fmonic x = refl _

Finally, we define bijective functions as follows.

::

    bijective : {A B : 𝓤₀ ̇ }(g : A → B) → 𝓤₀ ̇
    bijective g = epic g × monic g

    Bijective : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(g : A → B) → 𝓤 ⊔ 𝓦 ̇
    Bijective g = Epic g × monic g


---------------------------------------------

More extensionality
--------------------

Here we collect miscellaneous definitions and proofs related to extensionality that will come in handy later.

::

    -------------------------------------------------------
    --Function extensionality from univalence

    --Ordinary function extensionality
    extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
    extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
     →                f ∼ g   →   f ≡ g

    --Opposite of function extensionality
    intensionality : ∀ {𝓤 𝓦} {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
     →                f ≡ g  →  (x : A)
                      ------------------
     →                    f x ≡ g x

    intensionality  (refl _ ) _  = refl _

    --Dependent intensionality
    dep-intensionality : ∀ {𝓤 𝓦}{A : 𝓤 ̇ }{B : A → 𝓦 ̇ }
                         {f g : ∀(x : A) → B x}
     →                   f ≡ g  →  (x : A)
                        ------------------
     →                    f x ≡ g x

    dep-intensionality (refl _ ) _ = refl _

    --------------------------------------
    --Dependent function extensionality
    dep-extensionality : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
    dep-extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : A → 𝓦 ̇ }
      {f g : ∀(x : A) → B x} →  f ∼ g  →  f ≡ g

    ∀-extensionality : 𝓤ω
    ∀-extensionality = ∀  {𝓤 𝓥} → extensionality 𝓤 𝓥

    ∀-dep-extensionality : 𝓤ω
    ∀-dep-extensionality = ∀ {𝓤 𝓥} → dep-extensionality 𝓤 𝓥

    extensionality-lemma : {I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                           (p q : (i : I) → (X → A i) → 𝓣 ̇ )
                           (args : X → (Π A))
     →                     p ≡ q
       -------------------------------------------------------------
     → (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

    extensionality-lemma p q args p≡q =
     ap (λ - → λ i → (- i) (λ x → args x i)) p≡q


Unicode Hints
---------------

We assume you are using Emacs in a buffer agda2-mode_ enabled.

  +--------+----------------------+
  | To get | Type                 |
  +--------+----------------------+
  | 𝓘, 𝓙   | ``\MCI``, ``\MCJ``   |
  +--------+----------------------+
  | 𝓤 ̇    | ``\MCU \^.``         |
  +--------+----------------------+
  | 𝓤 ⁺    | ``\MCU \^+``         |
  +--------+----------------------+
  | 𝓤₀     |  ``\MCU\_0``         |
  +--------+----------------------+
  |  ⊔     |  ``\sqcup``          |
  +--------+----------------------+
  | 𝐴, 𝐵   | ``\MiA``, ``\MiB``   |
  +--------+----------------------+
  | 𝑨, 𝑩   | ``\MIA``, ``\MIB``   |
  +--------+----------------------+
  | 𝒜, ℬ   | ``\McA``, ``\McB``   |
  +--------+----------------------+
  | 𝓐, 𝓑   | ``\MCA``, ``\MCB``   |
  +--------+----------------------+
  | t ̇ 𝑨  | ``t \^. \MIA``       |
  +--------+----------------------+
  | 𝑓 ̂ 𝑨  | ``\Mif \^ \MIA``     |
  +--------+----------------------+
  | ≡      | ``\equiv``           |
  +--------+----------------------+
  |  𝓇ℯ𝒻𝓁  | ``\Mcr\Mce\Mcf\Mcl`` |
  +--------+----------------------+
  | ≡⟨ ⟩   | ``\equiv\< \>``      |
  +--------+----------------------+
  | ∎, ■   | ``\qed``, ``\sq``    |
  +--------+----------------------+
  | Σ, Π   | ``\Sigma``, ``\Pi``  |
  +--------+----------------------+
  | 𝕁      | ``\bJ``              |
  +--------+----------------------+
  | ¬, ⁻¹  |  ``\neg``, ``\^-\^1``|
  +--------+----------------------+
  | ×      | ``\times``           |
  +--------+----------------------+
  | 𝑖𝑑     | ``\Mii\Mid``         |
  +--------+----------------------+
  | 𝓟      | ``\MCP``             |
  +--------+----------------------+
  | ↪      | ``\hookrightarrow``  |
  +--------+----------------------+
  | 𝟘, 𝟙   | ``\b0``, ``\b1``     |
  +--------+----------------------+
  | ⇔      | ``\lr2``             |
  +--------+----------------------+
  | ∘, ●   | ``\cdot``, ``\cib``  |
  +--------+----------------------+
  |  ×     | ``\times``           |
  +--------+----------------------+
  | ∥_∥    | ``\||_\||``          |
  +--------+----------------------+
  | ∼,  ≃  | ``\~``, ``\~-``      |
  +--------+----------------------+
  | ∈₀     | ``\in\_0``           |
  +--------+----------------------+
  | ⊆₀     | ``\subseteq\_0``     |
  +--------+----------------------+

.. include:: hyperlink_references.rst

