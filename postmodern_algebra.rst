.. include:: _static/math_macros.rst

.. role:: cat

.. role:: code

.. _postmodern-algebra:

=======================
Postmodern Algebra [1]_
=======================

Up to now the goal of the :code:`ualib` development has been to remain faithful to the classical presentation of general (universal) algebra.  The motivation for this is so that the library seems natural to working algebraists.  However, there are real advantages to adopting a more modern and category theoretic approach.

In the remaining sections, we redesign the :code:`ualib` implementation to take advantage of the more elegant and more general language of category theory.  The downside is that the resulting definitions and theorem statements may turn out to be hardly recognizable to classical algebraists. 

This section assumes the reader is familiar with basic notions of category theory, as it is presented at categorytheory.gitlab.io_, for example.

---------------------------------

.. _tuple-functors:

Tuple functors
--------------

For :math:`m : ℕ`, the :math:`\mathrm{mtuple}` functor on :cat:`Set` is denoted and defined as follows by its action on

+ **objects**: if :math:`A` is a set, then :math:`\mathrm{mtuple}(A) := \{(a_0, \dots, a_{m-1}) ∣ a_i : A\}`;

+ **arrows**: if :math:`f : A → B` is a function from the set :math:`A` to the set :math:`B`, then :math:`\mathrm{mtuple} f : \mathrm{mtuple}(A) → \mathrm{mtuple}(B)` is defined for each :math:`(a_0, \dots, a_{m-1})` of type :math:`\mathrm{mtuple}(A)` as follows:

.. math:: \mathrm{mtuple} f (a_0, \dots, a_{m-1}) = (f a_0, \dots, f a_{m-1}),

which inhabits the type :math:`\mathrm{mtuple}(A)`.

Notice that 𝐚 has type :math:`\mathrm{mtuple}(A)` iff we can represent 𝐚 as a function of type :math:`\underline m → A`; that is, iff we can represent the mtuple :math:`(a_0, \dots, a_{m-1})` as a function, 𝐚, where :math:`𝐚(i) = a_i` for each :math:`0 ≤ i < n`. Thus, we have the following equivalence of types: :math:`\mathrm{mtuple}(A) ≅ \underline m \to A`.

Let :math:`𝐦 = (m_0, \dots, m_{n-1}) : \mathrm{ntuple}(ℕ)`.

The :math:`\mathbf{mtuple}` functor is defined as follows by its action on

+ **objects**: if :math:`A` is a set, then

  .. math:: \mathbf{mtuple}(A) = \{((a_{00}, \dots, a_{0(m_1-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(m_n-1)})) ∣ a_{ij} : A\}.

  (We may write :math:`𝐚_i` in place of :math:`(a_{i0}, \dots, a_{i(k-1)})`, if :math:`k` is clear from context.)

+ **arrows**: if :math:`f` is a function from :math:`A` to :math:`B`, then :math:`\mathbf{mtuple} f :  \mathbf{mtuple}(A) →  \mathbf{mtuple}(B)` is defined for each :math:`(𝐚_1, \dots, 𝐚_n)` in :math:`\mathbf{mtuple}(A)` as follows:

  .. math:: \mathbf{mtuple} f (𝐚_1, \dots, 𝐚_n) &= (\mathrm{m_1tuple}f 𝐚_1, \dots, \mathrm{m_ntuple} f 𝐚_n) \\
                                            &= ((f a_{11}, \dots, f a_{1m_1}), \dots, (f a_{n1}, \dots, f a_{nm_n})).

Notice that :math:`𝐚_i` has type :math:`\mathrm{m_ituple}(A)` iff it can be represented as a function of type :math:`\underline{m_i} → A`; that is, iff the tuple :math:`(a_{i0}, \dots, a_{i(m_i-1)})` is (the graph of) the function defined by :math:`𝐚_i(j) = a_{ij}` for each :math:`0 ≤ j < m_i`.

Thus, if :math:`𝐦 = (m_0, \dots, m_{n-1}) : \mathrm{ntuple}(ℕ)`, then :math:`\mathbf{mtuple}(A)` is the *dependent function type*,

.. math:: \prod_{i : \underline n} (\underline{m_i} → A).

-------------------------------------

.. _general-composition:

General composition
-------------------

fork and eval
~~~~~~~~~~~~~

.. .. raw:: latex

..    \begin{prooftree}
..    \AXM{\exists x A(x)}
..    \AXM{}
..    \RLM{1}
..    \UIM{A(y)}
..    \noLine
..    \UIM{\vdots}
..    \noLine
..    \UIM{B}
..    \RLM{1}
..    \BIM{B}
..    \end{prooftree}

.. .. include:: latex_images/first_order_logic.8.tex

Define the operation :math:`\mathrm{fork} : (A \to B)\to (A \to C) \to A \to (B \times C)` as follows: 

  if :math:`f  : A \to B`, :math:`g  : A \to C`, and :math:`a  : A`, then :math:`\mathrm{fork} (f) (g) (a) = (f (a), g (a)) : B \times C`.

(A more standard definition of fork might take the domain to be :math:`(A \to B)\times (A \to C)`, whereas we have described a "curried" version in order to support partial application.)

The fork function generalizes easily to dependent function types. Let :math:`A` be a type and for each :math:`a  : A` let :math:`B_a` and
:math:`C_a` be types. Define the *dependent fork*, denoted by

.. math:: \mathbf{fork} : \prod_{a : A} B_a\to \prod_{a : A} C_a \to \prod_{a : A}(B_a \times C_a),

as follows: if :math:`f  : \prod_{a : A} B_a`, :math:`g  : \prod_{a : A} C_a`, and :math:`a  : A`, then :math:`\mathbf{fork} (f) (g) (a) = (f (a), g (a)) : B_a × C_a`. Since we use a curried definition, we can partially apply :math:`\mathbf{fork}` and obtain the expected typing relations, viz.,

.. math:: \mathbf{fork} (f)  : \prod_{a:A} C_a \to \prod_{a:A} (B_a \times C_a)\quad \text{ and } \quad \mathbf{fork} (f) (g)  : \prod_{a:A} (B_a \times C_a).

Next, let :math:`\mathbf{eval}  : (A → B) × A` denote function application; that is, :math:`\mathbf{eval} (f, a) = f a`, if :math:`f  : A → B` and :math:`a : A`. Thus, if :math:`h  : \prod_{a : A}(C_a → D)`, :math:`k  : \prod_{a : A} C_a`, and :math:`a : A`, then

.. math:: \mathbf{fork} (h)(k)(a) = (h(a), k(a))  : (C_a → D) × C_a, \text{ and }

.. math:: \mathbf{eval} ∘ \mathbf{fork} (h)(k)(a) = h(a)k(a) : D.

Example: :cat:`Set`
~~~~~~~~~~~~~~~~~~~

In universal algebra we deal mainly with *finitary operations on sets*.

By an :math:`n`-**ary operation** on the set :math:`A` we mean a function :math:`f : A^n → A`, that takes :math:`n` elements of type :math:`A` and returns an element of type :math:`A`. [2]_

By identifying the :math:`\mathrm{ntuple}` type with the function type :math:`\underline n →  A`, we may represent the type of :math:`n`-ary operations on :math:`A` by :math:`(\underline n → A) → A`.

Evaluating such an :math:`f : (\underline n → A) → A` at a tuple :math:`a : \underline n → A` is simply function application, expressed by the usual rule (sometimes called "implication elimination" or "modus ponens").

.. raw:: latex

   \begin{prooftree}
   \AxiomC{$f : (\underline n → A) → A$}
   \AxiomC{$a : \underline n → A$}
   \RightLabel{$_{(→ \mathrm{E})}$}
   \BinaryInfC{$f a : A$}
   \end{prooftree}

If we let :math:`a_i` denote the value of :math:`a` at :math:`i`, and if we identify :math:`a` with it's graph (the tuple :math:`(a_0, \dots, a_{n-1})`), then
:math:`f a = f(a_0, \dots, a_{n-1})`.

Denote and define the collection of all finitary operations on :math:`A` by

.. math:: \mathrm{Op}(A) = \bigcup_{n<\omega} (A^n \to A)\cong \bigcup_{n<\omega} ((\underline{n} \to A) \to A).

We will now try to develop a formulation of *general function composition* that is more elegant and computationally practical than the standard formulation, but first, let us first briefly review the standard formulation of function composition.

Let :math:`f  : (\underline{n} → A) → A` be an :math:`n`-ary operation on :math:`A`, and suppose for each :math:`0≤ i < n` we have an operation :math:`g_i : (\underline{k_i} → A) → A`. Then we define :math:`f ∘ (g_0, \dots, g_{n-1})` in the following standard way: for each

.. math:: ((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})) : A^{k_0} × \cdots × A^{k_{n-1}},

.. math:: f∘ & (g_0, \dots, g_{n-1}))((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\\
                 &= f(g_0(a_{00}, \dots, a_{0(k_0-1)}), \dots, g_{n-1}(a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})).

Not only is this notation tedious, but also it lends itself poorly to computation. To improve upon it, let us first consider the ntuple :math:`(g_0, \dots, g_{n-1})`. This is an ntuple of operations from :math:`\mathrm{Op}(A)`.

If we denote by :math:`g` the function from :math:`\underline n` to :math:`\mathrm{Op}(A)` given by :math:`g i = g_i` for each :math:`0 ≤ i < n`, then :math:`g` inhabits the following dependent function type:

.. math:: \prod_{i : \underline n}  ((\underline{k_i} → A) → A).

Next, define the function :math:`a` as follows: :math:`a i  : \underline{k_i} → A` for each :math:`0≤ i < n` and for each :math:`j : \underline{k_i}`, :math:`a i j = a_{ij}`. Then the ntuple of arguments in the expression above can be identified with the tuple :math:`a = (a 0, \dots, a (n-1))` of functions.

Thus :math:`a` has dependent function type :math:`\prod_{i : \underline n} (\underline{k_i} → A)`, and for each :math:`i : \underline n`, we have :math:`a i j = a_{ij}`.

Now, looking back at :numref:`Section %s <general-composition>`, where we defined the fork and eval functions, we can see how to perform general composition using dependent types.

If :math:`g  : \prod_{i : \underline n} ((\underline{k_i} → A) → A)`, and :math:`a  : \prod_{i : \underline n}(\underline{k_i} → A)`, then

.. math:: \mathbf{fork} (g) (a) (i) = (g(i), a(i)) : ((\underline{k_i} → A) → A) × (\underline{k_i} → A)

and :math:`\mathbf{eval} (\mathbf{fork} (g) (a) (i)) = g(i) a(i)` has type :math:`A`.

Observe that the codomain :math:`A` does not depend on :math:`i`, so the types :math:`\prod_{i : \underline n} A` and :math:`\underline n → A` are equivalent. Therefore, :math:`\mathbf{eval} ∘ \mathbf{fork} (g) (a)` has type :math:`\underline n → A`.

On the other hand, we have

.. math:: \mathbf{eval} ∘ \mathbf{fork} (g) : \prod_{i : \underline n}  (\underline{k_i} → A) → (\underline n → A).

Thus, if we take an :math:`n`-ary operation, :math:`f : (\underline n → A) → A`, and an :math:`n`-tuple of operations, :math:`g : \prod_{i : \underline n} ((\underline{k_i} → A) → A)`, then we can *define* the **composition of** :math:`f` **with** :math:`g` as follows:

.. math:: f [g] := f ∘ (\mathbf{eval} ∘ \mathbf{fork}(g)) : \prod_{i : \underline n}(\underline{k_i} → A) → A.

Indeed, if :math:`a  : \prod_{i : \underline n}(\underline{k_i} → A)`, then :math:`\mathbf{eval} ∘ \mathbf{fork}(g)(a)` has type :math:`\underline n → A`, which is the domain type of :math:`f`; therefore, :math:`f (\mathbf{eval} ∘ \mathbf{fork}(g) (a))` has type :math:`A`, as desired.

----------------------------------------------------

.. index:: ! F-algebra, group, Set, Grp

.. _f-algebra:

F-algebras
----------

Let :math:`F` be an endofunctor on the category :cat:`Set`.

We define an **F-algebra** to be a structure :math:`𝔸 = ⟨A, f⟩`, where :math:`f : F A → A`.

Example: :cat:`Grp`
~~~~~~~~~~~~~~~~~~~

A **group** is an :math:`\FGrp`-algebra where :math:`\FGrp A = 1 + A + A × A`.

  A definition of a group that is closer to the standard one is the following:

  The *signature* of a group has three operation symbols, :math:`(e, \ ^{-1}, ∘)`.

   + :math:`e` is a nullary operation symbol (the "identity");
   + :math:`\ ^{-1}` is a unary operation symbol (the "inverse");
   + :math:`∘` is a binary operation symbol ("multiplication"). 

  Thus, a group is an algebraic structure, :math:`𝔸 = ⟨A, e, \ ^{-1}, ∘⟩`, where

   + :math:`e : A`;
   + :math:`^{-1} : A → A`;
   + :math:`∘ : A × A → A`.

  If we were to adopt Church's more precise :math:`λ` syntax, we could denote a group like this

  .. math:: 𝔸 = ⟨A, e, λ x . x^{-1}, λ x . λ y . x ∘ y⟩,

  and then the arity of each operation symbol could be read off immediately!

  To translate this into the language of F-algebras, observe that an element of the coproduct :math:`\FGrp A` has one of three forms,

   + :math:`ι_0 1 : 1`, the identity element of the group;
   + :math:`ι₁ x : A`, an arbitrary element of the group's universe;
   + :math:`ι₂ (x, y) : A × A`, an arbitrary pair of elements of the group's universe.

  So, we define and denote the group operations with a single symbol :math:`f : F A → A`, which acts on elements of the coproduct by pattern matching as follows:

   + :math:`f\ ι_0 1 = e`, the identity element of the group;
   + :math:`f\ ι₁ x = x^{-1}`, the group's inverse operation;
   + :math:`f\ ι₂ (x,y) = x\circ y`, the group's binary operation.

  In `Lean`_, the :code:`Grp` type could be implementation like this:

  .. code-block:: lean

     def f : 1 + ℕ + (ℕ × ℕ) → ℕ
     | ι₀ 1   := e
     | ι₁ x   := x⁻¹
     | ι₂ x y := x ∘ y

  .. code-block:: lean

      namespace hidden
      -- BEGIN
      variables {X Y Z : Type}
  
      def comp (f : Y → Z) (g : X → Y) : X → Z :=
      λx, f (g x)
  
      infixr  ` ∘ ` := comp
  
      def id (x : X) : X :=
      x
      -- END
      end hidden
  
.. index:: homomorphism
.. index:: ! group homomorphism
.. index:: ! f-algebra homomorphism

.. _f-algebra-homomorphism:

F-algebra homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~

Let :math:`𝔸 = ⟨A, f⟩` and :math:`𝔹 = ⟨B, g⟩` be two groups (i.e., :math:`\FGrp`-algebras).

A **homomorphism** from :math:`𝔸` to :math:`𝔹`, denoted by :math:`h : 𝔸 → 𝔹`, is a function :math:`h : A → B` that satisfies the following identity:

  .. math:: h ∘ f = g ∘ \FGrp h

To make sense of this identity, we must know how the functor :math:`\FGrp` acts on arrows (i.e., homomorphisms, like :math:`h`). It does so as follows:

  + :math:`(\mathrm F_{\mathbf{Grp}} h) (ι_0 1) = h(e)`;
  + :math:`(\mathrm F_{\mathbf{Grp}} h) (ι_1 x) = (h(x))^{-1}`;
  + :math:`(\mathrm F_{\mathbf{Grp}} h) (ι_2 (x,y)) = h(x) ∘ h(y)`.

Equivalently,

  + :math:`h ∘ f (ι_0 1) = h (e)` and :math:`g ∘ \FGrp h (ι_0 1) = g (h(e))`;
  + :math:`h \circ f (ι₁ x) = h (x^{-1})` and :math:`g ∘ \FGrp h (ι₁ x) = g (ι₁ h(x)) = (h(x))^{-1}`;
  + :math:`h \circ f (ι₂ (x,y)) = h (x ∘ y)` and :math:`g ∘ \FGrp h (ι₂ (x,y)) = g (ι₂ (h(x), h(y))) = h(x) ∘ h(y)`.

So, in this case, the indentity :math:`h ∘ f = g ∘ \FGrp h` reduces to

  + :math:`h (eᴬ) = g ( h(e) )`;
  + :math:`h (x^{-1_A}) = ( h(x) )^{-1_B}`;
  + :math:`h (x ∘ᴬ y) = h(x) ∘ᴮ h(y)`,

which are precisely the conditions we would normally verify when checking that :math:`h` is a group homomorphism.

--------------------

.. .. math:: \newcommand\hom{\operatorname{Hom}} \newcommand\hom{\operatorname{Hom}} \newcommand\epi{\operatorname{Epi}} \newcommand\aut{\operatorname{Aut}} \newcommand\mono{\operatorname{Mono}} \newcommand\Af{\ensuremath{\langle A, f \rangle}} \newcommand{\FGrp}{F_{\mathbf{Grp}}} \newcommand{\Sg}{\mathsf{Sg}}

.. role:: cat

.. role:: code

.. _observations-categorically:

Observations, categorically
---------------------------

.. todo:: rewrite this section (it's still based on the classical treatment)


Let us revisit the list of observations we made (in classical notation) above in :numref:`Section %s <basic-facts>`.

Throught this section,

+ :math:`F` is an endofunctor on **Set**;
+ :math:`𝔸 = ⟨A, f^{𝔸}⟩, \ 𝔹 = ⟨B, f^{𝔹}⟩, \ 𝐂 = ⟨C, f^{𝐂}⟩\ ` are :ref:`F-algebras <f-algebra>`.

Suppose :math:`F` yields :math:`m` operation symbols and :math:`k_i` is the arity of the :math:`i`-th symbol:

.. math:: F A : ∐_{i=0}^{m-1}(\underline{k_i} → A) \quad \text{ and } \quad F B : ∐_{i=0}^{m-1}(\underline{k_i} → B).

Let :math:`g, h : \hom(𝔸, 𝔹)` be :ref:`F-algebra homomorphisms <f-algebra-homomorphism>` from 𝔸 to 𝔹:

  :math:`g, h : A → B` are set maps satisfying

  .. math:: g ∘ f^{𝔸} = f^{𝔹} ∘ F g \quad \text{ and } \quad h ∘ f^{𝔸} = f^{𝔹} ∘ F h.

.. index:: ! equalizer

The **equalizer** of :math:`g` and :math:`h` is the set

.. math:: E(g,h) = \{ a : A ∣ g(a) = h(a) \}.


.. _obs1cat:

.. proof:observation::

   :math:`E(g,h)` is a subuniverse of 𝔸.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*
      
      Fix arbitrary :math:`0≤ i< m` and :math:`a : \underline{k_i} → E(g,h)`.

      We show that :math:`g (fᴬ (ι_i a)) = h (fᴬ (ι_i a))`, as this shows that :math:`E(g, h)` is closed under the i-th operation of :math:`⟨A, fᴬ⟩`.

      But this is trivial since, by definition of an :ref:`F-algebra homomorphism <f-algebra-homomorphism>`, we have

      .. math:: (g ∘ fᴬ)(ι_i a) = (fᴮ ∘ F g)(ι_i a) = (fᴮ ∘ F h)(ι_i a) = (h ∘ fᴬ)(ι_i a).
    
.. _obs2cat:

.. proof:observation::

   If the set :math:`X ⊆ A` generates 𝔸 and :math:`g|_X = h|_X`, then :math:`g = h`.

   .. container:: toggle
    
      .. container:: header
  
         *Proof*

      Suppose the subset :math:`X ⊆ A` generates :math:`⟨A, fᴬ⟩` and suppose :math:`g|_X = h|_X`.
 
      Fix an arbitrary :math:`a : A`. We show :math:`g(a) = h(a)`.
 
      Since :math:`X` generates 𝔸, there exists a term :math:`t` and a tuple :math:`x : ρt → X` of generators such that :math:`a = tᴬ x`.
 
      Therefore, since :math:`F g = F h` on :math:`X`, we have
    
      .. math:: g(a) = g(tᴬ x) = (tᴮ ∘ F g)(x) = (tᴮ ∘ F h)(x) = h(tᴬ x) = h(a).
    
.. _obs3cat:

.. proof:observation::

   If :math:`A, B` are finite and :math:`X` generates 𝔸, then :math:`|\hom(𝔸, 𝔹)| ≤ |B|^{|X|}`.

   .. container:: toggle
    
      .. container:: header
    
         *Proof*

      By :ref:`obs 2 <obs2cat>`, a homomorphism is uniquely determined by its restriction to a generating set.

      If :math:`X` generates 𝔸, then since there are exactly :math:`|B|^{|X|}` functions from :math:`X` to :math:`B` we have :math:`|\hom(𝔸, 𝔹)| ≤ |B|^{|X|}`.
    
.. _obs4cat:

.. proof:observation::

   If :math:`g : \epi (𝔸, 𝔹)` and :math:`h : \hom (𝔸, 𝐂)` satisfy :math:`\ker g ⊆ \ker h`, then

   .. math:: ∃ k ∈ \hom(𝔹, 𝐂)\ . \ h = k ∘ g.
    
   .. container:: toggle
    
      .. container:: header
    
         *Proof*

      We define :math:`k ∈ \hom(𝔹, 𝐂)` constructively, as follows:

      Fix :math:`b : B`.

      Since :math:`g` is surjective, the set :math:`g^{-1}\{b\} ⊆ A` is nonempty, and since :math:`\ker g ⊆ \ker h`, we see that every element of :math:`g^{-1}\{b\}` is mapped by :math:`h` to a single element of :math:`C`.

      Label this element :math:`c_b`. That is, :math:`h(a) = c_b`, for all :math:`a : g^{-1}\{b\}`.
   
      We define :math:`k(b) = c_b`. Since :math:`b` was arbitrary, :math:`k` is defined on all of :math:`B` in this way.
   
      Now it's easy to see that :math:`k g = h` by construction.
   
      Indeed, for each :math:`a ∈ A`, we have :math:`a ∈ g^{-1}\{g(a)\}`, so :math:`k(g(a)) = h(a)` by definition.
   
      To see that :math:`k` is a homomorphism, let there be :math:`m` operation symbols and let :math:`0≤ i< m` be arbitrary.
   
      Fix :math:`b : \underline{k_i} → B`.
   
      Since :math:`g` is surjective, for each :math:`i : \underline{k_i}`, the subset :math:`g^{-1}\{b(i)\}⊆ A` is nonempty and is mapped by :math:`h` to a single point of :math:`C` (since :math:`\ker g ⊆ \ker h`.
   
      Label this point :math:`c_i` and define :math:`c : \underline{k_i} → C` by :math:`c(i) = c_i`.
   
      We want to show :math:`(f^C ∘ F k) (b) = (k ∘ f^B)(b).`
   
      The left hand side is :math:`f^C c`, which is equal to :math:`(h ∘ fᴬ)(a)` for some :math:`a : \underline{k_i} → A`, since :math:`h` is a homomorphism.
   
      Therefore,
   
      .. math:: (f^C ∘ F k) (b) = (h ∘ f^A) (a) = (k ∘ g ∘ f^A)(a) = (k ∘ f^B ∘ F g)(a) = (k ∘ f^B)(b).
 
.. _obs5cat:

.. proof:observation::

   Let :math:`S = (F, ρ)` be a signature each :math:`f ∈ F` an :math:`(ρf)`-ary operation symbol.
 
   Define :math:`F_0 := \operatorname{Proj}(A)` and for all :math:`n > 0` in :math:`ω` let
 
   .. math:: F_{n+1} := F_n ∪ \{ f g ∣ f ∈ F, g : ρf → (F_n ∩ (ρg → A)) \}.
 
   Then :math:`\mathrm{Clo}^{𝔸}(F) = ⋃_n F_n`.
 
.. _obs6cat:

.. proof:observation::

   Let :math:`f` be a similarity type.
 
    (a) :math:`𝕋_ρ (X)` is generated by :math:`X`.
 
    (b) For every algebra :math:`𝔸 = ⟨A, F⟩` of type :math:`ρ` and every function :math:`h : X → A` there is a unique homomorphism :math:`g : 𝕋_ρ (X) → ⟨A, fᴬ⟩` such that :math:`g|_X = h`.
 
   .. container:: toggle
    
      .. container:: header
     
         *Proof*
     
      The definition of :math:`𝕋_ρ (X)` exactly parallels the construction in Theorem 1.14 :cite:`Bergman:2012`. That accounts for the first item.
     
      For b, define :math:`g(t)` by induction on :math:`|t|`.
     
      Suppose :math:`|t| = 0`.  Then :math:`t ∈ X ∪ \mathcal F_0`.
     
      If :math:`t ∈ X` then define :math:`g(t) = h(t)`. For :math:`t ∈ \mathcal F_0`, :math:`g(t) = t^{𝔸}`.
     
      Note that since :math:`𝔸 = ⟨A, fᴬ⟩` is an algebra of type :math:`f` and :math:`t` is a nullary operation symbol, :math:`t^{𝔸}` is defined.
     
      For the inductive step, let :math:`|t| = n + 1`. Then :math:`t = f(s_1, \dots, s_k)` for some :math:`f ∈ \mathcal F_k` and :math:`s_1, \dots, s_k` each of height at most :math:`n`. We define :math:`g(t) = f^{𝔸}(g(s_1), \dots, g(s_k))`.
     
      By its very definition, :math:`g` is a homomorphism. Finally, the uniqueness of :math:`g` follows from Exercise 1.16.6 in :cite:`Bergman:2012`.
 
.. _obs7cat:

.. proof:observation::

   Let :math:`𝔸 = ⟨A, f^{𝔸}⟩` and :math:`𝔹 = ⟨B, f^{𝔹}⟩` be algebras of type :math:`ρ`.
 
    (a) For every :math:`n`-ary term :math:`t` and homomorphism :math:`g : 𝔸 → 𝔹`, :math:`g(t^{𝔸}(a_1,\dots, a_n)) = t^{𝔹}(g(a_1),\dots, g(a_n))`.

    (b) For every term :math:`t ∈ T_ρ(X_ω)` and every :math:`θ ∈ \mathrm{Con}⟨A, fᴬ⟩`, :math:`𝔸 ≡_θ 𝔹` implies :math:`t^{𝔸}(𝔸) ≡_θ t^{𝔸}(𝔹)`.

    (c) For every subset :math:`Y` of :math:`A`,

        .. math:: \Sg^{𝔸}(Y) = \{ t^{𝔸}(a_1, \dots, a_n) : t ∈ Tᵨ (X_n), a_i ∈ Y, i ≤ n < ω\}.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*
    
      The first statement is an easy induction on :math:`|t|`.
    
      The second statement follows from the first by taking :math:`⟨B, f^{𝔹}⟩ = ⟨A, f^{𝔸}⟩/θ` and :math:`g` the canonical homomorphism.
    
      For the third statement, again by induction on the height of :math:`t`, every subalgebra must be closed under the action of :math:`t^{𝔸}`.
    
      Thus the right-hand side is contained in the left. On the other hand, the right-hand side is clearly a subalgebra containing the elements of :math:`Y` (take :math:`t = x_1`) from which the reverse inclusion follows.

-----------------------------

.. rubric:: Footnotes

.. [1]
   The tile of this chapter, "Postmodern Algebra," is borrowed from Johnathan Smith and Anna Romanowska, whose algebra textbook has the same title.

.. [2]
   Using the tuple constructor described in :numref:`Section %s <tuple-functors>`, we could also represent such an operation as :math:`f : \mathrm{ntuple} A → A`, but we prefer to reserve ntuple for instances in which it acts as a functor.

.. _categorytheory.gitlab.io: https://categorytheory.gitlab.io

.. _Lean: https://leanprover.github.io/
