.. File: glossary.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 8 Dec 2019
.. Updated: 13 Feb 2020
.. Copyright (c) 2019 William DeMeo (see the 𝐿ICENSE file)

.. .. include:: _static/math_macros.rst

.. role:: code

.. highlight:: agda


Glossary: logic and model theory
----------------------------------

Attribution
~~~~~~~~~~~

Sources used when compiling the material in this section include the following:

* `Introduction to Model Theory <https://books.google.cz/books?id=0\_NNAR6ztIUC>`_ by Philipp Rothmaler :cite:`Rothmaler:2000`.

* *Complexity of Infinite-Domain Constraint Satisfaction* by Manuel Bodirsky (to appear)

* `Wikipedia.org <https://en.wikipedia.org/>`_

Background
~~~~~~~~~~

:term:`Model theory <model theory>` is the study of classes of mathematical :term:`structures <structure>` (or :term:`models <model>`) from the perspective of mathematical logic. In particular, the objects of study are models of :term:`theories <theory>` in a formal :term:`language`. Model theory examines semantical elements (meaning and truth) by means of syntactical elements (formulas and proofs) of a language.

Some basic but important facts to keep in mind are these. Every constant symbol is a constant :term:`term`. An :term:`atomic sentence` contains no variables at all. 𝐿anguages without constant symbols have no atomic sentences. Every :term:`language` comes equipped with a countable supply of variables. The cardinality of a language 𝐿 is defined to be ∣𝐿∣ = max {ℵ₀, ∣𝐂 ∪ 𝐅 ∪ 𝐑∣}.

------------------------------

Miscellaneous facts
~~~~~~~~~~~~~~~~~~~~~

.. proof:lemma::

   For a :term:`language` 𝐿 and an 𝐿-:term:`theory` T, the following are equivalent:

     #. T is :term:`complete <complete theory>`;
     #. T is a :term:`maximal 𝐿-theory`;
     #. T is a maximal :term:`consistent` set of :term:`𝐿-sentences <𝐿-sentence>`;
     #. ∀ ℳ ⊧ T, T = Th ℳ;
     #. ∃ ℳ ⊧ T, T = Th ℳ.

.. proof:examples::

   :math:`\mathrm{T}^∞` is the theory of the class of all infinite models of T.

   :math:`\mathrm{T}_=` is the **theory of pure identity**, which is the

   :math:`\mathrm{𝐿}_=`-theory of all sets (regarded as :math:`𝐿_=`-structures).


Glossary
~~~~~~~~~

Here is a list of useful definitions from model theory.

.. glossary::

   α-equivalent
     Two formulas are called **α-equivalent** if one is obtained from the other by renaming bound variables (using variable names that do not clash with existing variable names).

   Agda
     An :term:`intensional`, :term:`predicative` :term:`ITP` supporting :term:`dependent types <dependent type>` and based on Martin 𝐿of type theory; url: https://wiki.portal.chalmers.se/agda/pmwiki.php

   alphabet
     The **alphabet** of the :term:`signature` σ is the collection of symbols in the following list:

       * **logical symbols**
       * **logical connectives**: ¬,  ∧, ∨ (negation, conjunction, disjunction, resp.),
       * **existential quantifier** ∃,
       * **equality** =.
       * **variables** (countably many)
       * **non-logical symbols** from σ (the constant, function, and relation symbols)
       * **parentheses** (, )

   𝖺𝗍
     By :math:`𝖺𝗍_𝐿` (or just 𝖺𝗍 when the context makes :math:`𝐿` clear) we mean the class of all atomic :math:`𝐿`-formulas.

   atomic formula
     An **atomic** :math:`𝐿`**-formula** (or just **atomic formula** when the context makes :math:`𝐿` clear) has one of the following forms:

       * :math:`s = t`, where :math:`s` and :math:`t` are :math:`𝐿`-terms;
       * :math:`R t`, where :math:`R` is a relation symbol in :math:`𝐿` and :math:`t: ρ R → 𝒯`  is a tuple of :math:`𝐿`-terms;

   atomic sentence
     An **atomic** :math:`𝐿`**-sentence** (or just **atomic sentence** when the context makes :math:`𝐿` clear) is either an equation of constant terms or a relational sentence, :math:`R t`, where :math:`t \, i` is a :term:`closed term` for every :math:`i`; in particular,

     * *an atomic sentence contains no variables at all*, and
     * *languages without constant symbols have no atomic sentences*.

   automated theorem prover
     See: https://en.wikipedia.org/wiki/Automated_theorem_proving

   axiom K
     See: https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29

   axiomatizable
     An **axiomatizable** (or **elementary**) class is a class that consists of all structures satisfying a fixed first-order :term:`theory`.

   axiomatization
     See: :term:`equational base`

   β-equivalent
     Two formulas are called **β-equivalent** if one can be obtained from the other using reduction steps defined in the prevailing logical system.

   base
     See: :term:`equational base`

   boolean combination
     𝐿et Σ be a set of formulae.  A **boolean combination** of Σ is obtained by connecting formulae from Σ using only the logical connectives ∨, ∧, and ¬.

     **Remark**. In this definition, we could have allowed → and ↔ among the logical connectives and we could have omitted ∨.

     **TODO**. Decide whether to include ⊤ and ⊥, by themselves, among boolean combinations, since after all ⊤ and ⊥ are logical connectives.

   boolean closure
     The **boolean closure** of Σ is the set of all :term:`boolean combinations` of Σ.

     For example, 𝐪𝐟 denotes the set of all boolean combinations of atomic formulae.

   bound variable
     A variable that is bound by a quantifier is called a **bound variable**.

     For instance, if the "domain of discourse" is the set of natural numbers, then the sentence :math:`∀ x \; (x ≥ 0)` asserts, "every natural number is greater than or equal to zero." The latter is an informal statement that makes no reference to the variable :math:`x`. It is not a statement about a particular variable; it is a statement about all natural numbers. The variable :math:`x` is simply a placeholder, or "dummy variable."  The sentence :math:`∀ x \; (x ≥ 0)` is logically equivalent to the sentence :math:`∀ y \; (y ≥ 0)`.

     A variable that is not bound is called a :term:`free variable`.

   Calculus of Inductive Constructions
     See: https://en.wikipedia.org/wiki/Calculus_of_constructions

   canonical form
     In type theory, a term belonging to some type is said to be in **canonical normal form** (or just **canonical form**) if it is explicitly built up using the constructors of that type. A canonical form is in particular a :term:`normal form` (one not admitting any reductions), but the converse need not hold.

     For example, the terms of type N (a natural numbers type) of canonical form are the numerals ``succ( succ( succ( ... ( succ zero ) ... )))``.

     A type theory is said to enjoy "canonicity" if every term reduces to a canonical form.

     See also: https://ncatlab.org/nlab/show/canonical+form

   categorical
     A :term:`theory` is said to be **categorical** in a given cardinality λ (or just **λ-categorical**) if it has, up to isomorphism, exactly one model of cardinality λ.

     An 𝐿-:term:`theory` is said to be **categorical** if it is categorical in some cardinality λ. We call an 𝐿-theory **totally categorical** if it has infinite models and every two models of the same cardinality (finite or inĥnite) are isomorphic.

   closed literal
     A **closed literal** (or **literal sentence**) is a literal with no :term:`free variables <free variable>`.  We denote by :math:`𝖼𝗅_𝐿` the set of all closed :math:`𝐿`-literals (literal :math:`𝐿`-sentences).

   closed term
     A **closed term** is a term with no free variables.

   compatible
     𝐿et :math:`σ  = (F, ρ)` be an :term:`algebraic signature` and for each :math:`i ∈ 𝐧 := \{0, 1, \dots, n-1\}` let :math:`𝔸_i = ⟨A_i, F^{𝔸_i}⟩` be a σ-algebra. If :math:`𝐀 = ∏_{i:𝐧}𝔸_i` is the product of these algebras, then a relation :math:`R` over 𝐀 with scope σ is called **compatible** with 𝐀 if it is closed under (or "preserved by") the basic operations in :math:`F^𝐀`. In other words, :math:`R` is compatible if the induced algebra :math:`ℝ = ⟨R,F^ℝ⟩` is a subalgebra of :math:`∏_{j:𝐤} 𝔸_{σ(j)}`.

   complete theory
     A 𝐿-theory T is **complete** if for every 𝐿-:term:`sentence` φ ∈ 𝐿₀, either φ ∈ T or ¬φ ∈ T.

   computable
     See: https://pdfs.semanticscholar.org/1364/d8e8763891b84a9383b722d82294ae0a736b.pdf

   consistent
     :math:`Σ` is **consistent** if :math:`Σ^⊢` (the :term:`deductive closure` of Σ) contains no :term:`contradictions <contradiction>`; otherwise, Σ is **inconsistent**.

   constructive
     See: https://plato.stanford.edu/entries/mathematics-constructive/ and https://en.wikipedia.org/wiki/Constructivism_(philosophy_of_mathematics) and https://en.wikipedia.org/wiki/Constructive_proof

   contradiction
     A logical **contradiction** is an 𝐿-sentence of the form φ ∧ ¬ φ.

   Coq
     An :term:`intensional`, :term:`impredicative` :term:`ITP` supporting :term:`dependent types <dependent type>` and based on :term:`CiC`; url: http://coq.inria.fr

   Curry-Howard correspondence
     the correspondence between propositions and types, and proofs and programs; a proposition is identified with the type of its proofs, and a proof is a program of that type.

     (Sometimes the misnomer "Curry-Howard isomorphism" is used to refer to the same concept, but this is silly because the correspondence is not even bijective, since not all types are propositions, and so not all programs are proofs of propositions; e.g., ℕ is not a proposition and 0 is not a proof of ℕ.)

     See also: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

   currying
     See: https://en.wikipedia.org/wiki/Currying

   decidable language
     see :term:`recursive language`

   deductive closure
     Given a :term:`logic`, the **deductive closure** of a set 𝑆 of statements, denoted by :math:`S^⊢`, is the set statements that can be deduced from 𝑆 using the deduction rules of the given logic.

     We call 𝑆 deductively closed provided :math:`S^⊢ ⊆ S`.

     For example, the set of all :term:`true propositions <true proposition>` of a logic is deductively closed. Indeed, if 𝕋 is the set of true propositions and if a proposition p belongs to 𝕋 and if p is ⊢-related to q (i.e., p ⊢ q), then q also belongs to 𝕋.

   definitionally equal
     In :term:`type theory`, two terms with the same :term:`normal form` are called **definitionally equal**.

   Δ(𝖢)
     is the **expansion** of Δ by :term:`new constants symbols <new constant symbol>` :math:`C` (not occuring in Δ), which is defined to be the class of all the :term:`formulas <formula>` obtained from formulas φ ∈ Δ upon substituting (at will) elements from C for variables in φ. ("At will" indicates that Δ ⊆ Δ(C).)

   Δ-part
     If Δ is an arbibtrary class of formulas, then the Δ-**part** of an 𝐿-theory :math:`T` is :math:`T_Δ = (T ∩ Δ)^⊢`.

   dependent function type
     See: :term:`Pi type`

   dependent pair type
     See: :term:`Sigma type`.

   dependent product type
     See: :term:`Sigma type`.

   dependent type
     A **dependent type** is actually a family of types indexed by some parameter. That is, a dependent type provides a *type schema*, which is a collection of types indexed by a set of values. For example, the type ``Fin n`` of finite sets of size ``n`` is a type that *depends* on the value ``n``.

   dependent type theory
     refers to any :term:`type theory` that supports :term:`dependent types <dependent type>`.

     In **dependent type theory**, every term has a computational behavior and may be *reduced* using certain reduction rules (e.g., the α, β, η rules).  The form beyond which a term :math:`t` is irreducible, if such a form exists, is called the :term:`normal form` of :math:`t`. Two terms with the same normal form are called :term:`definitionally equal`.

   elementary class
     See: :term:`axiomatizable`

   elementary map
     If 𝕄 = ⟨M, ...⟩ and ℕ = ⟨N, ...⟩ are 𝐿-structures, then a map f: M → N is called **elementary** if f: 𝕄 :math:`\stackrel{≡}{↪}` ℕ.

   elementarily embeddable
     𝐿et 𝕄 = ⟨M, ...⟩ and ℕ = ⟨N, ...⟩ be 𝐿-structures. We say that 𝕄 is **elementarily embeddable** in ℕ, and we write :math:`𝕄 \stackrel{≡}{↪} ℕ`, if there is an elementary map f: 𝕄 :math:`\stackrel{≡}{↪}` ℕ.

   entailment
     We say that :math:`Σ` **entails** :math:`φ`, and we write :math:`Σ ⊢ φ`, if just in case every model of :math:`Σ` also models :math:`φ`.

     See also: :term:`logical consequence`

   equational base
     An **equational base** (or **base**) for a variety 𝒱 is a set Σ of equations such that 𝒱 = Mod(Σ). We say that 𝛴 is a base for an algebra 𝐀 if Σ is a base for 𝕍(𝐀) (the variety generated by 𝐀).

     𝐿et 𝒦 be a class of algebras and Σ a set of equations, each of signature σ = (F, ρ). Recall,

     .. math:: \mathrm{Th}𝒦 = \{p ≈ q : 𝒦 ⊧ p ≈ q\} \qquad \quad \mathrm{Mod} Σ = \{ 𝐀 : 𝐀 ⊧ Σ\}.

     Classes of the form Mod Σ are called equational classes, and Σ is called an **equational base** or an :term:`axiomatization` of the class.

     Mod Σ is called the class of models of Σ.

     Dually, a set of identities of the form Th 𝒦 is called an **equational theory**.

   eval
     If :math:`A` and :math:`B` are types, then the **eval** (or **function application**) function on :math:`A` and :math:`B` is denoted by :math:`\mathbf{eval}: ((A → B) × A) → B` and defined by :math:`\mathbf{eval} (f, a) = f\, a`, for all :math:`f: A → B` and :math:`a: A`.

   extensional
     An *extensional* definition of a term lists everything that qualifies as something to which that term refers.

     See also: :term:`function extensionality`

   fork
     𝐿et :math:`A` and :math:`D` be types and for each :math:`a: A`, let :math:`C_a` be a type. Then the (dependent) **fork function**, denoted

     .. math:: \mathbf{fork}: ∏_{a:A}(C_a → D) → ∏_{a:A} C_a → ∏_{a:A} (C_a → D) × C_a,

     is defined as follows: for all :math:`h: ∏_{a:A}(C_a → D)` and :math:`k: ∏_{a:A} C_a`,

     .. math:: \mathbf{fork}\, (h)(k): ∏_{a:A}((C_a → D) × C_a),

     and for each :math:`a:A`,

     .. math:: \mathbf{fork}\, (h)(k)(a) = (h\,a, k\,a): (C_a → D) × C_a.

     Thus, :math:`\mathbf{eval} \, \mathbf{fork}\, (h)(k)(a) = (h\, a)(k\, a)` is of type :math:`D`.

   formula
     A **formula** in the :term:`signature` 𝑆, or **𝑆-formula** (or just **formula** when the signature is clear from context) is a member of the set of **𝑆-formulae**, which is defined recursively as follows:

       * if 𝑡 and 𝑠 are 𝑆-:term:`terms <term>`, then 𝑡 = 𝑠 is an 𝑆-formula;
       * if 𝑡 : {0, 1, …, 𝑛-1} → 𝒯 is a tuple of 𝑆-terms and 𝑅 ∈ 𝐑 is an 𝑛-ary relation symbol, then 𝑅 𝑡 is an 𝑆-formula;
       * if φ and ψ are 𝑆-formulae and 𝑥 is a variable, then ¬ φ, φ ∧ ψ, and ∃ 𝑥 φ are 𝑆-formulae, too;
       * if φ can be constructed in finitely many steps from some combination of the three items above, then φ is an 𝑆-formula.

   free variable
     A variable that is not :term:`bound <bound variable>` by a quantifier is called a **free variable**.

     A formula in first-order logic is an assertion about the free variables in the formula.

     For example, if the "domain of discourse" is the set of natural numbers, then the formula :math:`∀ y \; (x ≤ y)` asserts that :math:`x` is less or equal every natural number.

     This is logically equivalent (more precisely, "α-equivalent") to the formula :math:`∀ z \; (x ≤ z)`.

     On the other hand, the formula :math:`\forall y (w \le y)` says that :math:`w` is less than or equal to every natural number. This is an entirely different statement: it says something about :math:`w`, rather than :math:`x`. So renaming a *free* variable changes the meaning of a formula.

   function extensionality
     the principle that takes two functions :math:`f : X → Y` and :math:`g : X → Y` to be equal just in case :math:`f(x) = g(x)` holds for all :math:`x : X`; such functions are sometimes called "𝐿eibniz equal."

   functional programming
     See: https://en.wikipedia.org/wiki/Functional_programming

   implication elimination
     See, e.g., the `section on implication <https://leanprover.github.io/logic_and_proof/propositional_logic.html#implication>`_ in the `Logic and Proof`_ book.

   implicit arguments
     See: sections `Implicit arguments`_ and `More on implicit arguments`_ of `TPL`_.

   impredicative
     A self-referencing definition is called **impredicative**. A definition is said to be impredicative if it invokes (mentions or quantifies over) the set being defined, or (more commonly) another set which contains the thing being defined.

   inductive set
     A subset :math:`I` of a :term:`preorder` :math:`X` is called **inductive** if :math:`⋁_X D ∈ I` for every directed subset :math:`D ⊆ X` contained in :math:`I`. That is, if :math:`D ⊆ I`, and if every finite subset of :math:`D` has an upper bound in :math:`D`, then :math:`D` as a least upper bound in :math:`I`.

   inductive type
     A type is called **inductive** or **inductively defined** if... (**Todo**: fill in definition)

   intensional
     An **intensional** definition of a term specifies necessary and sufficient conditions that the term satisfies. In the case of nouns, this is equivalent to specifying all the properties that an object must have in order to be something to which the term refers.

   interactive theorem prover
     See: :term:`proof assistant`

   𝐿
     see :term:`language`

   𝐿₀
     denotes the set all sentences in the language 𝐿. We call 𝐿₀ the set of "𝐿-sentences".

   𝐿(𝐶)
     𝐿et 𝐿 be a :term:`language` and 𝐶 a collection of :term:`new constant symbols <new constant symbol>`. We denote by 𝐿(𝐶) the **expansion** of 𝐿, which is defined to be the (uniquely determined) language of :term:`signature` (𝐂 ∪ 𝐶, 𝐅, 𝐑, ρ).

   𝐿(𝑆)
     The **language** of the signature 𝑆 is denoted by 𝐿(𝑆) (or just 𝐿 if 𝑆 is clear from context) and defined to be the set of all :term:`𝑆-formulas <𝑆-formula>`.

   𝐿(𝑆)-structure
     See: :term:`𝑆-structure`

   𝐿-sentence
     see :term:`sentence` and :term:`𝐿₀`

   lambda calculus
     See: https://en.wikipedia.org/wiki/𝐿ambda_calculus

   language
     The **language** of the :term:`signature` 𝑆, denoted by 𝐿(𝑆) (or just 𝐿 if 𝑆 is clear from context) is the set of all :term:`𝑆-formulae <formula>`.

     Every language 𝐿 comes equipped with a countable supply of variables, and the **cardinality** of the language 𝐿 is ∣𝐿∣ = max {ℵ₀, ∣𝐂 ∪ 𝐅 ∪ 𝐑∣}.

   law of the excluded middle
     This is an axiom of classical logic asserting that for all propositions 𝑃 either ¬ 𝑃 or 𝑃 holds.

   Lean
     An :term:`extensional`, :term:`impredicative` :term:`ITP` supporting :term:`dependent types <dependent type>` and based on :term:`CiC`; url: https://leanprover.github.io/.

   Leibniz equal
     See: :term:`function extensionality`

   literal formula
     An 𝐿-**literal formula** (or just **literal** if 𝐿 is clear from context) is an :term:`atomic <atomic formula>` or negated atomic 𝐿-formula.

     We denote by :math:`𝗅𝗍_𝐿` the set of all 𝐿-literals; that is, :math:`𝖺𝗍_𝐿 ∪ \{¬ φ : φ ∈ 𝖺𝗍_𝐿\}`;

   logic
     A **logic** is a :term:`language` (set of formulae) along with an associated set of :term:`inference rules <inference rule>`.

   logical consequence
     The **logical consequence** (or **entailment**) relation, denoted by ⊢, is a binary relation on the set of all statements in a language; we write (φ, ψ) ∈ ⊢, or equivalently, φ ⊢ ψ holds, and we say "φ entails ψ" or "ψ is a logical consequence of φ", precisely when the statement ψ can be deduced from the statement φ.

     See also: :term:`entailment`

   logically equivalent
     Propositions P and Q are **logically equivalent** provided P implies Q and Q implies P.

   :math:`𝗅𝗍_{𝐿(𝑀)}`
     is the set of all atomic and negated atomic :math:`𝐿(𝑀)`-formulas.

   𝕄 ⊧ φ
     By :math:`𝕄 ⊧ φ` we denote the assertion that φ is :term:`valid` in 𝕄.

   metaprogram
     a program whose purpose is to modify the behavior of other programs; :term:`proof tactics <proof tactic>` form an important class of metaprograms.

   model
     A **model** of a theory is a :term:`structure` (e.g. an interpretation) that satisfies the :term:`sentences <sentence>` of that theory.

     More precisely, let

     * 𝐿 = the :term:`language` of the :term:`signature` 𝑆,
     * φ ∈ 𝐿₀, an 𝐿-sentence,
     * Σ ⊆ 𝐿₀, a collection of 𝐿-sentences,
     * ℳ = ⟨𝑀, … ⟩ and 𝒩 = ⟨𝑁, … ⟩, 𝑆-structures,
     * Δ = an arbitrary class of formulas (not necessarily from 𝐿).

     If 𝑀 is not empty and ℳ ⊨ Σ, then ℳ is a **model** of Σ; we also say "ℳ *models* Σ."

     𝐿et Mod(𝐿,Σ) denote the class of 𝑆-structures that model Σ. Then Mod(𝑆,∅) denotes the class of all nonempty 𝑆-structures.

   model theory
     The study of classes of mathematical structures (e.g. groups, fields, graphs, universes of set theory) from the perspective of mathematical logic is called **model theory**. The objects of study are models of :term:`theories <theory>` in a formal :term:`language`. A set of :term:`sentences <sentence>` in a formal language is one of the components that form a theory.

     Model theory examines semantical elements (meaning and truth) by means of syntactical elements (formulas and proofs) of a language. Model theory, like proof theory, is an interdisciplinary area that intersects with mathematics, philosophy, and computing science.

   modus ponens
     See: :term:`implication elimination`

   negative formula
     A negated :term:`positive formula` is called a **negative formula**. The class of all such formulas is denoted by :math:`\boldsymbol{-}`.

   new constant symbol
     𝐿et 𝐿 be a :term:`language`.  A **new constant symbol** (or **new constant**) for 𝐿 is a symbol not already present in the alphabet of 𝐿.

   normal form
     In :term:`dependent type theory`, every term has a computational behavior and may be *reduced* using certain reduction rules (e.g., the α, β, η rules).  The form beyond which a term :math:`t` cannot be reduced, if such a form exists, is called the **normal form** of :math:`t`.

     In a :term:`rewriting` system, a term is said to be in **normal form** if it does not admit any further rewrites.

     See also: https://ncatlab.org/nlab/show/normal+form

   Nuprl
     `Nuprl <http://www.nuprl.org/>`_ is an :term:`extensional`, :term:`predicative` :term:`ITP` supporting :term:`dependent types <dependent type>` and based on Martin 𝐿of type theory.  It is described on `its wikipedia page <https://en.wikipedia.org/wiki/Nuprl>`_ as follows:

       "Nuprl is a proof development system, providing computer-mediated analysis and proofs of formal mathematical statements, and tools for software verification and optimization... Nuprl functions as an automated theorem proving system and can also be used to provide proof assistance."

   Pi type
     The **Pi type** Π(𝑥 : 𝐴), 𝐵 𝑥, also known as a **dependent function type**, is a dependent type that generalizes the type :math:`A → B`; it is a :term:`dependent type` because the codomain :math:`B x` depends on the value :math:`x`.

   polymorphic type
     See: https://ncatlab.org/nlab/show/polymorphism

   positive boolean combination
     𝐿et Σ be a set of :term:`formulas <formula>`. A **positive boolean combination** of formulas from Σ is obtained by connecting formulas from Σ with only ∧ and ∨.

   positive formula
     A formal obtained from :term:`atomic formulas <atomic formula>` using only ∧, ∨, ∃, ∀ is called a **positive formula**.  The class of all positive formulas (of all possible languages) is denoted by :math:`\boldsymbol +`.

   power
     The **power** (or **cardinality**) of an 𝐿-:term:`theory` :math:`T` is denoted by :math:`|T|` and defined to be the cardinality of the language 𝐿.

   pp-construction
     𝐿et (𝔸, 𝔹) and :math:`(𝔸', 𝔹') = ((A', R_0, \dots, R_{n-1}), (B', S_0, \dots, S_{n-1}))`  be :term:`PCSP templates <PCSP template>`. We say that (𝔸, 𝔹) **pp-constructs** (𝔸', 𝔹') if there is a sequence

     .. math:: (𝔸, 𝔹)  = (𝔸_0, 𝔹_0), (𝔸_1, 𝔹_1), \dots, (𝔸_n, 𝔹_n) = (𝔸', 𝔹'),

     of PCSP templates such that each :math:`(𝔸_{i+1}, 𝔹_{i+1})` is a :term:`pp-power` or a :term:`homomorphic relaxation` of :math:`(𝔸_i, 𝔹_i)`.

   pp-definable
     𝐿et (𝔸, 𝔹) and :math:`(𝔸', 𝔹') = ((A', R_0, \dots, R_{n-1}), (B', S_0, \dots, S_{n-1}))`  be :term:`PCSP templates <PCSP template>`. We say that (𝔸', 𝔹') is **pp-definable** from  (𝔸, 𝔹) if, for each :math:`0≤ i < n`, there exists a :term:`pp-formula` φ over 𝔸 such that φ defines :math:`R_i` and the formula, obtained by replacing each occurrence of a relation of 𝔸 by the corresponding relation in 𝔹, defines :math:`S_i`.

   pp-formula
     A **primitive positive formula** (or **pp-formula**) is a :term:`primitive formula` :math:`∃ x₀, \dots, x₁ \ φ` such that no negated atomic formulas occur in φ.

   pp-power
     We say that (𝔸', 𝔹') is an :math:`n`-th **pp-power** of (𝔸, 𝔹) if :math:`A' = A^n`, :math:`B' = B^n` and (𝔸', 𝔹') is :term:`pp-definable` from (𝔸, 𝔹) (where we view :math:`k`-ary relations on 𝔸' and 𝔹' as :math:`kn`-ary relations on :math:`A` and :math:`B`, respectively).

   primitive formula
     A **primitive formula** is a :term:`formula` of the form :math:`∃ x₀, \dots, x₁ \ φ`, where φ is a conjunction of :term:`literals <literal formula>`. (The set :math:`\{x₀,\dots ,x₁\}` may be empty.)

   pp-sentence
     A **pp-sentence** is a :term:`pp-formula` that contains no :term:`free variables <free variable>`.

   predicative
     The opposite of :term:`impredicative`, *predicative* refers to building stratified (or ramified) theories where quantification over lower levels results in variables of some new type, distinguished from the lower types that the variable ranges over.

   primitive formula
     A **primitive formula** is a :term:`formula` of the form

     .. math:: ∃ x₀, …, x₁ \ φ,

     where φ is a conjunction of :term:`literals <literal formula>`. (The set {𝑥₀, …, 𝑥₁} may be empty.)

     Here's an equivalent definition with slightly more explicit notation, which might make the definition clearer: a formula is called **primitive** if it has the form :math:`∃ 𝐲 ⋀_{i < n} α_i(𝐱, 𝐲)`, where each αᵢ(𝐱, 𝐲) is an atomic or negated :term:`atomic formula`.

   proof assistant
     A **proof assistant**, or interactive theorem prover (ITP), is specialized software that aids the user in the task of formalizing and proving theorems in an interactive (as opposed to automated) way. Although some proof assistants have features (such as :term:`proof tactics <proof tactic>`) which may provide some automation and proof-search capabilities, proof assitants are distinguished from :term:`automated theorem provers <automated theorem prover>` by the fact that they primarily rely on substantial interaction with the user.

     Some examples of popular proof assistants are :term:`Agda`, :term:`Coq`, :term:`Lean`, and :term:`NuPrl`.

   proof tactic
     an automated procedure for constructing and manipulating proof terms.

   proof-irrelevant
     The type ``Prop`` is called **proof-irrelevant** if all proofs of the same proposition are :term:`definitionally equal`; that is, if ``P: Prop`` and ``proof₁: P`` and ``proof₂: P``, then ``proof₁ = proof₂``.

   proof-relevant
     A :term:`universe` level, say, ``Type u``, is called **proof-relevant** if inhabitants (proofs) of the same type (proposition) are not :term:`definitionally equal`.  That is, we may have ``T: Type u``, ``p: T``, ``q: T``, and ``p ≠ q``.

   proofs-as-programs
     In :term:`type theory`, constructing a proof of a proposition ``P`` is equivalent to constructing an inhabitant of the type to which ``P`` corresponds (under the :term:`propositions-as-types` correspondence). The construction of such a proof ``p: P`` is viewed as a program that computes ``p`` as output.

     See also: https://ncatlab.org/nlab/show/proofs+as+programs and :term:`Curry-Howard correspondence` and :term:`propositions-as-types`

   proposition extensionality
     This axiom asserts that when two propositions imply one another, they are :term:`definitionally equal`. This is consistent with set-theoretic interpretations in which an element ``a:Prop`` is either empty or the singleton set ``{*}``, for some distinguished element ``*``. The axiom has the effect that equivalent propositions can be substituted for one another in every context.

   propositions-as-types
     In :term:`type theory`, the propositions-as-types correspondence says that propositions and types are essentially the same. A proposition, when viewed as a type, is identified with the collection (or type) of all its proofs, and a type is identified with the proposition that there exists something of that type.

     See also: https://ncatlab.org/nlab/show/propositions+as+types and :term:`Curry-Howard correspondence` and :term:`proofs-as-programs`

   pseudoelementary class
     A **pseudoelementary class** is a class of structures derived from an :term:`axiomatizable` class by omitting some of its sorts and relations.

     This is the mathematical logic analog of the notion in category theory of (the codomain of) a forgetful functor. Axiomatizable classes are (vacuously) pseudoelementary but the converse is not always true; nevertheless pseudoelementary classes share some of the properties of axiomatizable classes such as being closed under :term:`ultraproduct`.

   quantifier-free formula
     A **quantifier-free formula** is a :term:`formula` that contains no quantifiers; naturally, we assume ⊤ and ⟂ are quantifier-free formulas.

     The class of all quantilier-free formulas (of arbitrary signature) is denoted by 𝐪𝐟.

   quasiidentity
     A **quasiidentity** in the language 𝐿 is an implication of the form s₁ ≈ t₁ ∧ ... ∧ sₙ ≈ tₙ ⟶  s ≈ t, where s, s₁, ..., sₙ, t, t₁, ..., tₙ are terms built up from variables using the operation symbols of 𝐿.

   record
     See: :term:`structure`

   recursive language
     A `formal language <https://en.wikipedia.org/wiki/Formal_language>`_ is called **recursive** if it is a :term:`recursive subset` of the set of all possible finite sequences over the alphabet of the language. Equivalently, a formal language is recursive if there exists a total :term:`Turing machine` that is total (i.e., always halts) and that, when given a finite sequence of symbols as input, accepts it if it belongs to the language and rejects it otherwise. Recursive languages are also called decidable.

     Source: https://en.wikipedia.org/wiki/Recursive_language

   recursive subset
     Given a set Ω, a subset 𝑆 ⊆ Ω is called **recursive** if there exists an algorithm that takes as input an element ω ∈ Ω and correctly decides after a finite number of steps whether or not ω belongs to 𝑆.

   recursively enumerable
     Given a set Ω, a subset 𝑆 ⊆ Ω is called **recursively enumerable** if there exists an algorithm that enumerates all the elements of 𝑆. Equivalently, there exists an algorithm takes input ω ∈ Ω and:

      if ω ∈ 𝑆, answers "yes" (after a finite amount of time);
      if ω ∉ 𝑆, may not terminate.

     Heuristically, there exists an algorithm that gives no "false positives", i.e., an algorithm that never makes a false claim that ω ∈ 𝑆.

   recursor
     Each :term:`inductively defined type <inductive type>` ``T`` is accompanied by an elimination principle known as a **recursor**. It is what makes the type "inductive" by allowing us to define a function on ``T`` by assigning values for each of ``T``'s constructors.

   relational structure
     A relational structure :math:`𝔸 = ⟨A, ℛ⟩` is a set :math:`A` together with a collection :math:`ℛ` of relations on :math:`A`.

     See also: the definition of a :term:`structure`.

   rewriting
     See: https://ncatlab.org/nlab/show/rewriting

   sentence
     A :term:`formula` φ is called a **sentence** (or **closed formula**) if it contains no :term:`free variables <free variable>`; that is, all variables appearing in φ are :term:`bound <bound variable>`.

   :math:`Σ^⊢`
     denotes the set {φ ∈ 𝐿₀ : Σ ⊢ φ} of :term:`logical consequences <logical consequence>` of Σ.

   Sigma type
     The **Sigma type** :math:`Σ(x:A),B x`, also known as the **dependent pair type**, generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second argument of the ordered pair to depend on the value :math:`x` of the first.

   signature
     In :term:`model theory`, a **signature** 𝑆 = (𝐂, 𝐅, 𝐑, ρ) consists of three (possibly empty) sets 𝐂, 𝐅, and 𝐑---called *constant symbols*, *function symbols*, and *relation symbols*, respectively---along with a function ρ: 𝐂 + 𝐅 + 𝐑 → 𝑁 that assigns an :term:`arity` to each symbol. Often (but not always) 𝑁 = ℕ.

   𝑆-formula
     See: :term:`formula`.

   𝑆-structure
     See: :term:`structure`.

   structure
     A **structure** in the :term:`signature` σ = (𝐂, 𝐅, 𝐑, ρ) consists of the pair 𝔸:=(A, {𝐂^𝔸, 𝐅^𝔸, 𝐑^𝔸}), where A is a set, 𝐂^𝔸 is a collection of named constants in A (one for each constant symbol in 𝐂), 𝐅^𝔸 is the collection of basic operations of 𝔸 (one for each operation symbol in 𝐅), and 𝐑^𝔸 is the collection of relations on 𝔸 (one for each relation symbol in 𝐑).

     In programming languages, a non-recursive inductive type that contains only one constructor is called a **structure**. In mathematics, a structure may refer to an :term:`algebraic structure` or a :term:`relational structure`.

   substitution
     The notation f ∘ 𝐚 is shorthand for :math:`(f(a_0), f(a_1), \dots)` and :math:`φ_{𝐱}(𝐚)` is shorthand for :math:`[a_0/x_0, a_1/x_1, \dots]φ(x_0, x_1, \dots)`, the sentence obtained from φ upon substituting :math:`a_i` for :math:`x_i`, for all :math:`i`.

   theory
     An :math:`𝐿`-**theory** (or **theory** when the context makes :math:`𝐿` clear) is a :term:`consistent` and :term:`deductively closed <deductive closure>` set of :math:`𝐿`-:term:`sentences <sentence>`.

   Th ℳ
     The collection {φ ∈ 𝐿₀: ℳ ⊧ φ} of all 𝐿-sentences that are true in ℳ is denoted by Th ℳ. This set is sometimes denoted by :math:`\mathrm{Th}_{𝐿_0}`.

     If Δ is an arbibtrary class of formulas, then Th_Δ ℳ := {φ ∈ 𝐿₀: φ ∈ Δ,\ ℳ ⊧ φ}, the set of all 𝐿-sentences in Δ that are true in ℳ.

   true quantified Boolean formula
     The language **TQBF** is a formal language consisting of the **true quantified Boolean formulas**. A (fully) quantified Boolean formula is a formula in quantified propositional logic where every variable is bound using either existential or universal quantifiers at the beginning of the sentence. Such a formula is equivalent to either true or false. If such a formula evaluates to true, then that formula is in the language TQBF.

     See also: https://en.wikipedia.org/wiki/True_quantified_Boolean_formula

   type class
     A **type class** is a family of types; each type in the family is called an :index:`instance` of the type class.

   type theory
     **Type theory** internalizes the interpretation of intuitionistic logic proposed by Brouwer, Heyting, and Kolmogorov---the so-called BHK interpretation. The types in type theory play a similar role to that of sets in set theory but *functions definable in type theory are always computable*.

     Intuitionistic **type theory** extends the :term:`Curry-Howard correspondence` to predicate logic by introducing :term:`dependent types <dependent type>`.

     See also: https://ncatlab.org/nlab/show/type+theory

   universal part
     We denote by :math:`\boldsymbol{∀}` the class of formulas in which ∃ does not appear; :math:`\mathrm T_{\boldsymbol ∀} = (\mathrm T ∩ \boldsymbol ∀)^⊢` is the **universal part** of T.

   universe polymorphism
     We use an example to demonstrate this concept. Given a type ``α``, no matter to which type universe ``α`` belongs, we can form the type ``list α`` of lists of elements of type ``α``, and this type will have the same type universe as ``α``. In other terms, ``α: Type u`` if and only if ``list α: Type u``.

   valid
     We say that φ is **valid** in 𝕄, and we write 𝕄 ⊧ φ, if for every tuple 𝐚 from 𝕄 (that is at least as long as 𝐱) the 𝐿-sentence φ(𝐚) is **true** in 𝕄.

-----------------------

Glossary: structures, categories, varieties
-------------------------------------------

.. glossary::

    abelian group
      A :term:`group` is called **abelian** just in case its binary operation is commutative.

    absorbing
      Let 𝐀 be a finite algebra in a :term:`Taylor variety` 𝒱 and let t ∈ Clo(𝐀) be a :math:`k`-ary term operation of 𝐀.

      A subalgebra 𝐁 ≤ 𝐀 is said to be **absorbing** in 𝐀 with respect to the **absorbing term** :math:`t` if for all :math:`1 ≤ j ≤ k` and for all

      .. math:: (b_1, \dots, b_{j-1}, a, b_{j+1}, \dots, b_k) ∈ B^{j-1} × A × B^{k-j},

      we have

      .. math:: t^𝐀 (b_1, \dots, b_{j-1}, a, b_{j+1}, \dots, b_k) ∈ B.

      In other terms, :math:`t^𝐀[B^{j-1} × A × B^{k-j}] ⊆ B` for all :math:`1 ≤ j ≤ k`, where :math:`t^𝐀[D] := \{t^𝐀(x) : x ∈ D\}`.

      We denote the fact that 𝐁 is an absorbing subalgebra of 𝐀 with respect to some term by writing :math:`𝐁 \triangleleft 𝐀`. If we wish to be explicit about the term, we write :math:`𝐁 \triangleleft_t 𝐀`.

    absorption-free
      An algebra is said to be **absorption-free** if it has no proper :term:`absorbing` subalgebras.

    abstract category
      An **abstract category** is one whose objects are not sets or whose :term:`morphisms <morphism>` are not functions defined on sets.

    additive
      Let :math:`𝔐 = \{M_λ: λ∈ Λ\}` be a collection of sets and let :math:`R` be a :term:`ring`.  An :math:`R`-valued function :math:`s: 𝔐 → R` defined on the collection :math:`𝔐` is called **additive** if for every subset :math:`Γ ⊆ Λ` such that :math:`\{M_γ : γ ∈ Γ\}` is a subcollection of *pairwise disjoint* subsets in :math:`𝔐`, we have

      .. math:: s \bigl( ⋃_{γ∈Γ}  M_γ \bigr) = ∑_{γ∈ Γ} s (M_γ).

    adjoint
      Suppose that :math:`X` and :math:`Y` are :term:`normed linear spaces <normed linear space>` and :math:`T ∈ 𝔅(X, Y)` (a :term:`bounded linear transformation`). The **adjoint** (or **transpose**) of :math:`T` is denoted by :math:`T^†: Y^∗ → X^∗` and defined for each :math:`f∈ Y^∗` by :math:`T^† f = f T`.
      
      It is not hard to show that :math:`T^† ∈ 𝔅(Y^∗, X^∗)` and :math:`\|T^†\| = \|T\|`.
 
    algebra
      See :term:`structure`.
 
    algebra of functions
      Let :math:`F` be a :term:`field` and let :math:`F^X` denote the collection of all functions from :math:`X` to :math:`F`.  A subset :math:`𝔄 ⊆ F^X` of :math:`F`-valued functions on :math:`X` is called an **algebra** if it is closed under point-wise product.  That is, for all :math:`f, g ∈ 𝔄`, the function :math:`h = f ⋅ g` defined by :math:`h: x ↦ f(x) ⋅ g(x)` also belongs to :math:`𝔄`.
 
    algebra of sets
      Let :math:`X` be a nonempty set. An **algebra of sets** on :math:`X` is a nonempty collection :math:`𝔄` of subsets of :math:`X` that is :term:`closed <closed set>` under finite unions and complements. (Some authors call this a "field of sets.")
 
    algebraic lattice
      a :term:`lattice` generated by its :term:`compact elements <compact element>`. 
 
    algebraic signature
      By an **algebraic signature** (or **signature** for :term:`algebraic structures <algebraic structure>`) we mean a pair :math:`σ = (F, ρ)` that consists of a collection :math:`F` of *operation symbols* and an :term:`arity` function :math:`ρ : F → N` that maps each operation symbol to its arity; here, :math:`N` denotes the arity type (which is often, but not always, taken to be ℕ).
 
    algebraic structure
      An **algebraic structure** in the :term:`signature` :math:`σ = (F, ρ)` (or, :math:`σ`-**algebra**) is denoted by :math:`𝔸 = ⟨A, F^𝔸⟩` and consists of 
 
      #. :math:`A` := a set, called the *carrier* (or *universe*) of the algebra,
      #. :math:`F^𝔸 = \{ f^𝔸 ∣ f ∈ F, \ f^𝔸: (ρ f → A) → A \}` := a set of operations on :math:`A`, and
      #. a collection of identities satisfied by elements of :math:`A` and operations in :math:`F^𝔸`.
 
    antichain
      A subset :math:`A` of the :term:`preordered <preorder>` set :math:`X` is called an **antichain** if for all :math:`x, y ∈ A` we have :math:`x ≤ y` implies :math:`y ≤ x`.
 
    antisymmetric
      A binary relation :math:`R` on a set :math:`X` is called **antisymmetric** provided :math:`∀  x, y ∈ X \ (x \mathrel{R} y ∧ y\mathrel{R} x \ → \ x=y)`.
 
    arity
      Given a :term:`signature` :math:`σ = (F, ρ)`, each operation symbol :math:`f ∈ F` is assigned a value :math:`ρ f`, called the **arity** of :math:`f`. (Intuitively, the arity can be thought of as the "number of arguments" that :math:`f` takes as "input".)
 
    associative algebra
      If :math:`𝔸` is a :term:`bilinear algebra` with an associative product---:math:`(a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)` for all :math:`a, b, c ∈ A`---then :math:`𝔸` is called an **associative algebra**.
      
      Thus an associative algebra over a field has both a :term:`vector space` :term:`reduct` and a :term:`ring` :term:`reduct`.
      
      An example of an associative algebra is the space of :term:`linear transformations <linear transformation>` (:term:`endomorphisms <endomorphism>`) of a vector space into itself.
 
    bilinear algebra
      Let :math:`𝔽= ⟨ F, 0, 1, -\, , +, ⋅⟩` be a field. An algebra :math:`𝔸 = ⟨ A, 0, -\, , +, ⋅, f_r⟩_{r∈ F}` is a **bilinear algebra** over :math:`𝔽` provided :math:`⟨A, 0, -, +, ⋅, f_r⟩_{r ∈ F}` is a :term:`vector space` over :math:`𝔽` and for all :math:`a, b, c ∈ A` and all :math:`r ∈ F`, we have
 
      .. math::   (a + b) ⋅ c &= (a ⋅ c) + (b ⋅ c)\\
                  c ⋅ (a + b) &= (c⋅ a) + (c⋅ b)\\
                   a⋅  f_r(b) &= f_r(a⋅ b) = f_r(a)⋅ b.
 
      If, in addition, :math:`(a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)` for all :math:`a, b, c ∈ A`, then :math:`𝔸` is called an **associative algebra over** :math:`𝔽`. Thus an associative algebra over a field has both a vector space reduct and a ring reduct. An example of an associative algebra is the space of linear transformations (endomorphisms) of any vector space into itself.
 
    binary operation
      An operation :math:`f` on a set :math:`A` is called **binary** if the arity of :math:`f` is 2.  That is, :math:`f: A × A → A` (or, in curried form, :math:`f: A → A → A`).
 
    Boolean algebra
      A **Boolean algebra** is a :term:`lattice` 𝐿 equipped with a unary operation ¬: 𝐿 → 𝐿 satisfying

      .. math:: a ∧ b ≤ c \quad ⟺ \quad a ≤ ¬b ∨ c

      See also: https://ncatlab.org/nlab/show/Boolean+algebra

    Boolean algebra homomorphism
      a :term:`lattice homomorphism` that also preserves complementation (but every lattice homomorphism between Boolean lattices automatically preserves complementation, so we may characterize the morphisms of this category more simply as the lattice homomorphisms).
 
    Cartesian product
      See :term:`product`.
 
    category of categories
      has categories as objects and :term:`functors <functor>` as :term:`morphisms <morphism>`.
 
    chain
      Let :math:`⟨ X, ≤ ⟩` be a :term:`preordered <preorder>` set and :math:`C ⊆ X`. We call :math:`C` a **chain** of :math:`⟨ X, ≤ ⟩` if for all :math:`x, y ∈ C` either :math:`x ≤ y` or :math:`y ≤ x` holds.
 
    characteristic function
      The **characteristic function** :math:`χ_A` of a subset :math:`A ⊆ X` is the function :math:`χ_A: X → \{0,1\}` that is 1 if and only if :math:`x ∈ A`; that is, :math:`χ_A(x) = 0` if :math:`x ∉ A` and :math:`χ_A(x) = 1` if :math:`x ∈ A`.
 
    Choice
      is short for the `Axiom of Choice <https://en.wikipedia.org/wiki/Axiom_of_choice>`_.
 
    clone
      An **operational clone** (or just **clone**) on a nonempty set :math:`A` is a set of operations on :math:`A` that contains all :term:`projection operations <projection operation>` and is closed under :term:`general composition`.
 
    closed set
      If :math:`𝖢` is a :term:`closure operator` on :math:`X`, then a subset :math:`A ⊆ X` is called **closed** with respect to :math:`𝖢` (or :math:`𝖢`-**closed**) provided :math:`𝖢(A) ⊆ A` (equivalently, :math:`𝖢(A) = A`).
 
      Here's an important example. 𝐿et :math:`σ = (F, ρ)` be a :term:`signature` and :math:`X` a set. Define for each :math:`A ⊆ X` the set :math:`𝖢(A) = \{f\, b ∣ f ∈ F, \, b: ρ f → A\}`.  Then :math:`𝖢` is a closure operator on :math:`X` and a subset :math:`A ⊆ X` is said to be "closed under the operations in :math:`F`" provided :math:`A` is :math:`𝖢`-closed.
 
    closed term
      A :term:`term` is said to be **closed** (or **constant**) if it contains no :term:`free variables <free variable>`. In particular, every constant symbol in the set 𝐂 of a :term:`signature` is a closed term.
 
    closure
       If :math:`X` is a :term:`metric <metric space>` or :term:`topological space` then the **closure** of a subset :math:`E ⊆ X` is denoted by :math:`Ē` and defined to be the smallest :math:`closed` subset of :math:`X` containing :math:`E`.
       
       The closure :math:`Ē` exists since the collection :math:`Ω` of all closed subsets of :math:`X` which contain :math:`E` is not empty (since :math:`X ∈ Ω`), so define :math:`Ē` to be the intersection of all members of :math:`Ω`.
 
       Here is an alternative, equivalent definition. The **closure** of :math:`E` is the intersection of all :term:`closed <closed set>` sets containing :math:`E`.
 
    closure operator
      Let :math:`X` be a set and let :math:`𝒫(X)` denote the collection of all subsets of :math:`X`. A **closure operator** on :math:`X` is a set function :math:`𝖢: 𝒫 (X) → 𝒫 (X)` satisfying the following conditions, for all :math:`A, B ∈ 𝒫 (X)`, 
 
      #. :math:`A ⊆ 𝖢(A)`,
      #. :math:`𝖢 ∘ 𝖢 = 𝖢`,
      #. :math:`A ⊆ B ⟹ 𝖢(A) ⊆ 𝖢(B)`.
 
    cocomplete
      See :term:`cocomplete poset`.
 
    cocomplete poset
      A :term:`poset` in which all joins exist is called **cocomplete**.
 
    codomain
      If f: A → B is a function or relation from A to B, then B is called the **codomain** of f, denoted by cod f.
 
    commutative diagram
      A **commutative diagram** is a diagram with the following property: for all objects C and D, all paths from C to D yield the same :term:`morphism`.
 
    commutative group
      See :term:`abelian group`.
 
    compact element
      an element 𝑥 of a :term:`lattice` 𝐿 is called **compact** provided for all 𝑌 ⊆ 𝐿, if 𝑥 ≤ ⋁ 𝑌, then there exists a finite subset 𝐹 ⊆ 𝑌 such that 𝑥 ≤ ⋁ 𝐹.
 
    complete
      A :term:`poset` in which all meets exist is called **complete**.
 
    complete lattice
      a :term:`poset` whose universe is closed under arbitrary meets and joins.
 
    complete lattice homomorphism
      A **complete lattice homomorphism** is a function :math:`f: X → Y` that preserves complete meets and joins.
 
    complete poset
      A :term:`poset` in which all meets exist is called **complete**.
 
    component    
      If :math:`α : F ⇒ G` is a :term:`natural transformation`, then the **component** of α at :math:`A` is the :term:`morphism` :math:`α_A : FA → GA`.
 
    composition of operations
      If :math:`f: (n → A) → A` is an :math:`n`-ary operation on the set :math:`A`, and if :math:`g: ∏_{(i:n)} ((k_i → A) → A)` is an :math:`n`-tuple of operations, then we define the **composition of** :math:`f` **with** :math:`g`, using the :term:`eval` and :term:`fork` operations, as follows:
   
      .. math:: f [g] := f\, (\mathbf{eval} \, \mathbf{fork}\, g): ∏_{(i:n)}(k_i → A) → A.
   
      Indeed, 
      
      .. math:: \mathbf{eval} \, \mathbf{fork} \, g: ∏_{(i:n)}(k_i → A) → (n → A)
      
      is the function that maps each :math:`a: ∏_{(i:n)}(k_i → A)` to :math:`∏_{(i:n)}\mathbf{eval} \,(g \, i, a\, i) = g ∘ a`, where for each :math:`(i:n)` :math:`(g ∘ a)(i) = (g i)(a i): A`.
      
      Thus, if :math:`a: ∏_{(i:n)}(k_i → A)`, then :math:`(\mathbf{eval} \, \mathbf{fork} \, g) (a)` has type :math:`n → A`, which is the domain type of :math:`f`.  Therefore, :math:`f \, (\mathbf{eval} \, \mathbf{fork}\, g)\, (a)` has type :math:`A`.
 
    concrete category
      A **concrete category** is one whose objects are sets and whose :term:`morphisms <morphism>` are functions defined on these sets (possibly satisfying some other special properties).
 
    congruence-permutable
      An :term:`algebraic structure` is called **congruence-permutable** if every pair of its congruences :term:`permute <permuting relations>`.
      
      A :term:`variety` is **congruence-permutable** if all of its members are congruence-permutable.

    constant term
      See :term:`closed term`.
 
    consecutive functions
      If :math:`f : A → B` and :math:`g : B → C`, then :math:`\cod f = \dom g` and we say that :math:`f` and :math:`g` are **consecutive functions**.
 
    contravariant powerset functor
      The **contravariant powerset functor** is a functor :math:`P^{\mathrm{op}}: \mathbf{Set} → \mathbf{Set}` such that for each :term:`morphism` :math:`g: B → A` the morphism :math:`P^{\mathrm{op}}g: 𝒫(A) → 𝒫(B)` is given by :math:`P^{\mathrm{op}} g (S) = \{b ∈ B : g(b) ∈ S\}` for each :math:`S ⊆ A`.
 
    coproduct
      Given two objects :math:`A` and :math:`B` a **coproduct** (or **sum**) of :math:`A` and :math:`B` is denoted by :math:`A+B` and defined to be an object with morphisms :math:`ι_1 : A → A + B` and :math:`ι_2 : B → A + B` such that for every object :math:`X` and all morphisms :math:`u : A → Y` and :math:`v : B → Y` there exists a unique morphism :math:`[u,v] : A+B → Y` such that :math:`[u,v] ∘ ι_1 = u` and :math:`[u,v] ∘ ι_2 = v`.
 
    countably additive
      Let :math:`𝒮 = \{S_λ: λ∈ Λ\}` be a collection of sets and let :math:`R` be a :term:`ring`.  A function :math:`s: 𝒮 → R` is called **countably additive** if for every *countable* subset :math:`Γ ⊆ Λ` such that :math:`\{S_γ : γ ∈ Γ\}` is a collection of *pairwise disjoint* subsets in :math:`𝒮`, we have
 
     .. math:: s \bigl( ⋃_{γ∈Γ}  A_γ \bigr) = ∑_{γ∈ Γ} s (A_γ).
 
    countably subadditive
      Let :math:`𝒮 = \{S_λ: λ∈ Λ\}` be a collection of sets and let :math:`R` be a :term:`ring`.  A function :math:`s: 𝒮 → R` is called **countably subadditive** if for every *countable* subset :math:`Γ ⊆ Λ` such that :math:`\{S_γ : γ ∈ Γ\}` is a collection of subsets in :math:`𝒮`, we have
 
    covariant powerset functor
      The **(covariant) powerset functor** is a functor :math:`P : \mathbf{Set} → \mathbf{Set}` such that for each :math:`f : A → B` the morphism :math:`Pf : PA → PB` is given by :math:`Pf(S) = \{f(x) : x ∈ S\}` for each :math:`S \subseteq A`.
 
    directed cocomplete poset
      an :term:`antisymmetric` :term:`directed cocomplete preorder`.
 
    directed cocomplete preorder
      a :term:`preorder` for which the joins of all :term:`directed <directed set>` subsets exist. 
      
    directed graph
      A **directed graph** is a :term:`relational structure` consisting of a vertex set :math:`V` (whose elements are called vertices) and an edge set :math:`E ⊆ V^2` (whose elements are called edges).
 
    directed set
      A subset :math:`D` of a :term:`preorder` is called **directed** if every finite subset of :math:`D` has an upper bound in :math:`D`. That is, if :math:`F ⊆ D` and :math:`F` is finite, then there exists :math:`d ∈ D` such that :math:`f ≤ d` for all :math:`f ∈ F`.
 
    division ring
      A :term:`ring` in which every nonzero element is a unit is called a **division ring**.
 
    domain
      If f : A → B is a function or relation from A to B, then A is called the **domain** of f, denoted by dom f.
 
    dual
      If :math:`X` is a :term:`normed linear space` over the :term:`field` :math:`F`, then the collection :math:`𝔅(X,F)` of :term:`bounded linear functionals <bounded linear functional>` is called the **dual space** (or **dual**) of :math:`X`.
 
      If :math:`F` is :term:`complete`, then :math:`𝔅(X,F)` is complete, hence a :term:`Banach space`.
 
    edge term
      Let 𝒱 be a variety and k>1, an integer. A (k+1)-ary term t is called a **k-edge term** for 𝒱 if the following k identities hold in 𝒱:
 
      .. math:: t(y,y,x,x,x,\dots,x) &≈ x\\
                t(y,x,y,x,x,\dots,x) &≈ x\\
                t(x,x,x,y,x,\dots,x) &≈ x\\
                &⋮ \\
                t(x,x,x,x,x,\dots,y) &≈ x.
 
      Clearly every edge term is :term:`idempotent <idempotent term>` and a :term:`Taylor term`; also, every :term:`Maltsev term` and every :term:`near unanimity term` is an edge term.
      
    endofunctor
      A :term:`functor` that maps a category to itself is called an **endofunctor**.
 
    endomorphism
      A :term:`morphism` from a structure to itself---say, f: 𝔸 → 𝔸 (i.e., dom f = cod f)---is called an **endomorphism**.
 
    epimorphism
      A :term:`morphism` :math:`f: X → Y` is called an **epimorphism** if for every object :math:`Z` and pair :math:`g_1, g_2: Y → Z` of morphisms we have :math:`g_1 ∘ f = g_2 ∘ f` implies :math:`g_1 = g_2`. When :math:`f: X → Y` is an **epimorphism** we often say ":math:`f` is epi" and write :math:`f: X ↠ Y`.
 
    equivalence class
      If :math:`R` is an :term:`equivalence relation` on :math:`A`, then for each :math:`a ∈ A`, there is an **equivalence class** containing :math:`a`, which is denoted and defined by :math:`a/R = \{b ∈ A ∣ a \mathrel R b\}`.
 
    equivalence relation
      An **equivalence relation** is a :term:`symmetric` :term:`preorder`. The collection of all equivalence relations on :math:`X` is denoted by :math:`\mathrm{Eq}(X)`.
 
    equivalent categories
      Two categories :math:`\mathcal C` and :math:`\mathcal D` are called **equivalent categories** if there are functors :math:`F : \mathcal C →  \mathcal D` and :math:`G : \mathcal D → \mathcal C` together with natural isomorphisms :math:`ε : FG ≅ \mathrm{id}_{\mathcal D}`, and :math:`η : \mathrm{id}_{\mathcal C} ≅ GF`. We say that :math:`F` is an equivalence with an inverse equivalence :math:`G` and denote the equivalence by :math:`F : \mathcal C ≃ \mathcal D : G`.
 
    essentially surjective on objects
      A functor :math:`F : C → D` is called **essentially surjective on objects** if for every object :math:`D ∈ \mathcal D`, there is some :math:`A ∈ \mathcal C` such that :math:`F A` is isomorphic to :math:`D`.
 
    Euclidean norm
      For :math:`𝐱 = (x_1,\dots, x_n) ∈ ℝ^n` the **Euclidean norm** of :math:`𝐱` is denoted and defined by :math:`\|𝐱\|_2 = \left(∑_{i=1}^n x_i^2\right)^{1/2}`.
 
    Euclidean space
      For :math:`n∈ ℕ` the :term:`normed linear space` :math:`(ℝ^n, \|\,⋅\,\|_2)`, where :math:`\|\,⋅\,\|_2` is the :term:`Euclidean norm`, is called :math:`n`-dimensional **Euclidean space**.
 
    evaluation functor
      The **evaluation functor** is the functor :math:`Ev : \mathcal C × \mathbf{Set}^{\mathcal C} → \mathbf{Set}`, which takes each pair :math:`(A, F) ∈ \mathcal C_{\mathrm{obj}} × \mathbf{Set}^{{\mathcal C}_{\mathrm{obj}}}` of objects to the set :math:`Ev(A, F) = FA`, and takes each pair :math:`(g, μ) ∈ \mathcal C_{\mathrm{obj}} × \mathbf{Set}^{\mathcal C_{\mathrm{mor}}}` of morphisms to a function on sets, namely, :math:`Ev(g, μ) = μ_{A'} ∘ F g = F' g ∘ μ_A`, where :math:`g ∈ \mathcal C(A, A')` and :math:`μ : F ⇒ F'`.
 
    evaluation natural transformation
      The **evaluation natural transformation** is denoted by :math:`eval^A : F_A →  \mathrm{id}_{\mathbf{Set}}` and defined by... (**Todo** complete definition)
 
    existential image functor
      the functor :math:`∃ f : P(A) → P(B)` defined by :math:`∃ f(X) = \{f(x) : x ∈  X\},` for :math:`X ∈ P(A)`.
 
    faithful functor
      A functor :math:`F : \mathcal C → \mathcal D` is called **faithful** if for all objects :math:`A`, :math:`B` in :math:`\mathcal C_{\mathrm{obj}}`, the map :math:`\mathcal C(A, B) → \mathcal D(F A, F B)` is injective.
      
      (Note: A faithful functor need not be injective on morphisms.)
 
    field
      A **field** is a commutative :term:`division ring`.
      
    filter
      A subset F of a partially ordered set (P, ≤) is a **filter** if the following conditions hold:
 
        * F is non-empty.
        * ∀ x, y ∈ F, x ∧ y ∈ F.
        * ∀ x ∈ F, ∀ y ∈ P, x ≤ y → y ∈ F.
 
      A filter is a **proper filter** if it is not equal to the whole set P. (Some authors add this last condition to the definition of a filter.)
 
      The dual notion is called an :term:`order ideal`.
 
    finite ordinals
      The category :math:`\mathrm{Ord}_{\mathrm{fin}}` of **finite ordinals** (also called the **simplex category** :math:`\Delta`) has :math:`\underline n = \{0, 1, \dots, n-1\}` for objects (for each :math:`n ∈ ℕ`) and :math:`f : \underline n → \underline m` :term:`monotone functions <monotone function>` for morphisms.
 
    finite set
      A set is called **finite** if it contains only a finite number of elements.
 
    finitely based
      A variety (or algebra) is called **finitely based** if it has a finite :term:`base`.

    finitely generated variety
      A :term:`variety` is called **finitely generated** if it is of the form :math:`𝒱(K)` where :math:`K` is a finite set of finite algebras.
      
    first category
      A set :math:`G` is of the **first category** if it is a countable union of :term:`nowhere dense` sets.
 
    free algebra
      The **free algebra** in a :term:`variety` is the :term:`initial object` in a category whose objects are :term:`algebraic structures <algebraic structure>`.
      
      Precisely, if :math:`𝒱` is a :term:`variety` of :term:`algebras <algebraic structure>` and if :math:`X` is a set, then the **free algebra** generated by :math:`X` is denoted by :math:`𝔽(X)` and defined as follows: for every algebra :math:`𝔸 ∈ 𝒱` and every function :math:`f: X → A`, there exists a unique :term:`homomorphism` :math:`h: 𝔽(X) → 𝔸` such that :math:`∀ x ∈ X, h(x) = f(x)`.  We say that :math:`𝔽(X)` is "universal", or "has the :term:`universal mapping property`", for :math:`𝒱`
 
    free object
      See :term:`initial object`.
 
    free monoid
      The **free monoid** is the :term:`initial object` in a category of :term:`monoids <monoid>`.
 
    free variable
      A variable that is not :term:`bound <bound variable>` by a quantifier is called a **free variable**.
     
      A formula in first-order logic is an assertion about the free variables in the formula.
     
      For example, if the "domain of discourse" is the set of natural numbers, then the formula :math:`∀ y \; (x ≤ y)` asserts that :math:`x` is less or equal every natural number.
     
      This is logically equivalent (more precisely, "α-equivalent") to the formula :math:`∀ z \; (x ≤ z)`.  
     
      On the other hand, the formula :math:`\forall y (w \le y)` says that :math:`w` is less than or equal to every natural number. This is an entirely different statement: it says something about :math:`w`, rather than :math:`x`. So renaming a *free* variable changes the meaning of a formula.
 
    full embedding
      a :term:`fully faithful functor` that is injective on objects.
 
    full functor
      A functor :math:`F : \mathcal C → \mathcal D` is called **full** if for all objects :math:`A`, :math:`B` in :math:`\mathcal C`, the map :math:`\mathcal C(A, B) → \mathcal D(F A, F B)` is surjective.
      
      (N.B. A full functor need not be surjective on morphisms.)
 
    full subcategory
      If there exists a :term:`full embedding` :math:`F : \mathcal C → \mathcal D`, then :math:`\mathcal C` is called a **full subcategory** of :math:`\mathcal D`.
 
    fully faithful functor
      a functor that is both :term:`full <full functor>` and :term:`faithfull <faithful functor>`.
 
    function application
      See :term:`eval`.
 
    functor
      A **functor** F: 𝒞 → 𝒟 consists of a function :math:`\mathrm F_0` that maps objects of 𝒞 to objects of 𝒟 and a function :math:`\mathrm F_1` that maps morphisms of 𝒞 to morphisms of 𝒟 such that F preserves (co)domains of morphisms, identities, and compositions.
 
    functor category
      The **functor category** from 𝒞 to 𝒟 has functors F: 𝒞 → 𝒟 as objects and natural transformations α: F ⇒ G as morphisms.
 
    Galois connection
      See https://en.wikipedia.org/wiki/Galois_connection.
 
    Galois pair
      See https://en.wikipedia.org/wiki/Galois_connection.
 
    general composition
      See :term:`composition of operations`.
 
    generalized element
      A :term:`morphism` h: X → A is sometimes called a **generalized element** of A.
      
      A morphism f is a :term:`monomorphism` when it is injective on the generalized elements of its domain.
 
    global element
      See :term:`point`.
 
    graph morphism
      Let :math:`𝐆_1 =(V_1, E_1)` and :math:`𝐆_2 = (V_2, E_2)` be graphs. We say that a pair of functions :math:`f=(f_v,f_e)` is a **graph morphism** from :math:`𝐆_1` to :math:`𝐆_2` provided :math:`f_v : V_1 → V_2`, :math:`f_e : E_1 → E_2`, and for any edge :math:`e = (v_1,v_2) ∈ E_1` we have that we have :math:`f_e(e) = (f_v(v_1), f_v(v_2))`.
 
    group
      A **group** is a :term:`monoid` expanded with a unary operation :math:`^{-1}`, called *multiplicative inverse*, which satisfies :math:`∀ a ∈ A`, :math:`a ⋅ a^{-1} =  a^{-1} ⋅ a = e`.
 
    groupoid
      See :term:`magma`.
 
    height
      If :math:`w` is a term, then the **height** of :math:`w` is denoted by :math:`|w|` and defined to be the least :math:`n` such that :math:`w ∈ T_n`.
 
      If :math:`α` is a type, then we sometimes refer to the **height** of :math:`α`, by which we mean the *universe level* of :math:`α`
      
    Heyting algebra
      A **Heyting algebra** :math:`⟨𝐿, ∧, ∨, ⊥, ⊤, →⟩` is a bounded :term:`lattice` with least and greatest elements ⊥ and ⊤, and a binary "implication" → that satisfies :math:`∀ a, b, c ∈ 𝐿, \ (c ∧ a ≤ b \ ⟺ \ c ≤ a → b)`.  𝐿ogically, this says a → b is the weakest proposition for which the modus ponens rule, :math:`\{a → b, a\} ⊢ b`, is sound. The class of Heyting algebras forms a variety that is finitely axiomatizable.
   
    Heyting algebra homomorphism
      a :term:`lattice homomorphism` that also preserves Heyting implications; that is, if :math:`x, x' ∈ X`, then :math:`f(x → x') = f(x) → f(x')`.
 
    hom set
      Some authors require that :math:`\mathcal C(A,B)` always be a set and call :math:`\mathcal C(A,B)` the **hom set** from :math:`A` to :math:`B`.
 
    homomorphism
      See :term:`morphism` and :term:`relational structure homomorphism`.
 
    ideal
      See :term:`order ideal`.
 
    idempotent algebra
      If :math:`𝐀 = ⟨A, F^𝐀⟩` is an algebraic structure and if every basic operation :math:`f ∈ F^𝐀` is :term:`idempotent <idempotent operation>`, then we call 𝐀 an **idempotent algebra**.
 
    idempotent operation
      An operation :math:`f: A^n → A` is called **idempotent** provided :math:`f(a, a, \dots, a) = a` for all :math:`a ∈ A`. That is, :math:`f` maps constant tuples to their constant image value.
      
      Equivalently, if the operation is presented in "curried," say, :math:`f: (ρ f → A) → A`, then we call :math:`f` idempotent iff for each constant tuple :math:`a: ρ f → A` (say, :math:`a\, i = c, ∀ i`) we have :math:`f\, a = c`.
 
    idempotent term
      A term :math:`t` in a variety 𝒱 is called **idempotent** provided :math:`t(s, s, \dots, s) = s` holds for all terms :math:`s` in 𝒱.
 
    idempotent variety
      If every term in a variety is :term:`idempotent <idempotent term>`, then we call the variety **idempotent**.  Equivalently, a variety 𝒱 is idempotent iff every algebra in 𝒱 is an :term:`idempotent algebra`.
 
    initial object
      An object :math:`0` in a category is called the **initial object**  (or **free object**) if for every object :math:`A` in the category there exists a unique morphism :math:`!_A: 0 → A`.
      
      The :term:`free algebra` in a :term:`variety` is a **free object** in a category whose objects are :term:`algebraic structures <algebraic structure>`.
     
    inner product 
      Let :math:`X` be a :term:`vector space` over the field :math:`F`.  An **inner product** on :math:`X` is a function :math:`⟨·,·⟩: X × X → F` satisfying the following conditions:
 
      #. :math:`⟨⋅,⋅⟩` is linear in the first variable; i.e., :math:`⟨α x + βy, z⟩ = α⟨x,z⟩ + β⟨y,z⟩` for all :math:`α, β ∈ F` and :math:`x, y, z ∈ X`;
      #. :math:`⟨⋅,⋅⟩` is symmetric; i.e., :math:`⟨x, y⟩ = ⟨y, x⟩` for all :math:`x, y ∈ X`; and
      #. :math:`⟨x, x⟩ ≥ 0` for each :math:`x∈ X` and :math:`⟨x, x⟩ = 0` if and only if :matH:`x = 0`.
 
    inner product space
      An **inner product space** is a vector space equipped with an :term:`inner product`.
 
    interpretation
      Let 𝒱 and 𝒲 be two varieties of algebraic structures. Suppose the algebras in 𝒱 have signature :math:`σ = (F, ρ)`, while those in 𝒲 have signature :math:`σ' = (F', ρ')`.

      A **strict interpretation** of 𝒱 in 𝒲 is a mapping :math:`D` from the set :math:`F` of operation symbols of 𝒱 to the term algebra :math:`T_{σ'}(X_ω)` of 𝒲 such that

        #. arities are preserved: :math:`∀ f ∈ F, ρ f = ρ'(D(f))`;
        #. for every algebra 𝐁 ∈ 𝒲, the algebra :math:`𝐁^D := ⟨B, \{D(f)^𝐁 : f ∈ F\}⟩` belongs to 𝒱.

      An **insignificant interpretation** of 𝒱 simply replaces nullary operation symbols with their corresponding constant unary terms.

      An **interpretation** of 𝒱 in 𝒲 consists of an (optional) insignificant interpretation followed by a strict interpretation.

      The transformations that are interpretations can be characterized succinctly using category theory, as follows: :math:`T: 𝒲 → 𝒱` is an interpretation iff it is a functor that commutes with the forgetful functor. In other words, for every :math:`𝐀, 𝐁 ∈ 𝒲` and homomorphism :math:`h: 𝐀 → 𝐁`,  the  underlying universes of 𝐀 and  :math:`T(𝐀)` are the same and :math:`h: T(𝐀) → T(𝐁)` is  a  homomorphism.

    isomorphism
      A morphism :math:`f: A → B` is called an **isomorphism** if there exists a morphism :math:`g: A → B` such that :math:`g ∘ f= \mathrm{id}_A` and :math:`f ∘ g = \mathrm{id}_B`. We write :math:`f^{-1}` to denote :math:`g` when it exists.
 
    kernel
      By the **kernel** of a function :math:`f: A → B` we mean the binary relation on :math:`A` denoted and defined by :math:`\mathrm{ker} f := \{(a₁, a₂) : f a₁  = f a₂\}`.   
 
    Kleene closure
      See :term:`free monoid`.
 
    language
      The **language** :math:`𝐿 = 𝐿(σ)` of the signature σ is the set of all :term:`σ-formulas <formula>`.
 
      Every language :math:`𝐿` comes equipped with a countable supply of variables.
      
      If σ =  so the cardinality of :math:`𝐿` is :math:`|𝐿| = \max \{ℵ_0, |𝐂 ∪ 𝐅 ∪ 𝐑|\}`.
 
    lattice
      a :term:`poset` whose universe is closed under all *finite* meets and joins is called a lattice.
     
    lattice homomorphism
      a function :math:`f: X → Y` preserving finite meets and joins.
 
    left module
       See :term:`module`.
 
    lift (n)
      See :term:`lifts (v)`
 
    lifts (v)
      For :math:`ρ ⊆ α × α`, and :math:`f: α → β`, we say that :math:`f` **lifts** to a function on the quotient :math:`α/ρ` provided the following implication holds for all :math:`x y: α`: if :math:`ρ x y` then :math:`f x = f y`.  The function to which :math:`f` lifts is called the **lift** of :math:`f`.
 
    linked product
      A product :math:`R ≤ A_0 × A_1` is called **linked** if it satisfies the following: for all :math:`a, a' ∈ \mathrm{Proj}_0 R` there exist elements :math:`c_0, c_2, \dots, c_{2n} ∈ A_0` and :math:`c_1, c_3, \dots, c_{2n+1} ∈ A_1` such that :math:`c_0 = a`, :math:`c_{2n} = a'`, and for all :math:`0≤ i<n`,
      
      .. math:: (c_{2i},c_{2i+1})∈ R \quad \text{ and } \quad (c_{2i+2},c_{2i+1}) ∈ R.
 
      Here is an easily proved fact that provides equivalent ways to define "linked."
 
      **𝐿emma**. Let :math:`R ≤ A_0 × A_1`, let :math:`η_{R_i} = \ker(R ↠ A_i)` denote the kernel of the projection of :math:`R` onto its i-th coordinate, and let :math:`R^{-1} = \{(y,x) ∈ A_1 × A_0 : (x,y) ∈ R\}`. Then the following are equivalent:
        
        #. :math:`R` is linked;
        #. :math:`η_{R_0} ∨ η_{R_1} = 1_R`;
        #. if :math:`a, a' ∈ \mathrm{Proj}_0 R`, then :math:`(a,a')` is in the transitive closure of :math:`R ∘ R^{-1}`.
 
    locally finite algebra
      An :term:`algebra` is called **locally finite** if every finitely generated subalgebra is finite.
      
    locally finite variety
      A :term:`variety` is **locally finite** if every member is :term:`locally finite <locally finite algebra>`.
 
    locally small category
      A category 𝒞 is **locally small** if for every pair A, B of objects in 𝒞 the collection of :term:`morphisms <morphism>` from A to B is a set.
 
    magma
      An algebra with a single binary operation is called a **magma** (or **groupoid** or **binar**). The operation is usually denoted by :math:`+` or :math:`⋅`, and we write :math:`a+b` or :math:`a ⋅ b` (or just :math:`ab`) for the image of :math:`(a, b)` under this operation, which we call the *sum* or *product* of :math:`a` and :math:`b`, respectively.
 
    Maltsev class
      We can formalize the notion of Maltsev condition through that of :term:`interpretation`.
      
      Write 𝒱 ≤ 𝒲 if there is an :term:`interpretation` of the variety 𝒱 in the variety 𝒲. 
      
      Observe, this ≤ relation is reflexive and transitive, but it is not anti-symmetric. (For example there are interpretations of rings into Abelian groups and vice versa, but the two varieties are not even :term:`term-equivalent`.)

      For a fixed, :term:`finitely based` variety 𝒲, the **strong Maltsev class** defined by 𝒲 is the class of all varieties 𝒱 such that 𝒲 ≤ 𝒱.
      
      The class of congruence-permutable varieties is an example of a strong Maltsev class.

      A **Maltsev class** is defined by an infinite sequence 𝒲₀ ≥ 𝒲₁ ≥ 𝒲₂ ≥ ... of finitely based varieties, and 𝒱 belongs to the Maltsev class if, for some :math:`i<ω, 𝒱 ≥ 𝒲`. (Congruence-distributivity is an example.)
      
      Finally, a **weak Maltsev class** is the intersection of a countable family of Maltsev classes.

    Maltsev condition
      See: :term:`Maltsev class`

    Maltsev term
      See: :term:`Maltsev term`

    Maltsev product
      Let 𝒱 and 𝒲 be idempotent varieties. The **Maltsev product** (or **Maltsev  product**) of 𝒱 and 𝒲 is the class
 
      .. math:: 𝒱 ∘ 𝒲 = \{𝐀 : ∃ θ ∈ \mathrm{Con} 𝐀, (𝐀/θ ∈ 𝒲 \text{ and } ∀ a ∈ A, a/θ ∈ 𝒱)\}.
 
      𝒱 ∘ 𝒲 is always an idempotent quasivariety, but is generally not closed under homomorphic images.
      
      Freese and McKenzie show in :cite:`Freese:2017` that a number of important properties are preserved under Maltsev product; in particular, they prove,
 
      **Theorem**. Let 𝒱 and 𝒲 be idempotent varieties. For each of the following properties, P, if both 𝒱 and 𝒲 have P, then so does 𝖧(𝒱 ∘ 𝒲). 
 
        * P = is idempotent;
        * P = has a :term:`Taylor term`;
        * P = is SD∧;
        * P = has an :term:`edge term`.
 
      It follows from the theorem that if both 𝒱 and 𝒲 are SD∧, or both have an edge term, then every finite member of 𝖧(𝒱 ∘ 𝒲) is tractable. 
      
      **Question**. Suppose 𝒱 has one of the properties in the list and 𝒲 has another.  Is every finite member of 𝖧(𝒱 ∘ 𝒲) is tractable?

    Maltsev term
      A **Maltsev term** is ternary term :math:`t` that satisfies the identities :math:`t(x, y, y) ≈ x ≈ t(y, y, x)`.
 
      One of the first theorems of universal algebra is the following famous result of Maltsev :cite:`Maltsev:1954`:
      
      **Theorem**.  If 𝒱 is a variety of algebras, then the following are equivalent:
     
        #. 𝒱 is :term:`congruence-permutable`;
        #. :math:`𝔽_𝒱^(3)` is congruence-permutable;
        #. 𝒱 has a :term:`Maltsev term`; i.e., there exists a term :math:`t`,
 
           .. math:: 𝒱 ⊧ t(x, y, y) ≈ x ≈ t(y, y, x).

      As Bergman puts it in :cite:`Bergman:2012`, the theorem above "initiated the study of congruence-permutable varieties. Besides providing one of the most important tools in universal algebra, it is also one of its most beautiful results, linking the algebraic and logical sides of the subject."

    metric space
      A **metric space** is a pair :math:`(X, d)` where :math:`X` is a set and :math:`d: X × X → ℝ` is a **metric** (or **distance function**), that is, a function satisfying the following conditions for all :math:`x, y, z ∈ X`:
 
      #. :math:`d(x, y) ≥ 0`
      #. :math:`d(x,y) = 0` if and only if :math:`x = y`
      #. (symmetry) :math:`d(x, y) = d(y, x)` 
      #. (triangle inequality) :math:`d(x, z) ≤ d(x, y)+d(y, z)`.
 
    middle linear map
      If :math:`B_r` and :math:`_rC` are modules over a ring :math:`R`, and :math:`A` is an abelian group, then a **middle linear** map from :math:`B × C` to :math:`A` is a function :math:`f: B × C → A` such that for all :math:`b, b_1, b_2 ∈ B` and :math:`c, c_1, c_2 ∈ C` and :math:`r ∈ R`:
 
      .. math:: f(b_1 + b_2, c) &= f(b_1,c) + f(b_2,c)\\
                f(b, c_1 + c_2) &= f(b,c_1) + f(b,c_2)\\
                       f(br, c) &= f(b,rc)
 
    minimal absorbing subalgebra
      We call 𝐁 a **minimal absorbing subalgebra** of 𝐀, and we write 𝐁 ◁◁ 𝐀, just in case 𝐁 is an absorbing subalgebra of 𝐀 and 𝐁 is minimal (with respect to set inclusion of universes) among the absorbing subalgebras of 𝐀.
 
    module
      Let :math:`R` be a :term:`ring` with unit. A **left unitary** :math:`R`-**module** (or simply :math:`R`-**module**) is an algebra :math:`⟨M, \{0, -, +\} ∪ \{f_r : r∈ R\}⟩` with an :term:`abelian group` :term:`reduct` :math:`⟨M, \{0, -, +\}⟩` and unary operations :math:`\{f_r : r ∈ R\}` that satisfy the following: :math:`∀ r, s ∈ R`, :math:`∀ x, y ∈ M`,
 
      #. :math:`f_r(x + y)  = f_r(x) + f_r(y)`
      #. :math:`f_{r+s}(x) = f_r(x) + f_s(x)`
      #. :math:`f_r(f_s(x)) = f_{rs}(x)`
      #. :math:`f_1(x) = x`.
 
    monoid
      If :math:`⟨M, ⋅⟩` is a :term:`semigroup` and if there exists :math:`e ∈ M` that is a multiplicative identity (i.e., :math:`∀ m ∈ M`, :math:`e ⋅ m = m = m ⋅ e`), then :math:`⟨M, \{e, ⋅\}⟩` is called a **monoid**.
 
    monoid homomorphism
      Given :term:`monoids <monoid>` :math:`𝐌_1 = (M_1, e_1, ⋆)` and :math:`𝐌_2 = (M_2, e_2, ∗)` we say that a function :math:`f : M_1 → M_2` is a **monoid homomorphism** from :math:`𝐌_1` to :math:`𝐌_2` provided :math:`f` preserves the :term:`nullary <nullary operation>` (identity) and :term:`binary operations <binary operation>`; that is, :math:`f(e_1) = e_2` and :math:`f (x ⋆ y) = f(x) ∗ f(y)` for all :math:`x, y ∈ M_1`.
 
    monomorphism
      A :term:`morphism` :math:`f: A → B` is called a **monomorphism** if for every object :math:`X` and every pair :math:`h, h' : X → A` of morphisms, :math:`f ∘ h = f ∘ h'` implies :math:`h = h'`. When :math:`f` is a monomorphism we often say :math:`f` is "mono" and write :math:`f: A ↣ B`.
 
    monotone function
      Given :term:`posets <poset>` :math:`⟨A, ≤ᴬ⟩` and :math:`(B, ≤ᴮ)` we say that a function :math:`f: A → B` is **monotone** from :math:`⟨A, ≤ᴬ⟩` to :math:`⟨B, ≤ᴮ ⟩` when for any :math:`x, y ∈ A` we have that :math:`x ≤ᴬ y` implies that :math:`f(x) ≤ᴮ f(y)`.
      
      See also: :term:`monotone increasing function`
 
    monotone increasing function
      A real- or extended real-valued function :math:`f` deifned on :math:`ℝ` is called **monotone increasing** (or **monotonically increasing**) on the interval :math:`[a,b] ⊆ ℝ` if :math:`a≤ x < y ≤ b` implies :math:`f(x) ≤ f(y)`.
      
      See also: :term:`monotone function`
 
    morphism
      If :math:`𝔸 = ⟨A, F^𝔸⟩` and :math:`𝔹 = ⟨B, F^𝔹⟩` are :term:`algebraic structures <algebraic structure>` in the :term:`signature` :math:`σ = (F, ρ)`, then a **morphism** (or **homomorphism**) :math:`h: 𝔸 → 𝔹` is a function from :math:`A` to :math:`B` that preserves (or commutes with) all operations; that is, for all :math:`f∈ F`, for all :math:`a_1, \dots, a_{ρ f} ∈ A`,
 
      .. math:: f^𝔹 (h\,a_1, \dots, h\,a_{ρ f}) = h f^𝔸(a_1, \dots, a_{ρ f}).
 
    multiplicative inverse
      Let :math:`𝔸 = ⟨ A, e, ∘, \dots ⟩` be an algebra in a signature with a nullary "identity" operation :math:`e: () → A` and a binary "multiplication" operation :math:`∘: A × A → A`. Then the element :math:`b ∈ A` is a **multiplicative inverse** of :math:`a ∈ A` provided :math:`a ∘ b = e = b ∘ a`.
 
    natural isomorphism
      An isomorphism in a functor category is referred to as a **natural isomorphism**.
      
    natural transformation
      Given :term:`functors <functor>` :math:`F, G : \mathcal C → \mathcal D`, a **natural transformation** :math:`α : F ⇒ G` is a family :math:`\{α_A : A ∈ \mathcal C_{\mathrm{obj}}\}` of morphisms in :math:`\mathcal D` indexed by the objects of :math:`\mathcal C` such that, for each :math:`A ∈ \mathcal C_{\mathrm{obj}}`, the map :math:`\alpha_A` is a morphism from :math:`FA` to :math:`GA` satisfying the *naturality condition*, :math:`Gf ∘ α_A = α_B ∘ Ff`, for each :math:`f : A → B` in :math:`\mathcal C_{\mathrm{mor}}`. We shall write :math:`α : F ⇒ G : \mathcal C → \mathcal D` to indicate that α is a natural transformation from :math:`F` to :math:`G`, where :math:`F, G : \mathcal C → \mathcal D`.
 
    naturally isomorphic
      If there is a natural isomorphism between the functors :math:`F` and :math:`G`, then we call :math:`F` and :math:`G` **naturally isomorphic**.
 
    near unanimity term
      An idempotent term w(x₁, ..., xₖ) satisfying w(y,x,...,x) ≈ w(x,y,x,...,x) ≈ ... ≈ w(x,...,x,y) ≈ x is called a **near unanimity** (or **NU**) term.

    nullary operation
      An operation :math:`f` on a set :math:`A` is called **nullary** if the arity of :math:`f` is 0; that is, :math:`f: () → A`; equialently, :math:`f` takes no arguments, so is simply a (constant) element of :math:`A`.
 
    ω-chain
      Let :math:`⟨ X, ≤ ⟩` be a preordered set. An ω-**chain** is an enumerable :term:`chain`; that is, a :term:`chain` the elements that can be indexed by the natural numbers.
 
    ω-chain cocomplete
      A :term:`preorder` in which joins of all ω-chains exist is called ω-**chain cocomplete**.
 
    ω-chain cocomplete poset
      an :term:`antisymmetric` :term:`ω-chain cocomplete` :term:`preorder`.
 
    opposite category
      Given a category 𝒞 the **opposite** (or **dual**) **category** :math:`𝒞^{\mathrm{op}}` has the same objects as 𝒞 and whenever f: A → B is a morphism in 𝒞 we define f: B → A to be a morphism in :math:`𝒞^{\mathrm{op}}`.
 
    order ideal
      A subset I of a partially ordered set (P, ≤) is a **order ideal** (or just **ideal**) if the following conditions hold:
 
        * I is non-empty.
        * ∀ x, y ∈ I, x ∨ y ∈ I.
        * ∀ x ∈ I, ∀ y ∈ P, x ≥ y → y ∈ I.
 
      An ideal is a **proper ideal** if it is not the whole of P. (Some authors add this last condition to the definition of an order ideal.)
 
      The dual notion is called a :term:`filter`.
 
    parallel morphisms
      Morphisms f, g: A → B are called **parallel morphisms** just in case dom f = dom g and cod f = cod g.
 
    partial function
      A **partial function** from A to B is a total function on some (potentially proper) subset, dom f, of A.
 
    partial order
      See :term:`partial order`.
 
    partial ordering
      A **partial ordering** (or "partial order") is an :term:`antisymmetric` :term:`preorder`.
      
    partially ordered set
      A **partially ordered set** (or "poset") ⟨X, R⟩ is a set X along with a :term:`partial ordering` R defined on X.
 
    permuting relations
      Binary relations α and β are said to **permute** if α ∘ β = β ∘ α.  If α and β are permuting congruences, then α ∘ β = α ∨ β in the congruence lattice.

    point
      Given a category with an initial object :math:`\mathbf{1}` and another object :math:`A`, the morphisms with domain :math:`\mathbf{1}` and codomain :math:`A` are called the **points** or **global elements** of :math:`A`.
 
    pointwise limit
      Let :math:`f_n: X → [-∞, ∞]` for each :math:`n∈ ℕ`. If the limit :math:`f(x) = \lim_{n→∞} f_n(x)` exist at every :math:`x ∈ X`, then we call :math:`f: X → ℝ` the **pointwise limit** of the sequence :math:`\{f_n\}`. 
 
    polymorphic function
      a function that operates in the "same way" independently of the object parameter.
 
    polymorphism
      Let :math:`𝔸 = ⟨ A, R₁^𝔸, \dots)` and :math:`𝔹 = ⟨ A, R₁^𝔹, \dots)` be relational structures of the same signature. A k-ary (total) function :math:`f: A^k → B` is called a **polymorphism** of (𝔸, 𝔹) if it is :term:`compatible` with every pair :math:`(R_i^𝔸, R_i^𝔹)`, that is, for all tuples :math:`𝐫 ∈ R_i^𝔸`, the tuple :math:`f 𝐫`  is in :math:`R_i^𝔹`.
 
      We denote the set of all polymorphisms of (𝔸, 𝔹) by Poly(𝔸, 𝔹).
 
    poset
      A **poset** :math:`⟨X, ⊑⟩` consists of a set :math:`X` and an :term:`antisymmetric` :term:`preorder` :math:`⊑` on :math:`X`.
 
    power set operator
      The **powerset operator** :math:`𝒫` maps a class :math:`X` to the class :math:`𝒫 (X)` of all subsets of :math:`X`.
 
    powerset functor
      The **(covariant) powerset functor** is a :term:`functor` :math:`P: \mathbf{Set} → \mathbf{Set}` such that for each :term:`morphism` :math:`f: A → B` the morphism :math:`P f : 𝒫(A) → 𝒫(B)` is given by :math:`P f(S) = \{f(x): x ∈ S\}` for each :math:`S ⊆ A`.
 
    preorder
      A **preorder** on a set :math:`X` is a :term:`reflexive` and :term:`transitive` subset of :math:`X × X`.
 
    preserves
      See :term:`respects`.
 
    product
      Given two objects :math:`A` and :math:`B` a **product** of :math:`A` and :math:`B` is defined to be an object, :math:`A × B`, along with :term:`morphisms <morphism>` :math:`π_1: A × B → A` and :math:`π_2: A × B → B` such that for every object :math:`X` and all morphisms :math:`f: X → A` and :math:`g: X → B` there exists a unique morphism :math:`⟨f,g⟩: X → A × B` such that :math:`p_1 ∘ ⟨f,g⟩ = f` and :math:`p_2 ∘ ⟨f,g⟩ = g`.
 
    projection operation
      The :math:`i`**-th** :math:`k`**-ary projection operation on** :math:`A` is denoted by :math:`π^k_i: (k → A) → A` and defined for each :math:`k`-tuple :math:`a: k → A` by :math:`π^k_i \, a  = a\, i`. 

    projection operator
      If :math:`σ: k → n` is a :math:`k`-tuple of numbers in the set :math:`n = \{0, 1, \dots, n-1\}`, then we can compose an :math:`n`-tuple :math:`a ∈ ∏_{0≤i<n} A_i` with :math:`σ` yielding :math:`a ∘ σ ∈ ∏_{0≤i<k} A_{σ\, i}`.
 
      The result is a :math:`k`-tuple whose :math:`i`-th component is :math:`(a ∘ σ)(i) = a(σ(i))`.
 
      If :math:`σ` happens to be one-to-one, then we call the following a **projection operator**:
 
      .. math:: \mathrm{Proj}\, σ: ∏_{0≤i< n} A_i → ∏_{0≤i<k} A_{σ\, i};  \ \ a ↦ a ∘ σ.
 
      That is, for :math:`a ∈ ∏_{0≤i<n} A_i` we define :math:`\mathrm{Proj}\,σ\, a = a ∘ σ`.
 
    quasivariety
      A **quasivariety** is a class K of algebras of the same signature satisfying any of the following equivalent conditions:
 
        #. K is a :term:`pseudoelementary class` closed under subalgebra and :term:`product`.
 
        #. K is the class of all :term:`models <model>` of a set of :term:`quasiidentities <quasiidentity>`.
 
        #. K contains a trivial algebra and is closed under isomorphism, subalgebra, and :term:`reduced product`.
 
        #. K contains a trivial algebra and is closed under isomorphism, subalgebra, product, and :term:`ultraproduct`.
 
    quotient
      If :math:`R` is an :term:`equivalence relation` on :math:`A`, then the **quotient** of :math:`A` modulo :math:`R` is denoted by :math:`A/R` and is defined to be the collection :math:`\{ a/R ∣ a ∈ A \}` of :term:`equivalence classes <equivalence class>` of :math:`R`.
 
    reduced product
      Let :math:`I` be an index set, and let :math:`𝕄_i` be a structure for each :math:`i ∈ I` (all of the same signature). Let :math:`F` be a :term:`filter` on :math:`I`.
      
      Define the equivalence relation ~ on the :term:`product` structure :math:`𝐌 := ∏_{i∈ I}𝕄_i` as follows: ∀ 𝐚, 𝐛 ∈ 𝐌, 
 
      .. math:: 𝐚 ∼ 𝐛 \ ⟺ \ \{i ∈ I : 𝐚 i = 𝐛 i\} ∈ F.
 
      The **reduced product** of 𝐌 over :math:`F` is the quotient 𝐌/~, which is sometimes denoted by
 
      .. math:: ∏_{i∈ I} 𝕄_i/F.
 
    reduct
      Given two :term:`algebras <algebraic structure>` :math:`𝔸` and :math:`𝔹`, we say that :math:`𝔹` is a **reduct** of :math:`𝔸` if both algebras have the same universe and :math:`𝔹` can be obtained from :math:`𝔸` by removing  operations.
 
    reflexive
      A binary relation :math:`R` on a set :math:`X` is called **reflexive** provided :math:`∀ x ∈ X, \ x \mathrel{R} x`.
 
    relation
      Given sets :math:`A` and :math:`B`, a **relation** from :math:`A` to :math:`B` is a subset of :math:`A × B`.
 
    relational product
      Given relations :math:`R : A → B` and :math:`S : B → C` we denote and define the **relational product** (or **composition**) of :math:`S` and :math:`R` to be :math:`S ∘ R = \{(a,c) : (∃ b ∈ B) a \mathrel{R} b ∧ b \mathrel{S} c \}`.
 
    relational signature
      A **relational signature** (or **signature** for :term:`relational structures <relational structure>`) is a pair :math:`σ = (R, ρ)` consisting of a collection :math:`R` of *relation symbols* and an :term:`arity` function :math:`ρ : R → N` that maps each operation symbol to its arity; :math:`N` denotes the arity type (which is often but not always ℕ).
 
    relational structure
      A relational structure :math:`𝔸 = ⟨A, ℛ⟩` is a set :math:`A` together with a collection :math:`ℛ` of relations on :math:`A`.
 
    relational structure homomorphism
      Let :math:`σ = (ℛ, ρ)` be a :term:`signature` for :term:`relational structures <relational structure>`.  Let :math:`𝔸 = ⟨A, ℛ^𝔸⟩` and :math:`𝔹 = ⟨B, ℛ^𝔹⟩` be relational structures in the signature σ. A function :math:`h: A → B` that "respects" or "preserves" the relations in the following sense is called a (relational structure) **homomorphism**: :math:`∀ R ∈ ℛ`, if :math:`(a_0, \dots, a_{n-1}) ∈ R^𝔸`, then :math:`(b_0, \dots, b_{n-1}) ∈ R^𝔹`.
 
    respects
      Given a function :math:`f: α → α`, we say that :math:`f` **respects** (or **preserves**) the binary relation :math:`R ⊆ α × α`, and we write :math:`f ⊧ R`, just in case :math:`∀ x, y :α \ (x \mathrel R y \ → \ f x \mathrel R f y)`.
        
      (The symbol ⊧ is produced by typing ``\models``.)
 
      If :math:`f: (β → α) → α` is a :math:`β`-ary operation on :math:`α`, we can extend the definition of ":math:`f` respects :math:`R`" in the obvious way.
      
      First, for every pair :math:`u : β → α` and :math:`v : β → α` (:math:`β`-tuples of :math:`α`), we say that :math:`(u, v)` "belongs to" :math:`R ⊆ α × α` provided
      
      .. math:: ∀ i: β \ ui \mathrel R vi
      
      Then we say :math:`f:  (β → α) → α` **respects** (or **preserves**) the binary relation :math:`R ⊆ α × α`, and we write :math:`f ⊧ R`, just in case :math:`∀ u, v, \ [(∀ i: β, \ u i \mathrel R v i) \ → \ f u \mathrel R f v]`.
        
    retract
      An object :math:`A` in a category is called a **retract** of an object :math:`B` if there are morphisms :math:`i: A → B` and :math:`r: B → A` such that :math:`r ∘ i = id_A`. In this case :math:`r` is called a **retraction** of :math:`B` onto :math:`A`.

    retraction
      See: :term:`retract`

    right module
      A **right module** :math:`M` over a :term:`ring` :math:`R` is...
 
    ring
      An algebra :math:`⟨R, \{0, -, +, ⋅\}⟩` is called a **ring** just in case the following conditions hold:
 
      #. the reduct :math:`⟨R, \{0, -,+\}⟩` is an abelian group,
      #. the reduct :math:`⟨R, ⋅ ⟩` is a semigroup, and
      #. "multiplication" :math:`⋅` distributes over "addition" :math:`+`; that is, :math:`∀ a, b, c ∈ R`, :math:`a ⋅ (b+c) = a ⋅ b + a ⋅ c` and :math:`(a+b)⋅ c = a ⋅ c + b ⋅ c`.
 
    ring of sets
      A nonempty collection :math:`R` of subsets of a set :math:`X` is said to be a **ring** if :math:`A, B ∈ R` implies :math:`A ∪ B ∈ R` and :math:`A-B ∈ R`.
 
    ring with unity
      A **ring with unity** (or **unital ring**) is an algebra :math:`⟨R, \{0, 1, -, +, ⋅\}⟩` with a ring :term:`reduct` :math:`⟨R, \{0, -, +, ⋅\}⟩` and a *multiplicative identity* :math:`1 ∈ R`; that is :math:`∀ r ∈ R`, :math:`r ⋅ 1 = r = 1 ⋅ r`.
 
    scope
      If :math:`k, n ∈ ℕ`, :math:`𝒜 = (A_0, A_1, \dots, A_{n-1})` is a list of sets, and :math:`σ: 𝐤 → 𝐧` is a :math:`k`-tuple of elements from :math:`𝐧:=\{0,1,\dots, n-1\}`, then a relation :math:`R` over 𝒜 with scope σ is a subset of the Cartesian product :math:`∏_{i:𝐤}A_{σ(i)} := A_{σ(0)} × A_{σ(1)} × \cdots × A_{σ(k-1)}`.
 
    section
      For a set :math:`E ⊆ X × Y`, the **x-section** of :math:`E` at the point :math:`t` is defined as follows:
 
      .. math:: G_t = \{y ∈ ℝ: (x,y) ∈ E \text{ and } x=t\}.
 
    semidistributive
      A lattice is called **meet-semidistributive** if it satisfies the quasiidentity
      
      .. math:: x ∧ y ≈ x ∧ z \ ⟹ \ x ∧ y ≈ x ∧ (y ∨ z).
 
      A lattice is called **join-semidistributive** if it satisfies the quasiidentity
      
      .. math:: x ∨ y ≈ x ∨ z \ ⟹ \ x ∨ y ≈ x ∨ (y ∧ z).
 
      A **semidistributive lattice** is one that is either meet- or join-semidistributive.
 
      We denote the class of meet-semidistributive lattices by SD∧, but we also use SD∧ as an adjective and write "𝐿 is SD∧" to mean "𝐿 is meet-semidistributive," i.e., 𝐿 ∈ SD∧.
      
      A variety 𝒱 is called **meet-semidistributive** (or SD∧) if every algebra in 𝒱 has a meet-semidistributive congruence lattice.
      
      Idempotent SD∧ varieties are known to be Taylor :cite:`Hobby:1988`. In :cite:`Barto:2012a`, Barto and Kozik proved the following: If 𝐀 is a finite idempotent algebra in an SD∧ variety, then CSP(𝐀) is tractable.
 
    semigroup
      A :term:`magma` whose binary operation is associative is called a **semigroup**.  That is, a semigroup is a magma :math:`⟨A, ⋅⟩` whose binary operation satisfies :math:`∀ a, b, c ∈ A`, :math:`(a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)`.
 
    semiring of sets
      A collection :math:`S` of subsets of a nonempty set :math:`X` is called a **semiring** if it satisfies the following properties:
      
      #. :math:`∅ ∈ S`;
      #. :math:`A, B ∈ S \; ⟹ \; A ∩ B ∈ S`;
      #. :math:`A, B ∈ S \; ⟹ \; ∃ C_1, \dots, C_n ∈ S`, :math:`A-B = ⋃_{i=1}^n C_i` and :math:`∀ i≠j, \,C_i ∩ C_j = ∅`.
 
    σ-term
      A **σ-term** is a :term:`term` in the :term:`signature` σ.
 
    signature
      In :term:`model theory`, a **signature** σ = (𝐂, 𝐅, 𝐑, ρ) consists of three (possibly empty) sets 𝐂, 𝐅, and 𝐑---called *constant symbols*, *function symbols*, and *relation symbols*, respectively---along with a function ρ: 𝐂 + 𝐅 + 𝐑 → N that assigns an :term:`arity` to each symbol. Often (but not always) N = ℕ. 
 
      By an **algebraic signature** (or **signature** for :term:`algebraic structures <algebraic structure>`) we mean a pair :math:`σ = (F, ρ)` that consists of a collection :math:`F` of *operation symbols* and an :term:`arity` function :math:`ρ : F → N` that maps each operation symbol to its arity; here, :math:`N` denotes the arity type (which is often, but not always, taken to be ℕ).
 
      A **relational signature** (or **signature** for :term:`relational structures <relational structure>`) is a pair :math:`σ = (R, ρ)` consisting of a collection :math:`R` of *relation symbols* and an :term:`arity` function :math:`ρ : R → N` that maps each operation symbol to its arity; :math:`N` denotes the arity type (which is often but not always ℕ).
 
    simplex category
      See :term:`finite ordinals`.
 
    simple algebra
      An algebra :math:`𝐀` is called **simple** if the only congruences of :math:`𝐀` are the trivial ones, :math:`0_𝐀 := \{(a,a) : a ∈ A\}` and :math:`𝐀 × 𝐀:=\{(x,y) : x,y ∈ A\}`.
 
    small category
      A category is called **small** if its collections of objects and morphisms are sets.
 
    source vertex
      Given a directed graph :math:`𝐆 = (V,E)` and an edge :math:`e=(v_1,v_2) ∈ E`, we refer to :math:`v_1` as the **source vertex** of :math:`e`.
 
    subalgebra
      Suppose :math:`𝔸 = ⟨A, F^𝔸⟩` is an algebra. If :math:`B ≠ ∅` is a :term:`subuniverse` of 𝔸, and if we let :math:`F^𝔹 = \{ f ↾ B : f ∈ F^𝔸 \}`, then :math:`𝔹 = ⟨ B, F^𝔹 ⟩` is an algebra, called a **subalgebra** of 𝔸.
 
    subdcpo
      If :math:`X` is a :term:`dcpo` then the subset :math:`A ⊆ X` is a **subdcpo** of :math:`X` if every directed subset :math:`D ⊆ A` satisfies :math:`⋁_X D ∈ A`.
 
    subdirect product
      Let :math:`σ  = (F, ρ)` be an :term:`algebraic signature`, let :math:`𝔸_i = ⟨A_i, F^{𝔸_i}⟩` be a σ-algebras, one for each :math:`i ∈ 𝐧 := \{0, 1, \dots, n-1\}`, and let :math:`𝐀 := ∏_{i:𝐧}𝔸_i` be the product σ-algebra. If :math:`R` is :term:`compatible` with 𝐀 and if the projection of :math:`R` onto each factor is surjective, then :math:`R` is called a **subdirect product** of the algebras in the list :math:`(𝔸_{σ(0)}, 𝔸_{σ(1)}, \dots, 𝔸_{σ(k-1)})`; we denote this situation by writing :math:`ℝ ≤_{sd} ∏_{j:𝐤} 𝔸_{σ(j)}`
 
    subuniverse
      Suppose :math:`𝔸 = ⟨A, F^𝔸⟩` is an algebra. If a subset :math:`B ⊆ A` is closed under :math:`F^𝔸`, then we call :math:`B` a **subuniverse** of :math:`𝔸`.
 
    symmetric
      A binary relation :math:`R` on a set :math:`X` is called **symmetric** provided :math:`∀ x, y ∈ X \ (x \mathrel{R} y \ → \ y \mathrel{R} x)`;
 
    target vertex
      Given a directed graph :math:`𝐆 = (V,E)` and an edge :math:`e=(v_1,v_2) ∈ E`, we refer to :math:`v_2` as the **target vertex** of :math:`e`.
 
    Taylor term
      An :term:`idempotent <idempotent operation>` term :math:`t` that satisfies for each :math:`i ∈ \{1,2,\dots, n\}`
 
      .. math:: t(∗, \cdots, ∗, x, ∗, \cdots, ∗) ≈ t(∗, \cdots, ∗, y, ∗, \cdots, ∗),
 
      where distinct variables :math:`x, y` appear in the :math:`i`-th position on either side of the identity is called a **Taylor term**.
 
    Taylor variety
      Walter Taylor proved in :cite:`Taylor:1977` that a variety 𝒱 satisfies some nontrivial idempotent :term:`Maltsev condition` if and only if it satisfies one of the following form: for some :math:`n`, 𝒱 has an idempotent :math:`n`-ary term  :math:`t` such that for each :math:`i∈ \{1, \dots, 2\}` there is an identity of the form
      
      .. math:: t(∗, \cdots, ∗, x, ∗, \cdots, ∗) ≈ t(∗, \cdots, ∗, y, ∗, \cdots, ∗),
 
      true in 𝒱 where distinct variables :math:`x, y` appear in the :math:`i`-th position on either side of the identity.  Such a term :math:`t` is now commonly called a :term:`Taylor term`.
 
    term
      The collection 𝒯 of **terms** in the :term:`signature` σ (or **σ-term**) is defined recursively as follows:
 
        * All *variables* are terms.
        * All *constant symbols* are terms.
        * If :math:`t: \{0, \dots, (n-1)\} → 𝒯` is an :math:`n`-tuple of terms and :math:`f ∈ 𝐅` is a function symbol of arity :math:`ρ f = n`, then :math:`f t` is a term.
        * :math:`t` is a terms if it can be obtained in finitely many steps from some combination of the three items above.
 
    term algebra
      Consider the collection :math:`T_σ (X)` of :term:`terms <term>` in the signature σ. We impose upon :math:`T_σ (X)` an algebraic structure, which we denote by 𝔉. We call 𝔉 the **term algebra in the signature** :math:`σ` **over** :math:`X` (or, the :math:`σ`-**term algebra over** :math:`X`); it is constructed as follows:

      For every basic operation symbol :math:`f ∈ F` let :math:`f^𝔉` be the operation on :math:`T_σ (X)` that maps each tuple :math:`s: ρ f → T_σ (X)` to the formal term :math:`f\,s`; define 𝔉 to be the algebra with universe :math:`T_σ (X)` and basic operations :math:`\{f^𝔉 | f ∈ F\}`.

    term-equivalent
      The varieties 𝒱 and 𝒲 are called **term-equivalent** if there are interpretations :math:`D` of 𝒱 in 𝒲 and :math:`E` of 𝒲 in 𝒱 such that for every 𝐀 ∈ 𝒱 and 𝐁 ∈ 𝒲 we have :math:`𝐀^{ED} = 𝐀` and :math:`𝐁^{DE} = 𝐁`.

    terminal object
      An object :math:`\mathbf{1}` is called a **terminal** (or **bound**) **object** if for every object :math:`A` in the same category there exists a unique morphism :math:`⟨\ ⟩_A: A → \mathbf{1}`.
 
    ternary operation
      An operation :math:`f` on a set :math:`A` is called **ternary** if the arity of :math:`f` is 3; that is, :math:`f: A × A × A → A` (or, in curried form, :math:`f: A → A → A → A`).
 
    total function
      Given sets :math:`A` and :math:`B`, a **total function** :math:`f` from :math:`A` to :math:`B` is what we typically mean by a "function" from :math:`A` to :math:`B`.
 
    total order
      A **total order** relation :math:`R` on a set :math:`X` is a partial order on :math:`X` satisfying :math:`∀ x, y ∈ X \ (x ≤ y \ ⋁ \ y ≤ x)`.
 
    transitive
      A binary relation :math:`R` on a set :math:`X` is called **transitive** provided :math:`∀ x, y, z ∈ X \ (x \mathrel{R} y ∧ y \mathrel{R} z\ → \ x \mathrel{R} z)`.
 
    trivial algebra
      A **trivial algebra** is an algebra with just one element in its universe.
 
    trivial structure
      A **trivial structure** is a structure with just one element in its universe.
 
    ultrafilter
      An **ultrafilter** on a :term:`poset` P is a maximal :term:`filter` on P, that is, a proper filter on P that will become improper if it is enlarged.
 
    ultraproduct
      Let :math:`I` be an index set, and let :math:`𝕄_i` be a structure for each :math:`i ∈ I` (all of the same signature). Let :math:`U` be an :term:`ultrafilter` on :math:`I`.
      
      Define the equivalence relation ~ on the :term:`product` structure :math:`𝐌 := ∏_{i∈ I}𝕄_i` as follows: ∀ 𝐚, 𝐛 ∈ 𝐌, 
 
      .. math:: 𝐚 ∼ 𝐛 \ ⟺ \ \{i ∈ I : 𝐚 i = 𝐛 i\} ∈ U.
 
      The **ultraproduct** of 𝐌 over :math:`U` is the quotient 𝐌/~, which is sometimes denoted by
   
      (The usual choice is for I to be infinite and U to contain all cofinite subsets of I; otherwise, the ultrafilter is principal, and the ultraproduct is isomorphic to one of the factors.)
    
      More generally, the construction above can be carried out whenever :math:`U` is a filter on :math:`I` and the resulting :math:`∏_{i∈ I}𝕄_i/U` is called a :term:`reduced product`.
 
    unary operation
      An operation :math:`f` on a set :math:`A` is called **unary** if the arity of :math:`f` is 1; that is, :math:`f: A → A`.
 
    underlying set functor
      The **underlying set functor** of :math:`𝐌` is denoted by :math:`U(𝐌)`, or by :math:`|𝐌|`; it returns the *universe* of the structure :math:`𝐌`, and for each morphism :math:`f`, :math:`Uf` (or :math:`|f|`) is :math:`f` viewed simply as a function on sets.
 
    unit
      If :math:`⟨R, \{0, 1, -, +, ⋅\}⟩` is a unital ring, an element :math:`r ∈ R` is called a **unit** if it has a multiplicative inverse, that is, there exists :math:`s ∈ R` with :math:`r ⋅ s = 1 = s ⋅ r`.  (We usually denote such an :math:`s` by :math:`r^{-1}`.)
 
    unital ring
      See :term:`ring with unity`.
 
    unique morphism property
      See :term:`universal property`.
 
    universal image functor
      the functor :math:`∀ f : P(A) → P(B)` defined by :math:`∀ f (X) = \{y ∈ B : f^{-1}(\{y\}) \subseteq  X\}`, for :math:`X ∈ P(A)`.
 
    universal mapping property
      Let :math:`η_A : A → |𝔸^*|` be the function that maps :math:`a ∈ A` to the "one-letter word" :math:`a ∈ A^*`. The :term:`functors <functor>` :math:`K (= \ ^∗)` and :math:`U (= |\ |)` are related by the **universal mapping property** of monoids, which says that for every :term:`monoid` :math:`𝐌` and every function :math:`f : A → U 𝐌` there exists a unique :term:`morphism` :math:`f̂ : KA → 𝐌` such that :math:`f = f̂ ∘ η`.
 
    universal property
      The **unique morphism property** of the :term:`initial object` in a category is what we refer to as a **universal property,** and we say that the :term:`free object` in a category :math:`𝒞` is "universal" for the category :math:`𝒞`.
 
    universe
      In :term:`type theory`, everything has a type---even a type has a type.  If ``α`` is a type, then ``α``'s type is ``Type u`` for some **universe** ``u``.  More accurately, the ``u`` here is actually a variable and whatever (natural number) value it takes on will be the universe *level* of the type ``α``.
   
      In universal algebra, the **universe** of an :term:`algebra <algebraic structure>` is the set on which an algebra is defined; e.g., the universe of the algebra :math:`𝔸 = ⟨A, F^𝔸⟩` is :math:`A`.  (N.B. we sometimes use the word **carrier** to mean universe in this sense, which can be helpful when we wish to avoid confusion with the universe levels in `type theory`_.)
 
    valuation
      The `absolute value`_ for real numbers can generalised to an arbitrary field by considering the four fundamental properties of absolute value. Thus, a real-valued function :math:`ν` on a field :math:`F` is called a **valuation** if it satisfies the following four axioms:
 
      #. :math:`ν(a)≥ 0` (non-negativity); 
      #. :math:`ν(a)=0 \; ⟺ \; a= \mathbf 0` (positive-definiteness); 	
      #. :math:`ν(ab)=ν(a)ν(b)` (multiplicativity);
      #. :math:`ν(a+b)≤ ν(a)+v(b)` (:term:`subadditivity <countably subadditive>`). 	
 
      Here :math:`\mathbf 0` denotes the additive identity element of :math:`F`. It follows from properties 2 and 3 that :math:`ν(1) = \mathbf 1`, where :math:`\mathbf 1` denotes the multiplicative identity element of :math:`F`. The real and complex absolute values are examples of valuations.
 
    variety
      A **variety** (or **equational class**) of structures in the language :math:`𝐿` is one that can be axiomatized by a set of equations in :math:`𝐿`.
 
    vector space
      If :math:`F` is a :term:`field`, then an :math:`F`-:term:`module` is called a **vector space** over :math:`F`.

    weak near unanimity term
      An idempotent term w(x₁, ..., xₖ) satisfying w(y,x,...,x) ≈ w(x,y,x,...,x) ≈ ... ≈ w(x,...,x,y) is called a **weak near unanimity** (or **WNU**) term.


Glossary: topology and analysis
-------------------------------

.. glossary::

   Banach space
     A **Banach space** is a :term:`normed linear space` :math:`(X, \|\,⋅\,\|)` such that :math:`X` is :term:`complete <complete set>` in the metric defined by its norm. (That is, each Cauchy sequence in :math:`(X, \|\,⋅\,\|)` converges to a point in :math:`X`.)

   bounded linear functional
     Let :math:`X` be a :term:`normed linear space` over the :term:`field` :math:`F`.  A **bounded linear functional** on :math:`X` is a :term:`bounded linear transformation` with codomain :math:`F`.
      
     We denote by :math:`𝔅(X,F)` the collection of all bounded linear functionals on :math:`X`.

   bounded linear transformation
     Let :math:`X` and :math:`Y` be two :term:`normed linear spaces <normed linear space>`. A :term:`linear transformation` :math:`T: X → Y` is called **bounded** if there exists :math:`C > 0` such that

     .. math:: \|Tx\| ≤ C \|x\| \; \text{ for all } x ∈ X.
    
     We denote the space of all bounded linear transformations from :math:`X` to :math:`Y` by :math:`𝔅(X,Y)`.
      
   bounded set
     A set :math:`E` in a metric space is called **bounded** if it has finite diameter, :math:`\mathrm{diam} E < ∞`.

   Cauchy sequence
     A sequence :math:`\{x_n\}` in a :term:`metric space` :math:`(X, d)` is called a **Cauchy sequence** if for all :math:`\epsilon >0` there exists :math:`N>0` such that :math:`d(x_m, x_n) < \epsilon` for all :math:`n, m \geq N`.

   cofinite topology
     If :math:`X` is an infinite set, then :math:`\{V ∈ X ∣ V = ∅ \text{ or } V^c \text{ is finite}\}` is a topology on :math:`X`, called the **cofinite topology**.

   compact set
     If :math:`(X,d)` is a :term:`metric space`, then a subset :math:`E ⊆ X` is compact iff every open :term:`covering` reduces to a finite subcover.

     If :math:`(X,τ)` is a :term:`topological space` then a set :math:`A ⊆ X` is called **compact** if every open :term:`covering` :math:`\{V_i ∣ i ∈ I\} ⊆ τ` of :math:`A` has a finite subcover. That is, 

     .. math:: A ⊆ ⋃_{i∈ I} V_i \quad \text{ implies } \quad A ⊆ ⋃_{j=1}^n V_{i_j}

     for some finite subcollection :math:`\{V_{i_j} ∣ j = 1, \dots, n\} ⊆ \{V_i ∣ i∈ I\}`.

   complete measure
     A :term:`measure` :math:`μ` on a :term:`measurable space` :math:`(X, 𝔐)` is called **complete** if all subsets of sets of measure 0 are :term:`measurable <measurable set>` (and have measure 0). [1]_

   complete measure space
     If :math:`μ` is a :term:`complete measure` on the :term:`measurable space` :math:`(X, 𝔐)`, then :math:`(X, 𝔐, μ)` is called a **complete measure space**.

   complete metric space
     A :term:`metric space` :math:`(X, d)` is called **complete** if :math:`X` is :term:`complete <complete set>`; that is, each :term:`Cauchy sequence` in :math:`X` converges to a point of :math:`X`.

   complete set
     A subset :math:`C` of a (metric or topological) space :math:`X` is called **complete** if every :term:`Cauchy sequence` in :math:`C` converges to a point in :math:`C`.

   complex measure
     A **complex measure** on a :term:`measurable space` :math:`(X, 𝔐)` is a map :math:`ν: 𝔐 → ℂ` such that :math:`ν ∅ = 0`, and :math:`ν` is :term:`countably additive` over :math:`𝔐`, which means that
     
     .. math:: ν(⋃_j A_j) = ∑_j ν(A_j)
        :label: count-add
         
     whenever :math:`\{A_j\}` is a collection of disjoint sets in :math:`𝔐`.
     
     Moreover, the sum on the right-hand side of :eq:`count-add` converges absolutely.

     Notice, we do not allow a complex measure to take on infinite values. Thus, a :term:`positive measure` is a complex measure only if it is :term:`finite <finite measure>`.

     The range of a complex measure is a subset of :math:`ℂ`, while a positive measure takes values in :math:`[0,∞]`. Thus the positive measures do not form a subclass of the complex measures.

   concentrated
     If there is a set :math:`A ∈ 𝔐` such that for all :math:`E ∈ 𝔐` we have :math:`λ E = λ (A ∩ E)`, then we say that :math:`λ` is **concentrated** on :math:`A`.
    
   conjugate exponents
      If :math:`p` and :math:`q` are positive real numbers such that :math:`p+q = pq` (equivalently, :math:`(1/p) + (1/q) = 1`), then we call :math:`p` and :math:`q` a pair of **conjugate exponents**.
 
      It's clear that conjugate exponents satisfy :math:`1 < p, q < ∞` and that as :math:`p → 1`, :math:`q → ∞` and vice-versa. Thus, :math:`(1, ∞)` is also regarded as a pair of conjugate exponents.
 
   continuous function
     Let :math:`(X, τ_1)` and :math:`(Y, τ_2)` be :term:`topological spaces <topological space>`. A function :math:`f: X → Y` is called **continuous** if :math:`f^{-1}(S) ∈ τ_1` for every :math:`S ∈ τ_2`.
 
     Let :math:`(X, |\;\;|_1)` and :math:`(Y, |\;\;|_2)` be :term:`metric spaces <metric space>`. A function :math:`f: X → Y` is called **continuous** at the point :math:`x_0 ∈ X` if for all :math:`ε >0` there exists :math:`δ > 0` such that

     .. math::  |x - x_0|_1 < δ \, ⟹ \, |f(x) -f(x_0)|_2 < ε.

     A function :math:`f : X → Y` is called **continuous** in :math:`E ⊆ X` if it is continuous at every point of :math:`E`.
     
   covering
     In a metric or topological space :math:`X`, a **covering** of a subset :math:`E ⊆ X` is a collection of subsets :math:`\{V_α\}` of :math:`X` such that :math:`E ⊆ ⋃_α V_α`.  If, in addition, each :math:`V_α` is an open subset of :math:`X`, then we call :math:`\{V_α\}` an **open covering** of :math:`E`.

   dense set
     A set :math:`G` is **dense** in :math:`X` if each :math:`x ∈ X` is a limit point of :math:`G`. Equivalently, the closure of :math:`G` contains :math:`X` (in symbols, :math:`X ⊆ Ḡ`.)

   diameter
     The **diameter** of a set :math:`E` in a metric space :math:`(X, d)` is denoted and defined by :math:`\mathrm{diam} E = \sup \{d(x, y) : x, y \in E\}`.
     
   discrete topology
     If :math:`X` is a nonempty set, the powerset :math:`𝒫(X)` is a topology on :math:`X` and is called the **discrete topology**.
 
   finite measure
     If :math:`(X, 𝔐, μ)` is a :term:`measure space`, then :math:`μ` is called a **finite measure** provided :math:`μ X < ∞`. 
     
   Hausdorff space
     A :term:`topological space` :math:`(X, τ)` is called a **Hausdorff space** if the topology :term:`separates the points` of :math:`X`.  In other words, distinct points have some disjoint neighborhoods.

   Hilbert space
     A :term:`normed linear space` whose norm arises from an :term:`inner product` is called a **Hilbert space**.

   homeomorphic
     We call a pair :math:`X, Y` of :term:`topological spaces <topological space>` **homeomorphic** if there is a homeomorphism between them.

   homeomorphism
     A :term:`continuous function` from a :term:`topological space` :math:`X` to a topological space :math:`Y` is called a **homeomorphism** provided it is one-to-one and onto, and has a continuous inverse from :math:`Y` to :math:`X`.
  
     Clearly the inverse of a homeomorphism is a homeomorphism and the composition of homeomorphisms, when defined, is a homeomorphism.

   indiscrete topology
     If :math:`X` is a nonempty set, then :math:`\{∅, X\}` is a topology on :math:`X`, called the **trivial** (or **indiscrete**) **topology**.

   ∞-norm
     Let :math:`(X, 𝔐, μ)` be a :term:`measure space`.  The :math:`∞`-**norm relative to** :math:`μ` is defined for each real- or complex-valued function :math:`f` on :math:`X` by
   
     .. math:: \|f\|_∞ := \inf \{a∈ ℝ^∗ ∣ μ\{x : |f(x)| > a\} = 0\} = \inf \{a∈ ℝ^∗ ∣ |f(x)| ≤ a \text{ for } μ-\text{a.e. } x∈ X\},

     where :math:`ℝ^∗ = ℝ ∪ \{-∞, ∞\}` and :math:`\inf ∅ = ∞`.

   integrable
     A real- or complex-valued :math:`μ`-:term:`measurable function` :math:`f` is called :math:`μ`-**integrable** (or **integrable with respect to** :math:`μ`, or just **integrable**) over :math:`X` if :math:`∫_X |f| \, dμ < ∞`.  We let :math:`𝐿_1(X, μ)` (or :math:`𝐿_1(μ)`, or just :math:`𝐿_1`) denote the collection of functions that are :math:`μ`-integrable over :math:`X`.

     When :math:`f∈ 𝐿_1(X, μ)` we define the :term:`integral` of :math:`f` over a measurable set :math:`E ⊆ X` by :math:`∫_E f\, dμ = ∫_E f^+\, dμ - ∫_E f^-\, dμ`.

   integral
     See :term:`𝐿ebesgue integral`.

   interior
     If :math:`X` is a :term:`topological space` and :math:`A ⊆ X`, then the union of all :term:`open sets <open set>` contained in :math:`A` is called the **interior** of :math:`A`.

   isometrically isomorphic
     Two :term:`Hilbert spaces <Hilbert space>` :math:`ℋ_1, ℋ_2` are called **isometrically isomorphic** if there exists a :term:`unitary operator` from :math:`ℋ_1` onto :math:`ℋ_2`.

     In other words, :math:`U: ℋ_1 ↠ ℋ_2` is a surjective :term:`isometry` from :math:`ℋ_1` to :math:`ℋ_2`.

   isometry
     Let :math:`(X, \|\,.\,\|_1)` and :math:`(Y, \|\,.\,\|_2)` be :term:`normed linear spaces <normed linear space>`.  A :term:`linear transformation` :math:`T: X → Y` is called an **isometry** if it preserves norms, that is, :math:`\|Tx\|_2 = \|x\|_1` holds for all :math:`x∈ X`.

   𝐿ebesgue integrable
     A function that is :term:`integrable` with respect to :term:`𝐿ebesgue measure` is called a **𝐿ebesgue integrable** function.

   𝐿ebesgue integral
     Let :math:`(X, 𝔐, μ)` be a :term:`measure space`.  If :math:`E ∈ 𝔐` and :math:`s: X → [0, ∞)` is a :term:`measurable <measurable function>` :term:`simple function` of the form :math:`s = ∑_{i=1}^n α_i χ_{A_i}`, where :math:`α_1, \dots, α_n ∈ ℝ` are the distinct values of :math:`s`, then we denote and define the **𝐿ebesgue integral** of :math:`s` over :math:`E` as follows:
     
     .. math:: ∫_E s\, dμ := ∑_{i=1}^n α_i μ(A_i ∩ E),
     
     where we adopt the convention that :math:`0⋅∞ = 0` (in case, e.g., :math:`α_i = 0` and :math:`μ(A_i ∩ E) = ∞` for some :math:`1≤ i ≤ n`).
     
     If :math:`f: X → [0, ∞]` is a nonnegative extended real-valued measurable function and :math:`E∈ 𝔐`, then we denote and define the **𝐿ebesgue integral** of :math:`f` over :math:`E` with respect to the measure :math:`μ` (or, the **integral** of :math:`f`) as follows:

     .. math:: ∫_E f\, dμ := \sup ∫_E s\, dμ,

     where the supremum is taken over all simple measurable functions :math:`s` such that :math:`0≤ s ≤ f`.

     If :math:`μ` is the only :term:`measure` in context, then we may write :math:`∫_E f` in place of :math:`∫_E f\, dμ`, and :math:`∫ f` in place of :math:`∫_X f`.

   𝐿ebesgue measurable function
     Let :math:`E⊆ ℝ`.  A function :math:`f: E → ℝ` is called **𝐿ebesgue measurable** provided :math:`f^{-1}(G)` is a :term:`𝐿ebesgue measurable set` for every open set :math:`G ⊆ ℝ`.  Equivalently, :math:`f` is 𝐿ebesgue measurable iff the set :math:`f^{-1}((α, ∞))` is 𝐿ebesgue measurable for every :math:`α ∈ ℝ`.

   𝐿ebesgue measurable set
     A set that is :term:`measurable <measurable set>` with respect to :term:`𝐿ebesgue measure` is called a **𝐿ebesgue measurable** set; that is, :math:`E⊆ ℝ` is 𝐿ebesgue measurable iff

     .. math:: m^∗ A = m^∗ (A ∩ E) + m^∗(A ∩ E^c)\; \text{ holds for all } A ⊆ R.

   𝐿ebesgue measure
     Let :math:`ℓ` be the :term:`measure` defined on the :term:`semiring <semiring of sets>` :math:`S := \{[a, b) ∣ a, b ∈ ℝ\}` of bounded intervals by :math:`ℓ[a, b)= b-a` for all :math:`a ≤ b`. Let :math:`ℓ^∗: 𝒫(ℝ) → [0, ∞]` be the :term:`outer measure` generated by :math:`ℓ`.  That is, for :math:`E⊆ ℝ`,
     
     .. math:: ℓ^∗(E) := \inf \{∑_{n=1}^∞ m(I_n) ∣ \{I_n\} ⊆ S \text{ and } E ⊆ ⋃_{n=1}^∞ I_n\}
     
     The measure obtained by restricting :math:`ℓ^∗` to the :term:`measurable subsets <measurable set>` in :math:`𝒫(ℝ)` is called **𝐿ebesgue measure**.
     
     Observe that the :math:`ℓ^∗`-:term:`measurable subsets <measurable set>` in :math:`𝒫(ℝ)` are those :math:`A∈ 𝒫(ℝ)` satisfying

     .. math:: ℓ^∗ E = ℓ^∗(E ∩ A) + ℓ^∗(E ∩ A^c)\; \text{ for all } E ⊆ ℝ.

   𝐿ebesgue null set
     A **𝐿ebesgue null set** is a set of :term:`𝐿ebesgue measure` zero.

   𝐿ebesgue outer measure
     See :term:`𝐿ebesgue measure`

   limit point
     A point :math:`x` is called a **limit point** (or **accumulation point**) of a set :math:`A` in a topological space if :math:`A ∩ (V \ {x}) ≠ ∅` for every :term:`neighborhood` :math:`V` of :math:`x`.

   linear functional
     Let :math:`X` be a :term:`vector space` over the :term:`field` :math:`F`.  A **linear functional** on :math:`X` is a :term:`linear transformation` with :term:`codomain` :math:`F`.

   linear operator
     See :term:`linear transformation`.

   linear space
     See :term:`vector space`.

   linear transformation
     A **linear transformation** (or **linear operator**) is a :term:`morphism` in the category of :term:`vector spaces <vector space>`.

     Explicitly, if :math:`X` and :math:`Y` are :term:`vector spaces <vector space>` over the :term:`field` :math:`F`, then a **linear transformation** from :math:`X` to :math:`Y` is a function :math:`T: X → Y` that is "linear" in that it preserves the vector space operations (addition and scalar products); that is,
     
       #. :math:`∀ x, x' ∈ X`, :math:`T(x + x') = T\,x + T\,x'`.
       #. :math:`∀ α ∈ F`, :math:`∀ x ∈ X`, :math:`T(α x) = α T\,x`.

     (These conditions are equivalent to the single condition :math:`∀ α ∈ F`, :math:`∀ x, x' ∈ X`, :math:`T(α x + x') = α T\,x + T\,x'`.)

   𝐿ipschitz condition
     A function :math:`f` satisfies a **𝐿ipschitz condition** on an interval if there is a constant :math:`M` such that :math:`|f(x) - f(y)| ≤ M|x-y|` for all :math:`x`and :math:`y` in the interval.

   𝐿ipschitz constant
     The number :math:`M` in the definition of :term:`𝐿ipschitz condition` is called the **𝐿ipschitz constant**.

   𝐿ipschitz continuous
     A function is called **𝐿ipschitz continuous** on an interval if it satisfies a :term:`𝐿ipschitz condition` on that interval.

   locally compact
     A :term:`topological space` :math:`(X,τ)` is called **locally compact** if every point of :math:`X` has a neighborhood whose :term:`closure` is :term:`compact <compact set>`.

   lower limit
     Let :math:`\{a_n\}` be a sequence in :math:`[-∞, ∞]`, and put :math:`b_k = \inf \{a_k, a_{k+1}, \dots\}` for :math:`k∈ ℕ` and :math:`β = \sup \{b_0, b_1, b_2, \dots \}`. We call :math:`β` the **lower limit** (or **limit inferior**) of :math:`\{a_n\}`, and write :math:`β = \liminf\limits_{n→ ∞} a_n`.  The :term:`upper limit`, :math:`\limsup\limits_{n→ \infty} a_n` is definied similarly.

     Observe that

       #. :math:`b_0 ≤  b_1 ≤ b_2 ≤ \cdots ≤ β` and :math:`b_k → β` as :math:`k→ ∞`;
       #. there is a subsequence :math:`\{a_{n_j}\}` of :math:`\{a_n\}` that converges to :math:`β` as :math:`j→ ∞` and :math:`β` is the smallest number with this property.
       #. :math:`\limsup\limits_{n→∞} a_n = -\liminf\limits_{n→∞} (- a_n)`.

     (See also the definition of :term:`upper limit` and the remarks following that definition.)

   measurable function
     Let :math:`(X, 𝔐)` and :math:`(Y, 𝔑)` be measurable spaces. A function :math:`f: X → Y` is called :math:`(𝔐, 𝔑)`-**measurable** (or just **measurable**) if :math:`f^{-1}(N) ∈ 𝔐` for every :math:`N ∈ 𝔑`.

   measurable set
     If :math:`𝔐` is a :term:`σ-algebra` in :math:`X`, then the members of :math:`𝔐` are called the **measurable sets** in :math:`X`.

     If :math:`μ^∗` is an :term:`outer measure` on :math:`X`, a set :math:`A ⊆ X` is called :math:`μ^∗`-**measurable set** (or **measurable with respect to** :math:`μ^∗`, or just **measurable**) provided
     
     .. math:: μ^∗ E = μ^∗(E ∩ A) + μ^∗(E ∩ A^c)\; \text{ for all } E ⊆ X.

     Equivalently, :math:`A` is **measurable** iff
     
     .. math:: μ^∗ E ≥ μ^∗(E ∩ A) + μ^∗(E ∩ A^c)\; \text{ for all } E ⊆ X \text{ such that } μ^∗ E < ∞.

   measurable space
     If :math:`𝔐` is a :term:`σ-algebra` in :math:`X`, then :math:`(X, 𝔐)` (or just :math:`X`) is called a **measurable space**.

   measure
     A (positive) **measure** is a function :math:`μ: 𝔐 → [0, ∞]`, defined on a :math:`σ`-algebra :math:`𝔐`, which is :term:`countably additive`.

   measure space
     A **measure space** is a triple :math:`(X, 𝔐, μ)` where :math:`X` is a :term:`measurable space`, :math:`𝔐` is the :term:`σ-algebra` of :term:`measurable sets <measurable set>` in :math:`X`, and :math:`μ: 𝔐 → [0, ∞]` is a :term:`measure`.

   metric space
     A **metric space** is a pair :math:`(X, d)` where :math:`X` is a set and :math:`d: X × X → ℝ` is a **metric** (or **distance function**), that is, a function satisfying the following conditions for all :math:`x, y, z ∈ X`:

     #. :math:`d(x, y) ≥ 0`
     #. :math:`d(x,y) = 0` if and only if :math:`x = y`
     #. (symmetry) :math:`d(x, y) = d(y, x)` 
     #. (triangle inequality) :math:`d(x, z) ≤ d(x, y)+d(y, z)`.

   mutually singular
     Suppose :math:`λ_1` and :math:`λ_2` are measures on :math:`𝔐` and suppose there exists a pair of disjoint sets :math:`A` and :math:`B` such that :math:`λ_1` is :term:`concentrated` on :math:`A` and :math:`λ_2` is concentrated on :math:`B`. Then we say that :math:`λ_1` and :math:`λ_2` are **mutually singular** and we write :math:`λ_1 ⟂ λ_2`.

   negative part
     The **negative part** of :math:`f: X → [-∞, ∞]` is the function that is denoted and defined for each :math:`x∈ X` by :math:`f^-(x) = \max\{-f(x),0\}`.
     
     Observe that :math:`f` is :term:`measurable <measurable function>` if and only if both the :term:`positive <positive part>` and negative parts of :math:`f` are measurable. Also, :math:`f^+, f^-: X → [0, ∞]`, :math:`f = f^+ - f^-`, and :math:`|f| = f^+ + f^-`.

   negligible
     A :term:`measurable set` is called **negligible** if it has measure 0.

   neighborhood
     A **neighborhood** of a point :math:`p` in a :term:`topological space` :math:`X` is a set :math:`A` in :math:`X` whose :term:`interior` contains :math:`p`; that is, :math:`p ∈ A^o`. [2]_

   nonnegative function
     A function :math:`f: X → ℝ` such that :math:`f(x) ≥ 0` for all :math:`x∈ ℝ` is called a **nonnegative function**.  We use the shorthand :math:`f ≥ 0` to denote that :math:`f` is a nonnegative function.

   norm
     Let :math:`X` be a :term:`vector space` over the :term:`field` :math:`F`, and let :math:`|\,⋅\,|: F → [0,∞)` be a :term:`valuation` on :math:`F`.  A **norm** on :math:`X` is a function :math:`\|\;\|: X → [0, ∞)` that satisfies the following conditions:

     #. :math:`\|x + y\| ≤ \|x\| + \|y\|`, for all :math:`x, y ∈ X`;
     #. :math:`\|α x\| = |α| \|x\|`, for all :math:`x ∈ X` and :math:`α ∈ F`;
     #. :math:`\|x\| = 0` if and only if :math:`x = 0`.

     Thus, a norm is a :term:`seminorm` satisfying: :math:`\|x\| = 0` only if :math:`x = 0`.

   normed linear space
     A **normed linear space** (or **normed vector space**) is a pair :math:`(X, \|\,⋅\,\|)` consisting of a :term:`vector space` :math:`X` and a :term:`norm` :math:`\|\,⋅\,\|` defined on :math:`X`.
 
   normed vector space
     See: :term:`normed linear space`
 
   nowhere dense
     A set :math:`G` is **nowhere dense** in :math:`X` if the :term:`closure` of :math:`G` contains no nonempty open subsets of :math:`X`. Equivalently, the :term:`interior` of the closure of :math:`G` is empty (in symbols, :math:`Ḡ^o = ∅`).
 
   open ball
     Let :math:`(X, d)` be a :term:`metric space`. If :math:`x ∈ X` and :math:`r > 0` are fixed, then the set denoted and defined by :math:`B(x, r) = \{y ∈ X ∣ d(x,y) < r\}` is called the **open ball** with center :math:`x` and radius :math:`r`.

   open covering
     See :term:`covering`.

   open mapping
     Let :math:`X` and :math:`Y` be metric or topological spaces.  A set function :math:`T: 𝒫(X) → 𝒫(Y)` is called an **open mapping** if :math:`T(G)` is open in :math:`Y` for every open :math:`G ⊆ X`.

   open set
     A subset :math:`V` of a metric or topological space is called **open** if for every :math:`x ∈ V` there is an open ball contained in :math:`V` that contains :math:`x`.

     For a metric space :math:`(X,d)` this means that a set :math:`V` is open iff for every :math:`x ∈ V` there exists :math:`δ > 0` such that

     .. math:: B(x,δ) := \{y ∈ X ∣ d(x,y) < δ\} ⊆ V

     For a topological space :math:`(X, τ)` the open sets are the sets belonging to the topology :math:`τ`.

   operator norm
     If :math:`X` and :math:`Y` are :term:`normed linear spaces <normed linear space>`, then the space :math:`𝔅(X,Y)` of :term:`bounded linear transformations <bounded linear transformation>` is a :term:`vector space` and the function :math:`T ↦ \|T\|` defined by

     .. math:: \|T\| = \sup \{ \|Tx\| : \|x\| = 1 \}

     is a :term:`norm` on :math:`𝔅(X,Y)`, called the **operator norm**.

     There are other, equivalent ways to express the operator norm; e.g.,

     .. math:: \|T\| = \sup \{ \frac{\|Tx\|}{\|x\|} : x ≠ O\} = \inf \{ C : \|Tx\| ≤ C\|x\| \text{ for all } x\}.

   orthogonal set
     Let :math:`(X, ⟨⋅, ⋅⟩)` be an :term:`inner product space`. A subset :math:`Q ⊆ X` is called **orthogonal** provided :math:`⟨ 𝐮, 𝐯 ⟩ = 0` for all :math:`𝐮 ≠ 𝐯` in :math:`Q`.
     
   orthonormal basis
     A maximal :term:`orthonormal set` in a :term:`Hilbert space` is known as an **orthonormal basis**. 

   orthonormal set
     Let :math:`(X, ⟨⋅, ⋅⟩)` be an :term:`inner product space`. An :term:`orthogonal set` :math:`U ⊆ X` is called **orthonormal** provided :math:`\|u\| = 1` for all :math:`𝐮 ∈ U`.
     
     In other terms, a subset :math:`Q ⊆ X` is called **orthonormal** provided for all :math:`𝐮, 𝐯 ∈ Q`,

     .. math:: ⟨ 𝐮, 𝐯 ⟩ = \begin{cases} 0,& 𝐮 ≠ 𝐯,\\
                                        1,& 𝐮 = 𝐯. \end{cases}

     Every inner product space has a maximal orthonormal set.

   outer measure
     An **outer measure** on a nonempty set :math:`X` is a function :math:`μ^∗: 𝒫(X) → [0, ∞]` that satisfies

     #. :math:`μ^∗ ∅ = 0`,
     #. :math:`μ^∗ A ≤ μ^∗ B` if :math:`A ⊆ B ⊆ X`,
     #. :math:`μ^∗\bigl(⋃_{i=1}^∞ A_i\bigr) ≤ ∑_{i=1}^∞ μ^∗ A_i` if :math:`A_i ⊆ X` for all :math:`1 ≤ i ≤ ∞`.

   positive measure
     See :term:`measure`.

   positive part
     The **positive part** of :math:`f: X → [-∞, ∞]` is the function that is denoted and defined for each :math:`x∈ X` by :math:`f^+(x) = \max\{f(x),0\}`.
     
     Observe that :math:`f` is :term:`measurable <measurable function>` if and only if both the positive and :term:`negative <negative part>` parts of :math:`f` are measurable. Also, :math:`f^+, f^-: X → [0, ∞]`, :math:`f = f^+ - f^-`, and :math:`|f| = f^+ + f^-`.
       
   product σ-algebra
     Let :math:`(X, 𝔐, μ)` and :math:`(Y, 𝔑, ν)` be :term:`measure spaces <measure space>`. If we want to make the product :math:`X × Y` into a :term:`measurable space`, we naturally consider the :term:`σ-algebra` generated by the sets in :math:`𝔐 × 𝔑 = \{A × B ⊆ X × Y ∣ A ∈ 𝔐, B ∈ 𝔑\}`, and we *define* :math:`𝔐 ⊗ 𝔑 := σ(𝔐 × 𝔑)`; that is, :math:`𝔐 ⊗ 𝔑` is the :term:`σ-algebra` generated by :math:`𝔐 × 𝔑`.  [3]_
 
   product topology
     Let :math:`\{(X_λ, τ_λ)\}_{λ∈ Λ}` be a collection of :term:`topological spaces <topological space>` indexed by a set :math:`Λ`. The **product topology** on the :term:`Cartesian product` :math:`∏_{λ∈ Λ}X_λ` is the topology that has a :term:`base` consisting of sets of the form :math:`∏_{λ∈Λ}V_λ`, where :math:`V_λ ∈ τ_λ` and :math:`V_λ = X_λ` for all but finitely many :math:`λ`.

     Equivalently, the product topology is the weakest topology that makes all the projection maps :math:`π_λ(\mathbf x) = x_λ` continuous.  In other words, if :math:`Π` denotes the :term:`clone` of all projection operations on :math:`∏_{λ ∈ Λ} X_λ`, then the product topology is the :math:`Π`-topology.

   relative topology
     If :math:`(X, τ)` is a :term:`topological space` and :math:`Y ⊆ X`, then :math:`τ_Y := \{V ∩ Y ∣ V ∈ τ\}` is a topology on :math:`Y`, called the **relative topology** induced by :math:`τ`.

   second category
     A set :math:`G` is of the **second category** if it is not of the :term:`first category`.

   self-adjoint 
     A linear transformation of a :term:`Hilbert space` :math:`ℋ` to itself is called self-adjoint just in case :math:`∀ x, y ∈ ℋ, ⟨x, Ty⟩ = ⟨Tx, y⟩`.

   self-dual
     A normed linear space :math:`X` is called **self-dual** provided :math:`X ≅ X^∗`.
     
     A category :math:`𝒞` is called **self-dual** if :math:`𝒞^{\mathrm{op}} = 𝒞`.

   seminorm
     Let :math:`X` be a :term:`vector space` over the :term:`field` :math:`F`.  A **seminorm** on :math:`X` is a function :math:`\|\;\|: X → [0, ∞)` that satisfies
      
     #. :math:`\|x + y\| ≤ \|x\| + \|y\|`, for all :math:`x, y ∈ X`;
     #. :math:`\|α x\| = |α| \|x\|`, for all :math:`x ∈ X` and :math:`α ∈ F`.

   separable
     An infinite :term:`Hilbert space` is called **separable** if it has a countable :term:`orthonormal basis`.

   separates the points
     We say that a collection :math:`S` of subsets of :math:`X` **separates the points** of :math:`X` if for every pair :math:`p, q` of distinct points in :math:`X` there exist disjoint sets :math:`S_1, S_2∈ S` such that :math:`p ∈ S_1` and :math:`q∈ S_2`.

     Let :math:`F` be a field.  We say that a collection :math:`𝔄⊆ F^X` of :math:`F`-valued functions **separates the points** of :math:`X` if for every pair :math:`p, q` of distinct points in :math:`X` there exists :math:`f ∈ 𝔄` such that :math:`f(u) ≠ f (v)`. 
     
   σ-algebra
     A collection :math:`𝔐` of subsets of a nonempty set :math:`X` is called a **σ-algebra** if it satisfies the following conditions:
    
     #. :math:`X ∈ 𝔐`;
     #. if :math:`A ∈ 𝔐` then :math:`A^c:= X - A` of :math:`A` also belongs to :math:`𝔐`.
     #. if :math:`A_n ∈ 𝔐` for :math:`n ∈ ℕ`, then :math:`⋃_{n = 0}^∞ A_n ∈ 𝔐`.

     Equivalently, a **σ-algebra** of sets is an :term:`algebra of sets` that is closed under countable unions.
     
     (For the algebraic meaning of the term :math:`σ`-algebra, see the definition of :term:`algebraic structure`.)

   σ-finite measure
     If :math:`(X, 𝔐, μ)` is a :term:`measure space`, then :math:`μ` is a **σ-finite measure** provided :math:`X = ⋃_j E_j` for some :math:`E_j ∈ 𝔐` such that :math:`μ E_j < ∞` for all :math:`1≤ j < ∞`.
    
   signed measure
     Let :math:`(X, 𝔐)` be a :term:`measurable space`. A **signed measure** on :math:`(X, 𝔐)` is a function :math:`ν: 𝔐 → [-∞, ∞]` such that
     
     #. :math:`ν ∅ = 0`;
     #. :math:`ν` assumes at most one of the values :math:`±∞`;
     #. :math:`ν` is countably additive.
     
     The last item means that
     
     .. math:: ν(⋃_j A_j) = ∑_j ν(A_j)
        :label: countably additive
         
     whenever :math:`\{A_j\}` is a collection of disjoint sets in :math:`𝔐`.
     
     Moreover, the sum on the right-hand side of :eq:`countably additive` converges absolutely if the left-hand side of :eq:`countably additive` is finite.

   simple function
     A complex- or real-valued function :math:`s` whose range consists of only finitely many points is called a **simple function**.

     Let :math:`s` be a simple function with domain :math:`X` and suppose :math:`α_1, \dots, α_n` is the set of distinct values of :math:`s`. If we set :math:`A_i = \{x\in X : s(x) = \alpha_i\}`, then clearly

     .. math:: s = ∑_{i=1}^n α_i χ_{A_i},
        :label: simple

     where :math:`χ_{A_i}` is the :term:`characteristic function` of the set :math:`A_i`.
     
     The definition of *simple function* assumes nothing about the sets :math:`A_i`; thus, a simple function is not necessarily measurable.

     Observe also that the function :math:`s` in :eq:`simple` is :term:`integrable` if and only if each :math:`A_i` has finite measure.
     
   step function
     A finite linear combination of characteristic functions of bounded intervals of :math:`ℝ` is called a **step function**.

   subadditive
     Let :math:`𝒮 = \{S_λ: λ∈ Λ\}` be a collection of sets and let :math:`R` be a :term:`ring`.  A function :math:`s: 𝒮 → R` is called **subadditive** if for every subset :math:`Γ ⊆ Λ` such that :math:`\{S_γ : γ ∈ Γ\}` is a collection of subsets in :math:`𝒮`, we have
     .. math:: s \bigl( ⋃_{γ∈Γ}  A_γ \bigr) ≤ ∑_{γ∈ Γ} s (A_γ).

   topological space
     A **topological space** is a pair :math:`(X, τ)` where :math:`X` is a set and :math:`τ` is a :term:`topology` on :math:`X`.

   topology
     A **topology** :math:`τ` on a set :math:`X` is a collection of subsets of :math:`X` containing :math:`X` and the empty set, and is closed under finite intersections and arbitrary unions.  That is, :math:`τ` satisfies

     #. :math:`∅ ∈ τ` and :math:`X ∈ τ`;
     #. :math:`\{V_i ∣ i = 1, \dots, n\} ⊆ τ` implies :math:`⋂_{i=1}^n V_i ∈ τ`;
     #. :math:`\{V_α ∣ α ∈ A\} ⊆ τ` implies :math:`⋃_{α∈A} V_α ∈ τ`.
 
   totally bounded
     A set :math:`E` in a metric space is called **totally bounded** if for every :math:`ε > 0` :math:`E` can be covered with finitely many balls of radius :math:`ε`.

   translation invariance
     Let :math:`(X, 𝔐)` be a :term:`measurable space`. Assume there is a binary operation defined on :math:`X`; e.g., addition :math:`+: X× X → X`. A :term:`measure` :math:`μ` on :math:`(X, 𝔐)` is called **translation invariant** provided :math:`μ(E + x) = μ E` holds for all :math:`E ∈ 𝔐` and all :math:`x∈  X`, where :math:`E+x := \{e+x ∣ e∈ E\}`.

   triangle inequality
     Let :math:`(X, \|\,⋅\,\|)` be a metric or normed space.  The inequality :math:`\|x + y\| ≤ \|x\| + \|y\|`, which holds for all :math:`x, y ∈ X` in a metric or normed space, is called the **triangle inequality**.  Equivalently (setting :math:`x = a-b` and :math:`y = b-c`), :math:`\|a - c\| ≤ \|a - b\| + \|b - c\|`.
 
   uniformly continuous
     Let :math:`(X, |\, |_X)` and :math:`(Y, |\, |_Y)` be :term:`metric spaces <metric space>`. A function :math:`f : X → Y` is called **uniformly continuous** in :math:`E ⊆ X` if
  
     .. math:: (∀ ε >0)\, (∃ δ >0)\, (∀ x, x_0 ∈ E) \, (|x - x_0| < δ \, ⟹ \, |f(x) -f(x_0)| < ε).

   unitary operator
     A **unitary operator** (or **unitary map**) is an :term:`isomorphism` in the category of :term:`Hilbert spaces <Hilbert space>`.
      
     Explicitly, if :math:`ℋ_1` and :math:`ℋ_2` are :term:`Hilbert spaces <Hilbert space>` with :term:`inner products <inner product>` :math:`⟨\,.\,,\,.\,⟩_1` and :math:`⟨\,.\,,\,.\,⟩_2` (reps.), then a **unitary operator** from :math:`ℋ_1` to :math:`ℋ_2` is an invertible :term:`linear transformation` :math:`U: ℋ_1 → ℋ_2` that preserves inner products in the following sense:

     .. math:: ⟨U x, U y⟩_2 = ⟨x, y⟩_1 \; \text{ for all } x, y ∈ ℋ_1.

     By taking :math:`y = x`, we have :math:`\|U x\|_2 = \|x\|_1`.

   upper limit
     Let :math:`\{a_n\}` be a sequence in :math:`[-∞, ∞]`, and put :math:`b_k = \sup \{a_k, a_{k+1}, \dots\}` for :math:`k∈ ℕ` and :math:`β = \inf \{b_0, b_1, b_2, \dots \}`. We call :math:`β` the **upper limit** (or **limit superior**) of :math:`\{a_n\}`, and write :math:`β = \limsup\limits_{n→ ∞} a_n`.  The :term:`lower limit`, :math:`\liminf\limits_{n→ \infty} a_n` is definied similarly.

     Observe that

       #. :math:`b_0 ≥  b_1 ≥ b_2 ≥ \cdots ≥ β` and :math:`b_k → β` as :math:`k→ ∞`;
       #. there is a subsequence :math:`\{a_{n_j}\}` of :math:`\{a_n\}` that converges to :math:`β` as :math:`j→ ∞` and :math:`β` is the largest number with this property.
       #. :math:`\liminf\limits_{n→∞} a_n = -\limsup\limits_{n→∞} (- a_n)`.

     Suppose :math:`\{f_n\}` is a sequence of extended real-valued functions on a set :math:`X`. Then :math:`\sup\limits_n f_n` and :math:`\limsup\limits_{n→∞}f_n` are the functions that are defined for each :math:`x∈ X` by
     
     .. math:: \left(\sup\limits_n f_n\right)(x) = \sup\limits_n (f_n(x)), \quad  \left(\limsup\limits_n f_n\right)(x) = \limsup\limits_n (f_n(x)).

--------------------------------

Glossary: complexity
--------------------

Some known inclusions of complexity classes are these:

  :term:`P` ⊆ :term:`NP` ⊆ :term:`PSPACE` ⊆ :term:`EXPTIME` ⊆ :term:`NEXPTIME` ⊆ :term:`EXPSPACE`

What follows is a list of useful definitions from computational complexity theory.

.. glossary::

   Cobham's thesis
     Also known as the **Cobham–Edmonds thesis** (named after Alan Cobham and Jack Edmonds), **Cobham's thesis** asserts that computational problems can be feasibly computed on some computational device only if they can be computed in :term:`polynomial time`; that is, if they lie in the complexity class :term:`P`.
     
     (See https://en.wikipedia.org/wiki/Cobham%27s_thesis )

   complete for polynomial time
     A decision problem or language D is **complete for polynomial time** if it is in :term:`P` and it is P-hard, which means for all A ∈ P, A :math:`≤_p` B; that is, there is a polynomial-time many-to-one reduction from A to B.  The class of problems that are complete for polynomial time is denote **P-complete**. 

     An example of a P-complete problem is deciding whether a given set generates a given algebra (see: https://orion.math.iastate.edu/cbergman/manuscripts/frattini.pdf).

   complete for polynomial space
     A decision problem or language B is **complete for polynomial space** if it is in :term:`PSPACE` and it is PSPACE-hard, which means for all A ∈ PSPACE, A :math:`≤_p` B; that is, there is a polynomial-time many-to-one reduction from A to B.  The class of problems that are complete for polynomial space is denote by **PSPACE-complete**. 

     An example of a PSPACE-complete problem is the :term:`quantified Boolean formula problem`.

   complete
     If a problem X is in C and is hard for C, then X is said to be **complete** for C.  This means that X is as hard or harder than every problem in C.
     
   complete for nondeterministic polynomial time
     A problem is **complete for nondeterministic polynomial time** (or **NP-complete**) complexity if it is :term:`NP-hard` and can be solved in :term:`nondeterministic polynomial time` (i.e., belongs to NP).
    
   complexity of an algebra
     We classify the **complexity of an algebra** 𝐀, or collection of algebras 𝔄, according to the complexity of their corresponding constraint satisfaction problems.

     An algorithm 𝖠 is called a :term:`polynomial-time algorithm` for CSP(𝔄) (or **runs in polynomial-time**) if there exist constants c and d such that, given an instance I of CSP(𝔄) of :term:`size` 𝖲 = size(I), 𝖠 halts in at most c𝖲ᵈ steps and outputs whether or not I has a solution.
     
     In this case, we say 𝖠 "solves the decision problem CSP(𝔄) in polynomial time" and we call the algebras in 𝔄 "jointly tractable."
     
     Some authors say that an algebra 𝐀 as tractable when 𝔄 = 𝖲(𝐀) is jointly tractable, or when :math:`𝔄 = 𝖲 𝖯_{\mathrm{fin}} (𝐀)` is jointly tractable.
     
     We say that 𝔄 is **jointly locally tractable** if, for every natural number, m, there is a polynomial-time algorithm 𝖠ₘ that solves CSP(𝔄,m).  

   constraint satisfaction problem
     Let 𝔄 be a collection of (finite) algebras of the same signature. Define the **constraint satisfaction problem** CSP(𝔄) to be the following decision problem:

       An n-variable **instance** of CSP(𝔄) is a quadruple (𝒱, 𝒜, 𝒮, ℛ) consisting of
  
       * a set 𝒱 of :math:`n` **variables**; often, simply, :math:`𝒱  = 𝐧 := {0, 1, ..., n-1}`;
       * a list :math:`𝒜 = (𝐀_0, 𝐀_1, \dots, 𝐀_{n-1}) ∈ 𝔄^n` of algebras from 𝔄, one for each variable;
       * a list :math:`𝒮 = (σ_0, σ_1, \dots, σ_{J-1})` of **constraint scope functions** with arities :math:`\mathrm{ar}(σ_j) = m_j`;
       * a list :math:`ℛ = (R_0, R_1, \dots, R_{J-1})` of **constraint relations**, where each :math:`R_j` is the universe of a subdirect product of algebras in 𝔄 with indices in :math:`\mathrm{im} σ_j`; that is, :math:`𝐑_j ≤_{sd} ∏_{0≤ i < m_j}𝐀_{σ_j(i)}`.
  
       A **solution** to the instance (𝒱, 𝒜, 𝒮, ℛ) is an assignment :math:`f: 𝒱 → ⋃_𝐧 A_i` of values to variables that satisfies all constraint relations.  More precisely, :math:`f ∈ ∏_𝐧 A_i` and for each :math:`0 ≤ j < J`, :math:`\mathrm{Proj}_{σ_j} f ∈ R_j`; that is,  :math:`f ∘ σ_j ∈ R_j`.

     (N.B. This is by no means the most general definition of a CSP.)

   exponential space
     A decision problem is said to have **exponential space** (or **EXPSPACE**) complexity if it is solvable by a deterministic Turing machine 
     
   exponential time
     A decision problem is said to have **exponential time** (or **EXPTIME**) complexity if it is solvable by a deterministic Turing machine that runs in :math:`O(2^{p(n)})` time, where :math:`p(n)` is a polynomial function of :math:`n`.
     
   homomorphic relaxation
     Let (𝔸, 𝔹) and (𝔸', 𝔹') be :term:`PCSP templates <PCSP template>`. We say that (𝔸', 𝔹') is a **homomorphic relaxation** of (𝔸, 𝔹) if there exist :term:`homomorphisms <relational structure homomorphism>` f: 𝔸' → 𝔸 and g: 𝔹 → 𝔹'.
      
   locally tractable
     We say that a collection 𝔄 of algebras is **jointly locally tractable** (or just **locally tractable**) if, for every natural number, m, there is a polynomial-time algorithm 𝖠ₘ that solves CSP(𝔄,m).  

   logarithmic space
     A decision problem or language has **logarithmic space complexity** if it can be solved by a deterministic :term:`Turing machine` using a logarithmic amount of writable memory space.  The complexity class of such problems is known as **𝐿OGSPACE** (or **𝐿** or **𝐿SPACE** or **D𝐿OGSPACE**).
     
     Formally, a Turing machine has two tapes, one encoding the input which can only be read from, and one of logarithmic size that can be both read from and written to.
     
     𝐿ogarithmic space is sufficient to hold a constant number of pointers into the input and a logarithmic number of boolean flags, and many basic 𝐿OGSPACE algorithms use the memory in this way.

   Nick's class
     The class **NC** (or "**Nick's Class**") is the class of problems decidable in polylogarithmic (or, O(logᶜ n)) time on a parallel computer with a polynomial number of processors.
     
     A decision problem D is in NC if there exist constants c, k such that D can be decided in time O(logᶜ n) using O(nᵏ) parallel processors. Stephen Cook named this class after Nick Pippenger, who researched circuits with polylogarithmic depth and polynomial size.

     NC is a subset of P because polylogarithmic parallel computations can be simulated by polynomial-time sequential ones.
     
     NC can be thought of as the problems that are :term:`tractable` using parallelism.    

     It is unknown whether NC = P, but most suspect this is false, meaning there are some tractable problems that are "inherently sequential" and cannot significantly be sped up by using parallelism. It is suggested in (citation needed) that problems in the class P-complete cannot be solved more efficiently with a parallel computer.
     
     The class NP-complete can be thought of as "intractable" (assuming P ≠ NP), and the class P-complete is, using NC reductions, the class of "not parallelizable" or "inherently sequential" problems.

     (Source: https://en.wikipedia.org/wiki/NC_(complexity).)

   nondeterministic exponential time
     A decision problem has **nondeterministic exponential time** complexity if it can be solved by a nondeterministic Turing machine in :math:`2^{n^{O(1)}}` time.  We let **NEXPTIME** denote the complexity class of problems that have nondeterministic exponential time complexity.

   nondeterministic logarithmic space
     A decision problem or language has **nondeterministic logarithmic space** complexity if it can be solved by a nondeterministic Turing machine using a logarithmic amount of writable memory space.  The class of such problems is usually denote by **N𝐿OGSPACE** (or **N𝐿** or **N𝐿SPACE**).

   nondeterministic polynomial time
     A decision problem or language has **nondeterministic polynomial time** complexity if it can be solved by a nondeterministic Turing machine in logarithmic amount of running time.

   NP-hard
     NP-hardness (non-deterministic polynomial-time hardness) is the defining property of a class of problems that are informally "at least as hard as the hardest problems in :term:`NP`."  A more precise specification is: a problem H is NP-hard when every problem in NP can be reduced in polynomial time to H.

   ω-categorical
     A :term:`theory` is called **ω-categorical** if it has, up to isomorphism, exactly one model of cardinality ω.

     A structure is called **ω-categorical** if its first-order theory has exactly one countable model up to isomorphism.

     See also the definition of :term:`categorical`.
     
   PCSP
     The **promise constraint satisfaction problem** (**PCSP**) over the :term:`PCSP template` (𝔸, 𝔹) is denoted PCSP(𝔸, 𝔹) and is defined to be the following decision problem: given a :term:`pp-sentence` φ over the relational symbols :math:`R_1, \dots, R_n`, answer "YES" if φ is true in 𝔸 and answer "No" if φ is not true in 𝔹.

   PCSP template
     Let :math:`𝔸 = ⟨A, R_1^𝔸, \dots, R_ℓ^𝔸⟩` and :math:`𝔹 = ⟨B, R_1^𝔹, \dots, R_ℓ^𝔹⟩` be finite relational structures of the same signature and assume that there exists a homomorphism 𝔸 → 𝔹. Then the pair (𝔸, 𝔹) is called a **promise constraint satisfaction problem template** (or **PCSP template**).

   polynomial space
     A decision problem has **polynomial space** complexity if it can be solved by a :term:`Turing machine` using a polynomial amount of space.  The class of such problems is denoted **PSPACE**.

   polynomial time
     **P** (or **PTIME**) is the class of decision problems that can be solved by a deterministic :term:`Turing machine` using a polynomial amount of computation time.

   polynomial-time algorithm
     An algorithm 𝖠 is called a **polynomial-time algorithm** for a decision problem 𝒟 if there exist constants c and d such that, given an instance I of 𝒟 of size 𝖲 = size(I), 𝖠 halts in at most c Sᵈ steps and outputs whether or not I has a solution.

     In this case, we say that 𝖠 "solves the decision problem 𝒟 in polynomial time" and we call the problem 𝒟 :term:`tractable`.
   
   size
     We bound the **size** of an instance I=⟨𝒱, 𝒜, 𝒮, ℛ⟩ of a :term:`constraint satisfaction problem` CSP(𝔄) as follows:
     
     Let :math:`q=\max(|A₀|, |A₁|, \dots, |A_{n-1}|)`, let r be the maximum rank of an operation symbol in the similarity type, and p the number of operation symbols.
     
     Then each member of the list 𝒜 requires at most :math:`pq^r\log q` bits to specify.  Thus,

     .. math:: \mathrm{size}(𝒜) ≤ npq^r\log q.

     Similarly, each constraint scope :math:`σ_j: 𝐦_j → 𝐧` can be encoded using :math:`m_j\log n` bits.
     
     Taking :math:`m=\max(m_1,\dots,m_{J-1})` we have :math:`\mathrm{size}(𝒮) ≤ J m \log n`.

     Finally, the constraint relation :math:`R_j` requires at most :math:`q^{m_j} m_j \log q` bits. Thus :math:`\mathrm{size}(ℛ) ≤ Jq^m m \log q`.

     Combining these encodings and using the fact that :math:`\log q ≤ q`, we deduce that

     .. math:: \mathrm{size}(ℐ) ≤ npq^{r+1} + Jmq^{m+1} + Jmn.

     In particular, for the problem :math:`\mathrm{CSP}(𝔄,m)`, the parameter :math:`m` is considered fixed, as is :math:`r`. In this case, we can assume :math:`J ≤ n^m`.
     
     Consequently size(ℐ) ∈ :math:`O((nq)^{m+1})`, which yields a polynomial bound (in :math:`nq`) for the size of the instance.

   tractable
     We say that a decision problem is **tractable** if there exists a deterministic :term:`polynomial-time algorithm` that can solve all instances of that problem.

     :term:`Cobham's thesis` asserts that the class :term:`P` can be thought of as the class of **tractable** problems.

   Turing machine
     See https://en.wikipedia.org/wiki/Turing_machine

   quantified Boolean formula problem
     The **quantified Boolean formula problem** (QBF) is a generalization of the Boolean satisfiability problem (SAT) in which both existential and universal quantifiers can be applied to each variable. Put another way, it asks whether a quantified sentential form over a set of Boolean variables is true or false. For example, the following is an instance of QBF: ∀ x\ ∃ y\ ∃ z\ ((x ∨ z) ∧ y).

     QBF is the canonical complete problem for :term:`PSPACE`, the class of problems solvable by a deterministic or nondeterministic Turing machine in polynomial space and unlimited time.
     
     Given the formula in the form of an abstract syntax tree, the problem can be solved easily by a set of mutually recursive procedures which evaluate the formula. Such an algorithm uses space proportional to the height of the tree, which is linear in the worst case, but uses time exponential in the number of quantifiers.





-----------------------------------



.. rubric:: Footnotes

.. [1]
   See Rudin :cite:`Rudin:1987` 1.35-6 for a nice discussion of the role played by sets of measure 0.  To summarize that discussion, it may happen that there is a set :math:`N ∈ 𝔐` of measure 0 that has a subset :math:`E ⊆ N` which is not a member of :math:`𝔐`.  Of course, we'd like all subsets of measure 0 to be measurable and have measure 0.  It turns out that in such cases we can extend :math:`𝔐` to include the offending subsets, assigning such subsets measure 0, and the resulting extension will remain a :math:`σ`-algebra.  In other words, we can always *complete* a measure space so that all subsets of negligible sets are measurable and negligible.

.. [2]
   The use of this term is not quite standardized; some (e.g., Rudin :cite:`Rudin:1987`) call any open set containing :math:`p` a "neighborhood of :math:`p`".

.. [3]
   This notation is not completely standard. In :cite:`Aliprantis:1998` (page 154) for example, :math:`𝔐 ⊗ 𝔑` denotes what we call :math:`𝔐 × 𝔑`, while :math:`σ(𝔐 ⊗ 𝔑)` denotes what we have labeled :math:`𝔐 ⊗ 𝔑`. At the opposite extreme, Rudin (in :cite:`Rudin:1987`) simply takes :math:`𝔐 × 𝔑` to be the :term:`σ-algebra` generated by the sets :math:`\{A × B ∣ A ∈ 𝔐, B ∈ 𝔑\}`.



..     In 𝐿ean, one defines function extensionality for functions of (dependent) type :math:`Π(x:α), β x` as follows:
 
..     .. code-block:: lean
 
..        def equiv (f₁ f₂: Π x:α, β x): Prop := ∀ x, f₁ x = f₂ x
 
   

.. include:: hyperlink_references.rst
