.. File: glossary_logic.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 8 Dec 2019
.. Updated: 8 Dec 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. role:: code

.. highlight:: lean


Glossary: logic and model theory
----------------------------------

Model theory is the study of classes of mathematical structures from the perspective of mathematical logic. The objects of study are models of theories in a formal language. A set of sentences in a formal language is one of the components that form a theory. A model of a theory is a structure (e.g. an interpretation) that satisfies the sentences of that theory.

What follows is a list of useful definitions from model theory.

.. glossary::

   α-equivalent
     Two formulas are called **α-equivalent** if one is obtained from the other by renaming bound variables (using variable names that do not clash with existing variable names).

   Agda
     An :term:`intensional`, :term:`predicative` :term:`ITP` supporting :term:`dependent types <dependent type>` and based on Martin Lof type theory; url: https://wiki.portal.chalmers.se/agda/pmwiki.php
 
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
     By :math:`𝖺𝗍_𝖫` (or just 𝖺𝗍 when the context makes :math:`𝖫` clear) we mean the class of all atomic :math:`𝖫`-formulas.

   atomic formula
     An **atomic** :math:`𝖫`**-formula** (or just **atomic formula** when the context makes :math:`𝖫` clear) has one of the following forms:
 
       * :math:`s = t`, where :math:`s` and :math:`t` are :math:`𝖫`-terms;
       * :math:`R t`, where :math:`R` is a relation symbol in :math:`𝖫` and :math:`t: ρ R → 𝒯`  is a tuple of :math:`𝖫`-terms;
 
   atomic sentence
     An **atomic** :math:`𝖫`**-sentence** (or just **atomic sentence** when the context makes :math:`𝖫` clear) is either an equation of constant terms or a relational sentence, :math:`R t`, where :math:`t \, i` is a :term:`closed term` for every :math:`i`; in particular,
     
     * *an atomic sentence contains no variables at all*, and
     * *languages without constant symbols have no atomic sentences*.
 
   automated theorem prover
     See: https://en.wikipedia.org/wiki/Automated_theorem_proving

   axiomatizable
     An **axiomatizable** (or **elementary**) class is a class that consists of all structures satisfying a fixed first-order :term:`theory`.

   axiomatization
     See: :term:`equational base`

   β-equivalent
     Two formulas are called **β-equivalent** if one can be obtained from the other using reduction steps defined in the prevailing logical system.

   base
     See: :term:`equational base`

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
 
     An L-:term:`theory` is said to be **categorical** if it is categorical in some cardinality λ. We call an L-theory **totally categorical** if it has infinite models and every two models of the same cardinality (finite or inĥnite) are isomorphic.
 
   closed literal
     A **closed literal** (or **literal sentence**) is a literal with no :term:`free variables <free variable>`.  We denote by :math:`𝖼𝗅_L` the set of all closed :math:`L`-literals (literal :math:`L`-sentences).

   closed term
     A **closed term** is a term with no free variables.

   compatible
     Let :math:`σ  = (F, ρ)` be an :term:`algebraic signature` and for each :math:`i ∈ 𝐧 := \{0, 1, \dots, n-1\}` let :math:`𝔸_i = ⟨A_i, F^{𝔸_i}⟩` be a σ-algebra. If :math:`𝐀 = ∏_{i:𝐧}𝔸_i` is the product of these algebras, then a relation :math:`R` over 𝐀 with scope σ is called **compatible** with 𝐀 if it is closed under (or "preserved by") the basic operations in :math:`F^𝐀`. In other words, :math:`R` is compatible if the induced algebra :math:`ℝ = ⟨R,F^ℝ⟩` is a subalgebra of :math:`∏_{j:𝐤} 𝔸_{σ(j)}`.

   complete theory
     A L-theory T is **complete** if for every L-:term:`sentence` φ ∈ L₀, either φ ∈ T or ¬φ ∈ T.  

   computable
     See: https://pdfs.semanticscholar.org/1364/d8e8763891b84a9383b722d82294ae0a736b.pdf
 
   consistent 
     :math:`Σ` is **consistent** if :math:`Σ^⊢` contains no :term:`contradictions <contradiction>`; otherwise, Σ is **inconsistent**.  

   constructive
     See: https://plato.stanford.edu/entries/mathematics-constructive/ and https://en.wikipedia.org/wiki/Constructivism_(philosophy_of_mathematics) and https://en.wikipedia.org/wiki/Constructive_proof
 
   contradiction
     A logical **contradiction** is an 𝖫-sentence of the form φ ∧ ¬ φ.

   Coq
     An :term:`intensional`, :term:`impredicative` :term:`ITP` supporting :term:`dependent types <dependent type>` and based on :term:`CiC`; url: http://coq.inria.fr
     
   Curry-Howard correspondence
     the correspondence between propositions and types, and proofs and programs; a proposition is identified with the type of its proofs, and a proof is a program of that type.
     
     See also: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

   currying
     See: https://en.wikipedia.org/wiki/Currying

   definitionally equal
     In :term:`type theory`, two terms with the same :term:`normal form` are called **definitionally equal**.

   deductive closure
     The **deductive closure** of a set S of statements is the set of all the statements that can be deduced from S.

     In propositional logic, the set of all true propositions exhibits deductive closure: if set O is the set of true propositions, and operation R is :term:`logical consequence` (⊢), then provided that proposition p is a member of O and p is R-related to q (i.e., p {\displaystyle \vdash }\vdash  q), q is also a member of O.

   definitionally equal
     In :term:`type theory`, two terms with the same :term:`normal form` are called **definitionally equal**.
 
   Δ(𝖢)
     is the **expansion** of Δ by :term:`new constants symbols <new constant symbol>` :math:`C` (not occuring in Δ), which is defined to be the class of all the :term:`formulas <formula>` obtained from formulas φ ∈ Δ upon substituting (at will) elements from C for variables in φ. ("At will" indicates that Δ ⊆ Δ(C).)
 
   Δ-part
     If Δ is an arbibtrary class of formulas, then the Δ-**part** of an L-theory :math:`T` is :math:`T_Δ = (T ∩ Δ)^⊢`.

   dependent function type
     See: :term:`Pi type`
 
   dependent pair type
     See: :term:`Sigma type`.
 
   dependent product type
     See: :term:`Sigma type`.
 
   dependent type
     A **dependent type** is actually a family of types indexed by some parameter. That is, a dependent type provides a *type schema*, which is a collection of types indexed by a set of values. For example, the type ``Fin n`` of finite sets of size ``n`` is a type that *depends* on the value ``n``.  More examples are in :numref:`dependent-types`_.
     
     See also: the `Dependent Types`_ section in the `TPL`_ tutorial.
 
   dependent type theory
     refers to any :term:`type theory` that supports :term:`dependent types <dependent type>`.
 
     In **dependent type theory**, every term has a computational behavior and may be *reduced* using certain reduction rules (e.g., the α, β, η rules).  The form beyond which a term :math:`t` is irreducible, if such a form exists, is called the :term:`normal form` of :math:`t`. Two terms with the same normal form are called :term:`definitionally equal`.
 
   elementary class
     See: :term:`axiomatizable`

   elementary map
     If 𝕄 = ⟨M, ...⟩ and ℕ = ⟨N, ...⟩ are 𝖫-structures, then a map f: M → N is called **elementary** if f: 𝕄 :math:`\stackrel{≡}{↪}` ℕ.
 
   elementarily embeddable
     Let 𝕄 = ⟨M, ...⟩ and ℕ = ⟨N, ...⟩ be 𝖫-structures. We say that 𝕄 is **elementarily embeddable** in ℕ, and we write :math:`𝕄 \stackrel{≡}{↪} ℕ`, if there is an elementary map f: 𝕄 :math:`\stackrel{≡}{↪}` ℕ.
 
   entailment
     We say that :math:`Σ` **entails** :math:`φ`, and we write :math:`Σ ⊢ φ`, if just in case every model of :math:`Σ` also models :math:`φ`.

     See also: :term:`logical consequence`
 
   equational base
     An **equational base** (or **base**) for a variety 𝒱 is a set Σ of equations such that 𝒱 = Mod(Σ). We say that 𝛴 is a base for an algebra 𝐀 if Σ is a base for 𝕍(𝐀) (the variety generated by 𝐀). 

     Let 𝒦 be a class of algebras and Σ a set of equations, each of signature σ = (F, ρ). Recall,
      
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
     Let :math:`A` and :math:`D` be types and for each :math:`a: A`, let :math:`C_a` be a type. Then the (dependent) **fork function**, denoted
  
     .. math:: \mathbf{fork}: ∏_{a:A}(C_a → D) → ∏_{a:A} C_a → ∏_{a:A} (C_a → D) × C_a,
     
     is defined as follows: for all :math:`h: ∏_{a:A}(C_a → D)` and :math:`k: ∏_{a:A} C_a`,
     
     .. math:: \mathbf{fork}\, (h)(k): ∏_{a:A}((C_a → D) × C_a),

     and for each :math:`a:A`,

     .. math:: \mathbf{fork}\, (h)(k)(a) = (h\,a, k\,a): (C_a → D) × C_a.

     Thus, :math:`\mathbf{eval} \, \mathbf{fork}\, (h)(k)(a) = (h\, a)(k\, a)` is of type :math:`D`.

   formula
     The **formulas** of a :term:`signature` σ (or σ-formulas) are defined recursively as follows:
 
       * if :math:`t_1` and :math:`t_2` are :term:`σ-terms <σ-term>`, then :math:`t_1 = t_2` is a σ-formula;
       * if :math:`t: n → 𝒯` is a tuple of σ-terms and :math:`R ∈ 𝐑` is an :math:`n`-ary relation symbol, then :math:`R t` is a σ-formula;
       * if φ and ψ are σ-formulas and x is a variable, then ¬ φ, φ ∧ ψ, and ∃ x φ are formulas too;
       * if φ can be constructed in finitely many steps from some combination of the three items above, then φ is a fornıula.
 
   free variable
     A variable that is not :term:`bound <bound variable>` by a quantifier is called a **free variable**.
     
     A formula in first-order logic is an assertion about the free variables in the formula.
     
     For example, if the "domain of discourse" is the set of natural numbers, then the formula :math:`∀ y \; (x ≤ y)` asserts that :math:`x` is less or equal every natural number.
     
     This is logically equivalent (more precisely, "α-equivalent") to the formula :math:`∀ z \; (x ≤ z)`.  
     
     On the other hand, the formula :math:`\forall y (w \le y)` says that :math:`w` is less than or equal to every natural number. This is an entirely different statement: it says something about :math:`w`, rather than :math:`x`. So renaming a *free* variable changes the meaning of a formula.

   function extensionality
     the principle that takes two functions :math:`f : X → Y` and :math:`g : X → Y` to be equal just in case :math:`f(x) = g(x)` holds for all :math:`x : X`; such functions are sometimes called "Leibniz equal."
 
     In Lean, one defines function extensionality for functions of (dependent) type :math:`Π(x:α), β x` as follows:
 
     .. code-block:: lean
 
        def equiv (f₁ f₂: Π x:α, β x): Prop := ∀ x, f₁ x = f₂ x
 
   functional programming
     See: https://en.wikipedia.org/wiki/Functional_programming

   implication elimination
     See: the `section on implication <https://leanprover.github.io/logic_and_proof/propositional_logic.html#implication>`_ in the `Logic and Proof`_ book.

   implicit arguments
     See: sections `Implicit arguments`_ and `More on implicit arguments`_ of `TPL`_.

   impredicative
     A self-referencing definition is called **impredicative**. A definition is said to be impredicative if it invokes (mentions or quantifies over) the set being defined, or (more commonly) another set which contains the thing being defined.

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

   𝖫
     The **language** of the signature σ is denoted by 𝖫(σ) (or just 𝖫 if σ is clear from context) and defined to be the set of all :term:`σ-formulas <σ-formula>`.
     
   𝖫₀
     denotes the set all sentences in the language :math:`𝖫`. We call :math:`𝖫_0` the set of ":math:`𝖫`-sentences".
 
   𝖫(𝖢)
     Let 𝖫 be a :term:`language` and C a collection of :term:`new constant symbols <new constant symbol>`. We denote by 𝖫(C) the **expansion** of 𝖫, which is defined to be the (uniquely determined) language of :term:`signature` (𝐂 ∪ C, 𝐅, 𝐑, ρ).
 
   𝖫(σ)
     The **language** of the signature σ is denoted by 𝖫(σ) (or just 𝖫 if σ is clear from context) and defined to be the set of all :term:`σ-formulas <σ-formula>`.
 
   𝖫(σ)-structure
     See: :term:`σ-structure`
 
   lambda calculus
     See: https://en.wikipedia.org/wiki/Lambda_calculus
 
   law of the excluded middle
     This is an axiom of classical logic asserting that for all propositions P either ¬ P or P holds.
     
     See also: the `LEM Section <https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html?highlight=reduction%20rule#the-law-of-the-excluded-middle>`_ of the :term:`TPIL`.

   Lean
     An :term:`extensional`, :term:`impredicative` :term:`ITP` supporting :term:`dependent types <dependent type>` and based on :term:`CiC`; url: https://leanprover.github.io/.

   language
     The formal **language** L = L(σ) is the set of all :term:`σ-formulas <formula>`.

   Leibniz equal
     See: :term:`function extensionality`
 
   literal formula
     An :math:`L`-**literal formula** (or just **literal** if :math:`L` is clear from context) is an :term:`atomic <atomic formula>` or negated atomic :math:`L`-formula.

     We denote by :math:`𝗅𝗍_L` the set of all :math:`L`-literals; that is, :math:`𝖺𝗍_L ∪ \{¬ φ : φ ∈ 𝖺𝗍_L\}`;
 
   logical consequence
     The **logical consequence** (or **entailment**) relation, denoted by ⊢, is a binary relation on the set of all statements in a language; we write (φ, ψ) ∈ ⊢, or equivalently, φ ⊢ ψ holds, and we say "φ entails ψ" or "ψ is a logical consequence of φ", precisely when the statement ψ can be deduced from the statement φ.

     See also: :term:`entailment`

   logically equivalent
     Propositions P and Q are **logically equivalent** provided P implies Q and Q implies P.

   :math:`𝗅𝗍_{𝖫(M)}`
     is the set of all atomic and negated atomic :math:`𝖫(M)`-formulas.
 
   𝕄 ⊧ φ
     By :math:`𝕄 ⊧ φ` we denote the assertion that φ is :term:`valid` in 𝕄.
 
   metaprogram
     a program whose purpose is to modify the behavior of other programs; :term:`proof tactics <proof tactic>` form an important class of metaprograms.

   model
     A **model** of a theory is a :term:`structure` (e.g. an interpretation) that satisfies the :term:`sentences <sentence>` of that theory.

   model theory
     The study of classes of mathematical structures (e.g. groups, fields, graphs, universes of set theory) from the perspective of mathematical logic is called **model theory**. The objects of study are models of :term:`theories <theory>` in a formal :term:`language`. A set of :term:`sentences <sentence>` in a formal language is one of the components that form a theory. 

     Model theory examines semantical elements (meaning and truth) by means of syntactical elements (formulas and proofs) of a language. Model theory, like proof theory, is an interdisciplinary area that intersects with mathematics, philosophy, and computing science.
 
   modus ponens
     See: :term:`implication elimination`

   negative formula
     A negated :term:`positive formula` is called a **negative formula**. The class of all such formulas is denoted by :math:`\boldsymbol{-}`.
 
   new constant symbol
     Let 𝖫 be a :term:`language`.  A **new constant symbol** (or **new constant**) for 𝖫 is a symbol not already present in the alphabet of 𝖫.
 
   normal form
     In :term:`dependent type theory`, every term has a computational behavior and may be *reduced* using certain reduction rules (e.g., the α, β, η rules).  The form beyond which a term :math:`t` cannot be reduced, if such a form exists, is called the **normal form** of :math:`t`. 
  
     In a :term:`rewriting` system, a term is said to be in **normal form** if it does not admit any further rewrites.

     See also: https://ncatlab.org/nlab/show/normal+form

   NuPRL
     An :term:`extensional`, :term:`predicative` :term:`ITP` supporting :term:`dependent types <dependent type>` and based on Martin Lof type theory; url: http://www.nuprl.org/

   Pi type
     The **Pi type** :math:`Π(x:A),B x`, also known as a **dependent function type**, is a dependent type that generalizes the type :math:`A → B`; it is a :term:`dependent type` because the codomain :math:`B x` depends on the value :math:`x`.
     
     See also: the `Dependent Types`_ section of the `TPL`_ tutorial.

   polymorphic type
     See: https://ncatlab.org/nlab/show/polymorphism

   positive boolean combination
     Let Σ be a set of :term:`formulas <formula>`. A **positive boolean combination** of formulas from Σ is obtained by connecting formulas from Σ with only ∧ and ∨. 
 
   positive formula
     A formal obtained from :term:`atomic formulas <atomic formula>` using only ∧, ∨, ∃, ∀ is called a **positive formula**.  The class of all positive formulas (of all possible languages) is denoted by :math:`\boldsymbol{+}`.
 
   power
     The **power** (or **cardinality**) of an L-:term:`theory` :math:`T` is denoted by :math:`|T|` and defined to be the cardinality of the language L.

   pp-construction
     Let (𝔸, 𝔹) and :math:`(𝔸', 𝔹') = ((A', R_0, \dots, R_{n-1}), (B', S_0, \dots, S_{n-1}))`  be :term:`PCSP templates <PCSP template>`. We say that (𝔸, 𝔹) **pp-constructs** (𝔸', 𝔹') if there is a sequence
     
     .. math:: (𝔸, 𝔹)  = (𝔸_0, 𝔹_0), (𝔸_1, 𝔹_1), \dots, (𝔸_n, 𝔹_n) = (𝔸', 𝔹'),
 
     of PCSP templates such that each :math:`(𝔸_{i+1}, 𝔹_{i+1})` is a :term:`pp-power` or a :term:`homomorphic relaxation` of :math:`(𝔸_i, 𝔹_i)`.
 
   pp-definable
     Let (𝔸, 𝔹) and :math:`(𝔸', 𝔹') = ((A', R_0, \dots, R_{n-1}), (B', S_0, \dots, S_{n-1}))`  be :term:`PCSP templates <PCSP template>`. We say that (𝔸', 𝔹') is **pp-definable** from  (𝔸, 𝔹) if, for each :math:`0≤ i < n`, there exists a :term:`pp-formula` φ over 𝔸 such that φ defines :math:`R_i` and the formula, obtained by replacing each occurrence of a relation of 𝔸 by the corresponding relation in 𝔹, defines :math:`S_i`. 
 
   pp-power
     We say that (𝔸', 𝔹') is an :math:`n`-th **pp-power** of (𝔸, 𝔹) if :math:`A' = A^n`, :math:`B' = B^n` and (𝔸', 𝔹') is :term:`pp-definable` from (𝔸, 𝔹) (where we view :math:`k`-ary relations on 𝔸' and 𝔹' as :math:`kn`-ary relations on :math:`A` and :math:`B`, respectively).
 
   primitive formula
     A **primitive formula** is a :term:`formula` of the form :math:`∃ x₀, \dots, x₁ \ φ`, where φ is a conjunction of :term:`literals <literal formula>`. (The set :math:`\{x₀,\dots ,x₁\}` may be empty.)

   pp-formula
     A **primitive positive formula** (or **pp-formula**) is a :term:`primitive formula` :math:`∃ x₀, \dots, x₁ \ φ` such that no negated atomic formulas occur in φ.

   pp-sentence
     A **pp-sentence** is a :term:`pp-formula` that contains no :term:`free variables <free variable>`.

   predicative
     The opposite of :term:`impredicative`, *predicative* refers to building stratified (or ramified) theories where quantification over lower levels results in variables of some new type, distinguished from the lower types that the variable ranges over.

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
     
     See also: the `Proposition Extensionality <https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#propositional-extensionality>`_ section of the :term:`TPIL`.

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
     A **quasiidentity** in the language L is an implication of the form s₁ ≈ t₁ ∧ ... ∧ sₙ ≈ tₙ ⟶  s ≈ t, where s, s₁, ..., sₙ, t, t₁, ..., tₙ are terms built up from variables using the operation symbols of L.
 
   record
     See: :term:`structure`

   recursor
     Each :term:`inductively defined type <inductive type>` ``T`` is accompanied by an elimination principle known as a **recursor** (denoted by ``T.rec`` in Lean). It is what makes the type "inductive" by allowing us to define a function on ``T`` by assigning values for each of ``T``'s constructors.
     
     See also: :numref:`inductively-defined-types`.

   relational structure
     A relational structure :math:`𝔸 = ⟨A, ℛ⟩` is a set :math:`A` together with a collection :math:`ℛ` of relations on :math:`A`.
 
     See also: the definition of a :term:`structure`.
 
   rewriting
     See: https://ncatlab.org/nlab/show/rewriting

   sentence
     A :term:`formula` φ is called a **sentence** (or **closed formula**) if it contains no :term:`free variables <free variable>`; that is, all variables appearing in φ are :term:`bound <bound variable>`.

   :math:`Σ^⊢`
     denotes the set {φ ∈ 𝖫₀ : Σ ⊢ φ} of :term:`logical consequences <logical consequence>` of Σ.
 
   :math:`σ`
     In :term:`model theory`, a **signature** σ = (𝐂, 𝐅, 𝐑, ρ) consists of three (possibly empty) sets 𝐂, 𝐅, and 𝐑---called *constant symbols*, *function symbols*, and *relation symbols*, respectively---along with a function ρ: 𝐂 + 𝐅 + 𝐑 → N that assigns an :term:`arity` to each symbol. Often (but not always) N = ℕ. 
 
   Sigma type
     The **Sigma type** :math:`Σ(x:A),B x`, also known as the **dependent pair type**, generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second argument of the ordered pair to depend on the value :math:`x` of the first.
      
     See also: the `Dependent Types`_ section of the `TPL`_ tutorial.

   σ-formula
     See: :term:`formula`.
 
   σ-structure
     See: :term:`structure`.

   structure
     A **structure** in the :term:`signature` σ = (𝐂, 𝐅, 𝐑, ρ) consists of the pair 𝔸:=(A, {𝐂^𝔸, 𝐅^𝔸, 𝐑^𝔸}), where A is a set, 𝐂^𝔸 is a collection of named constants in A (one for each constant symbol in 𝐂), 𝐅^𝔸 is the collection of basic operations of 𝔸 (one for each operation symbol in 𝐅), and 𝐑^𝔸 is the collection of relations on 𝔸 (one for each relation symbol in 𝐑).
     
     In Lean, a non-recursive inductive type that contains only one constructor is called a **structure**. In mathematics, a structure may refer to an :term:`algebraic structure` or a :term:`relational structure`.

   substitution
     The notation f ∘ 𝐚 is shorthand for :math:`(f(a_0), f(a_1), \dots)` and :math:`φ_{𝐱}(𝐚)` is shorthand for :math:`[a_0/x_0, a_1/x_1, \dots]φ(x_0, x_1, \dots)`, the sentence obtained from φ upon substituting :math:`a_i` for :math:`x_i`, for all :math:`i`.
 
   theory
     An :math:`L`-**theory** (or **theory** when the context makes :math:`𝖫` clear) is a :term:`consistent` and :term:`deductively closed <deductive closure>` set of :math:`L`-:term:`sentences <sentence>`.

   Th ℳ
     The collection {φ ∈ L₀: ℳ ⊧ φ} of all L-sentences that are true in ℳ is denoted by Th ℳ. This set is sometimes denoted by :math:`\mathrm{Th}_{L_0}`.

     If Δ is an arbibtrary class of formulas, then Th_Δ ℳ := {φ ∈ L₀: φ ∈ Δ,\ ℳ ⊧ φ}, the set of all L-sentences in Δ that are true in ℳ.

   true quantified Boolean formula
     The language **TQBF** is a formal language consisting of the **true quantified Boolean formulas**. A (fully) quantified Boolean formula is a formula in quantified propositional logic where every variable is bound using either existential or universal quantifiers at the beginning of the sentence. Such a formula is equivalent to either true or false. If such a formula evaluates to true, then that formula is in the language TQBF.

     See also: https://en.wikipedia.org/wiki/True_quantified_Boolean_formula

   type class
     A **type class** is a family of types; each type in the family is called an :index:`instance` of the type class.  **N.B.** Lean will infer an implicit argument using the type class mechanism if we put the argument in square brackets (instead of curly braces) in the declaration.

   type theory
     **Type theory** internalizes the interpretation of intuitionistic logic proposed by Brouwer, Heyting, and Kolmogorov---the so-called BHK interpretation. The types in type theory play a similar role to that of sets in set theory but *functions definable in type theory are always computable*.

     Intuitionistic **type theory** extends the :term:`Curry-Howard correspondence` to predicate logic by introducing :term:`dependent types <dependent type>`. 
      
     See also: https://ncatlab.org/nlab/show/type+theory

   universal part
     We denote by :math:`\boldsymbol{∀}` the class of formulas in which ∃ does not appear; :math:`\mathrm T_{\boldsymbol ∀} = (\mathrm T ∩ \boldsymbol ∀)^⊢` is the **universal part** of T.

   universe polymorphism
     We use an example to demonstrate this concept. Given a type ``α``, no matter to which type universe ``α`` belongs, we can form the type ``list α`` of lists of elements of type ``α``, and this type will have the same type universe as ``α``. In other terms, 
     
       ``α: Type u`` if and only if ``list α: Type u``.
       
     The Lean code for this example follows.

     :: 

       universes u v
       variables (α: Type u) (β: Type v)
       #check list      -- Type u_1 → Type u_1
       #check list α    -- Type u
       #check list β    -- Type v

     The variable ``u_1`` ranges over type levels.  As the output of the ``#check`` shows, ``list α`` has ``Type u`` because ``α`` has ``Type u``. Similarly for ``list β``. 

   valid
     We say that φ is **valid** in 𝕄, and we write 𝕄 ⊧ φ, if for every tuple 𝐚 from 𝕄 (that is at least as long as 𝐱) the 𝖫-sentence φ(𝐚) is **true** in 𝕄.

-----------------------
