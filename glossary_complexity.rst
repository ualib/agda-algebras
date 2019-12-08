.. File: glossary_complexity.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 8 Dec 2019
.. Updated: 8 Dec 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. role:: code

.. highlight:: lean


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
     A decision problem or language has **logarithmic space complexity** if it can be solved by a deterministic :term:`Turing machine` using a logarithmic amount of writable memory space.  The complexity class of such problems is known as **LOGSPACE** (or **L** or **LSPACE** or **DLOGSPACE**).
     
     Formally, a Turing machine has two tapes, one encoding the input which can only be read from, and one of logarithmic size that can be both read from and written to.
     
     Logarithmic space is sufficient to hold a constant number of pointers into the input and a logarithmic number of boolean flags, and many basic LOGSPACE algorithms use the memory in this way.

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
     A decision problem or language has **nondeterministic logarithmic space** complexity if it can be solved by a nondeterministic Turing machine using a logarithmic amount of writable memory space.  The class of such problems is usually denote by **NLOGSPACE** (or **NL** or **NLSPACE**).

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

