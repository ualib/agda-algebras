.. File: glossary_topology.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 8 Dec 2019
.. Updated: 8 Dec 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. role:: code

.. highlight:: lean


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
     A real- or complex-valued :math:`μ`-:term:`measurable function` :math:`f` is called :math:`μ`-**integrable** (or **integrable with respect to** :math:`μ`, or just **integrable**) over :math:`X` if :math:`∫_X |f| \, dμ < ∞`.  We let :math:`L_1(X, μ)` (or :math:`L_1(μ)`, or just :math:`L_1`) denote the collection of functions that are :math:`μ`-integrable over :math:`X`.

     When :math:`f∈ L_1(X, μ)` we define the :term:`integral` of :math:`f` over a measurable set :math:`E ⊆ X` by :math:`∫_E f\, dμ = ∫_E f^+\, dμ - ∫_E f^-\, dμ`.

   integral
     See :term:`Lebesgue integral`.

   interior
     If :math:`X` is a :term:`topological space` and :math:`A ⊆ X`, then the union of all :term:`open sets <open set>` contained in :math:`A` is called the **interior** of :math:`A`.

   isometrically isomorphic
     Two :term:`Hilbert spaces <Hilbert space>` :math:`ℋ_1, ℋ_2` are called **isometrically isomorphic** if there exists a :term:`unitary operator` from :math:`ℋ_1` onto :math:`ℋ_2`.

     In other words, :math:`U: ℋ_1 ↠ ℋ_2` is a surjective :term:`isometry` from :math:`ℋ_1` to :math:`ℋ_2`.

   isometry
     Let :math:`(X, \|\,.\,\|_1)` and :math:`(Y, \|\,.\,\|_2)` be :term:`normed linear spaces <normed linear space>`.  A :term:`linear transformation` :math:`T: X → Y` is called an **isometry** if it preserves norms, that is, :math:`\|Tx\|_2 = \|x\|_1` holds for all :math:`x∈ X`.

   Lebesgue integrable
     A function that is :term:`integrable` with respect to :term:`Lebesgue measure` is called a **Lebesgue integrable** function.

   Lebesgue integral
     Let :math:`(X, 𝔐, μ)` be a :term:`measure space`.  If :math:`E ∈ 𝔐` and :math:`s: X → [0, ∞)` is a :term:`measurable <measurable function>` :term:`simple function` of the form :math:`s = ∑_{i=1}^n α_i χ_{A_i}`, where :math:`α_1, \dots, α_n ∈ ℝ` are the distinct values of :math:`s`, then we denote and define the **Lebesgue integral** of :math:`s` over :math:`E` as follows:
     
     .. math:: ∫_E s\, dμ := ∑_{i=1}^n α_i μ(A_i ∩ E),
     
     where we adopt the convention that :math:`0⋅∞ = 0` (in case, e.g., :math:`α_i = 0` and :math:`μ(A_i ∩ E) = ∞` for some :math:`1≤ i ≤ n`).
     
     If :math:`f: X → [0, ∞]` is a nonnegative extended real-valued measurable function and :math:`E∈ 𝔐`, then we denote and define the **Lebesgue integral** of :math:`f` over :math:`E` with respect to the measure :math:`μ` (or, the **integral** of :math:`f`) as follows:

     .. math:: ∫_E f\, dμ := \sup ∫_E s\, dμ,

     where the supremum is taken over all simple measurable functions :math:`s` such that :math:`0≤ s ≤ f`.

     If :math:`μ` is the only :term:`measure` in context, then we may write :math:`∫_E f` in place of :math:`∫_E f\, dμ`, and :math:`∫ f` in place of :math:`∫_X f`.

   Lebesgue measurable function
     Let :math:`E⊆ ℝ`.  A function :math:`f: E → ℝ` is called **Lebesgue measurable** provided :math:`f^{-1}(G)` is a :term:`Lebesgue measurable set` for every open set :math:`G ⊆ ℝ`.  Equivalently, :math:`f` is Lebesgue measurable iff the set :math:`f^{-1}((α, ∞))` is Lebesgue measurable for every :math:`α ∈ ℝ`.

   Lebesgue measurable set
     A set that is :term:`measurable <measurable set>` with respect to :term:`Lebesgue measure` is called a **Lebesgue measurable** set; that is, :math:`E⊆ ℝ` is Lebesgue measurable iff

     .. math:: m^∗ A = m^∗ (A ∩ E) + m^∗(A ∩ E^c)\; \text{ holds for all } A ⊆ R.

   Lebesgue measure
     Let :math:`ℓ` be the :term:`measure` defined on the :term:`semiring <semiring of sets>` :math:`S := \{[a, b) ∣ a, b ∈ ℝ\}` of bounded intervals by :math:`ℓ[a, b)= b-a` for all :math:`a ≤ b`. Let :math:`ℓ^∗: 𝒫(ℝ) → [0, ∞]` be the :term:`outer measure` generated by :math:`ℓ`.  That is, for :math:`E⊆ ℝ`,
     
     .. math:: ℓ^∗(E) := \inf \{∑_{n=1}^∞ m(I_n) ∣ \{I_n\} ⊆ S \text{ and } E ⊆ ⋃_{n=1}^∞ I_n\}
     
     The measure obtained by restricting :math:`ℓ^∗` to the :term:`measurable subsets <measurable set>` in :math:`𝒫(ℝ)` is called **Lebesgue measure**.
     
     Observe that the :math:`ℓ^∗`-:term:`measurable subsets <measurable set>` in :math:`𝒫(ℝ)` are those :math:`A∈ 𝒫(ℝ)` satisfying

     .. math:: ℓ^∗ E = ℓ^∗(E ∩ A) + ℓ^∗(E ∩ A^c)\; \text{ for all } E ⊆ ℝ.

   Lebesgue null set
     A **Lebesgue null set** is a set of :term:`Lebesgue measure` zero.

   Lebesgue outer measure
     See :term:`Lebesgue measure`

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

   Lipschitz condition
     A function :math:`f` satisfies a **Lipschitz condition** on an interval if there is a constant :math:`M` such that :math:`|f(x) - f(y)| ≤ M|x-y|` for all :math:`x`and :math:`y` in the interval.

   Lipschitz constant
     The number :math:`M` in the definition of :term:`Lipschitz condition` is called the **Lipschitz constant**.

   Lipschitz continuous
     A function is called **Lipschitz continuous** on an interval if it satisfies a :term:`Lipschitz condition` on that interval.

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

.. rubric:: Footnotes

.. [1]
   See Rudin :cite:`Rudin:1987` 1.35-6 for a nice discussion of the role played by sets of measure 0.  To summarize that discussion, it may happen that there is a set :math:`N ∈ 𝔐` of measure 0 that has a subset :math:`E ⊆ N` which is not a member of :math:`𝔐`.  Of course, we'd like all subsets of measure 0 to be measurable and have measure 0.  It turns out that in such cases we can extend :math:`𝔐` to include the offending subsets, assigning such subsets measure 0, and the resulting extension will remain a :math:`σ`-algebra.  In other words, we can always *complete* a measure space so that all subsets of negligible sets are measurable and negligible.

.. [2]
   The use of this term is not quite standardized; some (e.g., Rudin :cite:`Rudin:1987`) call any open set containing :math:`p` a "neighborhood of :math:`p`".

.. [3]
   This notation is not completely standard. In :cite:`Aliprantis:1998` (page 154) for example, :math:`𝔐 ⊗ 𝔑` denotes what we call :math:`𝔐 × 𝔑`, while :math:`σ(𝔐 ⊗ 𝔑)` denotes what we have labeled :math:`𝔐 ⊗ 𝔑`. At the opposite extreme, Rudin (in :cite:`Rudin:1987`) simply takes :math:`𝔐 × 𝔑` to be the :term:`σ-algebra` generated by the sets :math:`\{A × B ∣ A ∈ 𝔐, B ∈ 𝔑\}`.

