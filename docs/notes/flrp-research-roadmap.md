<!-- File: docs/notes/flrp-research-roadmap.md -->

# FLRP research roadmap — a strategy for attacking the finite lattice representation problem

This note is the planning document for a research program on the Finite Lattice Representation Problem (FLRP), to be carried out inside agda-algebras with the formalization discipline of this library.  It records the decision about where the work lives, a snapshot of the state of the art (July 2026), the primary avenue of attack (interval-enforceable properties, after [DeMeo 2012b]), the secondary avenues, the formalization architecture, and a breakdown into PR-sized work packages.  It is a working research note, not library documentation; per `docs/STYLE_GUIDE.md` it lives in `docs/notes/` and is excluded from the rendered site.

Research-track separation reminder: the FLRP is distinct from the algebraic-complexity / finite-CSP track (M7) and from the Maltsev/interpretability infrastructure of M6, even where they share modules.  Nothing in this program should be conflated with CSP work (see `CLAUDE.md` and the warnings in `docs/GITHUB_PROJECT.md`).

## 1. Where the work lives — recommendation

**Recommendation: work inside agda-algebras, not a new repository.**  The reasons are structural, not sentimental:

+  The repository already anticipates this program: milestone M6 is literally titled "Toward the Finite Lattice Representation Problem", and its prerequisites are largely built — `Con 𝑨` and `Sub 𝑨` as complete lattices (`Setoid.Congruences.CompleteLattice`, `Setoid.Subalgebras.CompleteLattice`), quotients and the isomorphism theorems (`Setoid.Homomorphisms.Noether`), subdirect representation for finite algebras with a `FiniteAlgebra` interface (`Setoid.Subalgebras.Subdirect.Finite`), and even a formalized copy of the exceptional seven-element lattice (`Examples.Classical.Lattices.L7`).
+  Research-grade formalization will constantly add general-purpose modules (group actions, cosets, subgroup lattices, finite-lattice combinatorics).  In-repo, a single PR can extend the foundation and use the extension atomically; a separate repo would fight version skew against the very library it must keep changing.
+  The toolchain is already paid for: the Nix flake, CI type-checking, the literate style, the corpus-quality conventions (M8), and the worktree workflow all apply unchanged.  A new repo would duplicate all of it and then bit-rot.
+  The exit is cheap in one direction only.  If the program later accumulates heavy non-Agda assets (GAP search logs, SAT runs, LaTeX for papers), those can be spun out into a companion repo (working name `flrp-lab`) at that point; extracting is easy, but merging a diverged research repo back into the library would not be.
+  Separation of concerns is achieved by namespace and labels, not by repository boundary: a dedicated source tree (`src/FLRP/`, § 6), this notes file plus successors in `docs/notes/`, eventual papers in `docs/papers/` per the style guide, a GitHub label (proposed: `flrp-research`, distinct from the infrastructure label `milestone-6-flrp`), and a GitHub Project board scoped to that label.

Two consequences worth making explicit.  First, FLRP research modules should be marked experimental and exempted from the stable-API deprecation discipline until results stabilize, so research iteration does not create deprecation debt.  Second, `docs/GITHUB_PROJECT.md` milestone sections are generated (`BEGIN GENERATED` markers), so registering the research program as a milestone happens through that tooling after this plan is approved, not by hand-editing the file.

## 2. The problem and its equivalent forms

**FLRP.**  Is every finite lattice isomorphic to the congruence lattice `Con 𝑨` of some finite algebra `𝑨`?

+  Grätzer–Schmidt [1963] represent every algebraic lattice as `Con 𝑨` for an infinite algebra `𝑨`, so finiteness of the algebra is the entire content of the problem.
+  Pálfy–Pudlák [1980] prove the two universally quantified statements are equivalent: (i) every finite lattice is the congruence lattice of a finite algebra; (ii) every finite lattice is an interval `[H, G]` in the subgroup lattice of a finite group.  The equivalence is global, not lattice-by-lattice; the bridge from (ii) to (i) is the elementary isomorphism `Con (G ↷ G/H) ≅ [H, G]` for the transitive G-set on cosets.
+  Tůma [1989] shows every algebraic lattice is an interval in the subgroup lattice of an *infinite* group, so finiteness is also the entire content on the group side.
+  Pudlák–Tůma [1980] show every finite lattice embeds as a *sublattice* of a finite partition lattice (Whitman's problem); the contrast between sublattice embedding (solved) and interval/congruence representation (open) is instructive, and the sublattice-closure question for representable lattices remains open.

**Default bet.**  This program bets on a negative answer pursued through formulation (ii), with a positive-direction insurance policy for the exceptional lattice `L7` (§ 5, avenue A), so that effort is not wasted if the truth goes the other way: both branches produce publishable, formally verified artifacts.

## 3. State of the art — July 2026 snapshot

Known representable classes and closure properties:

+  Every finite distributive lattice is the congruence lattice of a finite lattice (Dilworth; first published proof Grätzer–Schmidt [1962]).
+  Every lattice with at most seven elements is representable, with the single possible exception of the lattice `L7` [DeMeo 2012a]; there are 53 seven-element lattices (OEIS A006966), so this closed 52 of 53, identifying `L7` as the unique smallest lattice with no known representation.
+  The class of representable lattices is closed under finite direct products, ordinal sums, and adjoining a new top or bottom; remarkably it is also closed under dualization (Kurzweil [1985] for intervals in solvable groups, Netter [1986] in general — the latter possibly never published, which makes it a rescue-worthy formalization target).
+  It is open whether the class is closed under sublattices; sublattice closure would in fact settle the whole problem via Pudlák–Tůma, which is strong evidence that it fails or is very hard.
+  `L7` itself: the 2×3 grid (product of a two-chain and a three-chain) side by side with a single doubly irreducible element `x` (`⊥ < x < ⊤`, `x` incomparable to the rest); it contains `N5` and is self-dual, so Kurzweil–Netter duality gives nothing new for it.  The lattice, its Cayley tables, non-distributivity, and the unique atom-coatom property are already machine-checked in `Examples.Classical.Lattices.L7`.

The `M_n` frontier (height-two lattices with `n` atoms), the classical stress test for formulation (ii):

+  `M_n` is known to be an interval in a finite subgroup lattice for `n = 1, 2`, `n = q + 1` (`q` a prime power, from two-dimensional vector spaces), `n = q + 2`, and `n = (qᵗ + 1)/(q + 1) + 1` (`t` an odd prime), the last two families due to Lucchini [1994]; Feit [1983] had realized `M_7` and `M_11` as intervals in `Sub(A₃₁)` via normalizers of Sylow-31 subgroups of `PSL(5,2)` and `PSL(3,5)` respectively.
+  The smallest `n` outside all known families is `n = 16`, and no `M_n` has ever been proved non-representable; verify the `M_16` claim against Pálfy's surveys during the Phase 0 bibliography pass.
+  Burness–Liebeck–Shalev [2017] tie the structure of second maximal subgroups (exactly the bottoms of `M_n`-type intervals) to the existence of certain "special primes", strong evidence that even the `M_n` subproblem is entangled with open number theory.

Group-theoretic reduction theorems (the raw material for § 4):

+  Core-free reduction: for `N = Core_G(H)` one has `[H, G] ≅ [H/N, G/N]`, so every interval representation induces one with `H` core-free; all serious structure theory happens under this normalization.
+  Baddeley–Lucchini [1997] reduce the `M_n` question to specific questions about almost simple groups and twisted wreath products; Baddeley [1998] ("A new approach to the finite lattice representation problem") widens the target class of lattices with the same philosophy; Börner [1999] gives related reductions.
+  Aschbacher [2008] attacks *disconnected* intervals (his class `D∆`; the parallel sums `L₁ ∥ L₂` sharing only top and bottom are the paradigm): a minimal representation of such a lattice forces `G` almost simple or produces a signalizer lattice, pushing the problem into CFSG territory; the program continues through Aschbacher [2009], [2012], [2013].  As of mid-2026 no finite lattice has been eliminated, but these theorems are exactly "interval shape forces group structure" statements — i.e., enforceability results in the sense of § 4.
+  On the positive side, the classification of Boolean overgroup lattices of rank ≥ 3 in alternating and symmetric groups (Lucchini–Moscatiello–Palcoux–Spiga [2019]) shows the "which shapes occur" program is active and CFSG-powered.

Universal-algebra-side methods:

+  The closure method and the G-set / overalgebra constructions of [DeMeo 2012a], with the expansion technique published as [DeMeo 2013] — these produced the ≤ 7 classification and are mechanizable (§ 5, avenue C).
+  Pálfy–Pudlák's minimality analysis: for suitable lattice shapes, a minimal-cardinality representing algebra is forced to be essentially a transitive G-set; combined with tame-congruence-theoretic constraints this is the UA-side forcing toolkit (§ 5, avenue D).

Adjacent problems worth monitoring (watchlist):

+  Intermediate subfactor lattices: Watatani [1996] proves finiteness for irreducible finite-index subfactors, and group–subgroup subfactors realize every interval `[H, G]` as an intermediate subfactor lattice; hence *non*-realizability in the subfactor world would imply non-realizability as an interval and settle the FLRP negatively via Pálfy–Pudlák.  The realization question there is open and active (dual Ore theorems, Palcoux and collaborators; Frobenius-lattice generalizations to tensor categories, arXiv:2502.19876 [2025]).
+  Computational tooling has improved materially since 2012: Hulpke's intermediate-subgroup algorithms in GAP [2017], mature SAT/SMT and finite-model finders, and cheap parallel compute; the counts of unlabeled lattices (8 elements: 222; 9: 1078; 10: 5994, OEIS A006966) put a frontier-pushing census within reach.

Bibliography caveat: this environment's egress policy blocks `arxiv.org`, `wikipedia.org`, and `api.semanticscholar.org`, so the snapshot above was assembled from search snippets plus prior knowledge; Phase 0 includes a verification pass over the full texts (and it would help to allow those hosts in the environment's network policy).

## 4. Primary avenue — interval-enforceable properties

The idea of [DeMeo 2012b]: classify group-theoretic properties by whether an interval shape can *force* them, then either combine enforceable properties into a contradiction (proving some lattice is not an interval, hence by Pálfy–Pudlák answering the FLRP negatively) or prove that no such contradiction is possible (a structural dead-end theorem, which would itself be a significant result about intervals).  Either outcome is progress; the point of this section is to make both outcomes precise enough to formalize.

Notation: for a finite lattice `L`, let `𝒢(L)` be the class of pairs `(H, G)` with `G` finite, `H ≤ G`, and `[H, G] ≅ L`, and let `𝒢₀(L) ⊆ 𝒢(L)` be the core-free pairs (`Core_G(H) = 1`).  A group property `P` is **interval enforceable (IE) via `L`** if `G ⊨ P` for every `(H, G) ∈ 𝒢(L)`, and **core-free interval enforceable (cIE) via `L`** if `G ⊨ P` for every `(H, G) ∈ 𝒢₀(L)`; Aschbacher-style *minimally* enforceable variants restrict further to representations minimizing `|G|`.  A definitional subtlety to get right in the formalization: if `𝒢(L) = ∅` then every property is vacuously enforced via `L`, and deciding emptiness *is* the original problem, so the framework must track witnesses explicitly rather than quantify them away.

Three elementary observations sharpen the program considerably; they should be reconciled against [DeMeo 2012b] (some appear there in some form) and then formalized first, because they redirect the search:

+  **N1 (inflation)**.  If `N ⊴ G` and `N ≤ H` then `[H, G] ≅ [H/N, G/N]`; in particular every representation induces a core-free one of the same lattice, and any interval in a quotient of `G` lifts to an interval of `G`, so plain-IE properties are stable under passing from `G/N` back up to `G`.
+  **N2 (fattening)**.  For every finite `S`, `[H × S, G × S] ≅ [H, G]`, because every subgroup containing `H × S` contains `1 × S` and hence splits as `A × S` with `H ≤ A ≤ G`.  Consequently any property that is plain-IE via an actually representable lattice is closed under adjoining arbitrary finite direct factors; no "upper-bound" property (solvability, nilpotence, bounded order, restricted composition factors, …) is plain-IE except vacuously.
+  **N3 (no contradictory plain-IE pair with witnesses)**.  Suppose `P` is IE via `L₁`, `¬P` is IE via `L₂`, and both lattices are actually intervals, say `[H₁, G₁] ≅ L₁` and `[H₂, G₂] ≅ L₂`.  Then in `G = G₁ × G₂` both `[H₁ × G₂, G] ≅ L₁` and `[G₁ × H₂, G] ≅ L₂` hold, so `G ⊨ P ∧ ¬P` — contradiction.  Hence contradictory plain-IE properties can exist only if one of the enforcing lattices is already non-representable: plain IE cannot *discover* a non-representable lattice from two separately witnessed enforcements.

The moral of N2/N3 is that the entire strategy necessarily lives at the **core-free** level, where the fattening trick fails (`1 × S` lies in `Core_{G×S}(H × S)`, so fattening destroys core-freeness), and cIE properties genuinely can be of upper-bound type — e.g. `[H, G]` a two-chain with `H` core-free forces `G` to be a primitive permutation group.  The crux is then the **composition problem**: how do two enforcing lattices combine into one lattice whose (core-free) representations force both properties at once?

+  Vertical (ordinal) gluing `L₁ ⊕ L₂` at a shared middle point `m` gives, from `[H, G] ≅ L₁ ⊕ L₂` with middle subgroup `M`, the two intervals `[H, M] ≅ L₁` and `[M, G] ≅ L₂` — but core-freeness of `H` in `G` passes to neither `(H, M)` nor `(M, G)`, so cIE facts do not compose vertically for free.
+  Parallel sums `L₁ ∥ L₂` have disconnected interiors, which is exactly Aschbacher's `D∆` setting: his reduction (minimal representation ⇒ almost simple or signalizer lattice) is an off-the-shelf composition engine for disconnected shapes, at the price of importing CFSG-adjacent theorems as explicit assumptions.
+  Identifying the right composition lemma — which gluing, which normalization (core-free where, minimality where), which side conditions — is the central technical question R1 below, and the precise content of [DeMeo 2012b] must be reconstructed and formalized as its starting point.

The research phases:

+  **R1 — formalize the framework**.  Reconstruct the definitions and lemmas of [DeMeo 2012b] precisely; formalize IE/cIE with explicit witness tracking, N1–N3, and the target meta-theorem schema: "if `P₁`, `P₂` are cIE via `L₁`, `L₂`, satisfy ⟨composition side conditions⟩, and are jointly unsatisfiable across ⟨the relevant subgroup/quotient relation⟩, then ⟨composite lattice⟩ is not an interval in any finite subgroup lattice; hence, by Pálfy–Pudlák (imported as an explicit hypothesis until formalized), the FLRP has a negative answer."  This machine-checks the *logic of the strategy itself*, so that all later effort concentrates on the genuinely mathematical gaps.
+  **R2 — the enforcement catalog**.  Recast the literature's reduction theorems as (c)IE facts with precise statements: Pálfy–Pudlák's `M_n` and minimality analyses, Kurzweil's solvable-interval structure, Baddeley–Lucchini, Börner, Aschbacher's `D∆`/signalizer theorems, Lucchini–Moscatiello–Palcoux–Spiga.  Each catalog entry gets a formal statement in Agda (assumption-parameterized where the proof stays on paper), creating the searchable, machine-readable inventory the hunt in R3 runs over.
+  **R3 — hunt for a contradictory pair**.  Systematically look for `(P₁, L₁)`, `(P₂, L₂)` in the catalog with `P₁, P₂` jointly unsatisfiable under a composition lemma from R1; the natural tension to exploit is between forced normal-subgroup structure ("unique minimal normal subgroup, nonabelian", "almost simple", signalizer configurations) on the two sides of a gluing.  Use computation as cheap falsification: before investing in a proof that a candidate lattice is non-representable, search for representations of it in the small-groups and primitive-groups libraries (Hulpke's algorithms), and for small candidate lattices attempt UA-side representations directly.
+  **R4 — the dead-end branch**.  Attempt structure theorems about the cIE class itself.  The sharpest formulation found so far: *is there a fattening construction that preserves core-freeness and the interval while adjoining arbitrary composition factors?*  The naive product `(H₁ × H₂, G₁ × G₂)` preserves core-freeness but not the interval (new intermediate subgroups appear), so the question has real content.  A positive answer would show cIE properties are also closed under fattening, killing the avenue with a theorem (the honorable dead end, formalized); obstructions to such a construction are precisely the places a contradiction can live, feeding back into R3.

Success criterion: a finite lattice `L` with a machine-checked proof (modulo the explicit assumption registry of § 6) that `L` is not an interval in any finite subgroup lattice.  Kill criterion for the avenue: an R4 dead-end theorem, or two consecutive review points (≈ quarterly) at which R3 produced no new viable candidate pair and R4 no new structural insight; in either case the program falls back to the secondary avenues with the catalog and infrastructure intact.

## 5. Secondary avenues

+  **A — computational campaign (with certificate discipline)**.  (i) Re-attack `L7` positively with 2026 resources: GAP interval searches over the small-groups, perfect-groups, and primitive-groups libraries using Hulpke's intermediate-subgroup algorithms, pruned by the thesis's restrictions on potential representations, plus SAT/model-finder searches for finite algebras with `Con ≅ L7` on carriers well beyond 2012 reach.  (ii) Push the census frontier from 7 to 8 elements (222 lattices) with the mechanized closure toolkit plus searches, producing a database of representability certificates.  (iii) Gather data on `M_16`.  Every positive find is imported as an Agda-checked certificate (§ 6), never trusted from the external tool alone.  First step: encode `Con(𝑨) ≅ L` as a SAT instance for tables on ≤ n elements.  Kill criterion: none — this avenue produces reusable artifacts regardless; it is insurance for the negative bet.
+  **B — Aschbacher-program engagement**.  Formalize the statements (not proofs) of the `D∆`/signalizer reduction theorems as R2 catalog entries; run GAP experiments realizing signalizer lattices in specific simple groups; the goal is either to finish a `D∆` case (a non-representable lattice) or to extract new cIE properties for R3.  This is the avenue most likely to benefit from expert correspondence.
+  **C — mechanize the overalgebra method**.  Implement the expansion constructions of [DeMeo 2013] as executable code (Haskell or Agda-with-extraction) and search the expansion space systematically where the thesis worked by hand with UACalc; target: new representations of stubborn small lattices, feeding avenue A's census.
+  **D — UA-side obstructions for `L7` directly**.  Formalize the Pálfy–Pudlák minimality forcing and the tame-congruence-theoretic constraints on a hypothetical minimal finite algebra `𝑨` with `Con 𝑨 ≅ L7`, aiming either at an outright contradiction (which would settle `L7` negatively without groups) or at a sharpened characterization that makes avenue A's searches drastically cheaper.  Long shot, but every intermediate result is a citable theorem about minimal representations.
+  **E — watchlist**.  Monitor the subfactor/tensor-category bridge (non-realizability there is *stronger* than non-interval, via group–subgroup subfactors), the Boolean-overgroup-lattice classification program, and any movement on `M_16` or the Burness–Liebeck–Shalev special-primes front; low ongoing cost, potentially decisive input.

## 6. Formalization architecture

+  **Namespace**.  A new top-level tree `src/FLRP/` (precedent: `Order/` was added as its own top-level tree), with a barrel module and submodules `FLRP.Problem` (representability predicate and the formal FLRP statement), `FLRP.Closure` (closure operations on the representable class), `FLRP.Intervals` (intervals in subgroup lattices, core-free normalization), `FLRP.Enforceable` (IE/cIE, N1–N3, composition meta-theorems), `FLRP.Reductions` (the R2 catalog), and `FLRP.Certificates` (checked representations).  Reusable mathematics — cosets, group actions, G-sets as unary algebras, normal cores, the subgroup lattice as an instance of `Setoid.Subalgebras.CompleteLattice` — goes into the `Classical/` and `Setoid/` trees proper, so the library gains value even if the research stalls; `FLRP/` holds only problem-specific content.
+  **`--safe` discipline for imported theorems**.  The library forbids postulates (`--safe`), and deep imports (Pálfy–Pudlák's hard direction, CFSG-adjacent reductions, Kurzweil–Netter duality until reproved) will not be formalized soon.  They enter as explicit hypotheses: an `FLRP.Assumptions` module defines named record types stating each imported theorem precisely, results take these as module parameters, and the registry documents source and citation for each.  The trusted base is thereby auditable and every formal result is honest about what it assumes.
+  **Certificate discipline for computation**.  External searches (GAP, UACalc, SAT) must emit finite data — operation tables plus an isomorphism witness — that Agda re-checks by decision over the finite carrier, in exactly the style `Examples.Classical.Lattices.L7` already uses for its law-checking.  Nothing enters the corpus on the authority of an external tool.  Search scripts and raw logs live outside `src/` (in the eventual companion repo if they grow large).
+  **Protection against oversight is the point**.  Formal statements are written even for results whose proofs stay on paper; conjectures and candidate enforcement facts are stated in Agda before being believed; LLM-assisted literature claims get flagged `verify` until checked against full texts.  This is the working answer to hallucination risk, and it doubles as M8 corpus material.

## 7. Work packages

PR-sized, roughly in order; WP-1 through WP-4 are the critical path to R1.

+  **WP-1 `FLRP.Problem`**.  Define `Representable L` (existence of a finite algebra with `Con ≅ L`), state the FLRP formally, wire up the existing examples (distributive baselines, `Con` of small algebras, `L7` as the distinguished open instance); promote the `FiniteAlgebra` interface from `Setoid.Subalgebras.Subdirect.Finite` if needed.
+  **WP-2 group-action infrastructure**.  Cosets, conjugation, normal core, G-sets as unary algebras (one operation per group element), `Sub(G)` as a complete lattice reusing `Setoid.Subalgebras.CompleteLattice` (generalizing the existing Klein-four worked example), and intervals `[H, G]` as bounded lattices.  Lands in `Classical/`/`Setoid/`, not `FLRP/`.
+  **WP-3 the Pálfy–Pudlák bridge, easy direction**.  Theorem: `Con (G ↷ G/H) ≅ [H, G]`; corollary: every interval in a finite subgroup lattice is representable.  First substantive FLRP theorem in the library and the workhorse for everything after.
+  **WP-4 `FLRP.Enforceable`**.  IE/cIE with witness tracking, N1 (inflation), N2 (fattening), N3 (the plain-IE no-go), and the composition meta-theorem schema with named holes; this formally pins down why the program lives at the core-free level.
+  **WP-5 closure toolkit**.  Formalize product and ordinal-sum closure of representability; state duality with Kurzweil–Netter as a registered assumption; stretch goal: reprove Netter's duality construction formally (finite combinatorial content, plausibly tractable, and rescues a possibly unpublished proof — a standalone paper).
+  **WP-6 certificate pipeline**.  The certificate schema (algebra tables + lattice iso witness), the Agda checker, a pilot re-verification of one thesis-era small-lattice representation, and the GAP/SAT emitter scripts.

After WP-4, research issues R1–R4 (§ 4) and avenues A–E (§ 5) proceed in parallel with a quarterly review that re-ranks avenues against the success/kill criteria.

## 8. Immediate next actions

+  Review and approve/amend this roadmap (especially § 1's recommendation and the § 7 sequencing).
+  Phase 0 hygiene: create the `flrp-research` label and Project board; file issues for WP-1…WP-6 and R1…R4; add `arxiv.org` (and ideally `en.wikipedia.org`, `api.semanticscholar.org`) to the session environment's allowed egress so future sessions can verify sources in full text; run the bibliography verification pass over § 3.
+  Start WP-1 and WP-2 (independent, parallelizable).
+  R1 kickoff alongside WP-4: reconcile N1–N3 with [DeMeo 2012b] and extract the note's composition lemma in precise form — the author's own copy of the source is the ground truth here.

## 9. References

Confidence key: entries marked `[verify]` were assembled from search snippets or memory under this environment's blocked egress and need a full-text check in Phase 0.

+  M. Aschbacher, *On intervals in subgroup lattices of finite groups*, J. Amer. Math. Soc. 21 (2008), 809–830.
+  M. Aschbacher, *Signalizer lattices in finite groups*, Michigan Math. J. 58 (2009), 79–103.
+  M. Aschbacher, *Lower signalizer lattices in alternating and symmetric groups*, J. Group Theory 15 (2012), 151–225.
+  M. Aschbacher, *Overgroup lattices in finite groups of Lie type containing a parabolic*, J. Algebra (2013).  `[verify volume/pages]`
+  R. Baddeley, *A new approach to the finite lattice representation problem*, Period. Math. Hungar. 36 (1998), 17–59.
+  R. Baddeley and A. Lucchini, *On representing finite lattices as intervals in subgroup lattices of finite groups*, J. Algebra 196 (1997).
+  A. Basile, *Second maximal subgroups of the finite alternating and symmetric groups*, PhD thesis, ANU (2001); arXiv:0810.3721.
+  F. Börner, reduction results toward the FLRP (1999).  `[verify exact title/venue]`
+  T. C. Burness, M. W. Liebeck, and A. Shalev, *Generation of second maximal subgroups and the existence of special primes*, Forum Math. Sigma 5 (2017), e25.
+  W. DeMeo, *Congruence lattices of finite algebras*, PhD dissertation, University of Hawai'i (2012); arXiv:1204.4305.  Cited as [DeMeo 2012a].
+  W. DeMeo, *Interval enforceable properties of finite groups*, unpublished note (2012); arXiv:1205.1927.  Cited as [DeMeo 2012b].
+  W. DeMeo, *Expansions of finite algebras and their congruence lattices*, Algebra Universalis 69 (2013); arXiv:1205.1106.  Cited as [DeMeo 2013].
+  W. Feit, *An interval in the subgroup lattice of a finite group which is isomorphic to M₇*, Algebra Universalis 17 (1983), 220–221.
+  G. Grätzer and E. T. Schmidt, *On congruence lattices of lattices*, Acta Math. Acad. Sci. Hungar. 13 (1962).  `[verify title/venue]`
+  G. Grätzer and E. T. Schmidt, *Characterizations of congruence lattices of abstract algebras*, Acta Sci. Math. (Szeged) 24 (1963), 34–59.
+  A. Hulpke, *Finding intermediate subgroups*, Port. Math. (2017); arXiv:1706.00769.
+  H. Kurzweil, *Endliche Gruppen mit vielen Untergruppen*, J. reine angew. Math. 356 (1985), 140–160.  `[verify pages]`
+  A. Lucchini, *Intervals in subgroup lattices of finite groups* / representation of `M_n` families (1994).  `[verify exact title/venue]`
+  A. Lucchini, M. Moscatiello, S. Palcoux, and P. Spiga, *Boolean lattices in finite alternating and symmetric groups* (2019); arXiv:1911.04516.
+  R. Netter, duality of representable lattices (1986), possibly unpublished.  `[verify]`
+  P. P. Pálfy, *Intervals in subgroup lattices of finite groups*, in Groups '93 Galway/St Andrews, LMS Lecture Note Ser. 212 (1995).  `[verify]`
+  P. P. Pálfy and P. Pudlák, *Congruence lattices of finite algebras and intervals in subgroup lattices of finite groups*, Algebra Universalis 11 (1980), 22–27.
+  P. Pudlák and J. Tůma, *Every finite lattice can be embedded in a finite partition lattice*, Algebra Universalis 10 (1980), 74–95.
+  J. W. Snow, *A constructive approach to the finite congruence lattice representation problem*, Algebra Universalis (c. 2000).  `[verify volume]`
+  J. Tůma, *Intervals in subgroup lattices of infinite groups*, J. Algebra 125 (1989), 367–399.  `[verify pages]`
+  Y. Watatani, *Lattices of intermediate subfactors*, J. Funct. Anal. 140 (1996), 312–334.  `[verify pages]`
+  arXiv:2502.19876, *Frobenius subalgebra lattices in tensor categories* (2025).
+  OEIS A006966, number of unlabeled lattices on n elements.
