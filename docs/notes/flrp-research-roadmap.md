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

Bibliography caveat: this snapshot was first assembled from search snippets plus prior knowledge under a blocked egress policy.  `arxiv.org` is now allowed and `api.semanticscholar.org` answers (with anonymous rate limits), so the Phase 0 verification pass is feasible in-session; `en.wikipedia.org` and the `ar5iv.labs.arxiv.org` subdomain remain blocked.  Several `[verify]` markers in § 9 have already been discharged against the sources; the rest are tracked by the Phase 0 issue.

## 4. Primary avenue — interval-enforceable properties

The idea of [DeMeo 2012b]: classify group-theoretic properties by whether an interval shape can *force* them, then either combine enforceable properties into a contradiction (proving some lattice is not an interval, hence by Pálfy–Pudlák answering the FLRP negatively) or prove that no such contradiction is possible (a structural dead-end theorem, which would itself be a significant result about intervals).  Either outcome is progress; the point of this section is to make both outcomes precise enough to formalize.  The note's LaTeX source is vendored in this repository at `docs/papers/flrp/ieprops/` (v4, matching arXiv:1205.1927), and the lemma/theorem numbers below refer to that source.

Notation and terminology follow the note: for a finite lattice `L`, let `𝒢(L)` be the class of pairs `(H, G)` with `G` finite, `H ≤ G`, and `[H, G] ≅ L`, and let `𝒢₀(L) ⊆ 𝒢(L)` be the core-free pairs (`Core_G(H) = 1`).  A group property `P` is **interval enforceable (IE) via `L`** if `G ⊨ P` for every `(H, G) ∈ 𝒢(L)`; **core-free interval enforceable (cf-IE) via `L`** if `G ⊨ P` for every `(H, G) ∈ 𝒢₀(L)`; and **min-IE via `L`** if `G ⊨ P` for every `(H, G) ∈ 𝒢(L)` with `|G|` minimal.  A lattice that occurs as an interval `[H, G]` in the subgroup lattice of a finite group is called **group representable**.  A definitional subtlety to get right in the formalization: if `𝒢(L) = ∅` then every property is vacuously enforced via `L`, and deciding emptiness *is* the original problem, so the formal framework must track group representability of the enforcing lattice explicitly rather than quantify it away.

The note already contains the structural spine, which this roadmap's first draft partially rediscovered; the mapping is worth recording because these are the first formalization targets (WP-4, RP-1):

+  **Core-free reduction and inflation**.  For `N = Core_G(H)` one has `[H, G] ≅ [H/N, G/N]` with `H/N` core-free in `G/N`, so every representation induces a core-free one of the same lattice; this drives the note's Lemma 3.1: if `P` is cf-IE and the complementary class `𝒢ᴾᶜ` is closed under homomorphic images, then `P` is already IE.
+  **Fattening**.  `[H × K, G × K] ≅ [H, G]` for every finite `K`, so no property that a direct factor can destroy (solvability, being alternating or symmetric, …) is IE except vacuously; the note uses exactly this to show solvability is not IE.
+  **No contradictory IE pair (Lemma 3.2)**.  If `P` is IE via a group-representable lattice, then `¬P` is not IE via any group-representable lattice: the product `G × G_c` of the two witnesses carries upper intervals isomorphic to both enforcing lattices, forcing `P ∧ ¬P`.  Fattening destroys core-freeness (`1 × K` lands in the core), so this no-go does *not* apply at the cf-IE level — which is precisely why the strategy lives there, and cf-IE properties genuinely can be of upper-bound type.
+  **The wreath no-go (Lemma 3.3)**.  Via a double application of Kurzweil's construction — whose core-freeness preservation is the technical heart of the proof — if `P` is cf-IE by a *group-representable* lattice, then for every finite nonabelian simple `S` some wreath product `S ≀ Ū` has property `P`.  Hence classes omitting such wreath products (solvable groups, alternating/symmetric groups, almost simple groups) are not cf-IE by group-representable lattices.  This is the note's partial answer to the dead-end question and the prototype for RP-4.

The composition machinery is the note's **parachute construction** `𝒫(L₁, …, Lₙ)`: a bottom element covered by `n` atoms, with `Lᵢ` the interval from the `i`-th atom to the shared top.  Its two pillars:

+  **Theorem 3.6 ((B) ⟺ (C))**.  Statement (B) of Pálfy–Pudlák (every finite lattice is group representable) is equivalent to: for every finite family of cf-IE classes `𝒢₁, …, 𝒢ₙ` enforced by `L₁, …, Lₙ` (`n ≥ 2`, at least two `|Lᵢ| > 2`), a *single* finite group `G ∈ ⋂ 𝒢ᵢ` realizes every `Lᵢ` as an upper interval over a core-free subgroup.  The proof shows core-freeness propagates to every proper subgroup above an atom, via Dedekind's rule and an antichain lemma about permuting complements — small, self-contained subgroup-lattice facts that are ideal early Agda material.  The kill shot this enables: **exhibit finitely many cf-IE classes with empty intersection and the FLRP has a negative answer**.
+  **Lemma 3.7 and Corollary 3.8**.  A core-free representation of a parachute (with `n ≥ 2` and at least two canopies of more than two elements) forces `G` subdirectly irreducible and nonsolvable, with `NH = G` and `C_G(N) = 1` for every nontrivial `N ⊴ G`; consequently cf-IE properties are closed under finite conjunction.

The note's known enforceable classes, seeding the RP-2 catalog: `𝒢₀` = nonsolvable (IE, via Pálfy's example of a lattice that is no upper interval in a solvable group, upgraded by Lemma 3.1); `𝒢₁` = neither alternating nor symmetric (IE, via Basile and Aschbacher–Shareshian); `𝒢₂` = subdirectly irreducible; `𝒢₃` = no nontrivial abelian normal subgroup; `𝒢₄` = `{G : C_G(M) = 1 for all 1 ≠ M ⊴ G}` (the last three cf-IE via parachutes, and provably not IE).  Parachutes have disconnected interiors, so Aschbacher's `D∆`/signalizer machinery plausibly applies to them directly; a concrete RP-2 task is to work out exactly what his reductions say about minimal parachute representations.

The research phases:

+  **RP-1 — formalize the framework end-to-end**.  Formalize the note's §§ 2–3: IE/cf-IE/min-IE with group-representability tracking, Lemma 3.1, Lemma 3.2, the fattening remark, Dedekind's rule and the antichain corollary, the parachute construction, Theorem 3.6, Lemma 3.7, and Corollary 3.8; cap it with the machine-checked strategy meta-theorem: "given finitely many cf-IE classes with empty intersection, the corresponding parachute is not group representable, hence — with Pálfy–Pudlák imported as an explicit hypothesis until formalized — the FLRP has a negative answer."  This machine-checks the *logic of the strategy itself*, so later effort concentrates on the genuinely mathematical gaps.  (The wreath Lemma 3.3 needs wreath products; defer it to the end of RP-1 or fold it into RP-4.)
+  **RP-2 — the enforcement catalog**.  Recast the literature's reduction theorems as (cf-/min-)IE facts with precise statements: the note's `𝒢₀`–`𝒢₄` with their sources; Pálfy's solvable-exclusion lattices; Köhler/Feit's `M₇` and Pálfy's minimality analysis of Feit's examples (min-IE); Baddeley–Lucchini and Börner reductions; Aschbacher's `D∆`/signalizer theorems specialized to parachutes; Lucchini–Moscatiello–Palcoux–Spiga.  Each catalog entry gets a formal statement in Agda (assumption-parameterized where the proof stays on paper), creating the machine-readable inventory the hunt in RP-3 runs over.
+  **RP-3 — hunt for an empty intersection**.  Target, per Theorem 3.6: finitely many cf-IE classes with `⋂ 𝒢ᵢ = ∅` (a property and its negation is the special case `n = 2`).  Constraint from Lemma 3.3: every cf-IE-by-representable class contains wreath products `S ≀ Ū` for every simple `S`, so every member of a candidate family is wreath-rich and the joint tension must come from finer invariants — the structure of the unique minimal normal subgroup Lemma 3.7 provides, its centralizer and complement behavior, and the permutation action on it.  Use computation as cheap falsification: before investing in proofs, search candidate parachutes for representations over the small-groups and primitive-groups libraries (Hulpke's algorithms), and attempt UA-side representations of small candidates directly.
+  **RP-4 — the dead-end branch**.  Prove or refute the note's implicit conjecture that a property and its negation cannot both be cf-IE by group-representable lattices, extending the wreath no-go of Lemma 3.3; more generally, characterize what an empty-intersection family would have to look like.  A proof is the honorable dead end for the `n = 2` case — and independently a publishable structure theorem about subgroup lattices; a refutation is a concrete path toward a negative FLRP answer.  A sobering asymmetry to keep in view: one cannot rule out the *existence* of empty-intersection families without proving statement (B) itself, so the realistic aim is structure theorems constraining the families we can actually construct.

Success criterion: a finite lattice `L` with a machine-checked proof (modulo the explicit assumption registry of § 6) that `L` is not an interval in any finite subgroup lattice.  Kill criterion for the avenue: an RP-4 dead-end theorem covering the constructible families, or two consecutive review points (≈ quarterly) at which RP-3 produced no new viable candidate family and RP-4 no new structural insight; in either case the program falls back to the secondary avenues with the catalog and infrastructure intact.

## 5. Secondary avenues

+  **A — computational campaign (with certificate discipline)**.  (i) Re-attack `L7` positively with 2026 resources: GAP interval searches over the small-groups, perfect-groups, and primitive-groups libraries using Hulpke's intermediate-subgroup algorithms, pruned by the thesis's restrictions on potential representations, plus SAT/model-finder searches for finite algebras with `Con ≅ L7` on carriers well beyond 2012 reach.  (ii) Push the census frontier from 7 to 8 elements (222 lattices) with the mechanized closure toolkit plus searches, producing a database of representability certificates.  (iii) Gather data on `M_16`.  Every positive find is imported as an Agda-checked certificate (§ 6), never trusted from the external tool alone.  First step: encode `Con(𝑨) ≅ L` as a SAT instance for tables on ≤ n elements.  Kill criterion: none — this avenue produces reusable artifacts regardless; it is insurance for the negative bet.
+  **B — Aschbacher-program engagement**.  Formalize the statements (not proofs) of the `D∆`/signalizer reduction theorems as RP-2 catalog entries; run GAP experiments realizing signalizer lattices in specific simple groups; the goal is either to finish a `D∆` case (a non-representable lattice) or to extract new cf-IE properties for RP-3.  This is the avenue most likely to benefit from expert correspondence.
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
+  **WP-4 `FLRP.Enforceable`**.  IE/cf-IE/min-IE with group-representability tracking, core-free reduction, fattening, and the note's Lemmas 3.1 and 3.2 (the plain-IE no-go); this formally pins down why the program lives at the core-free level, and RP-1 continues from here with Dedekind's rule, parachutes, and Theorem 3.6.
+  **WP-5 closure toolkit**.  Formalize product and ordinal-sum closure of representability; state duality with Kurzweil–Netter as a registered assumption; stretch goal: reprove Netter's duality construction formally (finite combinatorial content, plausibly tractable, and rescues a possibly unpublished proof — a standalone paper).
+  **WP-6 certificate pipeline**.  The certificate schema (algebra tables + lattice iso witness), the Agda checker, a pilot re-verification of one thesis-era small-lattice representation, and the GAP/SAT emitter scripts.

After WP-4, research issues RP-1…RP-4 (§ 4) and avenues A–E (§ 5) proceed in parallel with a quarterly review that re-ranks avenues against the success/kill criteria.

## 8. Immediate next actions

+  Review and approve/amend this roadmap (especially § 1's recommendation and the § 7 sequencing).
+  Phase 0 hygiene: create the `flrp-research` label and Project board; file issues for WP-1…WP-6 and RP-1…RP-4; finish opening egress (`arxiv.org` and `api.semanticscholar.org` now work, `en.wikipedia.org` and `ar5iv.labs.arxiv.org` are still blocked); run the bibliography verification pass over § 3.
+  Start WP-1 and WP-2 (independent, parallelizable).
+  RP-1 kickoff alongside WP-4: the note's source is vendored at `docs/papers/flrp/ieprops/`, so formalization proceeds directly against it; the first formal targets once WP-2 lands are Dedekind's rule and the antichain corollary, then the parachute theorems.

## 9. References

Confidence key: entries marked `[verify]` were assembled from search snippets or memory under this environment's blocked egress and need a full-text check in Phase 0.

+  M. Aschbacher, *On intervals in subgroup lattices of finite groups*, J. Amer. Math. Soc. 21 (2008), 809–830.
+  M. Aschbacher, *Signalizer lattices in finite groups*, Michigan Math. J. 58 (2009), 79–103.
+  M. Aschbacher, *Lower signalizer lattices in alternating and symmetric groups*, J. Group Theory 15 (2012), 151–225.
+  M. Aschbacher, *Overgroup lattices in finite groups of Lie type containing a parabolic*, J. Algebra (2013).  `[verify volume/pages]`
+  M. Aschbacher and J. Shareshian, *Restrictions on the structure of subgroup lattices of finite alternating and symmetric groups*, J. Algebra 322 (2009), 2449–2463.
+  R. Baddeley, *A new approach to the finite lattice representation problem*, Period. Math. Hungar. 36 (1998), 17–59.
+  R. Baddeley and A. Lucchini, *On representing finite lattices as intervals in subgroup lattices of finite groups*, J. Algebra 196 (1997), 1–100.
+  A. Basile, *Second maximal subgroups of the finite alternating and symmetric groups*, PhD thesis, ANU (2001); arXiv:0810.3721.
+  J. Berman, *Congruence lattices of finite universal algebras*, PhD thesis, University of Washington (1970).
+  F. Börner, *A remark on the finite lattice representation problem*, in Contributions to General Algebra 11 (Olomouc/Velké Karlovice, 1998), Heyn, Klagenfurt (1999).
+  T. C. Burness, M. W. Liebeck, and A. Shalev, *Generation of second maximal subgroups and the existence of special primes*, Forum Math. Sigma 5 (2017), e25.
+  W. DeMeo, *Congruence lattices of finite algebras*, PhD dissertation, University of Hawai'i (2012); arXiv:1204.4305.  Cited as [DeMeo 2012a].
+  W. DeMeo, *Interval enforceable properties of finite groups*, unpublished note (2012); arXiv:1205.1927.  Cited as [DeMeo 2012b]; LaTeX source vendored at `docs/papers/flrp/ieprops/` (v4).
+  W. DeMeo, *Expansions of finite algebras and their congruence lattices*, Algebra Universalis 69 (2013); arXiv:1205.1106.  Cited as [DeMeo 2013].
+  W. Feit, *An interval in the subgroup lattice of a finite group which is isomorphic to M₇*, Algebra Universalis 17 (1983), 220–221.
+  G. Grätzer and E. T. Schmidt, *On congruence lattices of lattices*, Acta Math. Acad. Sci. Hungar. 13 (1962).  `[verify title/venue]`
+  G. Grätzer and E. T. Schmidt, *Characterizations of congruence lattices of abstract algebras*, Acta Sci. Math. (Szeged) 24 (1963), 34–59.
+  A. Hulpke, *Finding intermediate subgroups*, Port. Math. (2017); arXiv:1706.00769.
+  P. Köhler, *M₇ as an interval in a subgroup lattice*, Algebra Universalis 17 (1983), 263–266.
+  H. Kurzweil, *Endliche Gruppen mit vielen Untergruppen*, J. reine angew. Math. 356 (1985), 140–160.
+  A. Lucchini, *Intervals in subgroup lattices of finite groups*, Comm. Algebra 22 (1994), 529–549.
+  A. Lucchini, M. Moscatiello, S. Palcoux, and P. Spiga, *Boolean lattices in finite alternating and symmetric groups* (2019); arXiv:1911.04516.
+  R. Netter, duality of representable lattices (1986), possibly unpublished.  `[verify]`
+  P. P. Pálfy, *On Feit's examples of intervals in subgroup lattices*, J. Algebra 116 (1988), 471–479.
+  P. P. Pálfy, *Intervals in subgroup lattices of finite groups*, in Groups '93 Galway/St Andrews, Vol. 2, LMS Lecture Note Ser. 212 (1995).
+  P. P. Pálfy and P. Pudlák, *Congruence lattices of finite algebras and intervals in subgroup lattices of finite groups*, Algebra Universalis 11 (1980), 22–27.
+  P. Pudlák and J. Tůma, *Every finite lattice can be embedded in a finite partition lattice*, Algebra Universalis 10 (1980), 74–95.
+  J. W. Snow, *A constructive approach to the finite congruence lattice representation problem*, Algebra Universalis (c. 2000).  `[verify volume]`
+  J. Tůma, *Intervals in subgroup lattices of infinite groups*, J. Algebra 125 (1989), 367–399.  `[verify pages]`
+  Y. Watatani, *Lattices of intermediate subfactors*, J. Funct. Anal. 140 (1996), 312–334.  `[verify pages]`
+  arXiv:2502.19876, *Frobenius subalgebra lattices in tensor categories* (2025).
+  OEIS A006966, number of unlabeled lattices on n elements.
