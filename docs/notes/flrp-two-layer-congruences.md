<!-- File: docs/notes/flrp-two-layer-congruences.md -->

# FLRP design note: the two-layer congruence discipline for finite algebras

This note records the design discussion triggered by the constructivity no-go theorem `chain₂-ConIso→WLEM` of `FLRP.Problem` (PR #462, work package WP-1, issue #452) and proposes the architecture that the FLRP program should adopt in response.  Companion documents: the roadmap `docs/notes/flrp-research-roadmap.md` (§§ 6–7), the finite-Birkhoff note `docs/notes/m6-8-finite-birkhoff.md`, and the module `Setoid.Subalgebras.Subdirect.Finite`.  Status: **proposal, for review discussion on PR #462**; nothing below is implemented except where explicitly noted.

## 1. The trigger, and the question it raises

WP-1 formalized the FLRP statement and proved, instead of the expected two-element instance, a no-go theorem: any order isomorphism `Con 𝑨 ≅ chain₂` — over any signature and any algebra — yields weak excluded middle, because `Con 𝑨` contains the *switch congruence* `θ[ P ] = Cg (λ _ _ → P)` for every proposition `P`, and reading off where the isomorphism sends it decides between `¬ P` and `¬ ¬ P`.  Consequently `Representable` is constructively inhabited only by the one-element lattice.

The review question (PR #462): is this a fundamental flaw in how the library defines congruences?  Should it even be possible to form `Cg (λ _ _ → P)`?  Should every definable congruence be reconstructible from the pairs that generate it, and shouldn't we always be able to decide which element of a congruence lattice corresponds to `Δ` and which to `∇`?

This note's answers, defended below: the definition of `Con` is correct and must not change; the no-go does not contradict the library's earlier decidability results but rather locates their classical content precisely; and the review's two closing principles — reconstructibility from generating pairs, and computability of `Δ`/`∇` identification — are exactly the *defining properties of a second, decidable layer* that the program should now build and quantify over.

## 2. Diagnosis

### 2.1 No contradiction with the existing decidability results

`Setoid.Subalgebras.Subdirect.Finite` proves decidability of pair-membership (`_∈?_`) for a `DecCon` — a congruence packaged with a decidability witness — and its `FiniteAlgebra` interface carries a finite list `cons` of `DecCon`s together with the field `complete : (φ : Con 𝑨 ℓ) → Σ[ d ] (d ∈ cons) × (φ ≑ proj₁ d)`.  That module's prose already observes (lines 38–45) that carrier-finiteness plus decidable `≈` do *not* make congruences decidable, gives the switch congruence as the example, and calls `complete` "exactly the classical content" of finiteness.  The WP-1 theorem is the machine-checked sharpening of that remark: `complete` on any nontrivial algebra implies weak excluded middle, and full excluded middle at the working level implies `complete`, so the field's strength sits in the interval between WLEM and LEM (pinning it exactly is a nice side question, not needed for the design).  Earlier decidability facts concern `DecCon`; the no-go concerns bare `Con`; both are true, and together they quarantine the classical content in a single named field.

### 2.2 Why `Cg (λ _ _ → P)` cannot and should not be banned

The switch congruence is not encoding junk; it is a **kernel**.  Quotient the carrier setoid by `x ∼ y iff x ≈ y ∨ P`; the kernel of the quotient map is `θ[ P ]`.  Any definition with "congruence = compatible equivalence relation" — which is what kernels, the isomorphism theorems (`Setoid.Homomorphisms.Noether`), quotient algebras, subdirect representation, free algebras, and the HSP theorem consume, including for infinite algebras — contains switch congruences.  Restricting the definition to Bool-valued relations or to relations-given-by-generators would break the kernel property (homomorphisms into arbitrary setoids have undecidable kernels) and with it the core of the `Setoid` tree.

The deeper fact: constructively, `Con 𝟚` *is not* the two-element lattice — a congruence on a bare two-element carrier is determined by the proposition "the two elements are related", so `Con 𝟚` is canonically the lattice of level-`0ℓ` propositions up to logical equivalence.  Demanding `Con 𝟚 ≅ 𝟚` is demanding that the lattice of truth values be `𝟚`, i.e. excluded middle.  No re-encoding escapes this, including the planned Cubical port: Prop-valued is not decidable there either.  The semantic `Con` faithfully mirrors the ambient logic; the repair is not to change the semantic object but to stop asking it computational questions.

### 2.3 The review's principles, relocated

+  **Reconstructibility**.  For a decidable congruence `d` on a finite algebra, the list of its related pairs is finite data, and `proj₁ d ≑ Cg ⟨related pairs⟩` holds constructively (`base` gives one inclusion, `Cg-least` the other).  Conversely, `Cg` of a finite pair list on a *tabulated* algebra (§ 3) has decidable membership.  So "reconstructible from its generating pairs" is not a constraint one can impose on `Con`; it is precisely the characterization of the decidable layer.
+  **Computing `Δ` and `∇`**.  On the decidable layer, `Δ` is the unique list entry relating no distinct enumerated pair, found by running `_∈?_`; the corresponding identification under any isomorphism is a computation, exactly as the review demands.

## 3. The design

Terminology: a **tabulated signature** has finitely many operation symbols, each of finite arity; a **tabulated algebra** is an algebra over a tabulated signature together with the `FiniteAlgebra` carrier data (decidable `≈`, finite surjective enumeration).  `Sig-Lattice` is tabulated; `Sig-Unary A` is tabulated whenever `A` is the carrier of a tabulated group, so the WP-2 coset algebras and the WP-3 bridge fall inside this scope.

The proposal is a **two-layer discipline**:

+  **Layer S (semantic, existing)**.  `Con 𝑨` stays exactly as is, and remains the home of the general theory — kernels, quotients, Noether, subdirect representation, HSP — and of impossibility results such as the no-go.
+  **Layer D (decidable, to build)**.  Finitely presented congruences and `DecCon` become first-class, with the following lemma stack.

The lemma stack (statements the implementation must realize; names indicative):

+  **L1 (presentation decidability)**.  On a tabulated algebra, membership in `Cg R` is decidable for every finite pair list `R`: the congruence closure of `R ∪ Δ` under symmetry, transitivity, and the finitely many finite-arity operations stabilizes on a finite carrier.  Hence `Cg R` upgrades to a `DecCon`.
+  **L2 (reconstruction)**.  On a finite algebra, every `DecCon` is `≑` to `Cg` of its related-pairs list; combined with L1, the finitely presented congruences and the decidable congruences coincide up to `≑` on tabulated algebras.
+  **L3 (constructive completeness for the decidable layer)**.  On a tabulated algebra one can enumerate all Bool-valued binary tables on `Fin card`, filter the compatible equivalences, and prove the resulting list complete for `DecCon` up to `≑` — with no classical axiom.  This yields a fully constructive interface `FiniteAlgebraᵈ` (decidable `≈`, enumeration, and a `DecCon`-complete list), of which the current `FiniteAlgebra` is the strengthening by the classical field.  Feasibility note: the enumeration is exponential and exists for the sake of the completeness *proof*; in practice the list is supplied by certificates (WP-6), not by running the enumeration.
+  **L4 (the single classical bridge)**.  The current `complete` field — every semantic congruence is `≑` to a decidable one — becomes the *one* registered classical assumption of the program (planned `FLRP.Assumptions`), stated once and imported explicitly by any result that genuinely needs to pass from Layer S to Layer D.  Its strength (between WLEM and LEM, § 2.1) is documented at the registration site.
+  **L5 (`Representableᵈ`)**.  The poset of `DecCon`s up to `≑` on a tabulated algebra is a finite lattice with decidable order; `Representableᵈ 𝑳` asserts an order isomorphism from it to `𝑳`, and `FLRP-Statementᵈ` quantifies as before.  Deliverables: the constructive instance for `chain₂` (a decidable congruence on `𝟚` decides its own value at the distinct pair, so the obstruction of § 1 vanishes); and, under L4, the equivalence `Representable 𝑳 ↔ Representableᵈ 𝑳`.

Interpretation: `Representableᵈ` becomes the program's working notion, and it is arguably the *more faithful* formalization of the informal FLRP — the "finite algebra" of Pálfy–Pudlák and of every UACalc computation is the tabulated object with concretely presented congruences.  `Representable` (Layer S) remains the stated semantic form, the two connected by L4 exactly once.

## 4. Audit tasks

+  **A1**.  Determine which downstream consumers of `FiniteAlgebra` use `complete` essentially — in particular whether `finiteSubdirectSIRep` and finite Birkhoff (M6-8) survive on `FiniteAlgebraᵈ` alone or genuinely need the bridge; either answer is informative and belongs in the m6-8 note as an addendum.
+  **A2**.  Check that the WP-2 group modules need no change: for tabulated groups, subgroup membership, normality, cores, cosets, and intervals in `Sub(G)` are decidable, so the WP-3 bridge should be stated at Layer D from the start.
+  **A3**.  Fix the packaging of "tabulated signature/algebra" (new records versus fields on `FiniteAlgebraᵈ`), respecting the one-canonical-form rule.

## 5. Impact on the work packages

+  **WP-1 (#452, PR #462)**.  No change required; the module already frames `Representable` as the semantic statement and names the decidable reformulation as its sequel.  This note supersedes that one-line pointer with a concrete design.
+  **WP-3 (#454)**.  State `Con (G ↷ G/H) ≅ [H, G]` at Layer D (tabulated groups); the Layer S version follows under L4 if ever needed.
+  **WP-4 (#455) and RP-1 (#458)**.  Unaffected in substance: the enforceability framework lives on the group side, where tabulated data keeps everything decidable.
+  **WP-6 (#457)**.  Certificates target `Representableᵈ`, as WP-1 already flagged; L1–L3 are the checker's mathematical core.
+  **New work package (proposed WP-7)**.  Implement L1–L5 and the audits A1–A3; PR-sized slices: (i) L1+L2, (ii) L3 + `FiniteAlgebraᵈ`, (iii) L4 registration + L5 with the `chain₂` instance.

## 6. Decision points for reviewers

+  Whether `Representable` keeps its name with `Representableᵈ` alongside (proposed), or the pair is renamed (`Representableˢ`/`Representableᵈ`) at the cost of touching PR #462.
+  Whether the `FiniteAlgebra` refactor (L3/L4) lands before or after WP-3; the proposal is before, since WP-3 should be stated at Layer D and A1 may simplify m6-8's trusted base.
+  Naming and packaging for tabulated signatures/algebras (A3).
+  Whether this note should be promoted to an ADR ("two-layer congruence discipline") once ratified, given it constrains all future finite-algebra work, not only the FLRP tree.
