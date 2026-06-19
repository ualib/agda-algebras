<!-- File: docs/notes/m6-3-maltsev-conditions.md -->

# M6-3 design note: basic Maltsev conditions (CP first), the encoding decision, and the deferred theorems

This note records the first pass of [M6-3][] (#273) — *basic Maltsev conditions*,
scoped (per the issue's acceptance criteria) to **congruence permutability** (CP)
first.  Read it with the M6 milestone description in [`GITHUB_PROJECT.md`][], the
just-merged interpretation layer note [`m4-5f-interpretations.md`](m4-5f-interpretations.md)
(which this builds on directly), and ADR-002 (the classical layer) and ADR-006 (the
signature-morphism category).

The deliverable is bounded: CP's Maltsev-term characterization is *proved* (the
concrete, "term ⟹ permutable" direction); the congruence-distributivity (CD) and
congruence-modularity (CM) conditions are *scaffolded* — their term theories and the
lattice properties they characterize are defined, and Jónsson's and Day's theorems,
together with the converse of Maltsev's theorem, are stated as the goals that remain.

## What landed

+  `Setoid.Congruences.Permutability` — the CP layer, pure congruence theory.
   Relation composition `θ ∘ φ` of two congruences (`(θ ∘ φ) x y = ∃ z. x θ z × z φ y`,
   a *bare* relation, since composition need not be transitive); the inclusion lemmas
   `∘-inˡ` / `∘-inʳ` (each factor embeds into the composite, by reflexivity); the
   `Permutes` predicate (`θ ∘ φ ⊆ φ ∘ θ`); the property `CongruencePermutable 𝑨 ℓ`
   ("every two congruences permute"); and `permutable⇒commute` (CP makes composition
   commutative on congruences, the conventional `θ ∘ φ = φ ∘ θ` read as mutual
   containment).

+  `Setoid.Congruences.Properties` — `CongruenceDistributive` and `CongruenceModular`,
   the lattice properties that CD and CM name, stated at the **absorbing** relation
   level `𝐋 ℓ₀ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ ℓ₀` of `Setoid.Congruences.CompleteLattice`, where
   the join `_∨_` lands back at the level of the meet `_∧_` so the lattice equations
   `θ ∧ (φ ∨ ψ) ≅ (θ ∧ φ) ∨ (θ ∧ ψ)` and the modular law type-check.

+  `Setoid.Varieties.MaltsevConditions` — the bridge from term-existence to the
   lattice property, and the scaffolding for CD/CM:
   +  `term-compatible` — *a congruence is compatible with every term operation*
      (structural induction: leaf is the hypothesis, node is `is-compatible`).  This
      is the load-bearing lemma of the forward theorem and a generally useful fact.
   +  `MaltsevTerm⇒CP` / `maltsev⇒CP` — **Maltsev's theorem, forward
      direction**: a theory with a Maltsev term is congruence-permutable.
   +  `Th-Jonsson n` / `HasJonssonTerms n` and `Th-Day n` / `HasDayTerms n` — the
      Jónsson and Day term theories, encoded as interpretations exactly as the Maltsev
      term theory is.
   +  `CongruencePermutableVariety` / `CongruenceDistributiveVariety` /
      `CongruenceModularVariety` — the conditions as properties of a whole variety.
   +  `CP⇒maltsev-Statement`, `Jonsson-Statement`, `Day-Statement` — the deferred
      theorems, each a checked (uninhabited) `Type` recording the precise remaining
      goal.

## The encoding decision

The issue poses the encoding question directly: how to represent a Maltsev condition
uniformly — "(a) a record bundling a term and its identities; (b) an inductive type of
schemes"?  M4-5f had already answered it for the Maltsev term, with a *third* option
that this milestone confirms scales: **a Maltsev condition is a theory interpretation**.

+  A condition is a small *theory* `Th-X` over its own signature `Sig-X` (one ternary
   symbol for Maltsev; `n+1` ternary symbols for Jónsson; `n+1` quaternary symbols for
   Day), and "variety `ℰ` satisfies the condition" is `Th-X ≼ ℰ` — the Maltsev/Jónsson/Day
   theory *interprets into* `ℰ`.  Unfolding `≼` (`Setoid.Varieties.Interpretation`),
   this is exactly an interpretation `I` (sending each `Sig-X` symbol to a *derived
   term* of `ℰ` — the witnessing terms) **together with** a proof that every model's
   reduct satisfies `Th-X` (the identities).  So the interpretation encoding *is*
   option (a) — "term(s) plus their identities" — but packaged so that the entire
   interpretability apparatus applies to it for free.

+  Why this over a bespoke record (a)?  Reflexivity, transitivity, and composition of
   conditions are already proved once and for all for `≼` (`≼-refl`, `≼-trans`), so the
   Garcia–Taylor ordering of conditions is inherited rather than re-derived per
   condition.  And the *same* satisfaction condition (`⊧-interp` / `⊧-uninterp`) that
   powered the group instance powers the extraction of the curried operation here (see
   below).  A standalone record would duplicate all of this.

+  Why this over an inductive scheme (b)?  An inductive datatype of "Maltsev-condition
   schemes" would have to re-encode signatures, terms, and satisfaction internally —
   precisely the apparatus `Sig-X` / `Term` / `≼` already provides.  The one place an
   *index* is genuinely needed is the **arity of the chain** (the number `n` of Jónsson
   or Day terms); we take that as an ordinary `ℕ` parameter to `Th-Jonsson` / `Th-Day`,
   and "has the condition" existentially quantifies it (`Σ[ n ∈ ℕ ] HasJonssonTerms n ℰ`).
   This is the minimal inductive content, kept outside the encoding of any single theory.

The reconciliation with `HasMaltsevTerm` is thus literal: `HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ`
is the `n`-free instance, and `HasJonssonTerms n ℰ = Th-Jonsson n ≼ ℰ`,
`HasDayTerms n ℰ = Th-Day n ≼ ℰ` are its arity-indexed siblings, all the same shape.

## The forward theorem and its bridge

`Setoid.Varieties.Maltsev` gave the term-existence side of CP (`HasMaltsevTerm`); the
congruence-lattice side (`CongruencePermutable`) is new here.  The forward theorem
joins them.  Given `mt : HasMaltsevTerm ℰ`, a model `𝑩` of `ℰ`, and congruences `θ`, `φ`
with `x θ z` and `z φ y` (i.e. `(x , y) ∈ θ ∘ φ`), the classical argument sets
`w = m(x, z, y)` and shows `(x , y) ∈ φ ∘ θ` via that `w`:

+  `x φ w`: from `m(x,z,z) ≈ x` (the identity `mxyy`) and `z φ y`, congruence of `m` in
   its third argument gives `x = m(x,z,z) φ m(x,z,y) = w`.
+  `w θ y`: from `m(x,x,y) ≈ y` (the identity `mxxy`) and `x θ z`, congruence of `m` in
   its second argument gives `w = m(x,z,y) θ m(x,x,y) = y`.

Two ingredients are needed to run this against the *interpretation*-based hypothesis.

**Extracting the curried `m` and its identities.**  `HasMaltsevTerm ℰ` carries an
interpretation `I : Interpretation Sig-Maltsev 𝑆` and, for each model `𝑩`, a proof
`reductᴵ 𝑩 I ⊨ₑ Th-Maltsev`.  The curried operation is the evaluation of the derived
term `I m-Op` against the named tuple: `m𝑩 a b c = ⟦ I m-Op ⟧ ⟨$⟩ tri a b c`
(definitionally `(m-Op ^ reductᴵ 𝑩 I)(tri a b c)`).  A single evaluation lemma
`eval-m` — `cong ⟦ I m-Op ⟧` over a three-way `Fin 3` split, every branch `refl` —
rewrites a Maltsev application in the reduct to `m𝑩`, and the two identities `mxxy` /
`mxyy` fall out by instantiating the reduct's `Th-Maltsev` satisfaction at the tuple
`tri a b b`.  This mirrors the group instance of `Classical.Interpretations.Maltsev`,
where the same `graft`/`eval` shape extracts the curried group laws.

**Congruences respect term operations.**  The Maltsev operation `m𝑩` is a *term
operation* (it is `⟦ I m-Op ⟧`), so its compatibility with any congruence `θ` of `𝑩` is
the special case `t = I m-Op` of the general lemma `term-compatible`: for every term `t`
and `θ`-related environments, the values of `t` are `θ`-related.  This is the fact that
every congruence is a congruence *of the clone*, not just of the basic operations, and
it is exactly what the two compatibility steps of the argument consume.

## CD and CM

`CongruenceDistributive` and `CongruenceModular` are the lattice-theoretic targets of
Jónsson's and Day's theorems.  They are phrased on the congruence lattice already
built in `Setoid.Congruences.{Lattice,Generation,CompleteLattice}`, at the absorbing
level so that meet and join are operations on a single type.  Distributivity implies
modularity, so the CD varieties sit inside the CM varieties; the FLRP cares
particularly about CM (modular congruence lattices are the natural testing ground for
representation questions), and Day's theorem is the bridge to it — see the track-hygiene
note below.

The Jónsson identities (`Th-Jonsson n`, ternary terms `d₀ … dₙ`) and the Day identities
(`Th-Day n`, quaternary terms `m₀ … mₙ`) are encoded with their "fork" identities split
by the parity of the index, via a small `even? : ℕ → Bool`.  The rendering follows
Burris–Sankappanavar (Def. 12.5 for Jónsson; Thm. 12.4 / Day 1969 for Day); the precise
even/odd-vs-argument-pattern convention is documentation here, to be re-confirmed when
the characterization theorems are proved.

## The deferred theorems and their construction plans

All three remaining theorems are stated as checked `Type`s; none is inhabited under
`--safe` (no postulates, no holes).  Each plan below is the standard textbook argument,
recorded so a successor can pick it up.

### Converse of Maltsev (`CP⇒maltsev-Statement`)

*A congruence-permutable variety has a Maltsev term.*  Construction (Burris–Sankappanavar
Thm. 12.2): work in the relatively free algebra `𝔽 = 𝔽[ Fin 3 ]` on three generators
`x , y , z` (`Setoid.Varieties.SoundAndComplete`), which is a model of `ℰ`
(`satisfies`), hence congruence-permutable by hypothesis.  Take the principal
congruences `β = Cg(x , y)` and `γ = Cg(y , z)` (`Setoid.Congruences.Generation`).
Then `x β y` and `y γ z`, so `(x , z) ∈ β ∘ γ`; permutability gives `(x , z) ∈ γ ∘ β`,
i.e. a witness `w` (necessarily `w = M(x,y,z)` for some term `M`, since the carrier of
`𝔽` *is* `Term (Fin 3)`) with `x γ w` and `w β z`.  Translate the two memberships
through the substitution homomorphisms `𝔽[ Fin 3 ] → 𝔽[ Fin 2 ]` collapsing `z ↦ y`
(resp. `x ↦ y`): a hom's kernel is a congruence containing the collapsed pair, hence
containing the principal congruence, so `x γ w` yields `E ⊢ M(x,y,y) ≈ x` and `w β z`
yields `E ⊢ M(x,x,y) ≈ y` — the two Maltsev identities, whence `I-M : Th-Maltsev ≼ ℰ`
by `⊧-interp` and soundness.

The machinery this needs and that is *not yet wired*: (i) the substitution-induced
homomorphism out of `𝔽[ X ]` and the fact that its kernel is a congruence
(`Setoid.Homomorphisms.Kernels` has `HomKerComp`; the free-algebra hom is the missing
piece); (ii) the bridge between `Cg` on `𝔽[ X ]` and derivability `E ⊢ X ▹ _≈_`; and
(iii) the small impedance match between the `Idx → Term × Term` theory shape used by
`≼` and the `I → Eq` shape used by `_⊢_▹_≈_` and `𝔽[_]`.  Each is a self-contained
development; together they are the bulk of a successor issue, which is why the converse
is deferred rather than rushed.  (The issue text says "the free algebra on two
generators"; the standard construction is on **three** generators `x , y , z`, since the
Maltsev term has three variables — recorded here to forestall confusion.)

### Jónsson's theorem (`Jonsson-Statement`)

*A variety is CD iff it has Jónsson terms for some `n`.*  The "terms ⟹ CD" direction is
the lattice computation that the Jónsson chain forces the distributive inequality
`θ ∧ (φ ∨ ψ) ≤ (θ ∧ φ) ∨ (θ ∧ ψ)`; the "CD ⟹ terms" direction is the free-algebra
construction on three generators, reading the `dᵢ` off the congruence
`Cg(x,z) ∧ (Cg(x,y) ∨ Cg(y,z))` and the distributive law.  Both directions reuse the
same free-algebra/`Cg`-vs-derivability bridge that the Maltsev converse needs.

### Day's theorem (`Day-Statement`)

*A variety is CM iff it has Day terms for some `n`.*  Same shape as Jónsson, with the
quaternary Day chain and the modular law in place of distributivity; this is the
direction of most interest to the FLRP, and is the natural next concrete target once the
free-algebra/`Cg` bridge is in place.

## Findings

+  **The satisfaction condition keeps paying off.**  The forward theorem never unfolds
   an interpretation by hand: `eval-m` is one `cong` over a `Fin 3` split, and the two
   identities are `trans`-sandwiches around the reduct's `Th-Maltsev` satisfaction —
   the same division of labour M4-5f found, now consumed one milestone downstream.

+  **`term-compatible` is the right abstraction.**  Phrasing "the Maltsev operation
   respects congruences" as the special case of "every term operation respects every
   congruence" turns the two compatibility steps of Maltsev's argument into two
   one-liners and yields a lemma reusable for Jónsson, Day, and any later
   clone-theoretic argument.

+  **Composition lives at `BinRel`, not `Con`.**  `θ ∘ φ` is deliberately *not* a
   congruence (it need not be transitive); making it a bare relation keeps the
   permutability statement honest and avoids smuggling in a join.  The lattice join
   `θ ∨ φ` and the composition `θ ∘ φ` coincide exactly when the algebra is CP — that
   coincidence, not a definitional identification, is the content.

+  **The absorbing level recurs.**  CD/CM, like the complete lattice, can only state
   their equations once meet and join share a level; reusing `𝐋 ℓ₀ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ ℓ₀`
   keeps them consistent with `Setoid.Congruences.CompleteLattice`.  A first cut that
   tried to spell the level inline tripped the generalizable-variable check (`𝓞`/`𝓥`
   are generalized in `Overture.Signatures`); binding them through a `{𝑆}` module
   parameter, as `CompleteLattice` does, is the fix.

## Track hygiene

This is **clone/Maltsev** material.  Per the milestone note, congruence modularity
*connects forward* to the FLRP — Day's theorem is the entry point — but the
interpretability / Maltsev / clone track and the Finite Lattice Representation Problem
are kept in separate research tracks.  Nothing here touches congruence-lattice
representation; the CP/CD/CM predicates are properties *of* congruence lattices, not
constructions *of* algebras realizing a given lattice.  Conflating the two is the error
the milestone note asks reviewers to flag.

## Build / check

+  Whole library (what CI runs): `nix develop --command make check`.
+  The new modules, one at a time: `nix develop --command agda src/Setoid/Congruences/Permutability.lagda.md`
   (then `Setoid/Congruences/Properties`, `Setoid/Varieties/MaltsevConditions`).

[M6-3]: https://github.com/ualib/agda-algebras/issues/273
[`GITHUB_PROJECT.md`]: ../GITHUB_PROJECT.md
