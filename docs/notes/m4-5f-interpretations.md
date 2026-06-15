<!-- File: docs/notes/m4-5f-interpretations.md -->

# M4-5f design note: theory interpretations, Maltsev conditions, and the interpretability quasi-order

This note records the outcome of [M4-5f][] (#344) — the last M4-5 subissue, whose
landing closes milestone M4-5.  Read it with the milestone map
[`milestone-signature-functors.md`](milestone-signature-functors.md), the session
handoff [`m4-5d-handoff.md`](m4-5d-handoff.md), and the term-monad note
[`m4-5e-term-monad.md`](m4-5e-term-monad.md) (whose `✶-sub` composability law this issue
generalizes).  M4-5f is *research-grade and bounded*: the deliverable, per the issue, is
a checked definition, one or two worked instances, and this scope note — no claim about
the full interpretability lattice is in scope.

## What landed

+  `Overture.Terms.Interpretation` — the setoid-free core.  `Interpretation 𝑆₁ 𝑆₂` is the
   term-valued generalization of a `SigMorphism`: a map sending each `𝑆₁`-operation symbol
   `o` to an `𝑆₂`-**term** (a *derived operation*) over `o`'s argument positions.  The
   action `_✦_` extends it from symbols to whole terms — the generalization of `_✶_` from
   M4-5e — built on `graft`, the term monad's bind stated at *heterogeneous* variable
   levels (positions at `𝓥`, term variables at an arbitrary `χ`), which the level-uniform
   `Sub` / `_[_]` cannot express.  Also `idᴵ`, `_∘ᴵ_` (composition, via `_✦_`), and the
   embedding `⟨_⟩ᴵ` of a signature morphism as an interpretation.
+  `Setoid.Terms.Interpretation` — the `_≐_`-laws, mirroring `Setoid.Terms.Translation`.
   The `graft` laws (`graft-cong`, `graft-assoc`, `graft-sub`) and the `_✦_` laws:
   `✦-cong` (so `_✦_` is a setoid map, packaged `✦-func`); `✦-id` and `✦-∘` (functoriality
   over the clone category — the composability law the milestone calls for); `✦-sub` (the
   monad-morphism square, the direct generalization of `✶-sub`); and `✦-⟨⟩` (the embedded
   signature morphism acts exactly as `φ ✶_`).
+  `Setoid.Varieties.Interpretation` — the algebra/satisfaction layer, mirroring
   `Setoid.Varieties.Invariance`.  The *interpretation reduct* `reductᴵ I 𝑩` (each
   `𝑆₁`-symbol interpreted as the derived operation `I o` evaluated in `𝑩`); the triangle
   `reductᴵ-interp` (built on the heterogeneous `graft-eval`); the satisfaction condition
   `⊧-interp` / `⊧-uninterp`; `reductᴵ-⟨⟩` (when `I = ⟨ φ ⟩ᴵ`, `reductᴵ` *is* `reduct`, by
   `refl`); the convenience lemma `⊧-≐` (the "second consumer" the M4-5e note anticipated);
   and the **interpretability quasi-order** `_≼_` on equational theories with `≼-refl`
   (via `idᴵ`/`✦-id`) and `≼-trans` (via `_∘ᴵ_`/`✦-∘`, routed through `reductᴵ-∘-⊧`).
+  `Setoid.Varieties.Maltsev` — the Maltsev condition *as universal algebra*: the
   one-ternary-symbol signature `Sig-Maltsev`, the two-equation theory `Th-Maltsev`
   (`m(x,x,y) ≈ y`, `m(x,y,y) ≈ x`), and the predicate `HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ`
   (a variety admits a Maltsev term — is congruence-permutable — iff the Maltsev theory
   interprets into it).  This is signature-agnostic, structure-free universal algebra, so
   it lives in the `Setoid/` foundation, beside `Setoid.Varieties.Interpretation`.
+  `Classical.Interpretations.Maltsev` — the *worked witness* for one concrete variety:
   the interpretation `I-grp` sending `m` to the group term `x ∙ (y ⁻¹ ∙ z)`, and the
   theorem `maltsev-≼-group : HasMaltsevTerm Th-Group` — "every group is
   congruence-permutable via that term."  This proof consumes the group operations and
   laws, so it is structure-specific and lives in `Classical/`, one layer above the general
   theory.  Plus `Classical.Interpretations`, the subtree aggregator.

## The definition, precisely

A **theory interpretation** of `𝑆₁` into `𝑆₂` has two layers, split exactly as the M4-5
chain splits signature-morphism material:

1.  *Syntactic* (`Overture/`): the assignment `I : (o : OperationSymbolsOf 𝑆₁) → Term {𝑆₂}
    (ArityOf 𝑆₁ o)` and its action `_✦_`.  A `SigMorphism` is the special case where each
    `I o` is a single application `node (ι φ o) (ℊ ∘ κ φ o)`; `✦-⟨⟩` / `reductᴵ-⟨⟩` certify
    the inclusion is faithful.

2.  *Equation-preserving* (`Setoid/`): the assignment **interprets** a theory `ℰ₁` into a
    class iff each `ℰ₁`-equation, translated by `_✦_`, holds there.  By the satisfaction
    condition this is the same as the reduct landing in the source variety, which is how
    `_≼_` is phrased: `ℰ₁ ≼ ℰ₂` iff some `I` carries every `ℰ₂`-model's `reductᴵ` into the
    `ℰ₁`-models.  This is the universal algebraist's "𝒱₁ is interpretable in 𝒱₂", whose
    order-reflection is the Garcia–Taylor lattice of interpretability types.

The two-layer split is the same one ADR-006 and the M4-5e note use, and it is why `_✦_`
needed no setoid and `_≼_` needs satisfaction.

## Findings

+  **The satisfaction condition is the load-bearing theorem, exactly as in M4-5e.**  Both
   `≼-refl` and `≼-trans` are short, and short *because* the `_≐_`-laws (`✦-id`, `✦-∘`) and
   the satisfaction condition (`⊧-interp` / `⊧-uninterp`) already isolate the content.
   Transitivity in particular cannot be proved purely syntactically: the interpretation `I`
   quantifies over `𝑆₂`-algebras, and the only `𝑆₂`-algebra one can manufacture from an
   `𝑆₃`-algebra `𝑪` is its `J`-reduct, so `reductᴵ` is *forced* into the transitivity
   proof.  This is the interpretation-level analogue of M4-5g's observation that
   class-level closure needs reconstruction.

+  **The M3-5 / `Fin`-η obstruction stays dissolved at the general level, and the worked
   instance pays exactly the residue the M4-5e note predicted.**  `_✦_`, its laws,
   `reductᴵ-interp`, and the satisfaction condition are structural inductions over abstract
   positions — no clause matches a neutral `ArityOf 𝑆 f ≡ Fin n`, no `interp-node` family,
   no `Fin`-η bridge.  The residue surfaces only in `Classical.Interpretations.Maltsev`, and
   in a sharpened form worth recording: the worked instance must evaluate the *grafted*
   derived term against the group's curried laws, and the grafted term's argument tuple is a
   `graft`-built `λ i → …`, not a `pair` — so the group's own `pair`-shaped node bridges do
   not apply on the nose.  The clean fix is `graft-eval` (evaluation commutes with `graft`,
   the heterogeneous analogue of the `substitution` lemma), which evaluates *any* tuple
   shape; the only `pair`-bridge work is the single `eval-m` lemma, which unfolds the fixed
   chosen term `I-grp m-Op` (written with `pair`, so the bridges apply).  Net: the curried
   group calculation is three lines per Maltsev equation, and the syntactic plumbing is one
   `eval-m` plus one `eval-node`.

+  **A `--safe` fresh-pattern-lambda gotcha, new to this issue.**  An extended (pattern-
   matching) lambda `λ { 0F → … }` elaborates to a *fresh* generated definition each time it
   is written, so two textually identical occurrences are **not** definitionally equal.  The
   first cut wrote the Maltsev tuple inline in `mlt` and tried to infer the `graft`
   substitution by unification — and Agda could neither invert `_✦_` to recover the tuple
   nor equate the two lambdas.  The fix is to name the tuple builder (`tri a b c`, an
   ordinary function with `0F`/`1F`/`2F` clauses) so the substitution `λ i → I-grp ✦ tri a b
   c i` references the *same* `tri` the term reduces through, and to make the worked lemma
   take `a b c` explicitly rather than infer them through `_✦_` (the implicit-pinning
   discipline of the handoff, recurring at a fifth site).

## Scope: done vs deferred

Done (this issue): the definition; its `_≐_`-laws and the satisfaction condition; the
quasi-order with reflexivity and transitivity; one genuinely term-valued worked instance
(Maltsev-in-groups) and the structural fact that signature morphisms embed
(`✦-⟨⟩` / `reductᴵ-⟨⟩`).

Deferred (out of scope here, candidates for a successor issue once M4-5-1..5 exist):

+  **Antisymmetry-up-to-equi-interpretability and the lattice structure.**  `_≼_` is a
   quasi-order; its quotient by mutual interpretability is the Garcia–Taylor *lattice of
   interpretability types*.  Building that quotient (and its join/meet) is a development in
   its own right, deliberately not started.
+  **A clone-category packaging.**  `Interpretation` with `idᴵ` / `_∘ᴵ_` and the `✦-id` /
   `✦-∘` laws is a category (the clone category / category of algebraic theories), and could
   be packaged as a `Category` instance like `TermKleisli`.  The laws are in hand (up to
   `_≐_`); only the bundling is left.  Not done, to keep this issue bounded.
+  **More Maltsev conditions.**  A majority term, a near-unanimity term, a chain of Jónsson
   terms — each is an interpretation of a small theory, and each is a natural next worked
   instance (lattices have a majority term; this is where the `Classical.Interpretations`
   subtree would grow).
+  **Interpreting derivations, not just equations.**  `✦-sub` (the monad-morphism square)
   is exactly what is needed to push an equational *derivation* (`SoundAndComplete`'s
   `_⊢_▹_≈_`, which uses the substitution rule) through an interpretation, giving the
   syntactic counterpart of the semantic `_≼_`.  The law is proved; wiring it to `_⊢_▹_≈_`
   is deferred.

## Forward connections, and a track-hygiene note

This material sits on the **clone/CSP** side of the library and connects forward to
**M9-2** (the Bodirsky–Pinsker program: infinitary CSP over ω-categorical templates), where
interpretability between (infinite-domain) clones is the governing relation and Maltsev-type
conditions classify tractability.  The `_≼_` quasi-order here is the finite/syntactic seed
of that relation.

It is **not** FLRP work.  Per the milestone note, the interpretability / Maltsev / clone
track and the Finite Lattice Representation Problem are kept in separate research tracks;
conflating them is an error to flag in review.  Nothing in M4-5f touches congruence-lattice
representation.

## Build / check

+  Whole library (what CI runs): `nix develop --command make check`.
+  The new modules, one at a time: `nix develop --command agda src/Overture/Terms/Interpretation.lagda.md`
   (then `Setoid/Terms/Interpretation`, `Setoid/Varieties/Interpretation`,
   `Setoid/Varieties/Maltsev`, `Classical/Interpretations/Maltsev`).

[M4-5f]: https://github.com/ualib/agda-algebras/issues/344
