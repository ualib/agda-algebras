<!-- File: docs/notes/m6-18-minimal-normal-descent.md -->

# M6-18 design note: minimal normal subgroups of a finite group

This note records M6-18 (issue #510), the proof that **every nontrivial normal subgroup of a finite group contains a minimal one**, and the exact classical residue that survives it.  Read it alongside the RP-1 note `docs/notes/flrp-rp1-parachutes.md` (§ 4, fourth assumption), the RP-2 note `docs/notes/flrp-rp2-catalog.md` (§ 4.2), and the two-layer note `docs/notes/flrp-two-layer-congruences.md`, whose Layer-S/Layer-D discipline this work instantiates on the group side.

The headline is not just the theorem.  It is that the fact RP-1 and RP-2 assumed splits cleanly in two: a *group-theoretic* half, which is now a theorem with no hypotheses beyond carrier finiteness, and a *presentational* half, which is the library's already-identified Layer-S bridge and provably cannot be removed.

## 1.  What landed

Six modules — three of them new — all `--cubical-compatible --exact-split --safe`, no postulates.

| Statement | Name | Module |
| --- | --- | --- |
| the group signature is finite finitary | `Sig-Group-FiniteSignature` | `Classical.Signatures.Finite` |
| counting by filtering, monotone and strict | `filter-length-mono` / `filter-length-strict` | `Overture.Counting` (new) |
| the normal closure of an element | `⟪_⟫`, `⟪⟫-dec`, `⟪⟫-mem`, `⟪⟫-least` | `Classical.Structures.Group.NormalClosure` (new) |
| witnessed nontriviality and minimality | `Witnessed`, `IsMinimalNormalʷ` | `Classical.Structures.Group.MinimalNormal` |
| **the theorem** | `minimal-normal-descentʷ` | `Classical.Structures.Group.MinimalNormalDescent` (new) |
| descent at Layer D | `minimal-normal-descentᵈ`, `minimalʷ→minimalᵈ` | *ibid.* |
| the no-go | `minimal→DNE`, `minimalᵈ→DNE`, `witnessing→DNE` | *ibid.* |
| descent in the catalog's own form | `minimal-normal-descent-sem` | *ibid.* |
| the catalog's antecedent, discharged | `finite-MinimalNormalDescent` | `FLRP.Reductions` |

`Overture.Counting` is a genuine deduplication: the two counting lemmas were `private` in `Setoid.Subalgebras.Subdirect.Finite`, where the maximal-congruence search of finite Birkhoff uses them; that module now imports them instead.

## 2.  Decisions

### 2.1  The finiteness interface is the bare one

The theorem takes `FiniteAlgebra` ([Setoid.Algebras.Finite][]) on the underlying algebra of the group — decidable setoid equality and a surjective enumeration of the carrier — and nothing else.  In particular it needs *no* enumeration of the subgroups, and no `FiniteCongruences`-style interface.  This was not obvious in advance: the textbook argument ("choose a nontrivial normal subgroup of least order") ranges over the normal subgroups, and a constructive rendering of *that* argument would need them enumerated, which carrier finiteness cannot supply.

What removes the need is § 2.3 below: the search ranges over the group's *elements*, and the normal closure turns each of them into a subgroup.

### 2.2  Which nontriviality — and why the theorem has two forms

`Nontrivial N` of `Classical.Structures.Group.MinimalNormal` is the negative statement `¬ (N ⊆ 1)`, chosen there deliberately because none of the parachute arguments needs a witness.  A descent, however, has nothing to descend *from* without one: the whole construction starts by naming an element of the subgroup that is not the identity.

So the module names the positive reading, `Witnessed N = Σ[ y ] (y ∈ N × ¬ (y ≈ ε))`, proves the theorem in that form, and reconciles the two exactly where they can be reconciled — on a *decidably presented* subgroup of a finite group, where `witness` recovers a witness by a finite search over the enumeration.  The unrestricted passage is the no-go of § 3.

The two forms are not a strong statement and a weak one.  `minimal-normal-descentʷ` delivers `IsMinimalNormalʷ M`, whose minimality clause quantifies over **every** normal subgroup, with no decidability assumed of it; only the *nontriviality hypothesis* on the competitor is in witnessed form.  The Layer-D reading `minimalʷ→minimalᵈ`, which takes the negative hypothesis but demands a decision procedure for the competitor, is a corollary of it, not the other way round.

### 2.3  The descent engine is the normal closure, not a subgroup enumeration

At each stage the argument asks a question about *elements*:

> is there an enumerated `y ∈ M` with `y ≉ ε` whose normal closure `⟪ y ⟫` is strictly smaller than `M`?

This is a decidable finite search (`Step?`), and it drives the recursion both ways.

+  **Yes**: recurse into `⟪ y ⟫`, which is normal, contains `y` (so is witnessed), lies inside `M` (leastness), and has strictly smaller order.  Well-founded recursion on `<` over the order does the rest.
+  **No**: `M` is minimal.  Given a competitor `N ⊆ M` with witness `y`, the closure `⟪ y ⟫` is trapped: `⟪ y ⟫ ⊆ N ⊆ M`.  The failed search says `⟪ y ⟫` is not of strictly smaller order than `M`, and a subgroup inside another of no smaller order *is* the other (`¬smaller→above`, the contrapositive of strict monotonicity of the count).  So `M ⊆ ⟪ y ⟫ ⊆ N`.

The second bullet is where the strength of the conclusion comes from.  The competitor `N` is never counted, never decided, never enumerated — only its witness is used, and the witness is passed straight to `⟪⟫-least`.  That is why the minimality clause can quantify over semantic normal subgroups while the descent itself lives at Layer D.

### 2.4  The normal closure is a congruence in disguise

`⟪ y ⟫` is not built by saturating a generating set.  Normal subgroups of `𝒢` are the congruences of its underlying algebra (`Classical.Structures.Group.Congruences`, #508), the congruence generated by a finite pair list of a finite finitary algebra has decidable membership (`Cg-DecCon`, Lemma L1 of `Setoid.Congruences.Presented.Decidable`), and the group signature is finite finitary (new, § 1).  So

    ⟪ y ⟫ = normalOf (Cg (fromPairs [ (y , ε) ]))

and the three facts the descent needs are, in order, L1's decision procedure, the `base` rule of congruence generation, and `Cg-least` pushed across the correspondence — about fifteen lines in total, against the several hundred a bespoke saturation with its own termination argument would have cost.  This is the first consumer of the #508 bridge that pays for itself outright.

Two incidental gains: the levels line up with no bookkeeping (`Sig-Group` has zero signature levels, so the generated congruence lands at `α ⊔ ρ`, which is exactly the level `L` of the subgroup lattice at `ℓ₀ = ρ`), and the enormous symbolic closure term L1's decider carries is sealed behind `abstract`, as `Setoid.Congruences.Finite.Decidable` seals the same term for the same reason.

### 2.5  Every decision is a named lemma

Four decisions occur — is this element in the subgroup, is it the identity, is the closure smaller, does the search succeed — and each is analysed in a small lemma that takes the `Dec` value as an ordinary argument (`decide` inside `¬smaller→above`, `found` inside `witness`, `step` inside `descend`) rather than being split on with `with`.  This is the house style, and here it is also what keeps the goals free of the closure matrix.

## 3.  The no-go: what the catalog was really assuming

`MinimalNormalDescent` of `FLRP.Reductions` asks for minimality against *every* normal subgroup, with nontriviality in the negative form.  That is not merely harder to prove than the witnessed form; it is classical.

**Theorem** (`minimal→DNE`).  If `M` is a normal subgroup of `𝒢`, minimal in that unrestricted sense, and `M` has a witness, then `¬ ¬ P → P` for every proposition `P` at the working level.

The witness is an **oracle subgroup**, in the style of the oracle congruence `θ[ P ]` that drives the WP-1 no-go `chain₂-ConIso→WLEM` of `FLRP.Problem`.  For a proposition `P`, the elements that are trivial *or* make `P` true form a normal subgroup `1 ∪ P`; intersect it with `M`.  The result is a normal subgroup inside `M`, and it is nontrivial *in the negative sense* precisely when `P` is not refutable — so `¬ ¬ P` makes minimality applicable, minimality puts `M` inside it, and reading the second component at the witness `x₀` yields `x₀ ≈ ε ⊎ P` with the left branch excluded.

`minimalᵈ→DNE` sharpens this: the same holds when `M` itself is decidably presented, so it is the *quantifier* that is classical, not the presentation of the minimal subgroup.  And `witnessing→DNE` prices the single principle that separates `IsMinimalNormalʷ` from `IsMinimalNormal` — witnessing nontriviality for arbitrary normal subgroups is itself double-negation elimination — which confirms that `minimalʷ→minimal` hides exactly one classical step, not two.

### 3.1  Consequence for the catalog

`DecidablyPresented 𝒢 𝑭` — every normal subgroup is `⊆`-equal to a decidably presented one — is the group-side reading of `complete` of `FiniteCongruences`, the field the two-layer note pins between weak excluded middle and excluded middle.  It subsumes the witnessing principle (`presented→witnessing`), and with it the descent is the catalog's property verbatim:

```agda
finite-MinimalNormalDescent : (𝒢 : Group 0ℓ 0ℓ)(𝑭 : FiniteAlgebra (proj₁ 𝒢))
  →  Descent.MinimalNormalDescent.DecidablyPresented 𝒢 𝑭 → MinimalNormalDescent 𝒢
```

So issue #510's acceptance criterion — Entries 1–3 reading `cfIE 𝒢ᵢ ⊕ᵖ-Lattice` with *no* antecedent — is not attained here, and on the witnessed route the no-go says why rather than leaving the failure as a gap: any discharge that returns witnessed minimal subgroups, which is what the descent construction produces and what the entries' proofs consume, would decide `¬ ¬ P → P`.  The no-go does not exclude a hypothetical proof of the bare negative form of the antecedent, but none is in sight and it would not feed the witnessed consumers; `DecidablyPresented` is the honest bridge on the route that exists.  What is attained is better than it looks: the antecedent is no longer an unproved statement of finite group theory, but the same layer-crossing datum every other finiteness theorem in the library crosses, and a concrete certificate supplies it by computation.

## 4.  What is still assumed

+  **`DecidablyPresented`** in the catalog's discharge, as above.  Irreducible for the witnessed route, by § 3; the bare negative form of the antecedent is not known to be derivable either.

+  **RP-1's `Structure.Minimal` still takes minimality as a module parameter.**  Its single use of that parameter is at `M ∩ K`, for `K` an interval element, so the parameter can be supplied from `IsMinimalNormalʷ` as soon as `M ∩ K` is decidably presented — that is, as soon as RP-1's interval data is threaded at Layer D (`Intervalᵈ` of `FLRP.Enforceable`) rather than at Layer S.  That refactor touches `FLRP.Parachute`, `FLRP.Parachute.Theorems`, and the `Rep` module of `FLRP.Reductions`, and is deliberately **not** done here; it is bookkeeping with a known shape, and it belongs with the Layer-D pass over the parachute modules rather than with the descent theorem.  Tracked as a follow-up to #510.

## 5.  Open items

+  **Constructing `DecidablyPresented`, or its `ᵈ`-restricted sibling.**  The congruence side already has the constructive Layer-D counterpart `FiniteCongruencesᵈ` (`Setoid.Congruences.Finite.Decidable`), built by enumerating Boolean grids and decoding each through `Cg-DecCon`.  Transporting it across the #508 correspondence would give a `DecidablyPresentedᵈ` for groups — every *decidably presented* normal subgroup is `⊆`-equal to a listed one — with no classical axiom.  That does not discharge `DecidablyPresented` (nothing constructive can), but it is the group-side completion of the two-layer picture and it is routine.

+  **The trivial-group edge case.**  `minimal-normal-descentʷ` needs a witness, so it says nothing about the trivial group — correctly, since the trivial group has no minimal normal subgroup.  Consumers that quantify over nontrivial groups (RP-1's parachute representations do, via `K-⊄H`) supply the witness from their own nondegeneracy data.

+  **A worked instance.**  `𝟏-FiniteAlgebra` exists, but the descent is vacuous on the one-element group.  Concrete groups are no longer the obstacle (`Examples.Classical.Groups.SymmetricGroup3` and, since #563, `AlternatingGroup5` live on `Fin` carriers with decidable equality); the obstacle, measured on the rebase of 2026-08-31, is the `abstract` seal itself: `∥ ⟪ x ⟫ᵈ ∥` over `s3-group` does not reduce to a numeral, closed evaluation being stuck on `Dec.does (⟪⟫-dec …)`, so no `refl`-style regression test can exercise `⟪_⟫` computationally while the seal is `abstract`.  A computational instance needs either `opaque` with `unfolding` in place of `abstract` (opt-in unfolding in the test module only, keeping goals sealed everywhere else) or an unsealed sibling of `⟪⟫-dec` for test consumption.  Propositional facts about a concrete instance (the ⊆-components the theorem returns, say) remain provable without unsealing.

## 6.  Reading order

`Overture.Counting` (two lemmas, no library dependencies), then `Classical.Structures.Group.NormalClosure` (short, and the only place the #508 bridge is used), then the two new sections of `Classical.Structures.Group.MinimalNormal` (`Witnessed`, `IsMinimalNormalʷ`, and the one principle separating it from `IsMinimalNormal`), then `Classical.Structures.Group.MinimalNormalDescent` front to back — the measure, the descent, then the no-go, which is where the design decisions of §§ 2.2 and 3 are justified rather than merely stated.
