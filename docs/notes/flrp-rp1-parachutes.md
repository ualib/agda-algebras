# RP-1 design note: the parachute theorems

Research phase RP-1 (GitHub [issue #458](https://github.com/ualib/agda-algebras/issues/458)) formalizes § 3 of the vendored note *Interval enforceable properties of finite groups* (`docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, arXiv:1205.1927 v4), from Dedekind's rule through the parachute construction to the strategy meta-theorem.  This note records what was built, the decisions that shaped it, where the formalization diverges from the paper proofs, and what is deferred.

## 1.  What landed

| Note                                         | Formal statement                     | Module(s)                                                                 |
| -------------------------------------------- | ------------------------------------ | ------------------------------------------------------------------------- |
| Dedekind's rule (Thm 3.4)                    | `dedekindˡ` / `dedekindʳ`            | `Classical.Structures.Group.Dedekind` (pre-existing)                      |
| Corollary 3.5 (antichain)                    | `complements-antichain`              | `Classical.Structures.Group.Complements`                                  |
| `𝒫(L₁ , … , Lₙ)`                             | `⊕ᵖ-Lattice`                         | `Classical.Structures.Lattice.Parachute`                                  |
| the interval above the `i`-th atom is `Lᵢ`   | `π` / `↑` and `canopyIso`            | `Classical.Structures.Lattice.Parachute`, `FLRP.Parachute.Representation` |
| core-freeness propagation (proof of Thm 3.6) | `proper-CoreFree`                    | `FLRP.Parachute`                                                          |
| Theorem 3.6, (B) → (C)                       | `parachute-representable`            | `FLRP.Parachute.Theorems`                                                 |
| Corollary 3.8                                | `conjunction-cfIE`                   | `FLRP.Parachute.Theorems`                                                 |
| Lemma 3.7 (i) `NY = G`                       | `normal-in-proper-trivial`, `NH-all` | `FLRP.Parachute`                                                          |
| Lemma 3.7 (i) `C_G(N) = 1`                   | `Minimal.centralizer-trivial`        | `FLRP.Parachute`                                                          |
| Lemma 3.7 remark (nonabelian)                | `Minimal.nonabelian`                 | `FLRP.Parachute`                                                          |
| Lemma 3.7 (ii) subdirect irreducibility      | `Minimal.normals-meet`               | `FLRP.Parachute`                                                          |
| the strategy meta-theorem                    | `strategy-meta-theorem`              | `FLRP.Parachute.Theorems`                                                 |
| Pálfy–Pudlák                                 | `PalfyPudlak` (Entry 3)              | `FLRP.Assumptions`                                                        |

Supporting reusable mathematics: `Classical.Structures.Group.Centralizer` (centralizers, and the commutator fact that normal subgroups meeting trivially centralize each other) and the level generalization of `Complexes.∙ᶜ-mono`.

## 2.  Decisions

### 2.1  Complements through the complex product

The note defines `A^⊥(H,G)` with the *join* (`⟨A , B⟩ = G`) and then hypothesizes that the members of `ℬ` permute with `A`.  Both hypotheses are used only through their conjunction, which is the single statement `B A = G` — the complex product exhausts the group.  `Factorize P Q` (`Classical.Structures.Group.Complements`) takes that as primitive.  This is equivalent to the note's pair of hypotheses (permuting subgroups satisfy `⟨A , B⟩ = A B`) and keeps the antichain argument free of the *generated* subgroup `Sg`, whose inductive presentation would otherwise have to be unfolded at every use.  The join's universal property is recovered by `Factorize-least` where consumers want it.

### 2.2  The parachute carrier is in normal form, not a quotient

The obvious carrier for `𝒫(L₁ , … , Lₙ)` is `⊥ + Σᵢ Lᵢ` with the setoid equality coarsened to identify the `n` tops, in the style of `GlueSetoid` (`Classical.Structures.Lattice.OrdinalSum`).  That construction *cannot be completed constructively*: with the tops glued, the meet of `inj (i , x)` and `inj (j , y)` for `i ≠ j` must be the bottom when both are proper canopy elements and must be `inj (j , y)` when `x` is the top, and choosing between the two decides `x ≈ ⊤ᵢ`.  Since an infimum is automatically congruent, no congruent meet exists without that decision.

So the carrier lists normal forms — the shared top, the fresh bottom, and the *proper* elements of each canopy tagged with their index — and the single decision that remains, "is this element the top of its canopy", is an explicit module parameter `top?`.  For the `Fin`-presented finite lattices the FLRP quantifies over it is free.  This is the ADR-008 layer discipline applied to a lattice construction rather than to congruences: the obstruction is documented and the decision procedure becomes data, instead of the construction being weakened.

An unexpected dividend: with no quotient, the parachute's order is an *inductive family indexed by its endpoints* (per issue #504), so the canopy index is carried once by the order constructor and matching a comparison of two canopy elements identifies their canopies with no appeal to decidable index equality.

### 2.3  Equality is mutual comparability

`_≈ᵖ_` is defined as `(u ≤ᵖ v) × (v ≤ᵖ u)` rather than as a second inductive family.  This is forced, not stylistic.  The canopy carrier `U i` *depends* on the index `i`, so inverting a proof about two elements that Agda already knows to lie in the same canopy requires eliminating the reflexive equation `i ≡ i`, which `--without-K` refuses.  With equality defined as mutual comparability, antisymmetry is the pairing function and no such inversion is ever needed.  (The one place where a comparison of a canopy index with itself is unavoidable — the meet and join of two elements of the *same* canopy — is discharged by `≟-diag`, which is Hedberg's theorem for `Fin`, not the K rule.)

### 2.4  Every case split is a named lemma

The construction makes exactly three decisions — is this canopy element the top of its canopy, do these two elements share a canopy, and (on the diagonal, where `--without-K` refuses to match `refl`) the comparison of an index with itself.  Each is analysed in one small `private` lemma that takes the `Dec` value as an *explicit argument*, and every consumer applies that lemma instead of repeating the split.  This is the library's house style (`CLAUDE.md`: "prefer named helper lemmas over inlined or opaque `rewrite` chains"), and it is also what makes the module cheap to type-check: a `with` inside a proof abstracts the *whole* goal, and these goals mention the canopy order, which unfolds into the generic interpretation machinery of `Algebra`.  Measured on issue #515: replacing the proof-level `with`s by lemmas on the decision, together with merging `ParachuteAtoms` into `LatticeParachute` (see § 2.5), cut the module's own type-checking cost from about 47 s to about 6 s.  The breakdown, from `agda --profile=internal`, is instructive — the expensive phases were *not* typing:

| phase | before | after |
| --- | --- | --- |
| Coverage | 15.6 s | 0.9 s |
| Serialization | 10.5 s | 1.0 s |
| InterfaceInstantiateFull | 10.1 s | 0.5 s |
| DeadCode | 5.7 s | 0.8 s |
| Positivity | 2.5 s | 0.3 s |
| Typing | 1.0 s | 1.5 s |

### 2.5  One module, not two

`LatticeParachute` takes the canopy bottoms and the nondegeneracy assumption alongside the tops and the top test, rather than layering an `ParachuteAtoms` module on top of a bottom-free construction.  The layered version was more general — the lattice structure genuinely does not need the bottoms — but the generality bought nothing (every consumer wants the atoms) and cost a module application that re-instantiated, re-serialized, and re-positivity-checked every definition of the inner module: 10 s of `InterfaceInstantiateFull` plus most of the serialization cost, for a module that takes 6 s in total once merged.  **Prefer one module with more parameters over two modules related by `open … public`** when the inner module has more than a handful of definitions.

### 2.6  The order comes first, the equations follow

The eight lattice equations, and in particular the two operation congruences, are not proved by hand.  The module establishes that `_≤ᵖ_` is a partial order with `_∧ᵖ_` its infimum and `_∨ᵖ_` its supremum, and the standard library's `Relation.Binary.Lattice.Properties.Lattice` derives the algebraic laws.  Congruence is then a theorem (an infimum is unique up to `≈`), not an obligation.  For comparison, the sibling ordinal-sum construction spends 32 hand-written congruence cases on the same kind of gluing; the parachute needs none.  **This is worth propagating**: any future lattice construction in the library should be built order-first.  (It is also cheap: the whole derivation, `⊕ᵖ-Lattice` included, costs under 40 ms — when the module was slow, this was not why.)

### 2.7  The parachute shape is group-theoretic data

`FLRP.Parachute.ParachuteConfig` states the shape of `[H , G]` — atoms, their meets and joins, and the covering property — as subgroup data, and `proper-CoreFree` is proved from that alone.  The bridge from the lattice (`FLRP.Parachute.Representation`) is a separate module.  The split keeps the substantive argument independent of how the parachute is presented, and it is what makes the *constructive* reading below possible.

## 3.  Divergences from the note's proofs

### 3.1  The core-freeness argument is direct, not by contradiction

The note proves Theorem 3.6 by assuming `N = core_G(Y) ≠ 1` and deriving a contradiction.  Constructively that yields `¬ ¬ (N = 1)`.  The formal proof instead uses the parachute's covering property, which is *data*: for the member `NH` of the interval, `covered` says either `NH ⊆ H` — whence `N` is a normal subgroup inside `H` and core-freeness of `H` finishes directly — or `NH` lies above an atom, and only in that branch is a contradiction derived (and genuinely available).  Nothing is weakened, no double negation is introduced, and the resulting proof is shorter than the paper's.

### 3.2  `NY = G` is stated contrapositively

Lemma 3.7 (i) says `NY = G` for every nontrivial normal `N` and every `H ≤ Y < G`.  Constructively one cannot pass from "`N` is not trivial" to the Π-statement "`NY` is everything" without a decision.  The formal statement is therefore the contrapositive `normal-in-proper-trivial`: *a normal subgroup contained in a proper member of the interval is trivial*.  It carries the same information, needs no decision, and is the form every consumer actually uses.  The positive form `NH-all` is also available, in the `Structure` module, where a decision procedure for properness is in scope — and in a parachute that procedure is free (`IsAll?`), because a member is everything exactly when its image is the parachute's top.

### 3.3  Subdirect irreducibility in pairwise form

The note derives "unique minimal normal subgroup" from `C_G(M) = 1`.  Formally, `Minimal.normals-meet` says: *no nontrivial normal subgroup meets the minimal normal subgroup `M` trivially*.  That is the constructive content of "`M` is the monolith" — it avoids quantifying over the collection of all normal subgroups and avoids deciding triviality — and it is derived from the same commutator computation the note uses (`normals-centralize`).

### 3.4  Minimality of the canopy-element hypothesis

The note's `|Lᵢ| > 2` becomes `BigCanopyᴸ i`: an element of `Lᵢ` that is neither its bottom nor its top.  On the group side this is `BigCanopy K`: a member of the interval strictly between the atom `K` and the top.  These are the same condition, stated so that no counting is needed.

## 4.  What is assumed, and why

No result in this phase is postulated.  Four hypotheses are threaded as ordinary arguments; the first is a registry entry, the other three are module parameters.

+  **Pálfy–Pudlák** (`FLRP.Assumptions`, Entry 3): statement (A) implies statement (B).  Registered at *statement* level, as published — the entry deliberately does not claim the stronger per-lattice reading, which is why `strategy-meta-theorem` concludes `¬ FLRP-Statement` rather than non-representability of the parachute itself.  Retirement path: the minimal-cardinality argument plus WP-3.

+  **The core-free reduction** (`CoreFreeReduction`, from WP-4): "we may assume `H` is core-free, else pass to `G/N`".  Needs quotient groups, which the library does not have yet.

+  **A finite presentation of the parachute**: a `FiniteLattice` isomorphic to `⊕ᵖ-Lattice`.  Needed *only* in the last step of the meta-theorem, because statement (B) is quantified over `Fin`-presented lattices.  Every concrete instance supplies it by computation; the general transport (enumerate a finite setoid lattice, rebuild its operation tables, and transport the eight equations) is routine and unformalized.  It is the cheapest of the four to discharge and the natural next task.

+  **A minimal normal subgroup** (in `Structure.Minimal`): existence follows from finiteness by well-founded descent, which the library does not have yet.  Only Lemma 3.7's centralizer half depends on it; the propagation theorem, Theorem 3.6, Corollary 3.8, and the meta-theorem do not.

## 5.  Open items

+  **Theorem 3.6, direction (C) → (B)**.  Immediate in the note ("obviously"), by applying (C) to a family containing the lattice to be represented, padded with two big canopies.  Formalizing it needs a concrete three-element lattice and the padding bookkeeping, and it carries no weight in the program — the strategy runs entirely on (B) → (C).  Not assumed anywhere; simply not done.

+  **Nonsolvability** (the second half of Lemma 3.7 (ii)).  The formalization proves the sharper structural fact the note uses to get there — every nontrivial normal subgroup of a core-free parachute representation is *nonabelian* (`Minimal.nonabelian`) — but "a group with a nonabelian minimal normal subgroup is nonsolvable" needs a theory of solvable groups, which the library does not have.  Deferred; it is catalog material for RP-2 in any case, since `𝒢₀` (nonsolvable) enters the enforcement catalog with its own citation.

+  **`Statement-C` of `FLRP.Enforceable`** is phrased over `FiniteLattice` families and is therefore not literally the conclusion proved here (which is phrased over `Lattice` families with explicit extremum and decision data).  The two differ exactly by the finite-presentation transport of § 4.  Reconciling them is bookkeeping, and worth doing when that transport lands.

+  **The parachute of a family of `FiniteLattice`s as a `FiniteLattice`.**  See § 4; this is the transport that closes the previous two items at once.

## 6.  Wreath Lemma 3.3 — deferred to RP-4

The note's Lemma 3.3 (`lem:IE-must-have-wreaths`) states that a property core-free interval enforceable by a *group representable* lattice is enjoyed by some wreath product `S ≀ Ū` for every finite nonabelian simple `S`, and concludes that classes omitting such wreath products (solvable groups, alternating and symmetric groups) are not cf-IE by representable lattices.  Its proof applies Kurzweil's construction twice, and its technical heart is that core-freeness is preserved by that construction.

It is **not** formalized in this phase, and it should not be: it needs wreath products, the permutation action of `G` on the cosets of `H`, the diagonal subgroup of `Sⁿ`, and the dual-lattice interval `[D , Sⁿ] ≅ Eq(n)′` — an infrastructure package comparable in size to everything RP-1 built, and one that overlaps with the Kurzweil–Netter duality work (`FLRP.Assumptions`, Entry 2) rather than with the parachute theorems.  Per issue #458 it moves to **RP-4**, where it belongs on the merits: RP-4 is the dead-end branch, and Lemma 3.3 is precisely the note's partial answer to the dead-end question ("can a property and its negation both be cf-IE by representable lattices?").  RP-3's hunt uses it only as a *constraint* on candidate families — every member of a candidate family is wreath-rich — which is a fact about the search, not a lemma the search consumes formally.

## 7.  Reading order

For a reader coming to this fresh: `Classical.Structures.Group.Complements` (small, self-contained, and the only place Dedekind's rule is used), then `Classical.Structures.Lattice.Parachute` (the construction and its design), then `FLRP.Parachute` (`ParachuteConfig` and `proper-CoreFree` — the mathematical heart), then `FLRP.Parachute.Representation` (transport), and finally `FLRP.Parachute.Theorems` (the three headline results).  The roadmap section that frames all of it is `docs/notes/flrp-research-roadmap.md` § 4.
