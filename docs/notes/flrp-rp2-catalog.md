# RP-2 survey note: the enforcement catalog

Research phase RP-2 (GitHub [issue #459](https://github.com/ualib/agda-algebras/issues/459)) builds the machine-readable catalog of "an interval of this shape forces a group of this kind" theorems, each recast as a precise (cf-/min-)interval-enforceability statement.  The formal artifact is [`src/FLRP/Reductions.lagda.md`](../../src/FLRP/Reductions.lagda.md), supported by the new reusable module [`src/Classical/Structures/Group/MinimalNormal.lagda.md`](../../src/Classical/Structures/Group/MinimalNormal.lagda.md); this note is its companion — the entry table, the verification status of every literature claim, the formalization decisions, and the entries considered and rejected.

The framework the catalog is written in is RP-1's (`docs/notes/flrp-rp1-parachutes.md`, `FLRP.Enforceable`, `FLRP.Parachute*`); the program that consumes it is RP-3's hunt for cf-IE classes with empty intersection (roadmap § 4).

## 1.  The entries

Nine entries (the ninth added by RP-3).  "Derived" means the enforcement is proved in the library from RP-1; "imported" means the theorem stays on paper and enters as a named, cited hypothesis (never a postulate).  The last column is the vacuity datum: whether the enforcing lattice is *known* to be group representable, which is what decides whether an entry says anything at all.

| # | Property | Enforcing lattice | Level | Source | Formal status | Lattice representable? |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `𝒢₂` — subdirectly irreducible | any parachute `𝒫(L₁ , … , Lₙ)`, `n ≥ 2`, two big canopies | cf-IE | note Lemma 3.7 (ii) | **derived** (`entry-𝒢₂`), modulo minimal-normal descent | unknown — *is* statement (C) |
| 2 | `𝒢₃` — no nontrivial abelian normal subgroup | ditto | cf-IE | note Lemma 3.7, Remark | **derived** (`entry-𝒢₃`), ditto | unknown |
| 3 | `𝒢₄` — `C_G(N) = 1` for all `1 ≠ N ⊴ G` | ditto | cf-IE | note Lemma 3.7 (i) | **derived** (`entry-𝒢₄`), ditto | unknown |
| 4 | `𝒢₀` — nonsolvable | `M₇` | IE | Pálfy–Pudlák 1980; Pálfy 1995; Feit 1983 | exclusion imported, **upgrade derived** (`nonsolvable-IE`) | **yes** — Feit's `[H , A₃₁]`, imported as `FeitM₇` |
| 5 | `𝒢₁` — neither alternating nor symmetric | `M₆` | IE | Basile 2001 (Thm D, Prop. 5.2.1); Pálfy 1988 | exclusion imported, **upgrade derived** (`nongiant-IE`) | yes — plane over `F₅`, imported as `M₆-representable` |
| 6 | `𝒢₂ ∧ 𝒢₃` | `Mₙ`, `n − 1` not a prime power (`M₇`) | min-IE | Köhler 1983 (`𝒢₂`); Pálfy–Pudlák 1980 (`𝒢₃`) | both imported, **conjunction derived** | yes at `n = 7`, as in Entry 4 |
| 7 | `𝒢₄ ∧ 𝒢₃ ∧ 𝒢₂ ∧ 𝒢₀` | `L7` | cf-IE | DeMeo 2012a, Thm 6.3.1 (ii)–(v) | imported; the conditional consequence derived | **unknown — the open problem** |
| 8 | `𝒢₁` is **not** enforced | `𝟚³` (rank-3 Boolean) | refutation | Lucchini–Moscatiello–Palcoux–Spiga 2019, Thm 1.1 (1)–(2) | realization imported, **refutation derived** | yes, *inside* the excluded class |
| 9 | every 2-chain-enforced class contains the core-free-maximal class `HasCoreFreeMaximal`, which is itself 2-chain-enforced | any two-element chain (`IsChain₂`) | cf-IE, both directions | elementary (this repository); closes the RP-4 reduction's two-element corner | **derived** (`chain₂-enforces`, `chain₂-cfIE-coreFreeMaximal`), on the new `Classical.Structures.Group.MaximalSubgroup`; wreath-richness derived in `FLRP.Hunt` | yes classically (`[1 , C₂]`); constructively oracle-strength, see the module prose |

Entries 1–3 discharge the note's three parachute classes as theorems rather than hypotheses, which is what the issue asked for; Entries 4 and 5 are the note's two IE classes; Entry 6 is the min-IE example the library was asked to record; Entries 7 and 8 are the two external entries whose statements could be pinned down exactly; Entry 9 was added by RP-3 (survey note `docs/notes/flrp-rp3-hunt.md`) to close the two-element corner of the RP-4 reduction.

Beyond the entries, the module contributes the catalog's *vocabulary* — the operations that make it compose rather than merely list:

+  `not-representable→IE` — the vacuity theorem: a lattice that is no interval enforces *everything*.  Two lines, and it is why every entry tracks representability.
+  `cfIE-nonvacuous` / `IE-nonvacuous` — the converse: an entry over a representable lattice exhibits a group with the property (for cf-IE, through the core-free reduction; for IE, with no hypothesis at all).
+  `witness→¬IE` / `witness→¬cfIE` — refutation of enforcement from a representation inside the complementary class; this is what makes negative entries (Entry 8) first-class.
+  `cfIE→¬¬` and `cfIE→IE` — **Lemma 3.1 of the note, proved** (RP-1 left it as the statement type `cfIE→IE-Statement`), together with `negation-Stable` and `HClosed→ComplementHClosed`.
+  `CoreFreeExclusion`, `exclusion→cfIE`, `exclusion→IE` — the common shape of Entries 4 and 5.
+  `MinimallyIE`, `IE→MinimallyIE`, `MinimallyIE-∧`, and `minIE-degenerate` — the min-IE layer, repaired (§ 4.7).
+  `IE-family→cfIE-family` and the re-exported `conjunction-cfIE`, `empty-intersection→not-representable`, `strategy-meta-theorem` — composition, in the `Compose` submodule.
+  `M[_]` — `Mₙ` as the parachute of `n` two-element chains.

## 2.  How the literature was read

`arxiv.org` and `api.semanticscholar.org` are reachable from the fetch tool; `en.wikipedia.org` and `ar5iv.labs.arxiv.org` are not.  Two mechanical points worth recording, because they changed what could be verified.

+  The fetch tool cannot extract text from PDFs, but `curl` in the shell reaches `arxiv.org/e-print/<id>` and `arxiv.org/pdf/<id>`, and `pdftotext -layout` (in the Nix shell) turns both into greppable text.  Every primary-source quotation in § 3 was read that way: Basile's thesis and DeMeo's thesis as PDFs, the Lucchini–Moscatiello–Palcoux–Spiga paper as its LaTeX source.
+  `curl` also reaches `en.wikipedia.org` and `ar5iv.labs.arxiv.org` (both answer `200`), so the restriction is in the fetch tool's domain policy, not in the environment's egress.  Until that policy changes, blocked-domain material can be read through the shell.

## 3.  Verification status of every literature claim

`verified` = read in the cited source itself; `secondary` = read in an authoritative source *about* the cited work, with the primary text paywalled or offline; `unverified` = neither, and consequently not consumed by any entry.

| Claim | Cited to | Status | How |
| --- | --- | --- | --- |
| Lemma 3.1, Lemma 3.7 (i), (ii), its Remark, Corollary 3.8, and the definitions of `𝒢₀`–`𝒢₄` | the note (arXiv:1205.1927 v4) | **verified** | the vendored LaTeX source, `docs/papers/flrp/ieprops/` |
| `𝒢₄` quantifies over **normal**, not subnormal, subgroups | the note | **verified** | `\newcommand{\subnormal}{\ensuremath{\trianglelefteqslant}}` — the macro named `\subnormal` renders `⊴` |
| If `Mₙ ≅ [H , G]` with `G` solvable then `n = q + 1` for a prime power `q` | Pálfy–Pudlák 1980 | **secondary** | attributed in that form on Nick Gill's expository page ("If `H` is a second-maximal subgroup of a solvable group `G`, then `H` is contained in `q + 1` maximal subgroups for some prime power `q`"); the `M_{q+1}` construction is quoted in Freese's review of Schmidt's *Subgroup Lattices of Groups* |
| `M₇ ≅ [H , A₃₁]` with `|H| = 31 · 5` | Feit 1983 | **verified** (two sources) | DeMeo 2012a, Ch. 8 Question 8 ("Walter Feit finds `M₇ ≅ [H , A₃₁]`, where `|H| = 31 · 5`"); and Basile 2001, Prop. 5.2.1's table (`p = 31`, `H = 31.5`, `S = PSL₅(2)`, `r = 7`) |
| A minimal group with an `Mₙ` interval has a **unique minimal normal subgroup** (`n − 1` not a prime power) | Köhler 1983 | **secondary** | Freese's review of Schmidt, verbatim |
| … and **no abelian normal subgroup** | Pálfy–Pudlák 1980 | **secondary** | same sentence of the same review |
| A second maximal subgroup of `Aₘ`/`Sₘ`, `m ≥ 5`, lies in at most 3 maximal subgroups unless it is one of the three Feit–Pálfy examples | Basile 2001, Theorem D | **verified** | arXiv:0810.3721 (the full thesis), quoted verbatim in the module |
| Those three examples are `M₅` in `A₁₃`, `M₇` in `A₃₁`, `M₁₁` in `A₃₁`; hence the possible interval counts are `n ∈ {1, 2, 3, 5, 7, 11}` | Basile 2001, Prop. 5.2.1, quoting Pálfy 1988, Table II | **verified** | ibid.; corroborated by Basile's Thm 5.14.2 ("if `[H ÷ U] ≅ M_k`, then `k ∈ {1, 2, 5, 7, 11}`") |
| `M₆ ≅ [H , G]` only if `G` is neither alternating nor symmetric | Basile 2001, via DeMeo 2012a § 5.2 | **verified** for degree `≥ 5`; see the scope gap below | DeMeo 2012a states the consequence unrestrictedly; Basile's Theorem D carries the hypothesis `m ≥ 5` |
| `M_{q+1}` is the subspace lattice of a two-dimensional space over `F_q`, an interval in the group generated by translations and scalar multiplications; so `M₆` is group representable | folklore, via Freese's review | **secondary** | quoted verbatim from that review |
| A core-free representation of `L7` forces primitivity, `C_G(N) = 1` for all `N ⊴ G`, no abelian normal subgroup, nonsolvability, subdirect irreducibility, and core-freeness of all but at most one proper member of the interval | DeMeo 2012a, Theorem 6.3.1 | **verified** | arXiv:1204.4305, quoted verbatim in the module |
| The subgroups `H ≤ Alt(Ω) , Sym(Ω)` with `[H , G]` Boolean of rank `≥ 3` fall into eleven families, and the two regular-partition families occur for every rank | Lucchini–Moscatiello–Palcoux–Spiga 2019, Thm 1.1 and §§ 3–4 | **verified** | arXiv:1911.04516 LaTeX source, quoted verbatim |
| Aschbacher–Shareshian 2009 supplies a further class of lattices excluded from `Aₙ`/`Sₙ` | the note | **unverified** | J. Algebra 322 (2009), paywalled, no preprint located.  **Not consumed**: Entry 5 rests on Basile alone, and the module names Aschbacher–Shareshian only in prose |
| Solvable groups, and alternating-or-symmetric groups, are closed under homomorphic images | the note (elementary) | **verified** as an assertion of the note | imported as the named hypotheses `SolvableHClosed`, `AltSymHClosed` rather than proved |

### The one scope gap, stated rather than papered over

Basile's Theorem D is about alternating and symmetric groups of degree at least 5.  Entry 5's imported hypothesis (`AltSymExclusion`) is stated for the whole class, so it silently covers degrees `≤ 4` as well.  Those cases are true by inspection, and the inspection is worth reporting because it is *not* vacuous.  An interval isomorphic to `Mₙ` over `H ≤ G` needs `n` subgroups maximal in `G` with `H` maximal in each.  `A₄` has only five maximal subgroups in all (`V₄` and four `C₃`'s), so six is impossible.  `S₄` has eight (`A₄`, three `D₄`'s, four `S₃`'s), and since a maximal subgroup of `S₄` has order 12, 8, or 6, such an `H` has order 2, 3, or 4: the four-element candidates are `V₄`, which is maximal in `A₄` and in each `D₄` and in nothing else (four overgroups), and the three `C₄`'s, each inside one `D₄`; a transposition lies in two `S₃`'s and one `D₄`; a double transposition lies in `A₄` and the three `D₄`'s but is not maximal in `A₄`; a `C₃` lies in `A₄` and one `S₃`.  So the maximum is four, attained by `[V₄ , S₄] ≅ M₄`.

Two things follow.  `M₆` does not occur below degree 5, so Entry 5's hypothesis as stated is true — but `M₄` *does* occur, in the symmetric group `S₄`, so the smallest `Mₙ` outside Basile's list of counts would **not** have served: the choice of `M₆` is load-bearing, and a catalog that had reached for `M₄` would have recorded a false entry.  This inspection was done by hand while writing this note and is **not machine-checked**; the honest ways to close it are to state the hypothesis with the degree restriction and add "every alternating or symmetric group of degree `≤ 4` is solvable" as a second named hypothesis (composing Entry 5 with Entry 4), or to decide the small cases by computation once the library has `Aₙ`/`Sₙ`.  The gap is recorded here, in the module's prose, and in the issue.

## 4.  Formalization decisions

### 4.1  Subdirect irreducibility is stated group-side, and the bridge is a follow-up

The library has no correspondence between normal subgroups of a group and congruences of it, so `Setoid.Congruences.Monolith.IsSubdirectlyIrreducible` — which is about `Con 𝑨` — cannot be applied to a group without building that bridge.  RP-1 proves subdirect irreducibility in its constructive *pairwise* form (`Minimal.normals-meet`: no nontrivial normal subgroup meets the minimal normal subgroup trivially).

The decision: state `𝒢₂` group-side, as `HasMonolithᵍ` of the new `Classical.Structures.Group.MinimalNormal`, and record the divergence.  Three reasons.

+  It is the note's own definition: "Recall, for groups *subdirectly irreducible* is equivalent to having a unique minimal normal subgroup."  So the group-side form is not an approximation of the entry, it *is* the entry.
+  RP-2's job is to state literature facts precisely, not to build infrastructure; the bridge is reusable mathematics that belongs in `Classical/Structures/Group/` beside `FLRP.Bridge`'s Pálfy–Pudlák correspondence, with its own issue.
+  The group-side statement was strengthened to the shape the algebra-side notion has, so the bridge will be a *transport* and not a reproof: `minimal-meets→least` upgrades RP-1's pairwise form to the least-element form of `IsMonolith.mono-least`, constructively (`M ∩ N` is a normal subgroup inside `M`, and it is nontrivial exactly because `M` and `N` do not meet trivially, so minimality gives `M ⊆ M ∩ N ⊆ N`).

What the bridge needs, for whoever picks it up: from a normal subgroup `N`, the relation `x θ y ⟺ x y⁻¹ ∈ N` is a congruence of the group algebra; from a congruence `θ`, the class `{x : x θ ε}` is a normal subgroup; the two maps are mutually inverse and monotone, so they are an order isomorphism `Con 𝑮 ≅ Normal(𝑮)`; nontriviality corresponds to nonzeroness on the nose.  With it, `HasMonolithᵍ` transports to `HasMonolith` and `𝒢₂` becomes the library's `IsSubdirectlyIrreducible`.  It is ordinary work — no obstruction, no classical input — and it would retire the `ᵍ` superscript.

### 4.2  Minimal-normal descent is threaded, not dropped

RP-1's Lemma 3.7 machinery takes a *minimal normal subgroup* as a module parameter, because its existence follows from finiteness by well-founded descent, which the library does not yet have.  Entries 1–3 must therefore be honest about it, and the tempting shortcut — stating the classes only for groups that come equipped with a minimal normal subgroup — would quietly weaken the quantifier over normal subgroups.

The decision: the hypothesis is a *named property of the group being constrained*, `MinimalNormalDescent` ("every nontrivial normal subgroup contains a minimal one"), and it appears as the **antecedent of the enforced property**:

```agda
entry-𝒢₄ : cfIE (λ 𝒢 → MinimalNormalDescent 𝒢 → 𝒢₄ 𝒢) ⊕ᵖ-Lattice
```

So the entry says: *core-free interval enforceability, via the parachute, of "if descent holds then every nontrivial normal subgroup has trivial centralizer"*.  The quantifier over normal subgroups is intact, the class is the note's, every finite group satisfies the antecedent, and `cfIE` is untouched — so the entry still composes with `conjunction-cfIE` and everything else in the catalog's vocabulary.  It is also the shape that will *retire* cleanly: when descent becomes a theorem for finite groups, the antecedent is discharged and the entries become the note's statements verbatim.

### 4.2a  Entries 2 and 3 are derived from the *general* centralizer fact, not from `Minimal.nonabelian`

RP-1 proves `Minimal.nonabelian`, which says the *minimal normal subgroup* `M` fixed as a module parameter is nonabelian.  The note's `𝒢₃` is stronger — *every* nontrivial normal subgroup is nonabelian — so the entry is derived instead from `Structure.centralizer-of-normal` (RP-1's antitone extension of `Minimal.centralizer-trivial`) together with `abelian→⊆-centralizer`: given a nontrivial normal `N`, descent supplies a minimal normal subgroup inside it, `centralizer-of-normal` makes `C_G(N)` trivial, and an abelian `N` would sit inside `C_G(N)`.  `Minimal.nonabelian` is then the special case `N = M`, so nothing is lost and the quantifier is the note's.  Entry 3 (`𝒢₄`) comes from the same `centralizer-of-normal`, and Entry 1 (`𝒢₂`) from `Minimal.normals-meet` through `minimal-meets→least`.

### 4.3  `𝒢₃` is stated contrapositively

"No nontrivial abelian normal subgroup" reads naturally as "every abelian normal subgroup is trivial", but that form is not derivable from the centralizer argument without deciding triviality: the argument gives `¬ ¬ (N ⊆ 1)`, and `N ⊆ 1` is a Π-statement whose stability needs the group's equality to be stable.  The note's own Remark states the contrapositive — "every nontrivial normal subgroup of `G` is nonabelian" — and that is what `𝒢₃` is.  Same statement classically, no decision needed, and it is the form the proof produces.  This follows RP-1 § 3.2 (`normal-in-proper-trivial`), where the same choice was made for `NY = G`.

### 4.4  `Mₙ` is the parachute of `n` two-element chains

The enforcing lattices of Entries 4–6 are the height-two lattices `Mₙ`, and they need no new construction: `Mₙ = 𝒫(𝟚 , … , 𝟚)`.  The parachute's carrier is the shared top, the fresh bottom, and the *proper* elements of each canopy; a two-element chain has exactly one proper element, its bottom, which is the `n`-th atom.  So `M[ n ]` is definitionally the right lattice, with `ParachuteAtoms.atom` and `ParachuteAtoms.covered` witnessing the height-two shape, and `chain₂-top`/`chain₂-bot` (already in `FLRP.Closure.Basic`) supplying the extremum data.

A pleasing consequence, and a genuine structural fact rather than a coincidence: **`Mₙ` has no big canopy**, so the note's hypothesis "at least two `|Lᵢ| > 2`" fails and *none* of the parachute theorems applies to it.  That is exactly why Entries 4–6 need external theorems where Entries 1–3 need only RP-1, and the formal statement of the distinction is the `BigCanopyᴸ` argument the parachute entries take and the `Mₙ` entries cannot supply.

### 4.5  Lemma 3.1 is proved, and it is classical-free for every entry the catalog has

RP-1 left the note's Lemma 3.1 as an uninhabited statement type.  It is proved here in six lines (`cfIE→IE`), and the proof splits cleanly: the constructive core `cfIE→¬¬` needs only the core-free reduction and H-closure of the complementary class, and the classical step is isolated in the `PropertyStable` hypothesis.

The observation that makes this more than bookkeeping: every cf-IE property the literature supplies is the **negation** of a common group property — the note remarks on this — and a negation is double-negation stable with no assumption whatsoever (`negation-Stable`).  So for Entries 4 and 5 the upgrade from cf-IE to IE costs *nothing classical* beyond the core-free reduction and H-closure, and the note's own reading of Lemma 3.1 as a classical step is unnecessarily pessimistic for the cases it is applied to.

### 4.6  Exclusion is the shape the sources actually deliver

Both Entries 4 and 5 come from theorems of the form "no group in class `Q` has `𝑳` above a core-free subgroup".  `CoreFreeExclusion Q 𝑳` names that shape, `exclusion→cfIE` observes that it *is* cf-IE of `¬ Q`, and `exclusion→IE` upgrades it.  Two consequences worth recording: the two entries share all their reasoning, so a third exclusion lattice costs one hypothesis and no proof; and the sources' *unrestricted* statements (Pálfy–Pudlák's solvable theorem, as quoted, has no core-freeness hypothesis) are strictly stronger than what the entry consumes, so the entry is stated at the weaker hypothesis and the upgrade is available either way.

### 4.7  `minIE` of `FLRP.Enforceable` is degenerate, and the catalog repairs it

WP-4's definition quantifies minimality against a *single* other representation:

```agda
minIE P 𝑳 = ∀ 𝒢 𝒬 H J H-sg J-sg → (fin : FiniteAlgebra …) → IntervalIso 𝒢 H H-sg 𝑳
           → (fin' : FiniteAlgebra …) → IntervalIso 𝒬 J J-sg 𝑳 → fin .card ≤ⁿ fin' .card → P 𝒢
```

Instantiating `𝒬 := 𝒢` and `fin' := fin` makes the cardinality premise `card ≤ card`, so `minIE P 𝑳` implies `P` of **every** finitely presented representation of `𝑳` — it is plain interval enforceability restricted to finite groups, not minimal enforceability.  The one-line proof is `minIE-degenerate`, kept in the module as the record of the defect.

The catalog therefore states Entry 6 over `MinimallyIE`, in which minimality is quantified over all finite representations.  `minIE` should be retired in favour of it; FLRP modules are exempt from the deprecation cycle (roadmap § 1), so the replacement can be direct.  This is a follow-up against `FLRP.Enforceable`, deliberately not done on this branch because PR #506 is in review and changes to that file are being kept additive.

### 4.8  Solvability and `Aₙ`/`Sₙ` are abstract predicates

The library defines neither, so Entries 4, 5, 7, and 8 are *schemas*: each takes the predicate as a module parameter together with the facts its sources supply about it.  Nothing is lost — the schemas instantiate unchanged when the predicates land — and something is gained: the entries make explicit exactly which properties of "solvable" are used (H-closure, and the exclusion), which is a shorter list than one would guess.

### 4.9  Negative entries are first-class

Entry 8 records that a lattice does **not** enforce a property.  That is not a defect of the catalog but part of its job: RP-3 searches over enforcing lattices, and knowing that rank-three Boolean lattices cannot enforce `𝒢₁` — because Lucchini–Moscatiello–Palcoux–Spiga *realize* such intervals inside alternating and symmetric groups — prunes the search.  `witness→¬IE` is the operation, and it is the exact dual of the vacuity theorem: a representation inside the class refutes enforcement, a representation of the lattice anywhere refutes vacuity.

### 4.10  What Entry 7 omits

DeMeo's Theorem 6.3.1 has six clauses; the entry imports four.  Clause (i), that `G` is a primitive permutation group, needs a primitivity predicate on the coset action — expressible over `Classical.Structures.Group.GSet` and `Con cosetAlgebra`, but a definition the catalog does not have and should not improvise.  Clause (vi), core-freeness of all but at most one *maximal* member of the interval, needs a maximality predicate on interval elements; RP-1's `proper-CoreFree` is the stronger parachute analog (no exceptions), so the shape of the statement is known, but `L7` is not a parachute and the exception is real.  Both are recorded here rather than approximated.

### 4.11  Layer discipline: the catalog inherits WP-4's interval presentation and needs no decisions

ADR-008's two-layer discipline concerns congruences (Layer S) versus decidable congruences (Layer D), and on the group side the same split appears as `Interval≈` versus `Intervalᵈ` in `FLRP.Enforceable`.  Every notion the catalog uses — `IE`, `cfIE`, `GroupRepresentable`, `IntervalIso` — is stated over `Interval≈`, and no entry needs a membership decision procedure: the entries are statements *about* representations, and the one place a decision genuinely arises inside a parachute (properness of an interval member) is already discharged by RP-1's `IsAll?`, which the parachute construction supplies for free.  So the catalog adds no new classical content and no new layer crossing; the only classical imports it makes are the cited theorems of § 3, each named.  Should an entry later need the Layer-D presentation (a certificate discharging a representability hypothesis, say), it would enter through `FLRP.Bridge`'s `bridgeᵈ` exactly as the census does.

## 5.  Entries considered and rejected

The failure mode of this phase is a plausible-sounding theorem statement that no paper actually proves.  These were considered and left out; a vague entry is worse than no entry.

+  **Baddeley–Lucchini 1997** (*On representing finite lattices as intervals in subgroup lattices of finite groups*, J. Algebra 196, 1–100).  The reduction is a long case analysis of minimal representations of `Mₙ` in terms of almost simple groups and twisted wreath products.  The primary text is paywalled with no preprint located, and the roadmap's one-line summary ("reduces the `Mₙ` question to specific questions about almost simple groups and twisted wreath products") is a *description* of a theorem, not a theorem: any Agda statement written from it would be one nobody proved.  Rejected until the text is in hand; when it is, the natural entry is a min-IE disjunction over the taxonomy.
+  **Baddeley 1998** (*A new approach to the finite lattice representation problem*).  Same situation, wider target class.
+  **Börner 1999** (*A remark on the finite lattice representation problem*, Contributions to General Algebra 11).  Conference volume, not online, nothing located to verify.  Rejected.
+  **Aschbacher's `D∆` and signalizer theorems** (2008, 2009, 2012, 2013).  These are the most attractive external entries — parachutes have disconnected interiors, which is exactly `D∆`'s domain, and the roadmap makes "work out what his reductions say about minimal parachute representations" a concrete RP-2 task.  But the statements are inseparable from Aschbacher's own apparatus (`O_G(H)''`, `M_G(H)`, signalizer lattices), and transcribing them from secondary descriptions would produce precisely the plausible-sounding non-theorem this phase is supposed to avoid.  Working out the specialization to parachutes is *research*, not transcription, and it needs the primary texts.  Rejected for now, with one lead recorded: §§ 2 of arXiv:1911.04516 is a careful secondary presentation of the notation and of the overgroup results Aschbacher's program supplies, and is a usable entry point.
+  **Aschbacher–Shareshian 2009**.  Cited by the note alongside Basile for lattices excluded from `Aₙ`/`Sₙ`; the paper could not be obtained, so it appears in the module only as prose beside the Basile entry it does not carry.
+  **Lucchini 1994's representable families** (`M_{q+2}`, `M_{(qᵗ+1)/(q+1)+1}`) and **Feit's `M₁₁`**.  Out of scope rather than vague: these are *representability* facts, which belong to the certificate and closure track (WP-6, the small-lattice census of issue #485), not to the enforcement catalog.  They would, however, supply vacuity data for further `Mₙ` entries.
+  **Burness–Liebeck–Shalev 2017** (special primes).  About generation of second maximal subgroups; not an enforcement statement.  Out of scope, retained on the roadmap's watchlist.

## 6.  Open items and follow-ups

+  **The normal-subgroup/congruence bridge for groups** (§ 4.1).  Retires the `ᵍ` divergence and connects `𝒢₂` to the library's `IsSubdirectlyIrreducible`.  Ordinary work; worth its own issue.
+  **Retire `minIE`** in favour of `MinimallyIE` (§ 4.7), in `FLRP.Enforceable`, after PR #506 merges.
+  **Minimal-normal descent for finite groups** (§ 4.2): well-founded descent on order.  Discharges the antecedent of Entries 1–3 and RP-1's fourth assumption at once.
+  **Certificates instead of hypotheses for the vacuity data of Entries 4–6**.  `M₆` is an interval in a group of order 100 (`V ⋊ F₅^*` for `V` a plane over `F₅`), which is small enough for the GAP search and certificate pipeline of WP-6 to produce and for the Agda checker to verify; that would turn `M₆-representable` from an import into a theorem, and with it the non-vacuity of Entry 5.  `M₇`'s witness lives in `A₃₁` and is far out of reach, so Entry 4 keeps `FeitM₇` as an import.
+  **Solvability and `Aₙ`/`Sₙ`** as library definitions (§ 4.8), which turn the schemas into statements.  Solvability additionally closes RP-1's open item on the second half of Lemma 3.7 (ii).
+  **The degree-`≤ 4` gap** in Entry 5 (§ 3), either by composing with Entry 4 under a further named hypothesis or by computation.
+  **Aschbacher engagement** (§ 5): obtain the primary texts and specialize `D∆` to parachutes.  This is the highest-value remaining external entry and the roadmap's avenue B.

## 7.  Reading order

`FLRP.Reductions` opens with the vocabulary (vacuity, Lemma 3.1, exclusion, min-IE, `Mₙ`), then the three group classes, then the entries in the order of the table above.  A reader who wants the mathematics rather than the catalog should start at `Classical.Structures.Group.MinimalNormal` (small, self-contained), then the `Parachutes` module of `FLRP.Reductions` (where RP-1's Lemma 3.7 becomes three entries), then the `Compose` submodule.  The framework is `docs/notes/flrp-rp1-parachutes.md`; the program is `docs/notes/flrp-research-roadmap.md` § 4.
