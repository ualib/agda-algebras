<!-- File: docs/notes/m6-6-forward-jonsson-day.md -->

# M6-6 design note: the forward direction of Jónsson's theorem, the Gen-vs-chain obstruction, and why Day is not a mirror

This note records [M6-6][] (#412) — the *forward* halves of Jónsson's and Day's
theorems (terms ⟹ lattice property).  Read it with the M6-3 design note
[`m6-3-maltsev-conditions.md`](m6-3-maltsev-conditions.md), which fixed the encodings
`Th-Jonsson n ≼ ℰ` / `Th-Day n ≼ ℰ` and stated the deferred `Jonsson-Statement` /
`Day-Statement`, and with the congruence-lattice modules
`Setoid.Congruences.{Lattice,Generation,Properties}`.

The deliverable landed in two stages, for reasons that are mathematical, not incidental.
The forward Jónsson direction was proved first, in full generality at the level of finite
alternating chains and — for the **finitary** signatures of ordinary universal algebra —
at the level of the library's actual congruence join, with no residual hypothesis.  The
one place the elementary term argument met the library's infinitary foundations was
isolated as the hypothesis `JoinIsChain` and then **discharged** for finitary signatures
(`finitary⇒JoinIsChain`), so the featured theorem
`jonsson-finitary⇒CongruenceDistributiveVariety` is unconditional.  The forward Day
direction was initially *deferred*, because its staircase is genuinely not a mechanical
mirror of Jónsson's; it has since been **proved** (#412, completing M6-6) with the
construction of Day 1969 in Freese–McKenzie's streamlined form, recorded below in the
section "Why Day is not a mirror — and the ladder that works".  With
the converse halves (M6-5, M6-7), all three classical Maltsev-condition theorems are now
proved in both directions: CP (`maltsev⇒CP` / `CP⇒maltsev`), CD (`jonsson-theorem`), and
CM (`day-theorem`).

## What landed

The chain machinery and its finitary collapse live in a new module
`Setoid.Congruences.ChainJoin`; the staircase, the forward theorems, and the featured
finitary corollary live in `Setoid.Varieties.Maltsev.Distributivity` (part of the
`Setoid.Varieties.Maltsev` subtree); a one-screen worked example lives in
`Examples.Setoid.FinitarySignatures`.

+  `Chain 𝑩 R` (in `Setoid.Congruences.ChainJoin`) — the **finite alternating chain**
   relation: the reflexive–transitive closure `x ≈ · R · R ⋯ R · ≈ y` of a relation `R`
   on the carrier of `𝑩`.  Used with `R = φ ∪ᵣ ψ`, so each `cons` step is tagged (by the
   `⊎` of `_∪ᵣ_`) as a φ-step or a ψ-step.  The carrier algebra is an *explicit*
   parameter, since it cannot be inferred from a relation on `𝕌[ 𝑩 ]` (the carrier
   projection is not injective).  `Chain⊆Gen` records that a chain is below the generated
   join `Cg(φ ∪ ψ)` (`base`/`rfl`/`transitive`).

+  The **generalized curried extraction**, the verbatim `Fin (n+1)` analogue of the
   Maltsev `m𝑩` / `eval-m` / `satM` block: `d𝑩 i a b c = ⟦ Iⱼ i ⟧ ⟨$⟩ tri a b c`, the
   one-`cong`-over-a-`Fin 3`-split lemma `eval-d`, the curried endpoint and "x,y,x"
   identities `d-fst` / `d-lst` / `d-mid`, and the term-operation compatibility `d-compat`
   (`term-compatible` at `Iⱼ i`).

+  `jonsson⇒chainDistributive` — **forward Jónsson, finiteness-free**: a variety with
   Jónsson terms satisfies `θ ∧ (φ ∨ ψ) ⊆ (θ∧φ) ∨ (θ∧ψ)` *along every φ/ψ-chain*.  This
   is the genuine content of Burris–Sankappanavar Thm. II.12.6, with no finiteness or
   infinitary commitment.

+  `JoinIsChain` and `jonsson⇒CongruenceDistributive` — the upgrade to the **literal**
   `CongruenceDistributive` (whose join is `Cg(φ ∪ ψ)`), modulo the single hypothesis
   `JoinIsChain` that membership in the generated join is witnessed by a finite chain.
   `jonsson⇒CongruenceDistributiveVariety` lifts it to the whole variety — the `proj₂`
   (term ⟹ CD) direction of `Jonsson-Statement`, modulo `JoinIsChain`.

+  `finitary⇒JoinIsChain` (in `Setoid.Congruences.ChainJoin`) — **discharges** that
   hypothesis for every finitary signature, by a coordinate-by-coordinate fold (`chain-op`)
   showing `Chain 𝑩 (φ ∪ᵣ ψ)` is itself a congruence, hence contains the generated join by
   `Cg-least`.  The witness it consumes, `Finitary 𝑆`, asks only that each operation symbol
   has a finite arity; for the `Fin`-arity signatures of the library it is the identity
   bijection, supplied in one line.

+  `jonsson-finitary⇒CongruenceDistributiveVariety` — the **featured theorem**: a variety
   over a finitary signature with Jónsson terms is congruence-distributive, *unconditionally*.
   This is the term ⟹ CD direction of `Jonsson-Statement` with no residual side condition —
   the form a working algebraist applies.  `Examples.Setoid.FinitarySignatures` shows the
   `Finitary` witness is a hoop-free one-liner (`λ _ → _ , ↔-id _`).

+  The **forward Day theorem** (landed later, closing #412): the quaternary extraction
   (`m𝑩` / `eval-m` / `m-fst` / `m-lst` / `m-mid` / `m-compat`), the collector `m-collect`
   (FM Lemma 2.3), the finiteness-free `day⇒chainModular`, the `JoinIsChain`-conditional
   `day⇒CongruenceModular`, the unconditional finitary
   `day-finitary⇒CongruenceModularVariety`, and — assembled with the M6-7 converse
   `CM⇒day` — the complete iff `day-theorem`, all in
   `Setoid.Varieties.Maltsev.Modularity`.  The construction is *not* the Jónsson
   staircase; see "Why Day is not a mirror — and the ladder that works" below.

## The staircase (forward Jónsson)

Fix a model `𝑩` of `ℰ` with `n+1` Jónsson terms, congruences `θ, φ, ψ`, and endpoints
`a, b` with `a θ b`.  Write `γ = (θ∧φ) ∨ (θ∧ψ)`.  The proof is the classical two-part
staircase, but phrased so each part is a small induction.

+  **Horizontal** (`horiz`, induction on the chain).  Along a φ/ψ-chain from `u` to `v`,
   `dᵢ(a,u,b)` and `dᵢ(a,v,b)` are `γ`-related, for every `i`.  The θ-component is
   automatic: every `dᵢ(a,·,b)` is θ-tied to `a`, because `dᵢ(a,c,a) ≈ a`
   (`d-mid`) and `a θ b` push the third argument from `b` to `a` (`dpin`).  Each single
   chain step then contributes its φ- or ψ-component (`d-compat` in the middle argument),
   landing the step in `θ∧φ` or `θ∧ψ`, hence in `γ` (`∨-upperˡ` / `∨-upperʳ`).  There is
   **no** `compatible` case, because a chain is built only from `nil`/`cons`.

+  **Vertical** (`rungs`, `Data.Fin.Induction.<-weakInduction`).  The rung predicate
   `Rung i = (a γ dᵢ(a,a,b)) × (a γ dᵢ(a,b,b))` climbs `i = 0 … n`.  The base is the
   endpoint identity `d₀(a,a,b) ≈ a`; the step `inject₁ i → fsuc i` uses the parity-split
   fork identity (`even? (toℕ i)`, matched against `satⱼ (d-fork i)`) to advance one column
   and the horizontal lemma to cross to the other.  At `fromℕ n` the endpoint
   `dₙ(a,a,b) ≈ b` closes the walk: `a γ b`.

`<-weakInduction` is exactly the right principle — its step is `P (inject₁ i) → P (suc i)`,
which is precisely how the fork `d-fork i : Fin n` connects rung `inject₁ i` to rung
`fsuc i`.

## The Gen-vs-chain obstruction

The library's join is `_∨_ = Cg(φ ∪ ψ) = Gen(φ ∪ ψ)`, the *inductively generated*
congruence (`Setoid.Congruences.Generation`).  Its `compatible` constructor closes the
relation under the basic operations, which is necessary and correct for **infinitary**
signatures (arities in this library are arbitrary types).  This is exactly where the
elementary term argument cannot reach the literal lattice statement:

+  The horizontal relation `dᵢ(a,u,b) γ dᵢ(a,v,b)` (`u`, `v` the join-variable) is
   **provably not closed under `compatible`**.  When an operation `f` is applied to the
   join-variable, `dᵢ(a, f(s⃗), b)` does not decompose into the `dᵢ(a, sₗ, b)`: the
   join-variable sits in a fixed argument slot of a fixed term, and operations applied
   there do not distribute out.  So a direct induction over `Gen` cannot carry the
   staircase, and for an infinitary signature the join genuinely exceeds the finite-chain
   closure.

+  The honest scope is therefore: prove everything against `Chain` (`jonsson⇒chainDistributive`,
   fully general), and isolate the one missing step — `Gen(φ ∪ ψ) ⊆ Chain` — as the
   explicit hypothesis `JoinIsChain` rather than impose a finiteness assumption on the
   whole development.

+  That hypothesis is then **discharged** for finitary signatures, in
   `Setoid.Congruences.ChainJoin`.  For a finitary signature `Gen` adds nothing beyond the
   transitive closure of the union, and the proof makes that precise: `chain-op` shows
   `Chain 𝑩 (φ ∪ᵣ ψ)` is closed under every basic operation, applying the operation one
   coordinate at a time over a finite-arity enumeration (`Finitary 𝑆`, the only finiteness
   input) and threading the per-coordinate chains through `Data.Vec.Functional.updateAt`.
   A `Chain` that is reflexive, symmetric, transitive, and operation-compatible is a
   congruence (`Chain-Con`), so it contains the *least* congruence above `φ ∪ ψ`, namely
   the generated join (`Cg-least`); that inclusion is exactly `finitary⇒JoinIsChain`.  The
   featured `jonsson-finitary⇒CongruenceDistributiveVariety` then drops the side condition
   altogether.

This is the M6-6 analogue of the M6-3/M6-5 finding "the satisfaction condition keeps
paying off": the *one* place the forward theorem meets the foundations is named and
isolated, not smeared across the proof.

## Why Day is not a mirror — and the ladder that works

The M6-3 note and the issue frame Day as the "mirror" of Jónsson with quaternary terms.
The curried extraction *is* a verbatim mirror (over `quad` in place of `tri`).  The
staircase is **not**, for a structural reason:

+  Jónsson's θ-pinning needs only that the *third* argument can be moved `b → a` and that
   `dᵢ(x,y,x) ≈ x` then collapses the term — the middle (chain) argument is free.

+  Day's pinning uses `mᵢ(x,y,y,x) ≈ x`, which requires the **two** middle arguments to be
   *equal*.  So only elements `mᵢ(a,c,c,b)` are ψ-pinnable.  The even-fork column
   `mᵢ(a,a,b,b)` (middle arguments `a , b`, unequal) is therefore **not** ψ-pinnable, and
   connecting it to the pinnable columns would demand a single-slot `a ↔ b` move that is
   not a `θ∨(φ∧ψ)`-step.  Jónsson's clean two-column staircase (`dᵢ(a,a,b)` / `dᵢ(a,b,b)`,
   bridged by one horizontal) has no analogue: the even- and odd-fork columns live in
   incompatible "pinnability classes".

The forward Day proof was initially deferred on the strength of this obstruction — it is
absent from *Algebras, Lattices, Varieties* (McKenzie–McNulty–Taylor), and Bergman's
*Universal Algebra* states the result but explicitly declines to prove it — and then
landed (#412) with the construction of Day 1969 in the streamlined form of
Freese–McKenzie's *Commutator Theory for Congruence Modular Varieties*, Thm. 2.2 and
Lemma 2.3.  The construction that works, as formalized in
`Setoid.Varieties.Maltsev.Modularity` (`day⇒chainModular`), has two parts:

+  **The collector (FM Lemma 2.3).**  For *any* congruence `μ` and any pair `b μ d`: if
   the two ladder columns `mᵢ(a,a,c,c)` and `mᵢ(a,b,d,c)` are μ-related at every rung,
   then `a μ c` (`m-collect`).  The climb alternates by fork parity: even forks advance
   the first column directly (the `(x,x,u,u)` identity at `(a,c)`); odd forks cross to
   the second column by the rung hypothesis, advance it — move slot three `d → b` by
   `b μ d`, apply the `(x,y,y,u)` fork, move back — and cross home at the next rung.
   The unpinnable even-fork column is thereby *never pinned*; it is handled by the
   hypothesis pair, which is the two-dimensional aspect of Day's construction (the pair
   `(b, d)` walks `A²` between the diagonal and the relation).

+  **The chain induction, measured by φ-count.**  The modular inclusion
   `(θ ∨ φ) ∧ ψ ⊆ θ ∨ (φ ∧ ψ)` (for `θ ⊆ ψ`) is proved along every θ/φ-chain by an
   outer induction on the number of φ-steps with an inner structural recursion that
   normalizes the head of the chain by transitivity-merging (θ-steps absorb; consecutive
   φ-steps merge).  At the first genuine alternation `a φ t₁ θ t₂ φ t₃ ⋯ c` the
   collector is applied at `μ = δ = θ ∨ (φ ∧ ψ)` with the θ-pair `(t₁ , t₂) ∈ δ`, and
   its rung hypotheses are the **induction hypothesis** at the pair
   `(mᵢ(a,t₁,t₂,c) , mᵢ(a,a,c,c))`: both columns are ψ-railed to `a` by the pinning
   plus single-slot ψ-moves (using `a ψ c` and `θ ⊆ ψ`) — which supplies the ψ-tie the
   induction statement demands — and they are connected by a chain whose first step
   moves slots two and three *simultaneously* (`t₁ → a` by the opening φ-step reversed,
   `t₂ → t₃` by the closing one) and whose tail is the remaining chain pushed through
   slot three coordinatewise (`m-push`).  The simultaneous move **fuses two φ-steps of
   the original chain into one**, so the crossing chain has strictly fewer φ-steps and
   the induction is well-founded.  This fusion is the step with no Jónsson analogue; in
   FM's presentation it appears silently, as the absorption `Rₖ ∘ β = Rₖ` in the proof
   of (4′) → (1).

The `Gen`-vs-chain treatment is then identical to Jónsson's: `day⇒chainModular` is
finiteness-free, `JoinIsChain` upgrades it to the literal `CongruenceModular` (applied
once, to the hypothesis join; the reverse inclusion of the `≑` holds in any lattice),
and `finitary⇒JoinIsChain` discharges the hypothesis for finitary signatures.  This
matters because congruence **modularity** is the FLRP-facing condition (the M6-3 note's
track-hygiene paragraph), so Day's theorem is the bridge of most downstream interest.

## Findings

+  **`<-weakInduction` is the staircase.**  The fork indexing (`inject₁ i` ↔ `fsuc i` over
   `Fin n`, parity by `even? (toℕ i)`) lines up exactly with the standard-library weak
   induction over `Fin (suc n)`; the vertical half is then four short clauses.

+  **Carrier non-injectivity dictates explicit-algebra parameters.**  `𝕌[ 𝑩 ]` is a
   projection, so neither the new `Chain` nor the library's `Gen` can infer their algebra
   from a `BinRel`-typed argument; `Chain` takes `𝑩` explicitly and `Gen` is pinned with
   `{𝑨 = 𝑩}` (cf. `Chain⊆Gen`, `JoinIsChain`).

+  **The obstruction is a feature, named once — then discharged.**  Rather than silently
   assume finitary arities, the development proves the general chain statement and surfaces
   `JoinIsChain` as the lone finitary lever — keeping the theorem honest about exactly what
   the infinitary `compatible` costs — and then pays that cost explicitly for finitary signatures
   in `Setoid.Congruences.ChainJoin` (`finitary⇒JoinIsChain`).  The general chain theorem
   and the unconditional finitary theorem coexist: nothing is assumed that is not either
   proved or quantified away.

+  **The finitary side condition is a one-liner for the user.**  `Finitary 𝑆` asks only for
   a finite arity per operation symbol; for every `Fin`-arity signature in the library the
   witness is `↔-id _`, so `jonsson-finitary⇒CongruenceDistributiveVariety fin jt` applies
   to a finitary algebra without threading any finiteness proof by hand.  This is the
   "universal algebra means finitary algebra" reading made convenient, demonstrated in
   `Examples.Setoid.FinitarySignatures`.

+  **The right measure for Day is the φ-count, and the decrease is a fusion.**  The forward
   Day induction terminates because one simultaneous two-slot `m-compat` move eats *two*
   φ-steps of the original chain while contributing only *one* to the crossing chain; no
   single-slot bookkeeping exhibits a decrease.  Structuring the Agda proof as an outer
   ℕ-induction on `countφ` with the induction hypothesis passed as an explicit argument to
   the inner structural recursion (`chainModStep K (chainModAt K)`) keeps the termination
   checker entirely out of the mathematics.

## Issue-text reconciliation

The issue says the forward halves "inhabit the *first* projections" of the statements; with
the actual orientation `P ⇔ Q = (P → Q) × (Q → P)` and
`Jonsson-Statement = CongruenceDistributiveVariety ⇔ (Σ n, HasJonssonTerms)`, the term ⟹
CD direction is the **second** projection.  The issue also rates the work "moderate" and
treats Day as a mechanical mirror; the Gen-vs-chain obstruction and the Day pinning
asymmetry above are the reasons the work landed in two stages — forward Jónsson first,
forward Day later, by the genuinely different ladder recorded above.  The issue text has
been updated at each stage to reflect this.

## Build / check

+  Whole library (what CI runs): `nix develop --command make check`.
+  The changed modules:
   `nix develop --command agda src/Setoid/Congruences/ChainJoin.lagda.md`,
   `nix develop --command agda src/Setoid/Varieties/Maltsev/Distributivity.lagda.md`,
   `nix develop --command agda src/Setoid/Varieties/Maltsev/Modularity.lagda.md`,
   `nix develop --command agda src/Examples/Setoid/FinitarySignatures.lagda.md`.

[M6-6]: https://github.com/ualib/agda-algebras/issues/412
