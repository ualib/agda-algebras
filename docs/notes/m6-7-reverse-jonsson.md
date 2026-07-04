<!-- File: docs/notes/m6-7-reverse-jonsson.md -->

# M6-7 design note: the converse of Jónsson's theorem (CD ⟹ Jónsson terms)

This note records the first half of [M6-7][] (#413) — the *converse* (hard) direction of
Jónsson's theorem: a congruence-distributive variety has Jónsson terms.  Read it with the
M6-4/M6-5 note [`m6-4-free-bridge.md`](m6-4-free-bridge.md), whose free-algebra
congruence/derivability bridge this proof consumes wholesale, and with the M6-6 note
[`m6-6-forward-jonsson-day.md`](m6-6-forward-jonsson-day.md), whose chain machinery
(`Setoid.Congruences.ChainJoin`) supplies the crux extraction.  The converse of Day's
theorem (CM ⟹ Day terms) is the remaining half of #413 and is *not* attempted here, per
the plan of record ("land reverse Jónsson before attempting reverse Day").

## What landed

Everything lives in `Setoid.Varieties.Maltsev.Distributivity`, next to the statement
`Jonsson-Statement` and the forward half — the same "converse lives next to its
statement" placement as `CP⇒maltsev` in `Maltsev.Permutability`.

+  `ParityChain` — a finite chain from `x` to `z` presented as an *indexed family*
   `elt : Fin (suc len) → 𝕌[ 𝑩 ]`, with an exact (`≡`) head, a derivable (`≈`) tail, and
   the parity-normal step field: the `i`-th step lies in `P` for even `i` and in `Q` for
   odd `i`.  The indexed-family shape is chosen because the elements become the
   interpretation of the `len + 1` Jónsson symbols verbatim.
+  `pnil` / `pcons` — the two constructors of the normal form.  `pcons` prepends a
   `P`-step to a chain *with the two relations swapped* (`ParityChain 𝑩 Q P y z`),
   because prepending one element shifts every position's parity by one.
+  `chain→parity` / `chain→parityᵒ` — the normalization: two mutually recursive passes
   over a `Chain 𝑩 (μ ∪ᵣ ν)` (the output shape of `finitary⇒JoinIsChain`), each tracking
   which relation the current position expects.  A step whose tag matches the expectation
   is consed directly; a mismatched step is preceded by a trivial step of the expected
   relation (congruence reflexivity), which flips the expectation so the real step then
   matches.  Both passes are structural in the chain.
+  `CD⇒jonsson` — the converse theorem: for a **finitary** signature, a
   congruence-distributive variety has `n + 1` Jónsson terms, i.e. the `proj₁` direction
   of `Jonsson-Statement`, at the levels of the free algebra
   `𝔽[ Fin 3 ] : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)` (the same instantiation as
   `CP⇒maltsev`).
+  `jonsson-theorem` — **Jónsson's theorem as a complete iff** (Burris–Sankappanavar,
   Thm. II.12.6): for a finitary signature, congruence distributivity of the variety is
   equivalent to the existence of a Jónsson chain.  The two components are `CD⇒jonsson`
   and the M6-6 `jonsson-finitary⇒CongruenceDistributiveVariety`.

## The construction

The classical recipe (Burris–Sankappanavar II.12.6, (1) ⟹ (2)), run through the M6-4
bridge:

+  Work in `𝔽 = 𝔽[ Fin 3 ]` on generators `x , y , z`; it models the theory
   (`satisfies`), hence is congruence-distributive by the hypothesis `cdv`.
+  Take `θ = Cg ❴ x , z ❵`, `φ = Cg ❴ x , y ❵`, `ψ = Cg ❴ y , z ❵`.  Then `(x , z)` lies
   in `θ` (a generator pair) and in `φ ∨ ψ` (one `φ`-step to `y`, one `ψ`-step to `z`),
   so distributivity moves it into `(θ ∧ φ) ∨ (θ ∧ ψ)`.
+  `finitary⇒JoinIsChain` (M6-6) turns that join membership into a finite alternating
   chain — **this extraction is the source of the `Σ[ n ∈ ℕ ]` in the statement**, the
   step #413 called the crux — and `chain→parity` normalizes it: `(θ∧φ)`-steps at even
   positions, `(θ∧ψ)`-steps at odd ones.
+  The chain's elements *are* terms (the carrier of `𝔽` is `Term (Fin 3)`), and they are
   the Jónsson terms: `I i = tᵢ`.  Each identity of `Th-Jonsson n` is a
   principal-congruence membership pushed through a collapsing substitution via
   `cg-pair→⊢`:
   +  `d₀(x,y,z) ≈ x` — the chain head is exactly `x`;
   +  `dₙ(x,y,z) ≈ z` — the chain tail is derivably `z`, and the setoid equality of `𝔽`
      *is* derivability, so the `sub` rule finishes;
   +  `dᵢ(x,y,x) ≈ x` — collapse `z ↦ x` (the `θ`-pair); every chain element is θ-tied
      to `x` because both step relations carry a θ-component (`xθt`, a
      `<-weakInduction`);
   +  the forks — collapse `y ↦ x` (the `φ`-pair) at even `i` and `z ↦ y` (the `ψ`-pair)
      at odd `i`, exactly the parity of the normalized chain's `i`-th step.
+  As in M6-5, the collapsing substitutions are chosen to be the `I ✦_` position maps, so
   every bridge output is definitionally the interpreted identity modulo one `graft≐[]`
   step, and every collapse condition is `refl`; `⊧-interp` + `sound` discharge
   satisfaction in an arbitrary model.

## Findings

+  **Parity normalization wants a swap, not a flag.**  The naive normal form indexes the
   step relation by a Boolean phase, which costs a `not`-shuffling lemma at every cons.
   Parameterizing `ParityChain` by the ordered pair `(P , Q)` and letting `pcons` demand
   a tail with the pair *swapped* makes the parity arithmetic silent: `even? (suc k)` is
   definitionally `not (even? k)` (the M6-3 `even?` was defined by `not`-recursion,
   which pays off here), so the shifted step field transports by a two-case Boolean
   split with no numeric lemmas.
+  **The exact head / derivable tail asymmetry is forced and sufficient.**  `pcons`
   cannot maintain a `≈`-head without demanding that `P` respect `≈` (a generic
   `BinRel` does not), but the head of every cons *is* the new element, so `elt-fst` can
   be propositional equality — and the two endpoint identities need exactly this pair of
   strengths: `d₀` is rewritten silently, `dₙ` goes through the `sub` inference rule.
+  **The crux was already paid for.**  The "extract `n` and the terms from the join
   membership" step that #413 flags as the part with no off-the-shelf analogue is
   `finitary⇒JoinIsChain` (M6-6) plus the parity normalization above; nothing else in
   the converse is more than the M6-5 bridge pattern instantiated three more times.
   The `Finitary` hypothesis is inherited from the chain collapse, mirroring the forward
   finitary theorem — both directions of `jonsson-theorem` carry the same one-liner
   witness.
+  **`θ`-tying is a rung induction, not part of the chain.**  The fact that every chain
   element is θ-related to `x` is *not* stored in `ParityChain` (which is generic in two
   raw relations); it is recovered afterwards by `<-weakInduction`, since both step
   relations are meets with `θ` on the left.  This keeps the normalization reusable for
   the eventual Day converse, whose chain lives in different congruences.

## Track hygiene

This is **clone/Maltsev** material on the M6-3 track (Maltsev conditions), consuming the
M6-4 bridge and the M6-6 chain machinery.  Congruence *distributivity* is not the
FLRP-facing condition (modularity is, via Day); nothing here touches congruence-lattice
representation.

## Remaining work on #413

+  CM ⟹ Day terms (reverse Day).  The free-algebra setup mirrors this module over
   `𝔽[ Fin 4 ]` (generators `x , y , z , u`; B–S II.12.4), and the `ParityChain`
   machinery is designed to be reusable for its fork parity; the modular-law membership
   and the pinning identities differ.  Unlike *forward* Day (deferred indefinitely,
   see the M6-6 note), reverse Day is carried out in Burris–Sankappanavar and is
   expected to be a mechanical mirror of this module.

## Build / check

+  Whole library (what CI runs): `nix develop --command make check`.
+  The changed module:
   `nix develop --command agda src/Setoid/Varieties/Maltsev/Distributivity.lagda.md`.

[M6-7]: https://github.com/ualib/agda-algebras/issues/413
