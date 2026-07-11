<!-- File: docs/notes/m6-7-reverse-day.md -->

# M6-7 design note: the converse of Day's theorem (CM ⟹ Day terms)

This note records the second and final half of [M6-7][] (#413) — the *converse* (hard)
direction of Day's theorem: a congruence-modular variety has Day terms.  It is the
planned mechanical mirror of the reverse-Jónsson proof
([`m6-7-reverse-jonsson.md`](m6-7-reverse-jonsson.md)), run over `𝔽[ Fin 4 ]` instead of
`𝔽[ Fin 3 ]`; it consumes that proof's `ParityChain` machinery wholesale, and the M6-4
free bridge ([`m6-4-free-bridge.md`](m6-4-free-bridge.md)) with one upgrade
(`cg-pairs→⊢`, below).  The *forward* Day
direction (Day terms ⟹ CM) is **not** part of this work: it needs the genuinely
two-dimensional ladder of Day 1969 and was tracked separately on #412, where it has
since **landed** (PR #442), assembling the complete iff `Day-theorem`; see the M6-6 note
([`m6-6-forward-jonsson-day.md`](m6-6-forward-jonsson-day.md)).

## What landed

+  `CM⇒Day` (`Setoid.Varieties.Maltsev.Modularity`, next to `Day-Statement` — the same
   "converse lives next to its statement" placement as `CD⇒jonsson` and `CP⇒maltsev`;
   born `CM⇒day`, renamed and given an explicit `Finitary 𝑆` argument in PR #442,
   mirroring `CD⇒jonsson` so `Day-theorem` assembles from a single witness):
   for a **finitary** signature, a congruence-modular variety has `n + 1` Day terms,
   i.e. the `proj₁` direction of `Day-Statement`, at the levels of the free algebra
   `𝔽[ Fin 4 ] : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)` (the same instantiation as
   `CD⇒jonsson`).
+  `cg-pairs→⊢` (`Setoid.Varieties.FreeSubstitution`): the principal-pair bridge upgraded to
   the **join of two principal congruences** — a substitution collapsing both generator
   pairs sends every pair of `Cg ❴ a , b ❵ ∨ Cg ❴ c , d ❵` to a derivable equation.
   The proof is the same `Cg⊆ker` instance as `cg-pair→⊢`, with the union of the two
   generating congruences included in the kernel componentwise.

## The construction

The classical recipe (Day 1969; Burris–Sankappanavar II.12.4, (1) ⟹ (2)), through the
M6-4 bridge:

+  Work in `𝔽 = 𝔽[ Fin 4 ]` on generators `x , y , z , u`; it models the theory
   (`satisfies`), hence is congruence-modular by the hypothesis `cmv`.
+  Take `θ = Cg ❴ y , z ❵`, `φ = Cg ❴ x , y ❵ ∨ Cg ❴ z , u ❵`,
   `ψ = Cg ❴ x , u ❵ ∨ Cg ❴ y , z ❵`; then `θ ⊆ ψ`, the modular side condition.  The
   pair `(x , u)` lies in `ψ` (a generator pair) and in `θ ∨ φ` (the walk
   `x φ y θ z φ u`), so the modular law `θ ∨ (φ ∧ ψ) ≑ (θ ∨ φ) ∧ ψ`, read right to
   left, moves it into `θ ∨ (φ ∧ ψ)`.
+  `finitary⇒JoinIsChain` (M6-6) turns that join membership into a finite alternating
   chain, and the **off-phase** pass `chain→parityᵒ` normalizes it: `(φ∧ψ)`-steps at
   even positions, `θ`-steps at odd ones.
+  The chain's elements *are* quaternary terms (the carrier of `𝔽` is `Term (Fin 4)`),
   and they are the Day terms: `I i = tᵢ`.  Each identity of `Th-Day n` is an endpoint
   fact or a congruence membership pushed through a collapsing substitution:
   +  `m₀(x,y,z,u) ≈ x` — the chain head is exactly `x`;
   +  `mₙ(x,y,z,u) ≈ u` — the chain tail is derivably `u`;
   +  `mᵢ(x,y,y,x) ≈ x` — collapse `z ↦ y , u ↦ x` (the two `ψ`-pairs, via
      `cg-pairs→⊢`); every chain element is ψ-tied to `x` (`head-linked` at `μ = ψ`,
      with `proj₂` for the meet steps and `θ ⊆ ψ` for the θ-steps);
   +  the forks — collapse `y ↦ x , z ↦ u` (the two `φ`-pairs, via `cg-pairs→⊢`) at
      even `i` and `z ↦ y` (the `θ`-pair, via `cg-pair→⊢`) at odd `i`, exactly the
      parity of the normalized chain's `i`-th step.
+  As in M6-5/M6-7-Jónsson, the collapsing substitutions are the `I ✦_` position maps,
   so every bridge output is definitionally the interpreted identity modulo one
   `graft≐[]` shim, every collapse condition is `refl`, and the local kit
   (`graft-bridgeˡ` / `graft-bridge` / `discharge`) makes the five identity families
   uniform one-liners.

## Findings

+  **The mirror held**.  The reverse-Jónsson design note predicted the Day converse
   would be a mechanical mirror; it was — the module type-checked on the first attempt,
   in ~6 s, with `abstract pc` from the start (the note's performance finding, adopted
   preemptively).  Everything specific to Day is confined to the three points below.
+  **Two of Day's three congruences are joins of principal congruences**.  Jónsson's
   `θ, φ, ψ` are all principal, so `cg-pair→⊢` sufficed; Day's `φ` and `ψ` each
   identify *two* generator pairs, so their collapsing substitutions must kill both
   pairs at once.  The upgrade is `cg-pairs→⊢`, one `⊎`-split on top of the existing
   `Cg⊆ker` argument; it lives next to `cg-pair→⊢` in `FreeSubstitution` because it is
   generic bridge machinery, not Day-specific.
+  **The modular law is consumed right-to-left, and the phase is swapped**.  The
   library states CM as `θ ⊆ ψ → θ ∨ (φ ∧ ψ) ≑ (θ ∨ φ) ∧ ψ`; the construction lands
   `(x , u)` in the *right*-hand side (both memberships are one or three `base` steps),
   and `proj₂` of the `≑` moves it left.  The extracted chain then carries its
   `θ`-steps in the **first** `∪ᵣ` tag while `Th-Day`'s even forks are the
   `φ`-collapses — so the normalization is the off-phase pass `chain→parityᵒ`, where
   Jónsson used `chain→parity`.  Parameterizing `ParityChain` by the ordered relation
   pair (the M6-7-Jónsson design) is exactly what makes this a one-token difference.
+  **Four generators, same bookkeeping**.  The four-variable substitutions
   (`σxyzu`, `σxyyx`, `σxxuu`, `σxyyu`) are read off `Th-Day`'s argument patterns the
   same way the Jónsson ones are read off `Th-Jonsson`'s; the only care point is the
   ψ-collapse `σxyyx`, which must send *both* `u ↦ x` and `z ↦ y` (the `quad x y y x`
   positions) so that both of ψ's generator pairs collapse definitionally (`refl`).

## Track hygiene

This is **clone/Maltsev** material on the M6-3 track.  Congruence *modularity* is the
FLRP-facing condition (via Day's theorem and the modular commutator), but nothing here
touches congruence-lattice representation itself; the FLRP remains a separate research
area, and this note keeps to the Maltsev-condition side of the boundary.

## Remaining work on #413

None — this completes the issue.  The one Day item that remained elsewhere, the
*forward* direction (Day terms ⟹ CM), was initially deferred on #412 for the structural
reason recorded in the M6-6 note and has since **landed** there (PR #442, the M6-6
note's "ladder that works"): `Day-Statement` is now assembled into the complete iff
`Day-theorem`, exactly as `jonsson-theorem` was.

## Build / check

+  Whole library (what CI runs): `nix develop --command make check`.
+  The changed modules:
   `nix develop --command agda src/Setoid/Varieties/Maltsev/Modularity.lagda.md`
   (and `src/Setoid/Varieties/FreeSubstitution.lagda.md`).

[M6-7]: https://github.com/ualib/agda-algebras/issues/413
