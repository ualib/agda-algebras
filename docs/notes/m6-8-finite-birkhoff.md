<!-- File: docs/notes/m6-8-finite-birkhoff.md -->

# M6-8 design note: finite Birkhoff — discharging the subdirect SI-representation

This note records [M6-8][] (#419), the constructive *discharge* of the choice
principle that [M6-2][] (#272) isolated.  Read it alongside the M6-2 note
[`m6-2-subdirect.md`][] (its "option (b)" is exactly this work) and the merged
modules `Setoid.Subalgebras.Subdirect` and `Setoid.Congruences.Monolith`.

M6-2 proved the choice-free core of Birkhoff's subdirect representation theorem and
stated the full theorem `Birkhoff-subdirect` *relative to* a module parameter
`sirep : ∀ 𝑨 → SubdirectSIRep 𝑨` — a separating family of SI-quotient congruences.
M6-8 constructs that family outright for finite algebras, with no choice and no
postulate, and feeds it to the choice-free reduction `SIRep→Representable`.

## What landed

One module, `Setoid.Subalgebras.Subdirect.Finite`, `--cubical-compatible
--exact-split --safe`.

+  `FiniteAlgebra 𝑨` — the finiteness/decidability interface (see below).
+  `finiteSubdirectSIRep 𝑭 : SubdirectSIRep 𝑨 ℓ (α ⊔ ρ)` — the discharged
   parameter: a separating family of congruences whose quotients are subdirectly
   irreducible, indexed by the distinct pairs of `𝑨`.
+  `finite-Birkhoff 𝑭 : SubdirectlyRepresentable 𝑨 ℓ (α ⊔ ρ)` — Birkhoff's theorem
   for finite algebras, unconditionally (no choice parameter).
+  `𝟏` / `𝟏-FiniteAlgebra` / `𝟏-SubdirectlyRepresentable` — the one-element algebra
   over the signature, a witness that `FiniteAlgebra` is genuinely inhabited and
   that `finite-Birkhoff` computes (so this is a real discharge, not a renamed
   parameter).

## The finiteness interface, and why it is what it is

The classical proof (Burris–Sankappanavar II.8.6) selects, for each pair `a ≢ b`, a
congruence **maximal** among those not relating `a` and `b`; it is completely
meet-irreducible, so its quotient is subdirectly irreducible, and the family over
all distinct pairs meets to the diagonal.  Two finiteness needs arise:

+  to find the maximal congruence by **search**, we enumerate the congruence
   lattice; and
+  to recognise subdirect irreducibility — whose monolith condition `mono-least`
   quantifies over **all** congruences of the quotient — the enumeration must be
   **complete**: every congruence equal, up to mutual containment `≑`, to a listed
   one.

The decisive constructive fact is that **carrier-finiteness with decidable `≈`
does not suffice** to produce such an enumeration.  A congruence is a
`Type`-valued relation, and an arbitrary relation on a finite carrier need not be
decidable: on a two-element carrier with no operations, the relation collapsing
the two points *iff* a proposition `P` holds is a congruence, and it is `≑`-equal
to a decidable one only if `P` is decidable.  A complete enumeration of
congruences-up-to-`≑` is therefore *strictly stronger* than decidable `≈` on a
finite carrier; it is exactly the classical content of "finite algebra" for
congruence-lattice purposes, and constructively it must be supplied.

So `FiniteAlgebra 𝑨` bundles: decidable `≈` on `𝕌[ 𝑨 ]`; a surjective enumeration
`Fin card → 𝕌[ 𝑨 ]` of the carrier (used to *count* related pairs); and a finite
list `cons` of **decidable** congruences (`DecCon`) that is **complete** up to `≑`.
This is decidable, computational data, classically furnished by every finite
algebra — not a choice principle.  The distinction from M6-2's option (a) is the
point: M6-2 assumed the theorem's *conclusion* (the separating SI family); M6-8
assumes only finiteness *data* and runs an algorithm to build that family.

## The construction

+  **Quotient congruences are congruences above `Θ`.**  For `Q = 𝑨 ╱ Θ`, a `Con Q`
   *is* a `Con 𝑨` containing `Θ`: the relation, equivalence proof, and operation
   compatibility transfer verbatim (the quotient's operations are `𝑨`'s, so
   `f ^ Q = f ^ 𝑨` definitionally), and a `Q`-congruence's reflexivity over the
   quotient equality `Θ` *is* the containment `Θ ⊆ ·`.  `Q→A` records this almost
   for free — no heavy correspondence theorem.

+  **The maximal congruence by counting.**  For a pair `a ≢ b`, filter `cons` to
   the congruences not relating `a , b` (non-empty: the diagonal's representative
   is one) and take a member of maximum `count`, where `count d` is the number of
   enumerated index pairs `d` relates.  Counting turns the partial order into ℕ:
   `count` is monotone under `⊆` and *strictly* monotone under proper containment
   (`count-mono` / `count-strict`, instances of two generic filtered-length
   lemmas), so a maximum-count element is `⊆`-maximal.  Maximality is proved by
   deciding carrier-containment and, on failure, extracting a witnessing pair via
   `¬∀⟶∃¬` to invoke strict monotonicity.

+  **The monolith is the principal congruence of `(a , b)`.**  `μ = Cg_Q (a , b)`
   is nonzero (it relates the `Q`-distinct `a , b`) and least nonzero: any nonzero
   `ψ` corresponds to `φ ⊇ Θ`; its representative `d ∈ cons`, were it not to relate
   `a , b`, would be forced `⊆ Θ` by maximality, making `ψ` zero — so `ψ` relates
   `a , b`, i.e. contains `μ`.  This gives `IsSubdirectlyIrreducible Q`.

+  **Separation closes the `¬¬`-gap.**  The family separates points because, for
   `x , y` not already `≈`-equal — *decidable*, by the interface — the chosen `Θ`
   for `(x , y)` keeps them apart.  Decidable `≈` is exactly what removes the
   double-negation the M6-2 note flags, so the meet is *exactly* the diagonal.

## Levels

Everything is carried at the absorbing congruence level `clv α ρ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ`,
at which the generated principal congruence `Cg_Q (a , b)` used for the monolith
stays put (`𝒈 (clv) = clv`).  This is the same discipline as
`Setoid.Congruences.CompleteLattice`.  The quotient family lands at level `clv` and
the index — distinct pairs — at `α ⊔ ρ`, so `finiteSubdirectSIRep` has type
`SubdirectSIRep 𝑨 (clv α ρ) (α ⊔ ρ)`.

## What remains (follow-ups)

+  A genuinely subdirectly irreducible **worked example** over a concrete signature
   (a small algebra whose congruence lattice is enumerated by hand), exercising the
   maximal-congruence search rather than the degenerate `𝟏` witness.
+  A **builder** producing `FiniteAlgebra` from more primitive data for tractable
   classes — e.g. a carrier `≃ Fin n` whose every congruence is *given* with a
   decision procedure — packaging the `complete` field once and for all.
+  Connecting finite subdirect representation to the FLRP setting (M6's target),
   where finiteness is exactly the hypothesis.

[M6-8]: https://github.com/ualib/agda-algebras/issues/419
[M6-2]: https://github.com/ualib/agda-algebras/issues/272
[`m6-2-subdirect.md`]: ./m6-2-subdirect.md
