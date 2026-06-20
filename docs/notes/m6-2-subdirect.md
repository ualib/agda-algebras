<!-- File: docs/notes/m6-2-subdirect.md -->

# M6-2 design note: subdirect products, subdirectly irreducible algebras, and Birkhoff's subdirect representation theorem

This note records the first pass of [M6-2][] (#272) — *subdirect products and
subdirectly irreducible algebras* — the foundational FLRP-prerequisite that the M6
track skipped over when it did congruence permutability (M6-3/#273) and the CP converse
(M6-4/M6-5, #410/#411) first.  Read it alongside the M6 milestone description in
[`GITHUB_PROJECT.md`][] and the merged congruence-lattice work
(`Setoid.Congruences.{Lattice,Generation,CompleteLattice}`).

The deliverable mirrors M6-3's discipline: the **constructive core is proved in full**,
and the one genuinely choice-dependent statement (the *existence* half of Birkhoff's
theorem) is isolated as an explicit module parameter rather than postulated, so the
library stays postulate-free under `--safe`.

## What landed

Two modules, both `--cubical-compatible --exact-split --safe`.

+  `Setoid.Congruences.Monolith` — pure congruence theory; the order-theoretic content
   of subdirect irreducibility.
   +  `Nontrivial 𝑨` / `Trivial 𝑨` — the carrier has two `≈`-distinct elements / all
      elements are `≈`-equal (the degenerate one-element case); `trivial⇒¬nontrivial`.
   +  `BelowDiagonal θ` (`θ` relates only `≈`-equal elements, i.e. `θ ≑ 0ᴬ`) and its
      negation `Nonzero θ` (the right "strictly above `0ᴬ`" notion).
   +  `⋂` — the meet (intersection) of an `ℓ`-small family of `ℓ`-level congruences, at
      the algebra's own relation level (the natural-level instance of the `⋀` that
      `Setoid.Congruences.CompleteLattice` packages at the absorbing level `L`).
   +  `IsMonolith μ` — `μ` is nonzero and is contained in every nonzero congruence (the
      least nonzero congruence); `HasMonolith`; `monolith-unique` (the monolith is
      unique up to `≑`, the mutual-containment equivalence on congruences).
   +  `IsSubdirectlyIrreducible 𝑨 = Nontrivial 𝑨 × HasMonolith 𝑨`, with `si⇒nontrivial`
      and `trivial⇒¬si`.
   +  `monolith⇒cmi` — the characterization: a monolith makes `0ᴬ` *completely
      meet-irreducible*; and `monolith⇒∧-irreducible` — its binary instance, the meet of
      two nonzero congruences is nonzero ("`0ᴬ` is meet-irreducible", the
      directly-indecomposable-adjacent fact).

+  `Setoid.Subalgebras.Subdirect` — the subdirect structures and the bridge.
   +  `⨅-proj` — the coordinate projection `⨅ 𝒜 → 𝒜 i` as a homomorphism (the
      `⨅-projection-hom` of `Setoid.Homomorphisms.Products` re-derived so the factor
      family alone determines it, without that version's vestigial domain parameter).
   +  `coord h i = projᵢ ∘ h` and `IsSubdirectEmbedding` (a hom that is injective and
      whose every coordinate map is surjective); `SubdirectEmbedding`; `subdirect→≤`
      (a subdirect embedding is in particular a subalgebra inclusion `𝑩 ≤ ⨅ 𝒜`).
   +  **The bridge.**  For a family `θ : I → Con 𝑨`, the natural map
      `natmap = ⨅-hom-co (πhom ∘ θ) : 𝑨 → ⨅ (λ i → 𝑨 ╱ θ i)`.  `Separates θ` says the
      meet `⋂ θ` is the diagonal (`∀ i, θ i a b ⟹ a ≈ b`).  Then `natmap-injective` /
      `natmap-separates` show injectivity of the natural map is **definitionally** the
      separation property, and `natmap-proj-onto` shows each coordinate map *is* the
      canonical quotient epimorphism, hence surjective — with no decidability or choice
      on the index.  `separating→SubdirectEmbedding` assembles them.
   +  **Birkhoff, reduced to existence.**  `SubdirectlyRepresentable 𝑨` (a family of SI
      algebras with a subdirect embedding of `𝑨` into their product) is the theorem's
      conclusion.  `SubdirectSIRep 𝑨` packages the bridge's input: a separating family
      whose quotients are all subdirectly irreducible.  `SIRep→Representable` is the
      fully-constructive reduction, and `Birkhoff-subdirect` is the theorem relative to
      the choice principle `(∀ 𝑨 → SubdirectSIRep 𝑨)`.

## The injectivity-is-separation identity

The technical pleasantness of the bridge is that the two halves are *definitional*, not
just provable.  The image of `a : 𝕌[ 𝑨 ]` under `natmap` is its tuple of congruence
classes `λ i → a`, and equality in `⨅ (λ i → 𝑨 ╱ θ i)` at that tuple unfolds to
`∀ i → proj₁ (θ i) a b` — exactly the hypothesis of `Separates`.  So
`IsInjective (proj₁ natmap)` and `Separates θ` are the *same type* — a fact we record
with a `refl`-checked `IsInjective (proj₁ natmap) ≡ Separates` (propositional `≡`) — and
`natmap-injective = id`.  Likewise `coord 𝑨╱ natmap i` reduces to the canonical
projection `πepi 𝒾𝒹 (θ i)`, so its surjectivity is `IsEpi.isSurjective` of that epi
verbatim.  This is the formal content of the brief's "injectivity is exactly *the meet is
the diagonal*".

## The choice decision for Birkhoff (option (a))

Birkhoff's subdirect representation theorem needs, for each pair `a ≢ b`, a congruence
**maximal** among those not relating `a , b`.  Such a congruence is completely
meet-irreducible, so its quotient is subdirectly irreducible, and the family of these
(over all distinct pairs) meets to the diagonal.  Producing the maximal congruence is a
Zorn's-lemma step: incompatible with postulate-free `--safe`.

The brief offered three ways to handle this; we took **(a)**: state the theorem relative
to an explicit choice principle taken as a module parameter.  Concretely
`Birkhoff-subdirect` abstracts over `sirep : (𝑨 : Algebra α ρ) → SubdirectSIRep 𝑨 ℓ ι`
and derives `SubdirectlyRepresentable 𝑨` for every `𝑨`.  The choice-free half — *given
the SI quotients with meet `0ᴬ`, you get the subdirect embedding* — is `SIRep→Representable`
and is proved unconditionally, so the theorem reduces to *exactly* the choice-dependent
existence claim `∀ 𝑨 → SubdirectSIRep 𝑨`, as the brief asks.

Why `SubdirectSIRep` (a separating SI-family) rather than the more atomic "for each
`a ≢ b`, a separating cmi congruence" as the parameter?  Because turning the per-pair
congruences into a family with meet *exactly* the diagonal is itself non-constructive.
Indexing by distinct pairs, the separation proof for a fixed `a , b` must inspect whether
`a ≈ b` to form the index `(a , b , _)`, which yields only `¬ ¬ (a ≈ b)`; recovering
`a ≈ b` needs `≈` to be stable (decidable equality, or a double-negation elimination).
That stability is precisely the classical input, so we fold it into the parameter and
take the directly-usable `SubdirectSIRep` — a separating family in the constructively
strong sense — as the assumption.  Option (b) (the finite/decidable case, where `≈` *is*
decidable and the maximal separating congruence is found by search over a finite
congruence lattice) is the natural way to *discharge* this parameter constructively for
finite algebras; it is left as a follow-up.  We did not take option (c) (state-and-defer
as a checked `Type`), since (a) both states the assumption and proves the theorem from it.

## The monolith characterization and its converse

`monolith⇒cmi` is stated in **contrapositive** form: *if every member of a family is
nonzero, the meet is nonzero*.  This is the constructively honest reading of "`0ᴬ` is
completely meet-irreducible" — the textbook form "`⋀ θ ≑ 0ᴬ ⟹ ∃ i, θ i ≑ 0ᴬ`" would
require extracting a witnessing index from a negated statement.  The proof is immediate
from the monolith: `μ ⊆ θ i` for every `i`, so `μ ⊆ ⋀ θ`, and `μ` nonzero forces `⋀ θ`
nonzero.

The **converse** (`0ᴬ` completely meet-irreducible ⟹ a monolith exists) is *not* added.
The natural construction takes `μ = ⋀ {θ : θ nonzero}`, the meet of all nonzero
congruences; but that family is indexed by `Σ[ θ ∈ Con 𝑨 ℓ ] Nonzero θ`, which lives one
universe up, so the resulting meet is a `Con 𝑨 ℓ′` with `ℓ′ > ℓ` — it is not a monolith
*at level `ℓ`*.  This is the same predicativity wall that the complete-lattice
construction meets (its completeness is only for `ℓ₀`-small families).  Stating the
converse cleanly would need an impredicative meet; we record it here as a known limitation
rather than forcing a level-bumped statement.  The forward direction is the one consumed
downstream.

## Levels

The congruence level of an SI algebra is fixed to the algebra's **own relation level**
`ρ`: for `𝑨 : Algebra α ρ` the diagonal `0ᴬ` is the setoid equality `_≈_ : Con 𝑨 ρ` and
the monolith (when present) is a `Con 𝑨 ρ`, so `IsSubdirectlyIrreducible` carries no
extra level parameter.  This is the natural predicative choice; a level-generic variant
is possible but unnecessary for the present clients.  The bridge keeps the family level
`ℓ` and index level `ι` generic (the product `⨅` lands at `Algebra (α ⊔ ι)(ℓ ⊔ ι)`, per
the standard product level arithmetic), so the Birkhoff index can be the
`(α ⊔ ρ)`-level type of distinct pairs without forcing `ℓ = ρ`.

## Homes and naming

+  Monolith/SI live under `Setoid.Congruences.` because they are congruence-lattice
   notions and depend only on `Setoid.Congruences.{Basic,Lattice}`; putting them under
   `Setoid.Algebras.` would invert the layering (Algebras is below Congruences).
+  Subdirect products/embeddings and Birkhoff live under `Setoid.Subalgebras.` (a
   subdirect product *is* a subalgebra of a product); `Subdirect` imports `Monolith` for
   the SI predicate, a clean one-way dependency.
+  The theorem is `Birkhoff-subdirect`, distinct from the HSP variety theorem's
   `Birkhoff` (`Setoid.Varieties.HSP`), so both can be re-exported through the top-level
   `Setoid` barrel without an ambiguous-name clash.

## What remains (follow-ups)

+  The constructive finite case (option (b)): for an algebra with decidable `≈` and a
   finite congruence lattice, *discharge* `SubdirectSIRep` by searching for maximal
   separating congruences — turning `Birkhoff-subdirect` into an unconditional theorem on
   finite algebras.
+  The impredicative converse `cmi ⟹ monolith`, if/when the library adopts an
   impredicative or resized meet.
+  Connecting `IsSubdirectlyIrreducible` to the *absence of a nontrivial subdirect
   decomposition* (an SI algebra's every subdirect embedding has an isomorphism
   coordinate) — the equivalence that makes "subdirectly irreducible" name what it does.

[M6-2]: https://github.com/ualib/agda-algebras/issues/272
[`GITHUB_PROJECT.md`]: ../GITHUB_PROJECT.md
