<!-- File: docs/notes/m4-5d-handoff.md -->

# M4-5d session handoff — the category-theoretic layer

This is a working handoff for the session that picks up **M4-5d** (the `F ⊣ reduct` free-expansion adjunction, #342) and the rest of the M4-5 category-theoretic chain.  Read it together with the design note [`milestone-signature-functors.md`](milestone-signature-functors.md) (the mathematical map and the a→g subissue dependency chain) and [ADR-006](../adr/006-signature-morphism-category.md) (the equality/realization decisions).  The dated *state* section below is transient; the conventions and gotchas under it are durable.

## Where things stand (2026-06-10)

The M4-5d spike is implemented (branch `claude/happy-curie-owacbr`): `Setoid.Categories.{Adjunction, FullSubcategory}`, `Classical.Categories.AdjoinUnit` (the `adjoinUnit ⊣ forgetUnit` adjunction with triangle identities and the explicit universal property), the `hom-preserves-∙` / `hom-preserves-ε` morphism invariants, the `expand-ε`-is-a-section lemma, and the design note [`m4-5d-free-expansion.md`](m4-5d-free-expansion.md) (which also records the implicit-pinning gotchas this spike re-confirmed).  The general raw-level free expansion (the issue's stretch task) is deferred there with a concrete construction plan.

M4-5a, b, c and the reduct-functoriality strengthening are all merged to `master`:

+  **M4-5a (#339 / #392)** — `Overture.Signatures.Morphisms`: `SigMorphism`, identity, composition, the `Sig` category laws (all `refl`); `reduct` re-expressed to consume a `SigMorphism` (`Classical.Structures.Reduct`).
+  **M4-5b (#340 / #393)** — `Setoid.Signatures.Functor`: `⟨ 𝑆 ⟩` functorial in the carrier (`map`) and the natural transformation `⟦_⟧` induced by a `SigMorphism`, each law strict (`refl`) with a `-ptw` pointwise corollary.
+  **M4-5c (#341 / #395)** — the category vocabulary and the reduct/forgetful functors: `Setoid.Categories.Category` (minimal `Category` record — objects, `Hom`, a per-hom-set equivalence `_≈_`, `id`, `_∘_`, the laws, and derived `≈-refl` / `≈-sym` / `≈-trans`); `Setoid.Categories.Functor` (`Functor` record: `F₀`, `F₁`, `F-resp-≈`, `identity`, `homomorphism`); `Setoid.Categories.Algebra` (`Alg 𝑆 α ρ : Category` with a **pointwise** hom-setoid `_≋_`); `Classical.Categories.Reduct` (`reductF φ : Functor (Alg 𝑆₂) (Alg 𝑆₁)`); and `Classical.Categories.Forgetful` (`monoid→semigroupF = reductF` of the `Sig-Magma ↪ Sig-Monoid` inclusion).
+  **Reduct strengthening (#339 / #394)** — `reduct-id` / `reduct-∘` in `Classical.Structures.Reduct` are now the strict `args`-free form (`o ^ reduct … ≡ o ^ …`, `refl`) with `-ptw` corollaries.

Loose ends, neither blocking:

+  A cosmetic orphan commit `5f538313` on branch `340-m4-5b-signature-functor` (two `##### → ####` heading tweaks plus a line-wrap in `Setoid/Signatures/Functor.lagda.md`), pushed after #393 merged so it never reached `master`.  Harmless; that branch is otherwise safe to delete.
+  Commits may show as **Unverified** on GitHub if commit signing is misconfigured (e.g. the configured signing key is missing/empty).  After rebasing, avoid workflows/hooks that run a blanket `git rebase --exec … origin/<branch>`: it can rewrite and re-author the upstream commits it replays.

## Conventions to carry

+  **Strict-first, then derive pointwise.**  Whenever `refl` proves a stronger *function-level* `≡` (e.g. `(λ x → f ⟨$⟩ x) ≡ g`), state that first and derive the pointwise corollary (`∀ x → f ⟨$⟩ x ≡ …`) by `cong-app`.  Suffix the pointwise one `-ptw`; never use `-≈` for a propositional `≡` result (`-≈` is reserved for genuine setoid-`≈` results).
+  **Equality per level (ADR-006).**  The *signature* category `Sig` uses propositional `_≡_` (laws by `refl`).  The *algebra* category `Alg` uses a **pointwise hom-setoid** `_≋_` (homomorphisms agree up to the codomain's `≈`) — `_≡_` cannot express this under `--safe` without funext.  The shared `Category` record carries `_≈_` as a field precisely so both instances fit.
+  **Self-contained, no `agda-categories`.**  Keep the minimal `Category` / `Functor` records; extend them (e.g. add `Adjunction` / `Monad` records for M4-5d/e) rather than taking on a dependency.
+  **Placement.**  Signature-level, setoid-free material lives in `Overture`; setoid/algebra-level category material in `Setoid.Categories`; anything whose object map is `reduct` (which ADR-006 keeps in `Classical.Structures.Reduct`) must live in `Classical.Categories` — a `Setoid.* → Classical.*` import is a cycle.

## Inference gotchas (Agda 2.8.0, `--cubical-compatible --exact-split --safe`)

+  **`cong-app` corollaries need their implicits pinned.**  Deriving `pointwise = cong-app strict` often leaves the strict law's implicit signature/setoid unsolved, because the goal is matched through `Carrier (⟨ 𝑆 ⟩ A)` or `o ^ 𝑨` — and `_^_`, `map`, `⟦_⟧` *unfold* through the non-injective `Carrier` / `Interp`, so the unifier cannot invert them.  Two fixes both work: wrap the law and its corollary in a `module _ {𝑆} {A} where …` block so the implicits are fixed locally (cleanest — what `Setoid.Signatures.Functor` does), or pass them explicitly (`cong-app (law {𝑆 = 𝑆} {A = A}) x`).
+  **The strict category/functor laws are `refl`, not setoid reasoning.**  The polynomial-functor action is post-composition on the position function, so the coherences reduce by `∘`-associativity, `id`-cancellation, function-η, record-η and Σ-η — all available under `--cubical-compatible`.  The `Fin n` η-gap of ADR-002 §6 does *not* bite here, because these laws compose *abstract* position maps; it bites only when a concrete `Fin`-pattern lambda must be normalized.
+  **Whole-algebra `≡` is not available.**  `reduct id-morphism 𝑨 ≡ 𝑨` cannot be `refl` (the `Interp.cong` proof field would need funext).  State operation- or hom-level equalities instead — which is exactly why the algebra category's hom-equality is pointwise.
+  **Two-signature functors.**  A functor like `reductF : Functor (Alg 𝑆₂) (Alg 𝑆₁)` needs the (`{𝑆}`-parameterized) `Alg` / `hom` / `Algebra` modules at *both* signatures.  Instantiate them by module application inside a `module _ {𝑆₁ 𝑆₂} (φ) where`: `private module A₁ = Setoid.Categories.Algebra {𝑆 = 𝑆₁}` and `module A₂ = … {𝑆 = 𝑆₂}`.  The `F₁` action keeps the underlying setoid map and reindexes the source `compatible` through `κ` (`compatible (proj₂ f) {ι φ o} {a ∘ κ φ o}`, definitionally).

## M4-5d specifics (from the design note)

+  Build the left adjoint `F ⊣ reduct` (free expansion).  Along signature *inclusions* this is structural; along inclusions that **add equations** it needs a quotient — a **setoid quotient** now, a cubical HIT at v4.0.
+  De-risk with **Spike B**: construct the free monoid on a semigroup (adjoin a unit) and prove its universal property against `reduct`.  If that single adjunction is clean with setoid quotients, the general theorem is plausible.
+  Keep `F` distinct from M3-6's chosen `expand-ε`.
+  You will likely add an `Adjunction` record (and, for M4-5e, a `Monad` record) to `Setoid.Categories`, reusing the `Category`'s `≈-refl` / `≈-sym` / `≈-trans` helpers for the triangle identities.

## Build / check

+  Toolchain: `nix develop` (Agda 2.8.0, standard-library 2.3, pinned by `flake.lock`).
+  Whole library (what CI runs): `nix develop --command make check`.
+  One module while iterating: `nix develop --command agda src/Path/To/Module.lagda.md`.
