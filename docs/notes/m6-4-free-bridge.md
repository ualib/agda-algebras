<!-- File: docs/notes/m6-4-free-bridge.md -->

# M6-4 / M6-5 design note: the free-algebra Cg↔derivability bridge, and the converse of Maltsev's theorem

This note records [M6-4][] (#410) — the *free-algebra congruence/derivability bridge* —
and its first client, [M6-5][] (#411) — the *converse of Maltsev's theorem*.  Read it
with the M6-3 design note [`m6-3-maltsev-conditions.md`](m6-3-maltsev-conditions.md),
especially its § "The deferred theorems and their construction plans", which spelled out
the recipe these two modules now execute.

The deliverable of M6-3 was bounded: the forward Maltsev theorem (`MaltsevTerm⇒CP`) was
*proved*, and the converse (`CP⇒maltsev-Statement`) was *stated* as a checked,
uninhabited `Type`.  M6-4 builds the reusable infrastructure the converse needs, and
M6-5 inhabits the statement, completing the iff for congruence permutability.

**Layout update (M6-7 cleanup)**.  The interim module `Setoid.Varieties.FreeBridge`
that originally packaged the bridge has since been dissolved, its pieces moved to their
canonical homes: the principal (single-pair) relation `❴_,_❵` to
`Setoid.Congruences.Generation` (`module principal`), the bridge lemma `Cg⊆ker` to
`Setoid.Homomorphisms.Properties`, the impedance shim `toEq` to
`Setoid.Varieties.SoundAndComplete` (next to the `Eq` record it targets), and the
substitution-induced homomorphism `subhom` / `renhom` with the principal-pair bridge
`cg-pair→⊢` (and the `recover` smoke test) to `Setoid.Varieties.FreeSubstitution`.
The mathematics below is unchanged; only the module names differ.

## What landed

+  `Setoid.Varieties.FreeBridge` — the reusable bridge (M6-4), four self-contained
   pieces (below).

+  `Setoid.Varieties.Maltsev.Permutability` — `CP⇒maltsev` (M6-5), inhabiting
   `CP⇒maltsev-Statement` in the same module (the converse lives next to its
   statement and the forward `maltsev⇒CP`).  Congruence permutability is now
   characterized by the Maltsev term — a complete iff.

## The bridge (M6-4)

The converse directions of the basic Maltsev conditions all read an equational identity
off a congruence of the relatively free algebra `𝔽[ X ]`
(`Setoid.Varieties.SoundAndComplete`).  The bridge packages the four facts that turn
"a pair lies in a principal congruence of `𝔽[ X ]`" into "an equation is derivable".

### (i) The substitution-induced homomorphism

A substitution `σ : Sub Y X` (a map `X → Term Y`) acts on the free algebra by `_[ σ ]`,
and `subhom σ : hom 𝔽[ X ] 𝔽[ Y ]` packages that action as a homomorphism.  Both
halves are immediate:

+  it respects derivable equality — its `Func` congruence is exactly the `sub`
   inference rule of `_⊢_▹_≈_`;
+  it is a homomorphism — the compatibility square is `refl`, because
   `(node f ts) [ σ ]` *is* `node f (λ i → ts i [ σ ])` on the nose, which is also
   `(f ^ 𝔽[ Y ])` applied to the substituted arguments.

The variable-renaming special case `renhom r = subhom (ℊ ∘ r)` (for `r : X → Y`) is
recorded too.

### (ii) The kernel of a homomorphism as a congruence

This already existed: `kercon` in `Setoid.Homomorphisms.Kernels` assembles the kernel
relation `kerRel _≈_ h` with its three congruence fields (`reflexive`, the equivalence
via `kerRelOfEquiv`, and compatibility `HomKerComp`).  The bridge re-exports it rather
than rebuild it.

### (iii) The bridge lemma

`Cg⊆ker h : R ⊆ ker h → Gen R ⊆ ker h` — for any hom `h` and relation `R` that `h`
collapses, the generated congruence `Cg R` is contained in the kernel of `h`.  This is
one line: `Cg-least (kercon h)`, since the kernel is a congruence above `R`, hence above
the *least* one.

Specialized to a single identified pair and the substitution hom, this is the
load-bearing lemma `cg-pair→⊢`: given a substitution `σ` that collapses `(a , b)` (i.e.
`E ⊢ Y ▹ a [ σ ] ≈ b [ σ ]`), every pair `(s , t)` in the principal congruence
`Cg ❴ a , b ❵` becomes derivably equal after `σ`, `E ⊢ Y ▹ s [ σ ] ≈ t [ σ ]`.  The
principal (single-pair) relation `❴ a , b ❵` is a one-constructor inductive family.

### (iv) The impedance shim

Two theory shapes are in play.  The interpretability relation `_≼_`
(`Setoid.Varieties.Interpretation`) records a theory as an `Idx → Term × Term`; the
derivation calculus `_⊢_▹_≈_` and the free algebra `𝔽[_]` consume an `I → Eq`.
`toEq ℰ i = proj₁ (ℰ i) ≈̇ proj₂ (ℰ i)` converts the former to the latter.  No companion
is needed for *satisfaction*: the two predicates `_⊨ₑ_` / `_⊨_` are *definitionally*
equal (both unfold to pointwise equality of the two terms under all environments), so a
proof of one is directly a proof of the other — no conversion function is written.

A *term-level* fact is also needed, and it lives with its kin (the laws of `graft`) in
`Setoid.Terms.Interpretation`, not in this module: the interpretation action `_✦_`
grafts at a node (`graft`, `Overture.Terms.Interpretation`), while the substitution hom
acts by `_[_]` (`Setoid.Terms.Basic`).  These two operations have identical defining
clauses, but for a *variable* term `w` they are distinct neutral forms — `graft w σ` and
`w [ σ ]` do not reduce to one another.  `graft≐[] : graft t σ ≐ (t [ σ ])` identifies
them by a one-line structural induction, at the inductive equality `_≐_`; `≐→⊢`
(`Setoid.Varieties.FreeSubstitution`) promotes it to a derivation when one is wanted.

### Smoke test

`recover` / `recover-gen` / `recover-swap`: for two variables `u , v` and a substitution
that merges them, every pair in `Cg ❴ ℊ u , ℊ v ❵` is recovered as a derivable equation
after the merge — in particular the generators themselves and (by `symmetric`) the swapped
pair.  This exercises the bridge end-to-end on `base`/`symmetric` memberships.

## The converse of Maltsev (M6-5)

The construction (Burris–Sankappanavar Thm. II.12.2) runs as the M6-3 note planned.
Work in `𝔽 = 𝔽[ Fin 3 ]` on three generators `x , y , z`; it models the theory by
`satisfies`, hence is congruence-permutable by the hypothesis `cpv`.  Take the principal
congruences `θ = Cg ❴ x , y ❵` and `φ = Cg ❴ y , z ❵`.  Then `x θ y` and `y φ z` give
`(x , z) ∈ θ ∘ φ`; permutability yields `(x , z) ∈ φ ∘ θ`, i.e. a witness term `w` with
`x φ w` and `w θ z`.  Since the carrier of `𝔽` *is* `Term (Fin 3)`, this `w` *is* the
Maltsev term `M(x , y , z)`, and it becomes the interpretation `I m-Op = w`.

The two memberships go through `cg-pair→⊢`:

+  `w θ z` (collapsing the `θ`-pair `(x , y)` by `y ↦ x`) gives `M(x , x , y) ≈ y`;
+  `x φ w` (collapsing the `φ`-pair `(y , z)` by `z ↦ y`) gives `M(x , y , y) ≈ x`.

These are the two Maltsev identities; `⊧-interp` and `sound`ness discharge the
satisfaction obligation `reductᴵ 𝑩 I ⊨ₑ Th-Maltsev` for an arbitrary model `𝑩`.

### The substitution-choice that removes the `graft`/`_[_]` gap

The one subtlety is matching the bridge's output with what `⊧-interp` wants.  `⊧-interp`
asks for `𝑩 ⊧ (I ✦ m x x y) ≈ (I ✦ y)`, and `I ✦ (m x x y)` unfolds (by the node clause
of `_✦_`) to `graft w (λ i → I ✦ tri x x y i)`.  The bridge, on the other hand, produces
`w [ σ ]` for whatever `σ` we feed the hom.

The clean fix is to make the hom's substitution *be* that very position map:

    σxxy i = I ✦ tri x x y i,   σxyy i = I ✦ tri x y y i.

Then `graft w σxxy` is **definitionally** `I ✦ (m x x y)`, so the only residual gap is
`graft w σ` vs `w [ σ ]`, closed once and for all by `graft≐[]`.  The collapsing
conditions also fall out by `refl`: `σxxy` sends both `x`- and `y`-positions to `I ✦ x`,
and `σxyy` sends both `y`- and `z`-positions to `I ✦ y`, so the collapsed pairs are
literally equal.  (The position maps are written via the Maltsev-signature generators
`ℊᴹ`, since `tri x x y` lives over `Sig-Maltsev`.)

This is why no per-`𝑩` `graft-eval` reasoning (as in `Classical.Interpretations.Maltsev`)
is needed: choosing `σ` to coincide with the `_✦_` position map collapses the two sides
to a single `graft≐[]` step, and the whole identity is then derived *once* in `𝔽` and
`sound`ed into each model.

### The `Type 0ℓ` restriction

The free construction `module FreeAlgebra {χ} … (E : I → Eq)` shares **one** universe
level `χ` between the equations' variable contexts and the free generators: `satisfies`
forms `Sub Δ (cxt (E i))`, which forces `Δ` and `cxt (E i)` to the same level.  Since
the construction is on `Fin 3 : Type 0ℓ`, the theory's variable type is taken at
`X : Type 0ℓ`.  This is no restriction for the finitary algebraic theories the Maltsev
condition concerns (their variable supplies are `ℕ`- or `Fin`-sized, all `Type 0ℓ`).

Accordingly `CP⇒maltsev` inhabits `CP⇒maltsev-Statement` at the levels of
`𝔽[ Fin 3 ] : Algebra (ov 0ℓ) (ι ⊔ ov 0ℓ)` (with `ov 0ℓ = lsuc 0ℓ`, since
`𝓞 = 𝓥 = 0ℓ`), and at the congruence level `ι ⊔ ov 0ℓ` where its principal congruences
live — `𝒈 (ov 0ℓ)`, the absorbing level of `Setoid.Congruences.Generation`.

## Findings

+  **The bridge is small because `Cg-least` does the work**.  Once the kernel is a
   congruence (it already was, `kercon`), "a generated congruence sits inside any
   collapsing kernel" is `Cg-least` verbatim.  The whole of M6-4 is then plumbing:
   the substitution hom (proof `refl`), the single-pair relation, and the `toEq` shim.

+  **Choosing `σ` to be the `_✦_` position map is the lever**.  It turns the
   interpretation/derivation mismatch from a per-model evaluation argument into one
   syntactic `graft≐[]` step, and makes both collapsing conditions `refl`.  This is the
   M6-5 analogue of M6-3's "the satisfaction condition keeps paying off."

+  **`graft` and `_[_]` are the same map but not definitionally so**.  The term monad's
   bind appears twice in the library — heterogeneous (`graft`, for `_✦_`) and
   level-homogeneous (`_[_]`, for `Sub`).  For closed terms they compute identically;
   for a variable term they are distinct neutrals.  `graft≐[]` is the one-line bridge,
   and belongs with the other `_≐_`-level substitution facts.

+  **The level sharing in `FreeAlgebra` is the real constraint, not the math**.  The
   converse is perfectly general mathematically; the `Type 0ℓ` restriction is an
   artifact of the one-`χ` free-algebra interface.  A future refactor giving
   `FreeAlgebra` independent levels for equation contexts and generators would lift it;
   it is recorded here so a successor need not rediscover it.

## Track hygiene

This is **clone/Maltsev** material, continuing the M6-3 track.  The bridge is the shared
prerequisite for the Jónsson (CD) and Day (CM) converses (#413), which the M6-3 note
flags as connecting forward to the FLRP via Day's theorem; nothing here touches
congruence-lattice *representation*, only properties of congruence lattices.

## Build / check

+  Whole library (what CI runs): `nix develop --command make check`.
+  The changed modules, one at a time:
   `nix develop --command agda src/Setoid/Varieties/FreeSubstitution.lagda.md`
   (then `Setoid/Varieties/Maltsev/Permutability`, which contains the converse).

[M6-4]: https://github.com/ualib/agda-algebras/issues/410
[M6-5]: https://github.com/ualib/agda-algebras/issues/411
