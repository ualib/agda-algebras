<!-- File: docs/adr/009-signature-genericity-generalized-variables.md -->

# ADR-009: Signature genericity via generalized variables in the core; module parameters at the Classical layer

## Status

Accepted — 2026-07-19.

## Context

A generic module of the `Setoid/` core can carry its signature in one of two ways.  It can take the signature as a *module parameter* — `module M {𝑆 : Signature 𝓞 𝓥} where` — so that `𝑆` is fixed for the module's whole scope and every definition inside reads against it.  Or it can leave the module un-parametrized — `module M where` — and let each definition generalize over a `variable 𝑆 : Signature 𝓞 𝓥`, so that `𝑆` is inferred per use, almost always from an algebra or structure argument whose type already carries it.

The library began overwhelmingly in the first style and has drifted, under concrete pressure, toward the second.  Three forces drove the drift, each a real incident rather than a preference:

+  **Multiple signatures in one scope.**  `Setoid.Algebras.Finite` was de-parametrized because `FLRP.Problem` consumes the finiteness interface at *two different signatures* in a single module; a module parametrized by one `𝑆` cannot serve two without a second `open` and renaming gymnastics.  `Setoid.Congruences.Generation` was de-parametrized for the same reason.
+  **Barrel re-export.**  Every `ModuleArityMismatch` error in the WP-7 work (PR #467, PR #468) came from *mixing* the two styles across a re-export: a parametrized barrel applying `{𝑆 = 𝑆}` to a submodule that had been de-parametrized, or the reverse.  A uniform style makes `open import M public` always well-formed and removes the entire error class.
+  **Standard-library idiom.**  Modern `agda-stdlib`, with which this library interoperates heavily through bundle views, uses per-definition generalized `variable`s rather than signature-parametrized modules; matching it lowers friction for contributors fluent in stdlib.

Two clarifications keep the decision honest.  First, for the definitions that dominate the API — those taking an algebra, group, or other structure whose type carries `𝑆` — the two styles produce *identical* call sites, because `𝑆` is inferred from the structure argument either way (`Con 𝑨`, `DecCon 𝑨 ℓ`, `Sub 𝑮` look the same under both).  The often-cited "no-parameter modules are a simpler API" is therefore mostly illusory at the point of use; the genuine differences are the three incidents above plus the ergonomics point below.  Second, the `clv`-style pinning friction that motivated the adjacent level refactor is *orthogonal* to this decision: a signature-dependent construction with no signature-carrying argument (a bare level) needs an explicit `{𝑆 = 𝑆}` under *both* styles, so it argues for neither — the fix there was to remove the indirection, not to change module style.

Against the drift stands one legitimate advantage of module parameters: **fix-once ergonomics**.  When an entire development works over a single fixed signature, `open M {𝑆 = mySig}` once specializes everything downstream with no repetition, and the header `module M {𝑆 : Signature 𝓞 𝓥}` documents "this module is about one signature."  This is exactly the situation of the `Classical/` layer, which fixes concrete signatures (`Sig-Group`, `Sig-Lattice`, …) and builds specific theories over them.

Finally, this decision is continuous with ADR-005, which already made `𝓞` and `𝓥` public generalized `variable`s co-located with `Signature` rather than per-module parameters, and with the library-wide `private variable α ρ : Level` convention.  Of the four quantities a generic algebraic definition ranges over — `𝓞`, `𝓥`, `α`, `ρ`, and the signature `𝑆` — only `𝑆` is still frequently a module parameter.  `𝑆` is the odd one out.

## Decision

Make signature genericity uniform in the core and reserve module parameters for the application layer.

+  **`Setoid/` generic core — generalized variable.**  A module of the generic core that ranges over an arbitrary signature is written `module M where` and generalizes over a `variable 𝑆 : Signature 𝓞 𝓥`, exactly as it already generalizes over `𝓞`, `𝓥`, `α`, `ρ`.  The variable is declared once, public, co-located with `Signature` in `Overture.Signatures` (extending ADR-005's treatment of `𝓞` / `𝓥` to the signature they parametrize), and imported by name — `open import Overture using ( 𝓞 ; 𝓥 ; Signature ; 𝑆 )` — never re-declared.  Where a definition's signature cannot be inferred (a signature-dependent construction with no signature-carrying argument), it takes `{𝑆}` explicitly like any other implicit; this is rare and is not a reason to parametrize the module.
+  **`Classical/` application layer — module parameter, selectively.**  A `Classical/` module *may* take a signature as a module parameter, or fix a concrete signature, when the whole module concerns a single signature throughout and making it explicit improves clarity or simplifies the code.  This is where fix-once ergonomics belong and where a reader benefits from the header naming the one signature in play.  The choice is local and deliberate, not automatic: a `Classical/` module that is genuinely generic over signatures follows the core convention instead.
+  **No mixing within a re-export chain.**  A barrel and the submodules it re-exports use one style, so that `open import Sub public` is uniform and no `{𝑆 = 𝑆}` is ever applied to an un-parametrized module (or omitted from a parametrized one).  This is the rule whose violation produced every `ModuleArityMismatch` in the WP-7 branches.

Migrating the remaining signature-parametrized `Setoid/` modules to the generalized-variable form is a mechanical follow-up sweep, guarded by `make check` and tracked in its own issue; no module is churned ahead of that scheduled work.

## Consequences

+  **Positive — the barrel error class is eliminated.**  With the core uniform, `open import M public` is always well-formed; the `ModuleArityMismatch` failures that recurred through WP-7 cannot arise.
+  **Positive — multiple instantiations in one scope are natural.**  Consumers like `FLRP.Problem` that use a generic interface at several signatures at once need no second `open` or renaming; this stops forcing one-off de-parametrizations.
+  **Positive — one convention for all four-plus generic quantities.**  `𝑆` joins `𝓞`, `𝓥`, `α`, `ρ` as a generalized variable, so a generic definition's telescope is uniform and the library stops treating the signature differently from the levels that describe it — the ADR-005 principle applied to the signature itself.
+  **Positive — stdlib alignment and mechanical Cubical porting.**  The generalized-variable form matches stdlib idiom and tends to port to Cubical (ADR-003) more mechanically, because each definition is self-contained rather than depending on an ambient module telescope.
+  **Positive — fix-once ergonomics are preserved where they belong.**  End users working over a single signature get "set it once" at the `Classical/` layer (ADR-002), which is where such work already lives, rather than through core-module parameters.
+  **Negative — a migration cost.**  The signature-parametrized `Setoid/` modules that remain must be swept to the new form; the change is mechanical and `make check`-guarded but non-trivial in extent, and it is the *reverse* of some parametrization still present, so it must be done deliberately, not opportunistically.
+  **Negative — noisier goal displays.**  A generalized `{𝑆}` implicit surfaces in goal and error output where a fixed module telescope would have hidden it; this is the same trade-off ADR-005 accepted for `𝓞` / `𝓥`, and the same mitigations apply.
+  **Neutral — two conventions coexist by layer.**  Core and Classical may read differently on the signature; the boundary is the `Setoid/`–`Classical/` line, which is already a load-bearing architectural seam (ADR-001, ADR-002), so the split adds no new concept to learn beyond "generic core generalizes, application layer may fix."

## Alternatives considered

+  **Parametrize the generic core uniformly.**  Rejected.  It fights all three drivers — barrels (a parametrized barrel must thread `{𝑆}` into every re-export and cannot cleanly re-export a de-parametrized submodule), multiple-instantiation scopes (`FLRP.Problem` would need repeated opens), and stdlib idiom — and it reverses the de-facto direction the library has already moved under real pressure.  Its one genuine merit, fix-once ergonomics, is better served at the `Classical/` layer without imposing a fixed signature on generic machinery.
+  **De-parametrize everything, `Classical/` included.**  Rejected.  It discards the legitimate clarity of a module whose entire subject is one signature; the `Classical/` structures are exactly such modules, and forcing every `Sig-Group` reference to be inferred per use where the whole module is about groups trades documentation and concision for uniformity that buys nothing there.  The carve-out for single-signature `Classical/` modules is deliberate.
+  **Keep the current mixed state.**  Rejected.  Mixing is the actual source of the `ModuleArityMismatch` churn and of the "which style is this module?" ambiguity; leaving it unresolved guarantees the errors recur as the two trees keep growing.

## References

+  ADR-005 — [Scope of the `𝓞` / `𝓥` universe-level variables](005-universe-level-variable-scope.md); this ADR extends the same generalized-`variable` treatment from `𝓞` / `𝓥` to the signature `𝑆`.
+  ADR-001 — [Setoid as canonical development tree](001-setoid-as-canonical.md); the `Setoid/`–`Legacy/` line and the canonical tree this convention governs.
+  ADR-002 — [Classical structures layer](002-classical-layer-design.md); the application layer that is the home for signature-fixing and fix-once ergonomics.
+  ADR-003 — [Cubical Agda as canonical long-term target](003-cubical-canonical-target.md); the port that benefits from self-contained, generalized-variable definitions.
+  `src/Overture/Signatures.lagda.md` — the declaration site where the public `variable 𝑆 : Signature 𝓞 𝓥` co-locates with `Signature`, `𝓞`, and `𝓥`.
+  Precedents forced by the drift — `src/Setoid/Algebras/Finite.lagda.md` and `src/Setoid/Congruences/Generation.lagda.md` (de-parametrized for multi-signature consumers), and the `ModuleArityMismatch` incidents on PRs #467 and #468.
+  `docs/STYLE_GUIDE.md` — the level-variable and signature conventions to be updated once the migration sweep lands.
