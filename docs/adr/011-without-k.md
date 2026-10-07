<!-- File: docs/adr/011-without-k.md -->

# ADR-011: `--without-K` for every module

## Status

Accepted (2026-10-06).

+  **Tracking**: [#594], the switch.
+  **Ancestry**: [#250], which moved the library from `--without-K` to
   `--cubical-compatible` in April 2026; [#279], the flag strategy and the
   import firewall; [#586], whose findings measured the import failure.
+  **Qualifies** [ADR-003](003-cubical-canonical-target.md): the Cubical target
   and its portability discipline stand, and this record says how a future
   `--cubical` tree relates to the library once the library is `--without-K`.
+  **Unblocks** [#588], the move to Agda 2.9.0 and standard-library 3.0.

## Summary

Every module of agda-algebras, and the two aggregator modules the `Makefile`
writes, is checked under `--without-K` again, as it was before April 2026,
when the library moved to the stronger flag `--cubical-compatible`.

The stronger flag was there so that a module checked under Cubical Agda could
import the library.  Nothing does: the Cubical port that ADR-003 plans derives
its modules from the library's by substitution, not by import.  Meanwhile the
standard library has gone back to `--without-K` in its version 3.0, and a
`--cubical-compatible` module cannot import a `--without-K` one, so keeping the
flag would have held the library to the 2.x standard library for good.  The
flag also cost time and space, as follows:

| measure (whole library, every module from source) | `--cubical-compatible` | `--without-K` | change |
|---|---:|---:|---:|
| wall time, mean of five alternating pairs | 115.8 s | 103.4 s | 10.7% less |
| CPU time of the main check, one pair (`+RTS -s`) | 109.3 s | 99.4 s | 9.1% less |
| heap allocated by the main check, the same pair | 276.5 GB | 251.9 GB | 8.9% less |
| bytes of all 346 interfaces | 60,529,263 | 54,338,653 | 10.2% less |
| bytes of the library's 92 interfaces that `Setoid.Varieties.HSP` imports | 18,110,993 | 15,582,809 | 14.0% less |

The switch changes no definition, statement or proof; the library's own
deprecation warnings are the same before and after.  Its price is the import
firewall of [#279]: a module checked under `--cubical` cannot import this
library, as it cannot import the standard library from version 3.0 on.

## Context

Four terms carry this record.

+  **Axiom K** (Streicher's) says that every proof of `x ≡ x` is `refl`; it is
   equivalent to uniqueness of identity proofs, and it is false in homotopy type
   theory.  Agda's **`--without-K`** restricts pattern matching so that no
   definition can depend on K; a library checked under it is compatible with type
   theories in which K fails.
+  **`--cubical-compatible`** (Agda 2.6.3 and later) implies `--without-K` and in
   addition makes Agda generate internal support code for several kinds of
   definition, which a module checked under `--cubical` (Cubical Agda) needs in
   order to import them.  Where Agda cannot extend a pattern match on an indexed
   family to cover Cubical's transports, it warns **`UnsupportedIndexedMatch`**;
   the library silenced that warning with `flags: -WnoUnsupportedIndexedMatch` in
   `agda-algebras.agda-lib`.
+  An option is **coinfective** when a module checked under it may import only
   modules checked under it too.  `--without-K` is coinfective, and so is
   `--cubical-compatible` under `--safe`.  So a `--without-K` module may import a
   `--cubical-compatible` one (the latter flag implies the former), and the
   reverse import fails with `CoInfectiveImport`.  Separately, a `--cubical`
   module may import `--cubical-compatible` modules but not modules checked under
   `--without-K` alone.
+  An **interface file** (`.agdai`) holds the result of checking one module, and
   Agda loads it instead of checking the module again.  Their total size matters
   to anything that ships them, such as an IDE running in a browser.

Until April 2026 the library was checked under `--without-K`.  Then [#250]
moved it to Agda 2.8.0 and standard-library 2.3 and replaced `--without-K` with
`--cubical-compatible` in every module.  The reason, given in
`Overture.Basic`'s paragraph on the pragma, was the Cubical port that ADR-003
plans: a `--cubical` module can import a `--cubical-compatible` module and not a
`--without-K` one.  (ADR-003 itself names no flag.)  Standard-library 2.x was
`--cubical-compatible` too, so the choice raised no import problem at the time.

Three things have changed since.

+  **The standard library went back**.  Version 3.0 restores `--without-K`
   ([agda/agda-stdlib#2967], merged 2026-06-17).  Its author measured the
   standard library's own check at about three quarters of the time under
   `--without-K`, saw no clear use for `--cubical-compatible`, and noted that the
   `UnsupportedIndexedMatch` warnings had been hidden rather than fixed.  Under
   both Agda 2.8.0 and the Agda 2.9.0 nightly, `Overture.Basic`'s first import of
   the 3.0 development head fails with `CoInfectiveImport` ([#586], row 4); [#279]
   had expected that import to work.  Nor can the library stay on 2.x and move to
   the next Agda: standard-library 2.3 and 2.4 both fail under the 2.9.0 nightly
   before any library module is reached ([#586], rows 1 and 2).
+  **The flag has no consumer**.  No module imports the library from Cubical
   Agda.  ADR-003's proof of concept, M5-1 ([#270]), is to obtain its Cubical
   modules by substitution from their `Setoid/` analogs, and a `--cubical` tree
   cannot import the standard library from 3.0 on, so it builds on a cubical
   library (agda/cubical, 1Lab) in any event.
+  **The flag has a cost**.  Agda's manual says Agda "tends to be quite a bit
   faster if `--without-K` is used instead of `--cubical-compatible`".  The
   measurements under *Evidence* put a figure on it for this library.

## Decision

Check every module of the library under
`{-# OPTIONS --without-K --exact-split --safe #-}`, and the two generated
aggregators under `{-# OPTIONS --without-K --safe #-}`.

+  **Every module, `Legacy/` included**.  `Legacy/` is frozen, but two of its
   modules import `Setoid/` modules, so it could not keep `--cubical-compatible`;
   nor, once the standard library is 3.0, could any other subtree, since every
   subtree imports the standard library.
+  **No warning is suppressed for the library as a whole**.
   `-WnoUnsupportedIndexedMatch` leaves `agda-algebras.agda-lib`, since under
   `--without-K` Agda generates no Cubical support code and the warning cannot
   arise.
+  **ADR-003 stands**.  The Cubical target, its promotion criteria and its
   portability discipline are unchanged: definitions are stated in terms of an
   algebra's own equivalence so that a Cubical module can be derived from each by
   substitution.  What changes is the relation between the two trees: a future
   `--cubical` tree derives its modules from these and imports none of them.
+  **The rule is stated where contributors read it**: the `OPTIONS` paragraph of
   `Overture.Basic`, `docs/STYLE_GUIDE.md` § Pragma, and `CONTRIBUTING.md`
   § File pragma.

## Evidence

Unless a figure says otherwise, it comes from a `make check` of the whole
library from an empty `_build` directory, under the flake's Agda 2.8.0 and
standard-library 2.3, with the standard library's interfaces prebuilt in the Nix
store, timed by GNU time.  Runs alternated between the two flags in one sitting,
so that the load other jobs put on the machine (20 cores, 64 GB) fell on both
alike; the load average before each run is the 1-minute figure from `uptime`.

**The probe of [#594]** (2026-10-06, commit `22f67aa5` and the sweep, keeping
`-WnoUnsupportedIndexedMatch`):

| run | flag | load before | wall | peak RSS |
|---|---|---:|---:|---:|
| 1 | `--cubical-compatible` | 1.95 to 1.99 | 85.3 s | 2,095,228 KiB |
| 2 | `--cubical-compatible` | 1.95 to 1.99 | 87.7 s | 2,095,516 KiB |
| 3 | `--without-K` | 1.95 to 1.99 | 74.9 s | 2,713,104 KiB |
| 4 | `--without-K` | 1.95 to 1.99 | 75.6 s | 2,713,168 KiB |

The probe's `_build` held 346 interfaces of 60,581,757 bytes under
`--cubical-compatible` and 54,255,026 under `--without-K` (10.4% less); 326
shrank, 2 kept their size and 18 grew by a few bytes.  The library's share of the
import closure of `Setoid.Varieties.HSP` (92 of its 314 modules) went from
18,110,993 to 15,585,129 bytes (13.9% less).

**This change** (2026-10-07, base `4b4b16db` against the branch of [#594],
which also drops `-WnoUnsupportedIndexedMatch`):

| pair | load before (each flag) | `--cubical-compatible` | `--without-K` | change |
|---|---|---:|---:|---:|
| 1 | 3.42, 3.72 | 125.66 s | 114.29 s | 9.0% less |
| 2 | 3.76, 4.62 | 128.22 s | 107.69 s | 16.0% less |
| 3, with `+RTS -s` | 2.03, 2.16 | 113.16 s | 103.26 s | 8.7% less |
| 4, with `+RTS -S` | 1.83, 3.33 | 115.26 s | 105.96 s | 8.1% less |
| 5 | 1.43, 1.57 | 96.80 s | 85.70 s | 11.5% less |

Peak RSS was 1,788,612 to 1,803,552 KiB in every `--cubical-compatible` run and
2,764,548 to 2,765,360 KiB in every `--without-K` run.  A last run of this
change's final commit, whose sources differ from those measured only in the
prose of three modules, took 84.98 s at a load of 1.07 and peaked at
2,665,964 KiB, about 100 MB lower (see *Peak memory*).

Every run exited 0 with 346 `Checking` lines (344 modules and the two
aggregators) and the same 951 `UserWarning` positions, the library's own
deprecations, and no other warning.  In particular no `UnsupportedIndexedMatch`
appeared, although nothing suppresses it any more.  Over the probe's two pairs
and these five, the wall time fell by 8 to 16%, by 11% on average.

**Interfaces**.  The 346 interfaces came to 60,529,263 bytes under
`--cubical-compatible` and 54,338,653 under `--without-K` (10.2% less), with
the same sizes in every run of each flag.  339 shrank and 7 grew, by 1 to 485
bytes; the largest change is `Setoid.Congruences.ChainJoin`, from 954,341 to
452,264 bytes.  The import closure of `Setoid.Varieties.HSP` (313 modules, from
`agda --dependency-graph`) holds 92 of the library's interfaces, and they went
from 18,110,993 to 15,582,809 bytes (14.0% less), as in the probe.

**Peak memory**.  The peak RSS of a whole run rose, in the probe and here, and
the cause is the garbage collector's schedule, not the flag.  Under `+RTS -s`
the main check (the `Everything` aggregator) allocated 8.9% less under
`--without-K` and spent less time both computing and collecting, while its
maximum residency, which GHC samples only at major collections, rose from
802 MB (20 samples) to 1,283 MB (17 samples).  The log of every collection
(`+RTS -S`) shows nearly the same curve of live data under both flags, except
that one major collection under `--without-K` fell, as the interleaved log
places it, while `Examples.Classical.Groups.AlternatingGroup5.Tables` (the
generated tables of the alternating group A₅) was being checked, and found
1,283 MB live, against 654 MB and 760 MB at the collections on either side of
it.
Checked alone, with a heap census every 0.05 s (`+RTS -hT -i0.05`), that module
peaks at 1,213 MB of live data under `--cubical-compatible` (281 samples) and
1,198 MB under `--without-K` (251 samples).  GHC's copying collector sizes the
heap from the largest live set it has seen, so a whole run's peak RSS depends on
whether a major collection happens to land on that module's peak, under either
flag.  The final commit's run is a control of that reading: prose alone, which
changes no definition, moved the peak by about 100 MB.

## Consequences

+  **Positive**.  Standard-library 3.0 becomes importable, so [#588] can move the
   library to Agda 2.9.0 once 3.0 and Agda 2.9.0 are released.
+  **Positive**.  A whole check is faster and the interfaces are smaller, which
   matters most to an IDE that ships them to a browser.
+  **Negative**.  A module checked under `--cubical` cannot import this library.
   A future `src/Cubical/` tree under `--cubical` may import modules checked under
   `--cubical` or `--cubical-compatible`, such as agda/cubical's, and none of
   `Overture/`, `Setoid/`, `Classical/` or the rest; it derives what it needs from
   them by substitution, which is how ADR-003 planned it.  The move to 3.0 would
   have forced this firewall in any event.
+  **Negative**.  A library checked under `--cubical-compatible` can no longer
   import this one; it must move to `--without-K` too, as it would have to in
   order to import standard-library 3.0.
+  **Neutral**.  A whole run's peak RSS rose, from 1.7 GiB to 2.6 GiB here and
   from 2.0 GiB to 2.6 GiB in the probe.  *Evidence* traces it to where the
   garbage collector's major collections fall: the largest live set, in the
   generated A₅ tables, is about 1.2 GB under both flags.
+  **Neutral**.  `UnsupportedIndexedMatch` no longer arises, and its suppression
   is gone.  The matches it reported were never errors; they were definitions
   whose Cubical support code Agda could not generate.
+  **Neutral**.  Ten modules and ADR-002 said that `Fin`-indexed tuples "lack η
   under `--cubical-compatible`", or that function or propositional
   extensionality is "unavailable under `--safe --cubical-compatible`".  Both are
   true under either flag: Agda's definitional equality has no η-rule for
   functions on a datatype, and extensionality cannot be proved outside Cubical
   mode or postulated under `--safe`.  The sentences now name that cause.  No
   statement or proof depended on the flag.

## Alternatives considered

+  **Keep `--cubical-compatible` and stay on standard-library 2.x**, patched for
   each new Agda.  Rejected: no released 2.x checks under the next Agda, the
   fixes live only on agda-stdlib's development branch, and [#588] rules out a
   patched standard library as this library's pin.  It would also keep paying for
   a consumer that does not exist.
+  **Both flags, by subtree**: `--without-K` where a subtree imports
   standard-library 3.0, `--cubical-compatible` elsewhere.  Rejected because
   coinfectivity forbids it: a `--cubical-compatible` subtree cannot import a
   `--without-K` one, `Legacy/` imports `Setoid/`, and every subtree imports the
   standard library, so under 3.0 every subtree would have to be `--without-K`
   anyway.
+  **Wait for a `--cubical-compatible` edition of standard-library 3.x**.
   Rejected: [agda/agda-stdlib#2967] merged without one, for want of a use case.

## References

+  Issue [#594]: the switch, with the probe's measurements.
+  Issue [#279]: the flag strategy and the import firewall.
+  Issue [#250]: the move to `--cubical-compatible`, April 2026.
+  Issue [#586]: Agda 2.9.0 and the standard libraries; its findings comment has
   the `CoInfectiveImport` runs (row 4).
+  Issue [#588]: the move to Agda 2.9.0 and standard-library 3.0.
+  Issue [#270]: M5-1, the Cubical proof of concept.
+  Pull request [agda/agda-stdlib#2967]: standard-library 3.0 restores
   `--without-K`.
+  Agda's manual: [Without K], [Cubical compatible], and the
   [checking options for consistency].
+  [ADR-003](003-cubical-canonical-target.md), which this record qualifies, and
   [ADR-002](002-classical-layer-design.md), whose η-gap sentences are corrected
   with it.

[#250]: https://github.com/ualib/agda-algebras/issues/250
[#270]: https://github.com/ualib/agda-algebras/issues/270
[#279]: https://github.com/ualib/agda-algebras/issues/279
[#586]: https://github.com/ualib/agda-algebras/issues/586
[#588]: https://github.com/ualib/agda-algebras/issues/588
[#594]: https://github.com/ualib/agda-algebras/issues/594
[agda/agda-stdlib#2967]: https://github.com/agda/agda-stdlib/pull/2967
[Without K]: https://agda.readthedocs.io/en/v2.8.0/language/without-k.html
[Cubical compatible]: https://agda.readthedocs.io/en/v2.8.0/language/cubical-compatible.html
[checking options for consistency]: https://agda.readthedocs.io/en/v2.8.0/tools/command-line-options.html#checking-options-for-consistency
