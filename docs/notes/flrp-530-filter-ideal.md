# Snow's filter-ideal lemma, and the L16 witness in Sub(A5)

Design note for issue #530 (M6-26).  Records what was formalized, the shape
of the concrete `L16` configuration, and — in § 4 — a type-checking
obstruction that blocks the last step of the `L16` application, with the
measurements that localize it.

## 1.  The lemma

`FLRP.Closure.FilterIdeal` formalizes the union-of-a-filter-and-an-ideal
closure lemma (Snow, *Algebra Universalis* 43 (2000)) in the direct form the
manuscript proves it (`docs/papers/fin-lat-rep/SmallLatticeReps.tex`
§ "Union of a filter and ideal", `lemma:union-filter-ideal`):

> Let `X` be a finite set.  If `L ≤ Eq(X)` is representable and `L₀ ≤ L` is a
> sublattice with universe `α↑ ∪ β↓`, then `L₀` is representable.

The formalization is at **Layer D** of the two-layer congruence discipline
(ADR-008): decidable congruences in place of subsets of `Eq(X)`.  Rather than
manipulating the function monoid `λ(L₀)`, which is never needed and could not
be enumerated, the ambient lattice is presented as the congruence lattice of
an algebra `𝑨`, and the representing algebra of `L₀` is the **extension** `𝑩`
of `𝑨` by one unary operation `h(a , b , u)` per triple of carrier elements:
the manuscript's two-valued map when `(a , b)` is an `α`-pair, the identity
otherwise, so the symbol family is total.  Both halves of the manuscript
proof survive verbatim:

+  every `h(a , b , u)` respects every congruence in the union
   (`hMap-compat`, the formal reading of `h ∈ λ(L₀)`), so each member of the
   union remains a congruence of `𝑩` (`liftᵈ`);
+  a decidable congruence of `𝑩` lying outside both the filter and the ideal
   is impossible (`h-violation`): the witness extraction `⊈ᵈ-witness` of
   `FLRP.Representable` supplies the pairs `(a , b) ∈ α ∖ θ` and
   `(u , v) ∈ θ ∖ β` constructively, and compatibility of the congruence with
   its *own* `h` operation at `(u , v)` is the contradiction.

Deciding the two containments then yields `snow`: every decidable congruence
of `𝑩` lies in `α↑ ∪ β↓`.  The `Assembly` submodule turns a closed finite
family presenting the union into `ConIsoᵈ 𝑩 𝑳₀` and a `Representableᵈ`
witness.  Everything type-checks under `--cubical-compatible --exact-split
--safe`, **with no postulate and no registry assumption** — in particular
without the Kurzweil–Netter duality of Entry 2 (`FLRP.Assumptions`), which
the duality route of #529 would have needed.

The order-theoretic half — `α↑ ∪ β↓` is always a sublattice — is
`Classical.Structures.Lattice.FilterIdeal`, one line in each direction.

## 2.  Why the ambient is closed without #501

The lemma needs `L = Con ⟨X , λ(L)⟩`.  In general that is the unary-reduction
theorem (#501, open), but both intended instances avoid it: the ambient is
`Sub(G)` presented as the coset partitions of `X = G`, and
`Con ⟨G , translations⟩ ≅ Sub(G)` is the WP-3 bridge (#454) at `H = 1`.

`Classical.Structures.Group.RegularAction` states that instance in the
`Classical/` tree (which cannot import `FLRP/`), where it simplifies: "above
the trivial subgroup" is no constraint, so the interval apparatus of
`FLRP.Enforceable` is not needed and the statements are about plain
`Subgroup`s and `DecSubgroup`s.  `cosetCon-Kθ` is the closedness fact —
every congruence of the regular action *is* the coset partition of its
`ε`-class.

Note the convention: the module uses **left** translations and **left**
cosets throughout.  `docs/GITHUB_PROJECT.md` (issue M6-26's rationale) says
"right translations"; that phrasing does not match the library, and the
statement is true either way, so the text there should be corrected rather
than the code.

## 3.  The L16 configuration

Found by `scripts/gap/flrp/bin/find_filter_ideal.g` (new here; it generalizes
the ad-hoc probe behind `bin/filter_ideal_216.g`), which scans groups of
order at most 100 for an interval `[H , G]` of prescribed antichain shape
together with a `K` of prescribed order lying below no middle, meeting each
middle trivially, and joining each to `G`.  The **only** configuration in
range is `A5`:

```text
G = A5  (SmallGroup(60,5)),  H = C3  (index 20),  K = C5
[C3 , A5]  =  { C3 , S3 , A4 , A4′ , A5 }  ≅  M3
L16        ≅  [C3 , A5] ∪ [1 , C5]        inside Sub(A5)
```

The committed artifact is `scripts/gap/flrp/out/l16_filter_ideal_a5.json`
(format `flrp-gap-filter-ideal v1`).  The ambient set has size **60**, not
the 180 of the printed entry — this is candidate erratum E2 of
`docs/notes/flrp-slr-census.md`, and the filter-ideal route settles it.

`scripts/python/flrp/filter_ideal_certs.py` rebuilds the same configuration
independently (permutations, not GAP), asserts the group axioms, the
three-middles fact, maximality of the middles, and agreement of the subgroup
order with the meet and join tables of `inputs/slr/slr16_lattice.json`, and
emits `FLRP.Certificates.FilterIdeal.A5Data` — the tables, the seven
characteristic vectors, and escalation word certificates for both interval
families.

`FLRP.Certificates.FilterIdeal.L16SubA5` then **re-verifies all of it in
Agda by decision**: that the tables form a group (associativity via the
faithful action of `Classical.Structures.Group.TableGroup`, not the 216 000-case
cubic sweep), that the seven vectors cut out subgroups, that the escalation
certificates are well-formed, that the `L16` Cayley tables satisfy the
lattice laws, and — the substantive claim — that containment among the seven
subgroups matches the meet order of those tables in both directions
(`ord-table`).

## 4.  The obstruction, and what it rules out

The final gluing step — handing that family to
`FilterIdealClosure.Assembly` — is not yet in the library.  It is blocked by
an Agda elaboration blowup, not by missing mathematics.  Measurements, all on
the `A5` instance under `agda +RTS -M6G -A128M`:

| what is checked | cost |
|---|---|
| the whole verified prefix (group, subgroups, escalation certificates, lattice laws, `ord-table`) | **9 s** |
| `ord-table`, i.e. all 49 subgroup containments decided | ~3 s of that |
| one `cosetCon-reflect (proj₁ (S k)) (proj₁ (S l))` at abstract `k , l` | **> 32 GB heap** |
| one congruence containment `γ k ⊆ᵈ γ l` at concrete `k , l` | **> 32 GB heap** |

So no decision procedure is at fault; the cost is in elaborating an
application of a coset-congruence lemma at this carrier size.  Four things
were tried, and the negative results are the useful part.

1.  **`abstract` is not a fix inside the defining module.**  Its definitions
    remain transparent there, so sealing the group-law witnesses in the same
    module that uses them changed nothing.  Sealing across a module boundary
    (or with `opaque`, which is by-name) does work, and is why
    `RegularAction` and `TableGroup` now seal their subgroup axioms,
    congruence proofs, and round trips.  That removed several layers of the
    blowup, but not the last one.

2.  **A `from-yes` is far cheaper to *state* than to *apply*.**  Checking the
    definition needs only enough reduction to see the decision says `yes`;
    applying the result forces the proof term, which here reaches the
    subgroup axioms and thence the group bundle, whose own law witnesses are
    decision sweeps over the carrier.  A decision that costs milliseconds at
    its definition can be ruinous one line later.

3.  **Module applications at concrete arguments are not free.**  Naming the
    coset relation as `Coset._∼_ 𝒢 K K-sg` re-instantiates `Coset` — and
    `Algebra.Properties.Group` with it — once per concrete subgroup.  Writing
    the relation out directly and consuming the `Coset` lemmas once,
    generically, inside an opaque block is strictly better and is what the
    module now does.

4.  **Pattern-matching a Σ argument blocks reduction where laziness was
    wanted.**  `cosetConᵈ (K , K?) = …` forces its argument open; reading
    the components with `proj₁`/`proj₂` instead lets `cosetConᵈ K` reduce
    while `K` stays stuck, which is the difference between a goal that
    normalizes a concrete subgroup and one that does not.

A retry should probably not push harder on opacity.  The more promising
direction is to keep the ambient algebra away from the group bundle
altogether — build the regular action directly as a unary algebra from the
multiplication table (`tablesToUnaryAlgebra`, which is known cheap at this
size from the WP-6 pilot) and carry the subgroup correspondence as *data*
about that algebra rather than as lemmas about a `Group` value.  The Snow
lemma itself is indifferent to how the ambient arrives.

## 5.  Status against the issue's acceptance criteria

+  *"The lemma type-checks under `--cubical-compatible --exact-split --safe`
   with no postulates and no registry assumption."*  **Met**
   (`FLRP.Closure.FilterIdeal`).
+  *"`L11` and `L16` are `Representableᵈ` in the library without Entry 2, and
   the census records them as certified by the filter-ideal route."*  **Not
   met.**  For `L16` every ingredient is built and machine-verified, and the
   remaining step is the mechanical assembly blocked by § 4.  `L11` (carrier
   216) was not attempted: it is the same construction at nearly four times
   the carrier, so it is gated on the same fix.

The census entries for `L11` and `L16` therefore stay parked, with their
`PARKED` text in `scripts/python/flrp/slr_catalog.py` updated to name the
filter-ideal route and this note.
