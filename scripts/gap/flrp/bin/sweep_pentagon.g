#############################################################################
##
##  scripts/gap/flrp/bin/sweep_pentagon.g   (issue #487, deliverable 3, full)
##
##  The pentagon minimality sweep: verify that no group of order below 216 has
##  a pentagonal (N5) upper interval [H, G], so that SmallGroup(216,153) — whose
##  pentagon interval bin/pentagon216.g reproduces — is a group of minimal
##  order with that property.
##
##  Two facts make this a fast, bounded search rather than a full subgroup-
##  lattice enumeration (which is intractable on the elementary-abelian slices):
##
##    1. In `[H, G] ≅ N5` the two coatoms β, γ are covered by G, hence maximal
##       in G, and their meet in Sub(G) is the bottom H = β ∩ γ.  So the only
##       candidate bottoms are the pairwise intersections of maximal subgroups;
##       each such H is large, so its interval [H, G] is small and cheap.
##    2. No p-group has an N5 upper interval: β, γ maximal in a p-group contain
##       the Frattini subgroup Φ(G), so H = β ∩ γ ⊇ Φ(G) and [H, G] ⊆ [Φ(G), G]
##       ≅ Sub(G/Φ(G)), a modular subspace lattice — and N5 is not modular.
##       So every p-group is skipped, which removes exactly the orders (128,
##       64, 32, 81, …) whose subgroup lattices are ruinous to enumerate.
##
##  For a minimal-order witness H may be taken core-free (if Core_G(H) = N ≠ 1
##  then [H/N, G/N] ≅ N5 lives in the smaller quotient), so only core-free H are
##  kept.  A cheap GAP-side prescreen keeps a size-5 interval only when it has
##  five covers and an interior cover; `gap_search.py` then decides N5 among the
##  survivors (no false positive slips through — the isomorphism test is
##  authoritative).
##
##  Run from the repo root inside `nix develop .#gap` (a couple of minutes):
##      gap -A -q -b scripts/gap/flrp/bin/sweep_pentagon.g
##  then confirm and commit the verdict:
##      python3 scripts/python/flrp/gap_search.py \
##          scripts/gap/flrp/out/pentagon_minimality.raw.json \
##          --target scripts/python/flrp/inputs/slr/slr01.json \
##          --out scripts/gap/flrp/out/pentagon_minimality.search.json --date 2026-07-24
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");
Read("scripts/gap/flrp/lib/interval.g");

maxOrder := 216;;
if IsBoundGlobal("FLRP_MAXORDER") then
  maxOrder := ValueGlobal("FLRP_MAXORDER");
fi;
idCap := 3000;;      # nothing in 1..216 exceeds this; guards pathological orders

cands := [];;
hist := rec();;
skipped := [];;
scanned := 0;;       # non-p-groups actually searched
pSkipped := 0;;      # p-groups skipped (proven N5-free)
t0 := Runtime();;

for o in [1 .. maxOrder] do
  n := NumberSmallGroups(o);
  if n > idCap then
    Add(skipped, rec( order := o, count := n ));
    continue;
  fi;
  for id in [1 .. n] do
    G := SmallGroup(o, id);
    if IsPGroup(G) then
      pSkipped := pSkipped + 1;
      continue;
    fi;
    scanned := scanned + 1;
    # Candidate bottoms: core-free intersections of maximal pairs, one per
    # conjugacy class (conjugate H give isomorphic intervals, so a single
    # representative suffices and keeps the report free of duplicates).
    maxes := MaximalSubgroups(G);
    Hs := [];
    for i in [1 .. Length(maxes) - 1] do
      for j in [i + 1 .. Length(maxes)] do
        H := Intersection(maxes[i], maxes[j]);
        if Order(Core(G, H)) = 1 and not ForAny(Hs, X -> IsConjugate(G, X, H)) then
          Add(Hs, H);
        fi;
      od;
    od;
    for H in Hs do
      poset := FLRP_IntervalPoset(G, H);
      szkey := String(poset.size);
      if IsBound(hist.(szkey)) then
        hist.(szkey) := hist.(szkey) + 1;
      else
        hist.(szkey) := 1;
      fi;
      if poset.size = 5 and Length(poset.covers) = 5
         and FLRP_HasInteriorCover(poset) then
        Add(cands, FLRP_IntervalRecord(
          rec( source := "SmallGroup", id := [ o, id ] ), G, H));
      fi;
    od;
  od;
  Print("order ", o, ": scanned ", scanned, " non-p-groups (", pSkipped,
        " p-groups skipped), ", Length(cands), " N5-plausible, ",
        Int((Runtime() - t0) / 1000), "s\n");
od;

out := rec(
  format := "flrp-gap-search-raw v1",
  engine := FLRP_Provenance(),
  config := rec( mode := "smallgroups-minimality",
                 maxOrder := maxOrder,
                 target := "N5",
                 targetSize := 5,
                 coreFree := true,
                 method := "maximal-subgroup-pair intersections; p-groups skipped (N5-free)",
                 pGroupsSkipped := pSkipped ),
  scanned := rec( groups := scanned, pGroupsSkipped := pSkipped ),
  sizeHistogram := hist,
  skippedOrders := skipped,
  candidates := cands );;

path := "scripts/gap/flrp/out/pentagon_minimality.raw.json";;
JSON_WriteFile(path, out);

Print("\nscanned ", scanned, " non-p-groups (orders 1..", maxOrder, "), skipped ",
      pSkipped, " p-groups; ", Length(cands), " N5-plausible intervals to confirm; ",
      Int((Runtime() - t0) / 1000), "s\n");
Print("wrote raw sweep report: ", path, "\n");
QUIT_GAP(0);
