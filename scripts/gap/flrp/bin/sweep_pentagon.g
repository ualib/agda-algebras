#############################################################################
##
##  scripts/gap/flrp/bin/sweep_pentagon.g   (issue #487, deliverable 3, full)
##
##  The pentagon minimality sweep: verify that no group of order below 216 has
##  a pentagonal (N5) upper interval [H, G], so that SmallGroup(216,153) — whose
##  pentagon interval bin/pentagon216.g reproduces — is a group of minimal
##  order with that property (the manuscript's TODO-appendix claim).
##
##  For a minimal-order witness H may be taken core-free (if Core_G(H) = N ≠ 1
##  then [H/N, G/N] ≅ N5 lives in the smaller quotient G/N), so the sweep only
##  enumerates core-free subgroup classes — correct for the minimality claim and
##  a strong prune.  A cheap GAP-side prescreen keeps a size-5 interval only
##  when it has five covers and an interior cover (which excludes the chain, M3,
##  and the graded five-element lattices); the Python confirmation
##  `gap_search.py` decides N5 among the survivors — no false positive can slip
##  through, since the isomorphism test is authoritative.
##
##  Run from the repo root inside `nix develop .#gap` (minutes; run in the
##  background, logs to a scratchpad):
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
totalGroups := 0;;
t0 := Runtime();;

for o in [1 .. maxOrder] do
  n := NumberSmallGroups(o);
  if n > idCap then
    Add(skipped, rec( order := o, count := n ));
    continue;
  fi;
  for id in [1 .. n] do
    totalGroups := totalGroups + 1;
    G := SmallGroup(o, id);
    for c in ConjugacyClassesSubgroups(G) do
      H := Representative(c);
      if H = G then
        continue;
      fi;
      if Order(Core(G, H)) <> 1 then
        continue;                        # core-free only (WLOG for minimality)
      fi;
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
  Print("order ", o, " (", n, " groups): cumulative ", totalGroups,
        " groups, ", Length(cands), " N5-plausible, ",
        Int((Runtime() - t0) / 1000), "s\n");
od;

out := rec(
  format := "flrp-gap-search-raw v1",
  engine := FLRP_Provenance(),
  config := rec( mode := "smallgroups-minimality",
                 maxOrder := maxOrder,
                 target := "N5",
                 targetSize := 5,
                 coreFree := true ),
  scanned := rec( groups := totalGroups ),
  sizeHistogram := hist,
  skippedOrders := skipped,
  candidates := cands );;

path := "scripts/gap/flrp/out/pentagon_minimality.raw.json";;
JSON_WriteFile(path, out);

Print("\nscanned ", totalGroups, " groups (orders 1..", maxOrder, "); ",
      Length(cands), " N5-plausible size-5 intervals to confirm; ",
      Int((Runtime() - t0) / 1000), "s\n");
Print("wrote raw sweep report: ", path, "\n");
QUIT_GAP(0);
