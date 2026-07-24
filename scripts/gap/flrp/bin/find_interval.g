#############################################################################
##
##  scripts/gap/flrp/bin/find_interval.g   (issue #487, deliverable 5)
##
##  Find a target-size upper interval [H, G] inside a single, explicitly
##  constructed group G — the manuscript's group-representation entries whose
##  group is not a SmallGroups id (A6, the double cover 2.A6, ...).  Unlike the
##  SmallGroups hunt, the group and the index are known from the manuscript, so
##  this is a parametric driver configured entirely on the command line; it
##  emits a raw search report (with coset actions, for the WP-3 bridge route)
##  that `gap_search.py` confirms against the target lattice.
##
##  Required globals (set with gap's -c):
##      FLRP_G           the group G (a GAP group object)
##      FLRP_SOURCE      rec(source := "...", id := [...])  provenance of G
##      FLRP_TARGETSIZE  the target lattice's element count
##      FLRP_INDEX       [G:H] to restrict to (0 = every subgroup class)
##      FLRP_OUT         output path for the raw search report
##
##  Example (L14 = upper interval in Sub(A6), index 90), from the repo root in
##  `nix develop .#gap`:
##      gap -A -q \
##        -c 'FLRP_G := AlternatingGroup(6);; \
##            FLRP_SOURCE := rec(source := "AlternatingGroup", id := [6]);; \
##            FLRP_TARGETSIZE := 7;;  FLRP_INDEX := 90;; \
##            FLRP_OUT := "scripts/gap/flrp/out/l14_a6.raw.json";;' \
##        -b scripts/gap/flrp/bin/find_interval.g
##      python3 scripts/python/flrp/gap_search.py \
##          scripts/gap/flrp/out/l14_a6.raw.json \
##          --target scripts/python/flrp/inputs/slr/slr14_lattice.json \
##          --out scripts/gap/flrp/out/l14_a6.search.json --date 2026-07-24
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");
Read("scripts/gap/flrp/lib/interval.g");
Read("scripts/gap/flrp/lib/cosets.g");

BindGlobal("FLRP_Need", function(name)
  if not IsBoundGlobal(name) then
    Print("FAIL: required global ", name, " is unset (use gap -c)\n");
    QUIT_GAP(1);
  fi;
end);
for nm in [ "FLRP_G", "FLRP_SOURCE", "FLRP_TARGETSIZE", "FLRP_INDEX", "FLRP_OUT" ] do
  FLRP_Need(nm);
od;

cands := [];;
hist := rec();;
for c in ConjugacyClassesSubgroups(FLRP_G) do
  H := Representative(c);
  if H = FLRP_G then
    continue;
  fi;
  if FLRP_INDEX > 0 and Index(FLRP_G, H) <> FLRP_INDEX then
    continue;
  fi;
  poset := FLRP_IntervalPoset(FLRP_G, H);
  szkey := String(poset.size);
  if IsBound(hist.(szkey)) then
    hist.(szkey) := hist.(szkey) + 1;
  else
    hist.(szkey) := 1;
  fi;
  if poset.size = FLRP_TARGETSIZE then
    record := FLRP_IntervalRecord(FLRP_SOURCE, FLRP_G, H);
    record.cosetAction := FLRP_CosetAction(FLRP_G, H);
    Add(cands, record);
  fi;
od;

out := rec(
  format := "flrp-gap-search-raw v1",
  engine := FLRP_Provenance(),
  config := rec( mode := "single-group-interval",
                 source := FLRP_SOURCE.source,
                 id := FLRP_SOURCE.id,
                 targetSize := FLRP_TARGETSIZE,
                 indexFilter := FLRP_INDEX ),
  scanned := rec( groups := 1 ),
  sizeHistogram := hist,
  candidates := cands );;

JSON_WriteFile(FLRP_OUT, out);
Print("\nfound ", Length(cands), " size-", FLRP_TARGETSIZE, " interval(s); histogram ",
      JSON_ToString(hist), "\n");
Print("wrote raw search report: ", FLRP_OUT, "\n");
QUIT_GAP(0);
