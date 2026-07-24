#############################################################################
##
##  scripts/gap/flrp/bin/scan_transitive.g   (issue #487, deliverable 4)
##
##  The degree-by-degree transitive scan for library L7 (with #484).  For each
##  TransitiveGroup(degree, k) the point stabilizer H has index `degree`, and
##  the interval [H, G] is the congruence lattice of that transitive G-set.  By
##  the manuscript's § 5 transitivity theorem, a minimal representation of
##  library L7 (a seven-element lattice) must be a transitive G-set, so testing
##  [H, G] ≅ L7 over all transitive groups of a degree settles existence of a
##  minimal representation of that size.
##
##  The scan collects, as a cheap GAP-side prescreen, every interval whose
##  element count equals |L7| = 7; the Python post-processor `gap_search.py`
##  confirms isomorphism against L7 on those survivors.  The verdict for
##  degree 8 MUST be negative: the committed Eq(8) closure sweep already
##  excludes every 8-point algebra (docs/notes/flrp-l7-eq6.md § 5), so
##  agreement cross-validates both engines.
##
##  Degrees of prime order are skipped elsewhere as free negatives (transitive
##  ⇒ primitive ⇒ two-element interval); degree 8 is composite, a genuine scan.
##
##  Run from the repo root inside `nix develop .#gap` (degree defaults to 8):
##      gap -A -q -b scripts/gap/flrp/bin/scan_transitive.g
##      gap -A -q -c 'FLRP_DEGREE := 9;;' -b scripts/gap/flrp/bin/scan_transitive.g
##  then confirm and commit the verdict:
##      python3 scripts/python/flrp/gap_search.py \
##          scripts/gap/flrp/out/l7_transitive_deg8.raw.json \
##          --target scripts/python/flrp/inputs/l7_lattice.json \
##          --out scripts/gap/flrp/out/l7_transitive_deg8.search.json --date 2026-07-24
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");
Read("scripts/gap/flrp/lib/interval.g");
Read("scripts/gap/flrp/lib/search.g");

degree := 8;;
if IsBoundGlobal("FLRP_DEGREE") then
  degree := ValueGlobal("FLRP_DEGREE");
fi;

targetName := "L7";;
targetSize := 7;;      # library L7 has seven elements

Print("scanning TransitiveGroup(", degree, ", *) by point stabilizer for [H,G] of size ",
      targetSize, " ...\n");
report := FLRP_ScanTransitive(degree, targetSize);;

out := rec(
  format := "flrp-gap-search-raw v1",
  engine := FLRP_Provenance(),
  config := rec( mode := "transitive-point-stabilizer",
                 degree := degree,
                 target := targetName,
                 targetSize := targetSize ),
  scanned := rec( groups := report.groupsScanned ),
  sizeHistogram := report.sizeHistogram,
  candidates := report.candidates );;

path := Concatenation("scripts/gap/flrp/out/l7_transitive_deg", String(degree), ".raw.json");;
JSON_WriteFile(path, out);

Print("\ndegree ", degree, ": scanned ", report.groupsScanned, " transitive groups\n");
Print("interval-size histogram: ", JSON_ToString(report.sizeHistogram), "\n");
Print("size-", targetSize, " candidates (to confirm vs ", targetName, "): ",
      Length(report.candidates), "\n");
Print("wrote raw search report: ", path, "\n");
QUIT_GAP(0);
