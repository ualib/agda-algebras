#############################################################################
##
##  scripts/gap/flrp/bin/demo_tg9x4.g   (issue #487, deliverable 6)
##
##  The end-to-end group→certificate demonstrator.  The manuscript's Figure 10
##  exhibits the four-element Boolean lattice 2×2 as the upper interval
##  [C2, C3×S3], the smallest-index congruence lattice of a transitive G-set in
##  its Eq(10) figure; C3×S3 is TransitiveGroup(9,4), and the interval is the
##  overgroup lattice of a point stabilizer H (index 9).  Nine cosets sit
##  comfortably within the emitter's Fin-literal cap, so this interval takes
##  the direct-certificate route: the coset action becomes a unary algebra, the
##  Python bridge emits a claim file, and `emit_agda.py` renders a module whose
##  type-checking re-verifies Con(coset algebra) ≅ 2×2 as a Representableᵈ
##  witness — a found interval carried all the way into Agda.
##
##  Run from the repo root inside `nix develop .#gap`:
##      gap -A -q -b scripts/gap/flrp/bin/demo_tg9x4.g
##  then the bridge emits the canonical artifact and the claim:
##      python3 scripts/python/flrp/gap_interval.py \
##          scripts/gap/flrp/out/tg9x4_two_by_two.raw.json \
##          --target scripts/gap/flrp/inputs/two_by_two.json \
##          --out scripts/gap/flrp/out/tg9x4_two_by_two.interval.json \
##          --emit-claim scripts/python/flrp/inputs/tg9x4_two_by_two.json \
##          --name TG9x4TwoByTwo --module FLRP.Certificates.Group \
##          --date 2026-07-24
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");
Read("scripts/gap/flrp/lib/interval.g");
Read("scripts/gap/flrp/lib/cosets.g");

BindGlobal("FLRP_Fail", function(msg)
  Print("FAIL: ", msg, "\n");
  QUIT_GAP(1);
end);

G := TransitiveGroup(9, 4);;
source := rec( source := "TransitiveGroup", id := [ 9, 4 ] );;

# The point stabilizer of the natural degree-9 action; its overgroup lattice
# is the interval [H, G] of the transitive G-set.
H := Stabilizer(G, 1);;
if Index(G, H) <> 9 then
  FLRP_Fail("point stabilizer does not have index 9");
fi;

record := FLRP_IntervalRecord(source, G, H);;
record.cosetAction := FLRP_CosetAction(G, H);;

rawPath := "scripts/gap/flrp/out/tg9x4_two_by_two.raw.json";;
JSON_WriteFile(rawPath, record);

Print("\nwrote raw interval artifact: ", rawPath, "\n");
Print("  group ", record.group.structureDescription,
      " (TransitiveGroup(9,4)),  |G| = ", record.group.order, "\n");
Print("  interval covers (0 = H .. ", record.interval.size - 1, " = G): ",
      record.interval.covers, "\n");
Print("  [G:H] = ", record.subgroup.index,
      ",  interval size = ", record.interval.size,
      ",  coset points = ", record.cosetAction.points,
      ",  directCertifiable = ", record.cosetAction.directCertifiable, "\n");
QUIT_GAP(0);
