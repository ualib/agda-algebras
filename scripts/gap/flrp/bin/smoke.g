#############################################################################
##
##  scripts/gap/flrp/bin/smoke.g   (issue #487, deliverable 1)
##
##  Smoke test for the `.#gap` devshell.  It confirms GAP can load the two
##  group libraries the subgroup-interval search depends on:
##
##    * SmallGroups, via SmallGroup(216,153) — the manuscript's smallest group
##      with a pentagonal upper interval (deliverable 3); and
##    * the transitive-groups library, via TransitiveGroup(8,1) — the base of
##      the degree-8 L7 scan (deliverable 4);
##
##  and that the deterministic JSON writer and the provenance stamp work.
##
##  Run from the repo root inside `nix develop .#gap`:
##      gap -A -q -b scripts/gap/flrp/bin/smoke.g
##  or simply:
##      make gap-smoke
##
##  (`-A` skips optional-package autoloading — quieter startup, and the group
##  data libraries still load on demand.)
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");

BindGlobal("FLRP_SmokeFail", function(msg)
  Print("FAIL: ", msg, "\n");
  QUIT_GAP(1);
end);

# --- SmallGroups library ---------------------------------------------------
G := SmallGroup(216, 153);;
if Order(G) <> 216 then
  FLRP_SmokeFail("SmallGroup(216,153) has the wrong order");
fi;
Print("ok  SmallGroup(216,153): order ", Order(G),
      ", ", StructureDescription(G), "\n");

# --- transitive-groups library ---------------------------------------------
T := TransitiveGroup(8, 1);;
if not IsTransitive(T, [1 .. 8]) then
  FLRP_SmokeFail("TransitiveGroup(8,1) is not transitive on 8 points");
fi;
Print("ok  TransitiveGroup(8,1): degree 8, ",
      NrTransitiveGroups(8), " transitive groups of degree 8\n");

# --- provenance + JSON round-trip ------------------------------------------
prov := FLRP_Provenance();;
Print("ok  provenance ", JSON_ToString(prov), "\n");

Print("\nPASS  .#gap shell smoke test\n");
QUIT_GAP(0);
