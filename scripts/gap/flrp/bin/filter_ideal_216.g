#############################################################################
##
##  scripts/gap/flrp/bin/filter_ideal_216.g   (issue #487, deliverables 3 & 5)
##
##  Reproduce the manuscript's L11 filter-ideal construction in
##  SmallGroup(216,153).  Start from the pentagonal upper interval [H, G] ≅ N5
##  (bin/pentagon216.g); label its three interior subgroups α ≺ β (the
##  comparable pair) and γ (incomparable).  The manuscript observes that Sub(G)
##  is itself a congruence lattice, so if there is a minimal subgroup K with
##  1 ≺ K ≤ G that lies below β but below neither α nor γ, then L11 is the union
##  of the ideal [1, K] and the filter [H, G] — a filter-ideal representation on
##  216 points.  We locate K robustly (the size-6 conjugacy class of order-3
##  subgroups of β, none of which lie in α or γ) rather than by the manuscript's
##  version-specific class index, and emit the group data #485 needs.
##
##  Run from the repo root inside `nix develop .#gap`:
##      gap -A -q -b scripts/gap/flrp/bin/filter_ideal_216.g
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");
Read("scripts/gap/flrp/lib/interval.g");

BindGlobal("FLRP_Fail", function(msg)
  Print("FAIL: ", msg, "\n");
  QUIT_GAP(1);
end);

G := SmallGroup(216, 153);;

# The pentagon subgroup H (order 6), as in bin/pentagon216.g.
H := fail;;
for c in ConjugacyClassesSubgroups(G) do
  if Order(Representative(c)) = 6 then
    if FLRP_IntervalPoset(G, Representative(c)).size = 5
       and FLRP_HasInteriorCover(FLRP_IntervalPoset(G, Representative(c))) then
      H := Representative(c);
      break;
    fi;
  fi;
od;;
if H = fail then FLRP_Fail("no pentagon subgroup H found"); fi;

# Label the interior subgroups: the interior–interior cover is α ≺ β, and the
# remaining interior node is γ.  IntermediateSubgroups indexes 0 = H, 1..3 =
# subgroups, 4 = G.
im := IntermediateSubgroups(G, H);;
top := Length(im.subgroups) + 1;;
icov := First(im.inclusions, e -> e[1] <> 0 and e[2] <> top);;
if icov = fail then FLRP_Fail("no interior cover in the pentagon"); fi;
alphaIdx := icov[1];;  betaIdx := icov[2];;
gammaIdx := First([1 .. Length(im.subgroups)],
                  k -> k <> alphaIdx and k <> betaIdx);;
A := im.subgroups[alphaIdx];;   # α
B := im.subgroups[betaIdx];;    # β
C := im.subgroups[gammaIdx];;   # γ

# K: an order-3 subgroup in the size-6 conjugacy class of subgroups of β,
# lying in neither α nor γ.
K := fail;;
for cl in ConjugacyClassesSubgroups(B) do
  if Order(Representative(cl)) = 3 and Size(cl) = 6 then
    if not IsSubgroup(A, Representative(cl))
       and not IsSubgroup(C, Representative(cl)) then
      K := Representative(cl);
      break;
    fi;
  fi;
od;;
if K = fail then FLRP_Fail("no suitable minimal subgroup K found"); fi;

record := rec(
  format := "flrp-gap-filter-ideal v1",
  engine := FLRP_Provenance(),
  target := "L11",
  group := rec( source := "SmallGroup", id := [ 216, 153 ],
                order := Order(G),
                structureDescription := StructureDescription(G) ),
  filter := rec( name := "[H, G] pentagon (N5)",
                 H := rec( order := Order(H), generators := FLRP_GensString(H) ),
                 alpha := rec( order := Order(A), generators := FLRP_GensString(A) ),
                 beta := rec( order := Order(B), generators := FLRP_GensString(B) ),
                 gamma := rec( order := Order(C), generators := FLRP_GensString(C) ),
                 interval := FLRP_IntervalPoset(G, H) ),
  ideal := rec( name := "[1, K]",
                K := rec( order := Order(K), index := Index(G, K),
                          generators := FLRP_GensString(K) ),
                belowBeta := IsSubgroup(B, K),
                belowAlpha := IsSubgroup(A, K),
                belowGamma := IsSubgroup(C, K) ) );;

path := "scripts/gap/flrp/out/l11_filter_ideal_216_153.json";;
JSON_WriteFile(path, record);

Print("\nL11 filter-ideal in SmallGroup(216,153):\n");
Print("  pentagon |H|=", Order(H), "; α|", Order(A), "| ≺ β|", Order(B),
      "|, γ|", Order(C), "|\n");
Print("  K: order ", Order(K), ", index ", Index(G, K),
      "; below β=", IsSubgroup(B, K), ", below α=", IsSubgroup(A, K),
      ", below γ=", IsSubgroup(C, K), "\n");
Print("  (manuscript expects: order 3, below β only)\n");
Print("wrote committed artifact: ", path, "\n");
QUIT_GAP(0);
