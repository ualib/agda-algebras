#############################################################################
##
##  scripts/gap/flrp/bin/pentagon216.g   (issue #487, deliverable 3)
##
##  Reproduce the SmallLatticeReps manuscript's claim that SmallGroup(216,153)
##  carries a pentagonal (N5) upper interval [H, G] with H of order 6, hence
##  index [G:H] = 36 (§ "Minimal Representations"; the group is the base of the
##  L11 and L20 constructions).  Rather than hard-code the manuscript's
##  conjugacy-class index (which is not stable across GAP/library versions),
##  we locate H robustly: the first class of order-6 subgroups whose interval
##  [H, G] is pentagon-shaped (five elements, five covers, and — unlike M3 or
##  the graded 5-element lattices — an interior cover).  The Python bridge
##  `gap_interval.py` then confirms the interval is N5 up to isomorphism and
##  writes the canonical `flrp-gap-interval v1` artifact.
##
##  Emits the raw interval record (poset + coset action) as JSON; the raw copy
##  is engine output (git-ignored), the committed artifact is the bridge's.
##
##  Run from the repo root inside `nix develop .#gap`:
##      gap -A -q -b scripts/gap/flrp/bin/pentagon216.g
##  then the Python bridge writes the committed canonical artifact:
##      python3 scripts/python/flrp/gap_interval.py \
##          scripts/gap/flrp/out/pentagon_216_153.raw.json \
##          --target scripts/python/flrp/inputs/slr/slr01.json \
##          --out scripts/gap/flrp/out/pentagon_216_153.interval.json \
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

G := SmallGroup(216, 153);;
source := rec( source := "SmallGroup", id := [ 216, 153 ] );;

Print("scanning conjugacy classes of subgroups of SmallGroup(216,153)...\n");
ccsg := ConjugacyClassesSubgroups(G);;

# Order-6 subgroup classes whose interval [H, G] is pentagon-shaped.
cands := [];;
for c in ccsg do
  H := Representative(c);
  if Order(H) = 6 then
    poset := FLRP_IntervalPoset(G, H);
    if poset.size = 5 and Length(poset.covers) = 5
       and FLRP_HasInteriorCover(poset) then
      Add(cands, H);
    fi;
  fi;
od;

Print("order-6 subgroup classes with a pentagon-shaped interval: ",
      Length(cands), "\n");
if Length(cands) = 0 then
  FLRP_Fail("no order-6 pentagon interval found in SmallGroup(216,153)");
fi;

H := cands[1];;
record := FLRP_IntervalRecord(source, G, H);;
record.cosetAction := FLRP_CosetAction(G, H);;
record.selection := rec(
  rule := "first order-6 subgroup class whose upper interval is pentagon-shaped",
  candidateClasses := Length(cands) );;

rawPath := "scripts/gap/flrp/out/pentagon_216_153.raw.json";;
JSON_WriteFile(rawPath, record);

Print("\n");
Print("wrote raw interval artifact: ", rawPath, "\n");
Print("  interval covers (0 = H .. ", record.interval.size - 1, " = G): ",
      record.interval.covers, "\n");
Print("  [G:H] = ", record.subgroup.index,
      ",  |H| = ", record.subgroup.order,
      ",  coreFree = ", record.subgroup.coreFree,
      ",  coset points = ", record.cosetAction.points, "\n");
Print("\nnext: python3 scripts/python/flrp/gap_interval.py ", rawPath, " ...\n");
QUIT_GAP(0);
