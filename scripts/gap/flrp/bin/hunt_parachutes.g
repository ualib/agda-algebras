#############################################################################
##
##  scripts/gap/flrp/bin/hunt_parachutes.g   (issue #460, RP-3)
##
##  The RP-3 parachute realizability sweep: hunt the four smallest parachutes
##  with two big canopies -- P(3,3) at six elements; P(3,3,2), P(3,4), and
##  P(3,2x2) at seven -- as core-free upper intervals [H, G] over the
##  SmallGroups library.  A hit is a positive instance of the note's
##  statement (C) for the corresponding family of cf-IE classes (and kills
##  "this parachute is not group representable" as a cheap negative-FLRP
##  shortcut); an exhausted slice is a recorded lower bound, never a
##  non-representability claim.
##
##  The pentagon sweep's two bounding facts apply verbatim, because every
##  parachute with a canopy of more than two elements contains N5 (the
##  pentagon bottom, an atom of another canopy, and a big canopy's chain
##  atom < interior < top):
##
##    1. In any parachute with at least two canopies, two coatoms drawn from
##       different canopies meet at the bottom, so H is an intersection of
##       two maximal subgroups of G; enumerating pairwise intersections of
##       maximal subgroups is therefore a complete bottom enumeration.
##    2. No p-group has such an upper interval: two maximal subgroups of a
##       p-group contain the Frattini subgroup, so [H, G] embeds in the
##       modular lattice Sub(G/Phi(G)), and the target contains N5.
##
##  For a minimal-order witness H may be taken core-free (else pass to
##  [H/N, G/N] in the smaller quotient), so only core-free H are kept.
##  Cheap GAP-side gates (element count 6 or 7, two or three atoms, an
##  interior cover) keep the candidate lists small; gap_search.py decides
##  each isomorphism type authoritatively.
##
##  Run from the repo root inside `nix develop .#gap`:
##      gap -A -q -b scripts/gap/flrp/bin/hunt_parachutes.g
##  then confirm and commit one verdict per target:
##      python3 scripts/python/flrp/gap_search.py \
##          scripts/gap/flrp/out/rp3_parachutes_s6.raw.json \
##          --target scripts/gap/flrp/inputs/p33.json \
##          --out scripts/gap/flrp/out/rp3_p33.search.json --date 2026-08-29
##      # and rp3_parachutes_s7.raw.json against p332.json, p34.json,
##      # p3m2.json, writing rp3_p332 / rp3_p34 / rp3_p3m2 .search.json.
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");
Read("scripts/gap/flrp/lib/interval.g");

maxOrder := 300;;
if IsBoundGlobal("FLRP_MAXORDER") then
  maxOrder := ValueGlobal("FLRP_MAXORDER");
fi;
idCap := 3000;;      # skips order 256 (56092 groups) inside 1..300; recorded

##  The number of atoms of the interval poset (covers whose lower end is the
##  bottom); the four targets have two or three.
FLRP_AtomCount := function(interval)
  local e, n;
  n := 0;
  for e in interval.covers do
    if e[1] = 0 then
      n := n + 1;
    fi;
  od;
  return n;
end;;

cands6 := [];;
cands7 := [];;
hist := rec();;
skipped := [];;
scanned := 0;;
pSkipped := 0;;
t0 := Runtime();;

for o in [2 .. maxOrder] do
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
    # conjugacy class (conjugate H give isomorphic intervals).
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
      if poset.size in [6, 7] and FLRP_AtomCount(poset) in [2, 3]
         and FLRP_HasInteriorCover(poset) then
        if poset.size = 6 then
          Add(cands6, FLRP_IntervalRecord(
            rec( source := "SmallGroup", id := [ o, id ] ), G, H));
        else
          Add(cands7, FLRP_IntervalRecord(
            rec( source := "SmallGroup", id := [ o, id ] ), G, H));
        fi;
      fi;
    od;
  od;
od;

mkReport := function(targetNote, targetSize, cands)
  return rec(
    format := "flrp-gap-search-raw v1",
    engine := FLRP_Provenance(),
    config := rec( mode := "rp3-parachute-hunt",
                   maxOrder := maxOrder,
                   target := targetNote,
                   targetSize := targetSize,
                   coreFree := true,
                   method := Concatenation(
                     "maximal-subgroup-pair intersections (complete for ",
                     "parachute bottoms); p-groups skipped (targets contain N5)"),
                   pGroupsSkipped := pSkipped ),
    scanned := rec( groups := scanned, pGroupsSkipped := pSkipped ),
    sizeHistogram := hist,
    skippedOrders := skipped,
    candidates := cands );
end;;

JSON_WriteFile("scripts/gap/flrp/out/rp3_parachutes_s6.raw.json",
               mkReport("P(3,3)", 6, cands6));
JSON_WriteFile("scripts/gap/flrp/out/rp3_parachutes_s7.raw.json",
               mkReport("P(3,3,2) / P(3,4) / P(3,2x2)", 7, cands7));

Print("\nscanned ", scanned, " non-p-groups (orders 2..", maxOrder, "), skipped ",
      pSkipped, " p-groups; ", Length(cands6), " size-6 and ", Length(cands7),
      " size-7 parachute-plausible intervals; ",
      Int((Runtime() - t0) / 1000), "s\n");
Print("wrote raw sweep reports: scripts/gap/flrp/out/rp3_parachutes_s{6,7}.raw.json\n");
QUIT_GAP(0);
