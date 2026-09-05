#############################################################################
##
##  scripts/gap/flrp/bin/find_filter_ideal.g   (issue #530)
##
##  Search for filter-ideal configurations: triples (G, H, K) in which the
##  upper interval [H, G] has a prescribed shape and K is a subgroup meeting
##  the ideal conditions Snow's lemma needs, so that
##
##      [H, G]  ∪  [1, K]        inside Sub(G)
##
##  is a union of a filter and an ideal, hence representable, by
##  lemma:union-filter-ideal of the SmallLatticeReps manuscript, on |G|
##  points.  This generalizes the ad-hoc probe that produced
##  bin/filter_ideal_216.g's L11 configuration.
##
##  The default target is the manuscript's L16: an interval [H, G] with a
##  prescribed number of pairwise incomparable intermediate subgroups (the
##  Mn shape), together with a K of prescribed order that lies in none of
##  the middles, meets each trivially, and joins each to G.  Over all groups
##  of order at most 100 the only configuration is A5 with H ≅ C3 and
##  K ≅ C5, which is what this script emits by default.
##
##  Run from the repo root inside `nix develop .#gap`:
##      gap -A -q -b scripts/gap/flrp/bin/find_filter_ideal.g
##
##  Options (edit the CONFIG record below, or set FLRP_FI_CONFIG first):
##      maxOrder    -- largest group order to scan          (default 100)
##      middles     -- required number of interval middles  (default 3)
##      idealOrder  -- required order of K                  (default 5)
##      target      -- census label recorded in the output  (default "L16")
##      out         -- artifact path
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");
Read("scripts/gap/flrp/lib/interval.g");

BindGlobal("FLRP_Fail", function(msg)
  Print("FAIL: ", msg, "\n");
  QUIT_GAP(1);
end);

if not IsBound(FLRP_FI_CONFIG) then
  FLRP_FI_CONFIG := rec( maxOrder := 100,
                         middles := 3,
                         idealOrder := 5,
                         target := "L16",
                         out := "scripts/gap/flrp/out/l16_filter_ideal_a5.json" );
fi;

#############################################################################
##  The interval test: [H, G] must be Mn: exactly `middles` intermediate
##  subgroups, pairwise incomparable.  IntermediateSubgroups indexes 0 = H
##  and top = G, so an interior-to-interior inclusion would be a comparable
##  pair among the middles.
#############################################################################

BindGlobal("FLRP_IsAntichainInterval", function(G, H, middles)
  local im, top;
  im := IntermediateSubgroups(G, H);
  if Length(im.subgroups) <> middles then return false; fi;
  top := Length(im.subgroups) + 1;
  return ForAll(im.inclusions, e -> e[1] = 0 or e[2] = top);
end);

#############################################################################
##  The ideal test: K meets every middle trivially and joins each to G.
##  (Meeting trivially and joining to G is what makes the union a copy of
##  the target lattice rather than something larger.)
#############################################################################

BindGlobal("FLRP_IsIdealWitness", function(G, mids, K)
  return ForAll(mids, M -> Order(Intersection(M, K)) = 1)
         and ForAll(mids, M -> Order(ClosureGroup(M, K)) = Order(G));
end);

#############################################################################
##  The scan.  For each group of order ≤ maxOrder, for each subgroup class
##  H whose interval is the required antichain shape, look for a K of the
##  required order satisfying the ideal conditions.
#############################################################################

BindGlobal("FLRP_FindFilterIdeal", function(cfg)
  local n, i, G, cls, c, H, im, mids, kcls, kc, K;
  for n in [2 .. cfg.maxOrder] do
    for i in [1 .. NumberSmallGroups(n)] do
      G := SmallGroup(n, i);
      cls := ConjugacyClassesSubgroups(G);
      for c in cls do
        H := Representative(c);
        if Order(H) > 1 and Order(H) < Order(G)
           and FLRP_IsAntichainInterval(G, H, cfg.middles) then
          im := IntermediateSubgroups(G, H);
          mids := im.subgroups;
          for kc in cls do
            K := Representative(kc);
            if Order(K) = cfg.idealOrder
               and ForAll(mids, M -> not IsSubgroup(M, K))
               and FLRP_IsIdealWitness(G, mids, K) then
              return rec( G := G, id := [ n, i ], H := H, mids := mids, K := K );
            fi;
          od;
        fi;
      od;
    od;
    Print("  scanned order ", n, "\n");
  od;
  return fail;
end);

hit := FLRP_FindFilterIdeal(FLRP_FI_CONFIG);;
if hit = fail then FLRP_Fail("no filter-ideal configuration found in range"); fi;

record := rec(
  format := "flrp-gap-filter-ideal v1",
  engine := FLRP_Provenance(),
  target := FLRP_FI_CONFIG.target,
  search := rec( maxOrder := FLRP_FI_CONFIG.maxOrder,
                 middles := FLRP_FI_CONFIG.middles,
                 idealOrder := FLRP_FI_CONFIG.idealOrder ),
  group := rec( source := "SmallGroup", id := hit.id,
                order := Order(hit.G),
                structureDescription := StructureDescription(hit.G) ),
  filter := rec( name := Concatenation("[H, G] antichain M",
                                       String(FLRP_FI_CONFIG.middles)),
                 H := rec( order := Order(hit.H),
                           index := Index(hit.G, hit.H),
                           structureDescription := StructureDescription(hit.H),
                           generators := FLRP_GensString(hit.H) ),
                 middles := List(hit.mids,
                                 M -> rec( order := Order(M),
                                           structureDescription := StructureDescription(M),
                                           generators := FLRP_GensString(M) )),
                 interval := FLRP_IntervalPoset(hit.G, hit.H) ),
  ideal := rec( name := "[1, K]",
                K := rec( order := Order(hit.K),
                          index := Index(hit.G, hit.K),
                          structureDescription := StructureDescription(hit.K),
                          generators := FLRP_GensString(hit.K) ),
                meetsMiddlesTrivially :=
                  ForAll(hit.mids, M -> Order(Intersection(M, hit.K)) = 1),
                joinsMiddlesToTop :=
                  ForAll(hit.mids, M -> Order(ClosureGroup(M, hit.K)) = Order(hit.G)),
                belowNoMiddle :=
                  ForAll(hit.mids, M -> not IsSubgroup(M, hit.K)) ) );;

JSON_WriteFile(FLRP_FI_CONFIG.out, record);

Print("\n", FLRP_FI_CONFIG.target, " filter-ideal configuration:\n");
Print("  G  = SmallGroup(", hit.id[1], ",", hit.id[2], ") = ",
      StructureDescription(hit.G), ", order ", Order(hit.G), "\n");
Print("  H  = ", StructureDescription(hit.H), ", index ", Index(hit.G, hit.H),
      "; interval has ", Length(hit.mids), " incomparable middles\n");
Print("  K  = ", StructureDescription(hit.K), ", order ", Order(hit.K), "\n");
Print("wrote committed artifact: ", FLRP_FI_CONFIG.out, "\n");
QUIT_GAP(0);
