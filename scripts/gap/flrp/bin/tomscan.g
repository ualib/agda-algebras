#############################################################################
##
##  scripts/gap/flrp/bin/tomscan.g   (issue #513; RP-3 sweep companion)
##
##  Hunt a target finite lattice as an upper interval [H, G] across the GAP
##  library of tables of marks (TomLib, 414 tables of almost simple and
##  related groups).  The canonical copy of the scan behind the skill
##  `hunting-lattice-intervals-in-tomlib`; `make gap-tomscan` runs it for the
##  RP-3 parachute targets and summarizes each run with
##  scripts/python/flrp/tomscan_summary.py.
##
##  Run from the agda-algebras repo root inside `nix develop .#gap`:
##
##    gap -A -q \
##      -c 'FLRP_TARGET := [[1,2,3,4,5,6,7],[2,5,7],[3,5,6,7],[4,7],[5,7],[6,7],[7]];;' \
##      -b scripts/gap/flrp/bin/tomscan.g
##
##  FLRP_TARGET lists, for each element k = 1 .. N of the target lattice,
##  the set of elements j with k <= j (1 = bottom, N = top).  The example is
##  the library's L7 (manuscript L10): the 2 x 3 grid with a doubly
##  irreducible complement, numbered as in Examples.Classical.Lattices.L7.
##
##  Optional globals (also set with -c):
##    FLRP_RESOLVE_BOUND  resolve ambiguous cases with |G| <= bound explicitly
##                        through IntermediateSubgroups (default 20000000;
##                        0 skips the resolution pass).
##    FLRP_TABLES         the TomLib names to scan (default: all of them).
##
##  Method.  For a fixed representative H of class i, the number of class-j
##  subgroups containing H is mark(j, i) * |K_j| * |class j| / |G|, so the
##  marks give the size of [H, G] and the classes it meets.  When every
##  multiplicity is one the poset is determined by the marks (the unique
##  class-j member lies in the unique class-k member iff some class-k
##  subgroup contains a class-j subgroup) and the isomorphism test is exact.
##  When a class occurs twice the marks do not determine the poset; such a
##  case survives only if its multiset of up-counts (elements above each
##  member) matches the target's, and it is then recomputed explicitly.
##
#############################################################################

if not IsBoundGlobal("FLRP_TARGET") then
  Print("FAIL: set FLRP_TARGET (list of up-sets, 1 = bottom, N = top) with gap -c\n");
  QUIT_GAP(1);
fi;
if not IsBoundGlobal("FLRP_RESOLVE_BOUND") then
  FLRP_RESOLVE_BOUND := 20000000;
fi;
if LoadPackage("tomlib") <> true then
  Print("FAIL: the tomlib package is not available\n");
  QUIT_GAP(1);
fi;
##  The engine line the summarizer records (the shell banner is not relied on).
Print("engine GAP ", GAPInfo.Version, " tomlib ",
      InstalledPackageVersion("tomlib"), "\n");
if not IsBoundGlobal("FLRP_TABLES") then
  FLRP_TABLES := AllLibTomNames();
fi;

FLRP_N := Length(FLRP_TARGET);;
FLRP_TargetUpProfile := SortedList(List(FLRP_TARGET, Length));;

##  Is the poset given by up-sets `leq` (1 = bottom, N = top) isomorphic to
##  the target?  Backtracking over the elements in target order, each mapped
##  to an unused element with the same up-count and down-count (both are
##  isomorphism invariants) and checked, against every earlier assignment,
##  to preserve and reflect the order.  The brute force over the interior
##  permutations this replaces (M6-21) was fine at seven elements and is
##  12! steps at the fourteen of DDelta(3,3); the two agree on every target
##  (the M6-27 pass re-ran the hexagon scan against the committed record).
FLRP_IsTarget := function(leq)
  local N, downT, downL, invT, invL, cand, assign, used, extend;
  N := FLRP_N;
  if Length(leq) <> N then
    return false;
  fi;
  downT := List([1 .. N], j -> Filtered([1 .. N], i -> j in FLRP_TARGET[i]));
  downL := List([1 .. N], j -> Filtered([1 .. N], i -> j in leq[i]));
  invT := List([1 .. N], i -> [Length(FLRP_TARGET[i]), Length(downT[i])]);
  invL := List([1 .. N], i -> [Length(leq[i]), Length(downL[i])]);
  if SortedList(invT) <> SortedList(invL) then
    return false;
  fi;
  # cand[i]: the elements of leq that target element i may be sent to.
  cand := List([1 .. N], i -> Filtered([1 .. N], k -> invL[k] = invT[i]));
  assign := ListWithIdenticalEntries(N, 0);
  used := BlistList([1 .. N], []);
  # Extend the partial isomorphism on target elements 1 .. i - 1 to i.
  extend := function(i)
    local k, j, ok;
    if i > N then
      return true;
    fi;
    for k in cand[i] do
      if not used[k] then
        ok := true;
        for j in [1 .. i - 1] do
          if (j in FLRP_TARGET[i]) <> (assign[j] in leq[k])
             or (i in FLRP_TARGET[j]) <> (k in leq[assign[j]]) then
            ok := false;
            break;
          fi;
        od;
        if ok then
          assign[i] := k;
          used[k] := true;
          if extend(i + 1) then
            return true;
          fi;
          used[k] := false;
          assign[i] := 0;
        fi;
      fi;
    od;
    return false;
  end;
  return extend(1);
end;;

##  1-based up-sets from Hulpke's 0-based cover list (0 = H, size - 1 = G).
FLRP_LeqFromCovers := function(size, covers)
  local leq, e, changed, i, j, k;
  leq := List([1 .. size], i -> [i]);
  for e in covers do
    AddSet(leq[e[1] + 1], e[2] + 1);
  od;
  changed := true;
  while changed do
    changed := false;
    for i in [1 .. size] do
      for j in ShallowCopy(leq[i]) do
        for k in leq[j] do
          if not k in leq[i] then
            AddSet(leq[i], k);
            changed := true;
          fi;
        od;
      od;
    od;
  od;
  return leq;
end;;

##  Recompute [H, G] explicitly for class `class` of table `name` and test it.
FLRP_VerifyTomInterval := function(name, class)
  local tom, G, H, t, r, size, leq, ok;
  tom := TableOfMarks(name);
  G := UnderlyingGroup(tom);
  H := RepresentativeTom(tom, class);
  t := Runtime();
  r := IntermediateSubgroups(G, H);
  size := Length(r.subgroups) + 2;
  leq := FLRP_LeqFromCovers(size, r.inclusions);
  ok := size = FLRP_N and FLRP_IsTarget(leq);
  Print("EXPLICIT ", name, " class ", class, ": |G| = ", Size(G), " |H| = ", Size(H),
        " (", StructureDescription(H), ") index ", Index(G, H),
        " core-free ", Size(Core(G, H)) = 1, "; interval size ", size,
        " orders ", List(r.subgroups, Size), " covers ", r.inclusions,
        "; target: ", ok, " (", Runtime() - t, " ms)\n");
  return ok;
end;;

hits := [];;
surv := [];;
nsize := 0;;
ntables := 0;;
for name in FLRP_TABLES do
  tom := TableOfMarks(name);
  if tom = fail then
    Print("skip ", name, "\n");
    continue;
  fi;
  ntables := ntables + 1;
  ords := OrdersTom(tom);
  n := Length(ords);
  lens := LengthsTom(tom);
  subs := SubsTom(tom);
  marks := MarksTom(tom);
  sizeG := ords[n];
  # m[i]: the pairs [j, multiplicity] of overgroup classes of a fixed class-i subgroup
  m := List([1 .. n], i -> []);
  for j in [1 .. n] do
    for k in [1 .. Length(subs[j])] do
      i := subs[j][k];
      mult := marks[j][k] * ords[j] * lens[j] / sizeG;
      if mult > 0 then
        Add(m[i], [j, mult]);
      fi;
    od;
  od;
  for i in [1 .. n - 1] do
    if Sum(List(m[i], x -> x[2])) <> FLRP_N then
      continue;
    fi;
    nsize := nsize + 1;
    over := List(m[i], x -> x[1]);
    up := [];
    for x in m[i] do
      cnt := Sum(List(over, k -> ContainingTom(tom, x[1], k)));
      for c in [1 .. x[2]] do
        Add(up, cnt);
      od;
    od;
    Sort(up);
    if up <> FLRP_TargetUpProfile then
      continue;
    fi;
    if ForAll(m[i], x -> x[2] = 1) then
      SortBy(over, j -> ords[j]);
      leq := List(over, j -> Filtered([1 .. FLRP_N], t -> ContainingTom(tom, j, over[t]) > 0));
      if FLRP_IsTarget(leq) then
        Add(hits, rec(name := name, class := i, sizeG := sizeG, ordH := ords[i]));
        Print("HIT ", name, " |G|=", sizeG, " class ", i, " |H|=", ords[i],
              " index ", sizeG / ords[i], " interval orders ", List(over, j -> ords[j]), "\n");
      fi;
    else
      Add(surv, rec(name := name, class := i, sizeG := sizeG, ordH := ords[i]));
      Print("AMBIGUOUS ", name, " |G|=", sizeG, " class ", i, " |H|=", ords[i],
            " index ", sizeG / ords[i], " multiplicities ", m[i], "\n");
    fi;
  od;
od;
Print("scanned ", ntables, " tables; size-", FLRP_N, " upper intervals: ", nsize,
      "; marks-exact hits: ", Length(hits), "; ambiguous survivors: ", Length(surv), "\n");
SortBy(surv, s -> s.sizeG);
for s in surv do
  if s.sizeG <= FLRP_RESOLVE_BOUND then
    FLRP_VerifyTomInterval(s.name, s.class);
  else
    Print("UNRESOLVED (|G| = ", s.sizeG, " above FLRP_RESOLVE_BOUND) ", s.name, " class ", s.class, "\n");
  fi;
od;
QUIT_GAP(0);
