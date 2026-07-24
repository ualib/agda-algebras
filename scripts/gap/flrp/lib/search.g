#############################################################################
##
##  scripts/gap/flrp/lib/search.g   (issue #487)
##
##  Search drivers over the GAP group libraries.  Two modes:
##
##    * FLRP_ScanTransitive — the point-stabilizer scan of a transitive-group
##      family (deliverable 4, with #484).  A transitive G-set of degree n is,
##      up to equivalence, G acting on the cosets of a point stabilizer H
##      (index n), and Con(G-set) ≅ [H, G]; so for each TransitiveGroup(n, k)
##      the interval [point stabilizer, G] is that G-set's congruence lattice.
##      By the manuscript's § 5 transitivity theorem a minimal representation of
##      library L7 must be such a transitive G-set, so a degree-by-degree scan
##      settles existence of minimal representations of a given size.
##
##    * FLRP_ScanSmallGroups — the subgroup-interval hunt over a slice of the
##      SmallGroups library (deliverables 3-full and 5), enumerating conjugacy
##      classes of subgroups H (optionally only core-free ones, which is WLOG
##      for a smallest group and a strong prune) and collecting the intervals
##      [H, G] of a wanted size.
##
##  Both collect only a cheap GAP-side invariant — the interval's element count
##  — as a prescreen; the Python bridge confirms isomorphism against the target
##  lattice on the (few) survivors.  A size histogram is returned so a negative
##  verdict is self-evident (no interval of the target size ⇒ no representation
##  of that size in the slice).
##
##  Depends on: lib/provenance.g, lib/interval.g.
##
#############################################################################

##  Increment a size-count histogram (a record keyed by the size as a string).
BindGlobal("FLRP_BumpHistogram", function(hist, sz)
  local key;
  key := String(sz);
  if IsBound(hist.(key)) then
    hist.(key) := hist.(key) + 1;
  else
    hist.(key) := 1;
  fi;
end);

##  Point-stabilizer scan of TransitiveGroup(degree, *).  Returns the number of
##  groups scanned, the histogram of interval sizes, and the raw interval
##  records of every group whose interval [H, G] has exactly `targetSize`
##  elements (candidates for the target lattice).
BindGlobal("FLRP_ScanTransitive", function(degree, targetSize)
  local nr, cands, hist, k, G, H, poset;
  nr := NrTransitiveGroups(degree);
  cands := [];
  hist := rec();
  for k in [1 .. nr] do
    G := TransitiveGroup(degree, k);
    H := Stabilizer(G, 1);
    poset := FLRP_IntervalPoset(G, H);
    FLRP_BumpHistogram(hist, poset.size);
    if poset.size = targetSize then
      Add(cands, FLRP_IntervalRecord(
        rec( source := "TransitiveGroup", id := [ degree, k ] ), G, H));
    fi;
  od;
  return rec( groupsScanned := nr, sizeHistogram := hist, candidates := cands );
end);

##  Subgroup-interval hunt over a list of SmallGroups orders.  For each group,
##  enumerate conjugacy-class representatives of subgroups H (only core-free
##  ones when `coreFreeOnly`), and collect the intervals [H, G] with exactly
##  `targetSize` elements.  Orders whose NumberSmallGroups exceeds `idCap` are
##  skipped and reported, so a bounded run never silently blows up on a
##  pathological order (512, 1024, ...).
BindGlobal("FLRP_ScanSmallGroups", function(orders, targetSize, coreFreeOnly, idCap)
  local cands, hist, skipped, o, n, id, G, ccsg, c, H, poset;
  cands := [];
  hist := rec();
  skipped := [];
  for o in orders do
    n := NumberSmallGroups(o);
    if n > idCap then
      Add(skipped, rec( order := o, count := n ));
      continue;
    fi;
    for id in [1 .. n] do
      G := SmallGroup(o, id);
      ccsg := ConjugacyClassesSubgroups(G);
      for c in ccsg do
        H := Representative(c);
        if H <> G and (not coreFreeOnly or Order(Core(G, H)) = 1) then
          poset := FLRP_IntervalPoset(G, H);
          FLRP_BumpHistogram(hist, poset.size);
          if poset.size = targetSize then
            Add(cands, FLRP_IntervalRecord(
              rec( source := "SmallGroup", id := [ o, id ] ), G, H));
          fi;
        fi;
      od;
    od;
  od;
  return rec( sizeHistogram := hist, skippedOrders := skipped,
              candidates := cands );
end);
