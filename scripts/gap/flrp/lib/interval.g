#############################################################################
##
##  scripts/gap/flrp/lib/interval.g   (issue #487)
##
##  The core of the subgroup-interval engine: given finite groups H <= G,
##  extract the upper interval [H, G] in Sub(G) as a finite poset, using
##  A. Hulpke's `IntermediateSubgroups(G, H)`.  That routine returns the
##  subgroups strictly between H and G together with the cover (maximality)
##  relation among the nodes 0 = H, 1..m = the intermediate subgroups, and
##  m+1 = G.  We package that as a raw JSON-ready record; the Python bridge
##  turns the poset into meet/join tables (`eqsearch.tables_from_leq`) and
##  tests isomorphism against a target lattice.  Core-free normalization of H
##  is recorded (Core_G(H)), the pivot of the minimality theory (roadmap § 4).
##
##  Depends on: lib/provenance.g (FLRP_Provenance).
##
#############################################################################

##  The generators of a (sub)group as a GAP-printed string, e.g. "[ f1, f4 ]".
##  Enough to cross-check against the manuscript and to reproduce the subgroup
##  within a fixed GAP + library version (recorded in the engine stamp).
BindGlobal("FLRP_GensString", K -> String(GeneratorsOfGroup(K)));

##  The reflexive-transitive closure of a cover list, as a size x size boolean
##  matrix `leq` with `leq[i+1][j+1] = true` iff node i <= node j.  `covers`
##  is a list of 0-based pairs [lower, upper] (exactly Hulpke's `inclusions`).
BindGlobal("FLRP_LeqFromCovers", function(size, covers)
  local leq, i, j, k, e;
  leq := List([1 .. size], i -> List([1 .. size], j -> false));
  for i in [1 .. size] do
    leq[i][i] := true;
  od;
  for e in covers do
    leq[e[1] + 1][e[2] + 1] := true;
  od;
  # Warshall transitive closure.
  for k in [1 .. size] do
    for i in [1 .. size] do
      for j in [1 .. size] do
        if leq[i][k] and leq[k][j] then
          leq[i][j] := true;
        fi;
      od;
    od;
  od;
  return leq;
end);

##  The interval [H, G] as a poset record: its size (endpoints included), the
##  cover list (0 = H, size-1 = G), the reflexive order matrix, and per-node
##  metadata (order, role, generators).  Pure poset data — no lattice tables,
##  no target; those are the Python bridge's job.
BindGlobal("FLRP_IntervalPoset", function(G, H)
  local im, inter, m, size, top, nodes, k;
  im := IntermediateSubgroups(G, H);
  inter := im.subgroups;
  m := Length(inter);
  size := m + 2;
  top := m + 1;                         # 0-based index of G
  nodes := [ rec( index := 0, order := Order(H), role := "bottom",
                  generators := FLRP_GensString(H) ) ];
  for k in [1 .. m] do
    Add(nodes, rec( index := k, order := Order(inter[k]), role := "interior",
                    generators := FLRP_GensString(inter[k]) ));
  od;
  Add(nodes, rec( index := top, order := Order(G), role := "top",
                  generators := FLRP_GensString(G) ));
  return rec( size := size,
              covers := im.inclusions,
              leq := FLRP_LeqFromCovers(size, im.inclusions),
              nodes := nodes );
end);

##  Does the interval contain a cover between two interior nodes?  For a
##  size-5 interval this distinguishes N5 (which has the interior cover
##  alpha < beta) from M3 and the graded 5-element lattices; a light GAP-side
##  gate before the Python side confirms the isomorphism type authoritatively.
BindGlobal("FLRP_HasInteriorCover", function(interval)
  local e, top;
  top := interval.size - 1;
  for e in interval.covers do
    if e[1] <> 0 and e[2] <> top then
      return true;
    fi;
  od;
  return false;
end);

##  The full raw interval artifact for one pair H <= G.  `source` is a record
##  describing how G was obtained, e.g. rec(source := "SmallGroup",
##  id := [216, 153]); it is echoed into the artifact so the group is
##  reconstructible.  Coset-action tables are added by the caller (lib/cosets.g)
##  only when wanted, since they are only needed for the certificate routes.
BindGlobal("FLRP_IntervalRecord", function(source, G, H)
  local core;
  core := Core(G, H);
  return rec(
    format := "flrp-gap-interval-raw v1",
    engine := FLRP_Provenance(),
    group := rec( source := source.source,
                  id := source.id,
                  order := Order(G),
                  structureDescription := StructureDescription(G) ),
    subgroup := rec( order := Order(H),
                     index := Index(G, H),
                     coreOrder := Order(core),
                     coreFree := Order(core) = 1,
                     generators := FLRP_GensString(H) ),
    interval := FLRP_IntervalPoset(G, H) );
end);
