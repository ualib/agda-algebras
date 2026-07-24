#############################################################################
##
##  scripts/gap/flrp/lib/cosets.g   (issue #487)
##
##  The coset action of G on G/H as a unary algebra, for the certificate
##  routes.  By the Pálfy–Pudlák easy direction (`FLRP.Bridge`, issue #454)
##  the congruence lattice of the transitive G-set on the [G:H] cosets is
##  isomorphic to [H, G]; so dumping the action of a generating set of G on
##  the cosets as unary value tables gives a finite algebra whose congruence
##  lattice is the found interval.  For an index within the renderer's literal
##  cap this feeds `emit_agda.py` directly (the direct-certificate route,
##  deliverable 6); for larger indices it is the concrete G-set the WP-3
##  bridge consumes.
##
##  Depends on: nothing beyond core GAP.
##
#############################################################################

##  The coset-action algebra of G on G/H: one unary operation per element of a
##  small generating set of G, as a 0-based value table on the [G:H] cosets.
##  The point numbering is GAP's own; the congruence lattice is invariant
##  under it, so no canonicalization is needed.  `directCertifiable` flags
##  whether the carrier fits the emitter's Fin-literal cap: n points use the
##  literals 0F..(n-1)F, so the module renders directly iff n - 1 < LITERAL_LIMIT
##  (= 32 in emit_agda.py), i.e. n ≤ 32.
BindGlobal("FLRP_CosetAction", function(G, H)
  local hom, n, gens, ops, i, perm, table;
  hom := FactorCosetAction(G, H);
  n := Index(G, H);
  gens := SmallGeneratingSet(G);
  ops := [];
  for i in [1 .. Length(gens)] do
    perm := Image(hom, gens[i]);
    # table[k] (1-based list position k) is the 0-based image of the 0-based
    # point k-1, i.e. GAP point k maps to k^perm, minus one for 0-basing.
    table := List([1 .. n], k -> (k ^ perm) - 1);
    Add(ops, rec( name := Concatenation("g", String(i - 1)),
                  arity := 1,
                  table := table ));
  od;
  return rec( points := n,
              directCertifiable := n <= 32,
              generators := ops );
end);
