#############################################################################
##
##  scripts/gap/flrp/bin/hunt_witnesses.g   (issue #460, RP-3)
##
##  Witness checks for the RP-3 candidate table (docs/notes/flrp-rp3-hunt.md):
##  for a fixed list of small groups, decide membership in the catalog's
##  classes and in the two-element-chain class.  Each verdict is an instance
##  supporting (never proving) a candidate-family kill recorded in the note:
##  a group found in the intersection of a candidate family kills that family
##  outright, and a wreath product found inside a class is the concrete face
##  of the Lemma 3.3 wreath-richness constraint.
##
##  The class tests, and why testing minimal normal subgroups suffices for a
##  finite group:
##
##    G2 (subdirectly irreducible)      <=>  exactly one minimal normal
##                                           subgroup;
##    G3 (no nontrivial abelian normal) <=>  no abelian minimal normal
##                                           subgroup (every nontrivial normal
##                                           subgroup of a finite group
##                                           contains a minimal one, and
##                                           subgroups of abelian groups are
##                                           abelian);
##    G4 (trivial centralizers)         <=>  every minimal normal subgroup has
##                                           trivial centralizer (centralizers
##                                           are antitone in the subgroup);
##    CFMax (core-free maximal subgroup, catalog Entry 9's class)
##                                       =   some maximal subgroup has trivial
##                                           normal core;
##    G0 (nonsolvable)                   =   not IsSolvableGroup.
##
##  Everything is decided by the GAP library; the output is data for the
##  survey note, not proof.  Run from the repo root inside `nix develop .#gap`:
##      gap -A -q -b scripts/gap/flrp/bin/hunt_witnesses.g
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");

##  The class-membership record of one group.
FLRP_WitnessRecord := function(name, G)
  local mns;
  mns := MinimalNormalSubgroups(G);
  return rec(
    name := name,
    order := Order(G),
    structureDescription := StructureDescription(G),
    minimalNormalCount := Length(mns),
    G0_nonsolvable := not IsSolvableGroup(G),
    G2_subdirectlyIrreducible := Length(mns) = 1,
    G3_noAbelianNormal := ForAll(mns, N -> not IsAbelian(N)),
    G4_trivialCentralizers := ForAll(mns, N -> Order(Centralizer(G, N)) = 1),
    CFMax_coreFreeMaximal := ForAny(MaximalSubgroupClassReps(G),
                                    M -> Order(Core(G, M)) = 1) );
end;;

##  The witness list: two nonabelian simple groups (common members of every
##  catalog class), the two smallest wreath shapes of Lemma 3.3 over them
##  (the transitive point-permuting action of C2), and two small solvable
##  contrasts (C2 separates CFMax from G3/G4; S4 separates G2 and CFMax from
##  G0 and G3).
witnesses := [
  rec( name := "C2",          G := CyclicGroup(2) ),
  rec( name := "S4",          G := SymmetricGroup(4) ),
  rec( name := "A5",          G := AlternatingGroup(5) ),
  rec( name := "PSL(3,2)",    G := PSL(3, 2) ),
  rec( name := "A5 wr C2",    G := WreathProduct(AlternatingGroup(5), Group((1,2))) ),
  rec( name := "PSL(3,2) wr C2",
       G := WreathProduct(PSL(3, 2), Group((1,2))) ),
];;

out := rec(
  format := "flrp-gap-hunt-witness v1",
  date := "2026-08-29",
  engine := FLRP_Provenance(),
  purpose := Concatenation(
    "RP-3 candidate-table witness data: class membership of the groups the ",
    "survey note uses to kill candidate families (docs/notes/flrp-rp3-hunt.md)"),
  groups := List(witnesses, w -> FLRP_WitnessRecord(w.name, w.G)) );;

path := "scripts/gap/flrp/out/rp3_witnesses.json";;
JSON_WriteFile(path, out);
Print("wrote witness report: ", path, "\n");
QUIT_GAP(0);
