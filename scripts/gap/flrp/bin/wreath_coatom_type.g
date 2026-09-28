#############################################################################
##
##  scripts/gap/flrp/bin/wreath_coatom_type.g   (issue #578, path 3)
##
##  The type of the coatoms of a Kurzweil wreath interval.  For a core-free
##  H <= G of index n and a nonabelian simple S, Kurzweil's interval
##  [Diag x G, S wr G] is the dual of [H, G]; its coatoms correspond to the
##  atoms K of [H, G] and are the partition subgroups S^{pi_K} : G, so each
##  meets the socle S^n in a product of full diagonal subgroups (Aschbacher's
##  type II, "diagonal type") and meets every coordinate trivially.  This
##  script checks that on the smallest instance with a proper coatom,
##  [1, C4] (a three-element chain) with S = A5, and writes the record
##  scripts/gap/flrp/out/wreath_coatom_type_a5_c4.json.  Run from the repo
##  root inside `nix develop .#gap`:
##
##    gap -A -q -b scripts/gap/flrp/bin/wreath_coatom_type.g
##
##  Optional globals (set with -c): FLRP_OUT (the record path) and FLRP_DATE
##  (the date field, pinned so the committed record re-derives byte for byte).
##
##  The classification recorded per coatom K, with B the base S^n:
##    "diagonal"  K meet B is nontrivial and meets every coordinate trivially;
##    "product"   K meet B meets every coordinate nontrivially;
##    "other"     anything else (does not occur here).
##  GAP's ONanScottType of the coset action is recorded as well, as data; the
##  verdict rests on the stabilizer-in-the-socle computation, not on it.
##
#############################################################################

Read("scripts/gap/flrp/lib/json.g");
Read("scripts/gap/flrp/lib/provenance.g");

if not IsBoundGlobal("FLRP_OUT") then
  FLRP_OUT := "scripts/gap/flrp/out/wreath_coatom_type_a5_c4.json";
fi;
if not IsBoundGlobal("FLRP_DATE") then
  FLRP_DATE := "2026-09-28";
fi;

##  The type of a subgroup K of W with respect to the base B and its
##  coordinate subgroups.
FLRP_CoatomType := function(K, B, coords)
  local KB, meets;
  KB := Intersection(K, B);
  meets := List(coords, C -> Size(Intersection(KB, C)));
  if Size(KB) > 1 and ForAll(meets, m -> m = 1) then
    return rec(type := "diagonal", meetBaseOrder := Size(KB), meetCoordinateOrders := meets);
  elif ForAll(meets, m -> m > 1) then
    return rec(type := "product", meetBaseOrder := Size(KB), meetCoordinateOrders := meets);
  else
    return rec(type := "other", meetBaseOrder := Size(KB), meetCoordinateOrders := meets);
  fi;
end;;

##  The Kurzweil wreath of S over the regular action of a cyclic group of
##  order n, with H = Diag x C_n, and the record of its coatoms.
FLRP_WreathCoatomRecord := function(S, Sname, n)
  local Cn, W, embs, coords, base, diag, top, H, ints, coatoms, K, t, act, entry;
  Cn := Group(PermList(Concatenation([2 .. n], [1])));
  W := WreathProduct(S, Cn);
  embs := List([1 .. n], i -> Embedding(W, i));
  coords := List(embs, e -> Image(e));
  base := Subgroup(W, Concatenation(List(coords, GeneratorsOfGroup)));
  diag := Subgroup(W, List(GeneratorsOfGroup(S),
            g -> Product(List([1 .. n], i -> Image(embs[i], g)))));
  top := Image(Embedding(W, n + 1));
  H := ClosureGroup(diag, top);
  ints := IntermediateSubgroups(W, H);
  coatoms := [];
  for K in ints.subgroups do
    if Length(IntermediateSubgroups(W, K).subgroups) = 0 then
      t := FLRP_CoatomType(K, base, coords);
      act := Action(W, RightCosets(W, K), OnRight);
      entry := rec(order := Size(K), type := t.type,
                   meetBaseOrder := t.meetBaseOrder,
                   meetCoordinateOrders := t.meetCoordinateOrders,
                   cosetActionDegree := NrMovedPoints(act),
                   primitive := IsPrimitive(act),
                   gapONanScottType := ONanScottType(act));
      Add(coatoms, entry);
    fi;
  od;
  return rec(
    base := rec(name := Sname, order := Size(S)),
    top := rec(name := Concatenation("C", String(n)), order := n,
               action := "regular, the coset action of [1, C_n]"),
    wreath := rec(order := Size(W), degree := NrMovedPoints(W)),
    H := rec(description := "Diag x C_n", order := Size(H),
             index := Index(W, H), coreFree := Size(Core(W, H)) = 1),
    interval := rec(size := Length(ints.subgroups) + 2,
                    intermediateOrders := List(ints.subgroups, Size)),
    coatoms := coatoms);
end;;

result := FLRP_WreathCoatomRecord(AlternatingGroup(5), "A5", 4);;
out := rec(format := "flrp-wreath-coatom-type v1", date := FLRP_DATE,
           engine := FLRP_Provenance(),
           instance := "[Diag x C4, A5 wr C4], the Kurzweil wreath over [1, C4]",
           result := result);;
JSON_WriteFile(FLRP_OUT, out);
Print("wrote ", FLRP_OUT, "\n");
Print("coatom types: ", List(result.coatoms, c -> c.type), "\n");
QUIT_GAP(0);
