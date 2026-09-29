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
##  The classification recorded per coatom K, with B the base S^n, by the
##  exact tests documented at FLRP_CoatomType below: "product" (K meet B is
##  the direct product of its nontrivial coordinate meets), "diagonal" (K meet
##  B is a product of full diagonal subgroups over a partition of the
##  coordinates; the number of blocks is recorded as diagonalBlocks), or
##  "other".  A first version of the script tested only the necessary
##  conditions (all coordinate meets nontrivial, or all trivial); the exact
##  tests give the same labels on the instance recorded here.
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
##  Exact tests.  With KB = K meet B and C_i the coordinate subgroups of the
##  base B = S^n (S nonabelian simple):
##    "product"   KB is the direct product of its coordinate meets KB meet C_i,
##                all of them nontrivial: the meets generate a subgroup of
##                order the product of their orders, so this is the equation
##                |KB| = prod_i |KB meet C_i| together with every factor > 1;
##    "diagonal"  every coordinate meet is trivial, every coordinate projection
##                of KB is all of S, the relation "the projection of KB onto
##                C_i x C_j has order |S|" is an equivalence on the coordinates
##                with b blocks, and |KB| = |S|^b: then KB is the product of one
##                full diagonal subgroup per block (KB lies in that product,
##                which has order |S|^b), which is Aschbacher's type II;
##    "other"     anything else (Aschbacher's types III and IV, or a subgroup of
##                neither shape).  Necessary conditions alone (all meets
##                nontrivial, or all trivial) would mislabel, e.g., a subgroup
##                lying diagonally over nontrivial coordinate meets.
##  Coordinate projections are read off the wreath product's point blocks:
##  coordinate i acts on the i-th block of moved points, so the projection of
##  KB onto C_i is its action on that block.
FLRP_CoordinateBlocks := function(W, coords)
  return List(coords, C -> MovedPoints(C));
end;;

FLRP_CoatomType := function(K, B, coords, S)
  local KB, meets, blocks, n, proj, pairs, linked, i, j, classes, seen, cls, k, b;
  KB := Intersection(K, B);
  meets := List(coords, C -> Size(Intersection(KB, C)));
  n := Length(coords);
  if Size(KB) = 1 then
    return rec(type := "other", meetBaseOrder := 1, meetCoordinateOrders := meets);
  fi;
  if ForAll(meets, m -> m > 1) and Size(KB) = Product(meets) then
    return rec(type := "product", meetBaseOrder := Size(KB), meetCoordinateOrders := meets);
  fi;
  if ForAll(meets, m -> m = 1) then
    blocks := List(coords, C -> MovedPoints(C));
    proj := List([1 .. n], i -> Size(Action(KB, blocks[i])));
    if ForAll(proj, p -> p = Size(S)) then
      # linked[i][j]: the pair projection is a diagonal (order |S|), not S x S.
      linked := List([1 .. n], i -> List([1 .. n], j ->
                  i = j or Size(Action(KB, Union(blocks[i], blocks[j]))) = Size(S)));
      # The relation must be an equivalence; symmetry is built in.
      if ForAll([1 .. n], i -> ForAll([1 .. n], j -> ForAll([1 .. n], k ->
           not (linked[i][j] and linked[j][k]) or linked[i][k]))) then
        seen := []; classes := 0;
        for i in [1 .. n] do
          if not i in seen then
            classes := classes + 1;
            cls := Filtered([1 .. n], j -> linked[i][j]);
            Append(seen, cls);
          fi;
        od;
        if Size(KB) = Size(S)^classes then
          return rec(type := "diagonal", meetBaseOrder := Size(KB),
                     meetCoordinateOrders := meets, diagonalBlocks := classes);
        fi;
      fi;
    fi;
  fi;
  return rec(type := "other", meetBaseOrder := Size(KB), meetCoordinateOrders := meets);
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
      t := FLRP_CoatomType(K, base, coords, S);
      act := Action(W, RightCosets(W, K), OnRight);
      entry := rec(order := Size(K), type := t.type,
                   meetBaseOrder := t.meetBaseOrder,
                   meetCoordinateOrders := t.meetCoordinateOrders,
                   diagonalBlocks := t.diagonalBlocks,
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
