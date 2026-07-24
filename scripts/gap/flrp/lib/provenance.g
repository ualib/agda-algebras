#############################################################################
##
##  scripts/gap/flrp/lib/provenance.g
##
##  The engine/library version stamp embedded in every emitted artifact.
##  Issue #487 requires the GAP version and the versions of the group
##  libraries a run consulted to be recorded, so that a JSON artifact is
##  self-describing and reproducible: the same lattice found under a later
##  GAP or a later SmallGroups/transitive-groups library is a distinguishable
##  fact, not a silent drift.
##
#############################################################################

##  A record `rec( gap := <version>, libraries := rec( smallgrp := ...,
##  transgrp := ..., primgrp := ... ) )`.  A library that is not installed is
##  recorded as "absent" rather than omitted, so its absence is explicit.
BindGlobal("FLRP_Provenance", function()
  local libs, name, info;
  libs := rec();
  for name in [ "smallgrp", "transgrp", "primgrp" ] do
    info := PackageInfo(name);
    if Length(info) > 0 then
      libs.(name) := info[1].Version;
    else
      libs.(name) := "absent";
    fi;
  od;
  return rec( gap := GAPInfo.Version, libraries := libs );
end);
