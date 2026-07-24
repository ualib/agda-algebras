#############################################################################
##
##  scripts/gap/flrp/lib/json.g
##
##  Minimal deterministic JSON writer for GAP.  The FLRP certificate
##  discipline (docs/notes/flrp-research-roadmap.md § 6) requires that GAP —
##  an untrusted engine — leave its results as deterministic JSON artifacts;
##  this is the serializer those artifacts are written with.  It handles
##  integers, booleans, genuine (non-empty) strings, lists (rendered as JSON
##  arrays) and records (rendered as JSON objects with keys in sorted order,
##  so output is byte-stable across runs).  No external GAP package is used,
##  so it works in the lean `.#gap` shell exactly as in a full GAP install.
##
##  Caveat inherent to GAP: the empty string and the empty list are the same
##  object, so both render as `[]`.  Emit a placeholder rather than an empty
##  string where the distinction would matter.
##
#############################################################################

##  Forward declaration so the recursive renderer can refer to itself without
##  tripping GAP's unbound-global check (the standard package idiom).
DeclareGlobalFunction("JSON_ToStringInner");

##  Escape a GAP string into a JSON string literal (with surrounding quotes).
BindGlobal("JSON_EscapeString", function(s)
  local out, c;
  out := "\"";
  for c in s do
    if c = '"' then
      Append(out, "\\\"");
    elif c = '\\' then
      Append(out, "\\\\");
    elif c = '\n' then
      Append(out, "\\n");
    elif c = '\t' then
      Append(out, "\\t");
    else
      Add(out, c);
    fi;
  od;
  Add(out, '"');
  return out;
end);

##  A string of 2*i spaces (the indent at nesting depth i).
BindGlobal("JSON_Indent", i -> ListWithIdenticalEntries(2 * i, ' '));

##  Recursively render `obj` as pretty-printed JSON at nesting `level`.
InstallGlobalFunction(JSON_ToStringInner, function(obj, level)
  local parts, keys, k, inner, elt;
  if IsBool(obj) then
    if obj = true then return "true"; else return "false"; fi;
  elif IsInt(obj) then
    return String(obj);
  elif IsString(obj) and Length(obj) > 0 and IsChar(obj[1]) then
    return JSON_EscapeString(obj);
  elif IsRecord(obj) then
    keys := Set(RecNames(obj));
    if Length(keys) = 0 then return "{}"; fi;
    parts := [];
    for k in keys do
      inner := JSON_ToStringInner(obj.(k), level + 1);
      Add(parts, Concatenation(JSON_Indent(level + 1),
                               JSON_EscapeString(k), ": ", inner));
    od;
    return Concatenation("{\n", JoinStringsWithSeparator(parts, ",\n"),
                         "\n", JSON_Indent(level), "}");
  elif IsList(obj) then
    if Length(obj) = 0 then return "[]"; fi;
    parts := [];
    for elt in obj do
      Add(parts, Concatenation(JSON_Indent(level + 1),
                               JSON_ToStringInner(elt, level + 1)));
    od;
    return Concatenation("[\n", JoinStringsWithSeparator(parts, ",\n"),
                         "\n", JSON_Indent(level), "]");
  fi;
  Error("JSON_ToStringInner: unsupported object of type ", TNAM_OBJ(obj));
end);

##  Render `obj` as a JSON document (no trailing newline).
BindGlobal("JSON_ToString", obj -> JSON_ToStringInner(obj, 0));

##  Write `obj` as JSON to `path` (overwriting), with a trailing newline, and
##  with GAP's line-width formatting disabled so long rows are not wrapped.
BindGlobal("JSON_WriteFile", function(path, obj)
  local out;
  out := OutputTextFile(path, false);
  SetPrintFormattingStatus(out, false);
  PrintTo(out, JSON_ToString(obj), "\n");
  CloseStream(out);
end);
