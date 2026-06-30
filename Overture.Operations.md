---
layout: default
title : "Overture.Operations module (The Agda Universal Algebra Library)"
date : "2022-06-17"
author: "the agda-algebras development team"
---

### <a id="Operations">Operations</a>

This is the [Overture.Operations][] module of the [Agda Universal Algebra Library][].

For consistency and readability, we reserve two universe variables for special
purposes.

The first of these is `𝓞` which we used in the [Overture.Signatures][]
as the universe of the type of *operation symbols* of a signature.

The second is `𝓥` which we reserve for types representing *arities* of relations or operations.

The type `Op` encodes the arity of an operation as an arbitrary type `I : Type 𝓥`,
which gives us a very general way to represent an operation as a function type with
domain `I → A` (the type of "tuples") and codomain `A`.

<pre class="Agda">

<a id="855" class="Symbol">{-#</a> <a id="859" class="Keyword">OPTIONS</a> <a id="867" class="Pragma">--without-K</a> <a id="879" class="Pragma">--exact-split</a> <a id="893" class="Pragma">--safe</a> <a id="900" class="Symbol">#-}</a>

<a id="905" class="Keyword">module</a> <a id="912" href="Overture.Operations.html" class="Module">Overture.Operations</a> <a id="932" class="Keyword">where</a>

<a id="939" class="Comment">-- Imports from Agda and the Agda Standard Library -----------------------------</a>
<a id="1020" class="Keyword">open</a> <a id="1025" class="Keyword">import</a> <a id="1032" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>               <a id="1061" class="Keyword">using</a> <a id="1067" class="Symbol">()</a> <a id="1070" class="Keyword">renaming</a> <a id="1079" class="Symbol">(</a> <a id="1081" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="1085" class="Symbol">to</a> <a id="1088" class="Primitive">Type</a> <a id="1093" class="Symbol">)</a>
<a id="1095" class="Keyword">open</a> <a id="1100" class="Keyword">import</a> <a id="1107" href="Level.html" class="Module">Level</a>                        <a id="1136" class="Keyword">using</a> <a id="1142" class="Symbol">(</a> <a id="1144" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1150" class="Symbol">;</a> <a id="1152" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a> <a id="1156" class="Symbol">)</a>

<a id="1159" class="Keyword">private</a> <a id="1167" class="Keyword">variable</a> <a id="1176" href="Overture.Operations.html#1176" class="Generalizable">a</a> <a id="1178" href="Overture.Operations.html#1178" class="Generalizable">b</a> <a id="1180" href="Overture.Operations.html#1180" class="Generalizable">ρ</a> <a id="1182" href="Overture.Operations.html#1182" class="Generalizable">𝓥</a> <a id="1184" class="Symbol">:</a> <a id="1186" href="Agda.Primitive.html#742" class="Postulate">Level</a>

<a id="1193" class="Comment">-- The type of operations on A of arity I</a>
<a id="Op"></a><a id="1235" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="1238" class="Symbol">:</a> <a id="1240" href="Overture.Operations.html#1088" class="Primitive">Type</a> <a id="1245" href="Overture.Operations.html#1176" class="Generalizable">a</a> <a id="1247" class="Symbol">→</a> <a id="1249" href="Overture.Operations.html#1088" class="Primitive">Type</a> <a id="1254" href="Overture.Operations.html#1182" class="Generalizable">𝓥</a> <a id="1256" class="Symbol">→</a> <a id="1258" href="Overture.Operations.html#1088" class="Primitive">Type</a> <a id="1263" class="Symbol">(</a><a id="1264" href="Overture.Operations.html#1176" class="Generalizable">a</a> <a id="1266" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1268" href="Overture.Operations.html#1182" class="Generalizable">𝓥</a><a id="1269" class="Symbol">)</a>
<a id="1271" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="1274" href="Overture.Operations.html#1274" class="Bound">A</a> <a id="1276" href="Overture.Operations.html#1276" class="Bound">I</a> <a id="1278" class="Symbol">=</a> <a id="1280" class="Symbol">(</a><a id="1281" href="Overture.Operations.html#1276" class="Bound">I</a> <a id="1283" class="Symbol">→</a> <a id="1285" href="Overture.Operations.html#1274" class="Bound">A</a><a id="1286" class="Symbol">)</a> <a id="1288" class="Symbol">→</a> <a id="1290" href="Overture.Operations.html#1274" class="Bound">A</a>

</pre>

For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op A I` as follows.

<pre class="Agda">

<a id="1440" class="Comment">-- Example (projections)</a>
<a id="π"></a><a id="1465" href="Overture.Operations.html#1465" class="Function">π</a> <a id="1467" class="Symbol">:</a> <a id="1469" class="Symbol">{</a><a id="1470" href="Overture.Operations.html#1470" class="Bound">I</a> <a id="1472" class="Symbol">:</a> <a id="1474" href="Overture.Operations.html#1088" class="Primitive">Type</a> <a id="1479" href="Overture.Operations.html#1182" class="Generalizable">𝓥</a><a id="1480" class="Symbol">}</a> <a id="1482" class="Symbol">{</a><a id="1483" href="Overture.Operations.html#1483" class="Bound">A</a> <a id="1485" class="Symbol">:</a> <a id="1487" href="Overture.Operations.html#1088" class="Primitive">Type</a> <a id="1492" href="Overture.Operations.html#1176" class="Generalizable">a</a> <a id="1494" class="Symbol">}</a> <a id="1496" class="Symbol">→</a> <a id="1498" href="Overture.Operations.html#1470" class="Bound">I</a> <a id="1500" class="Symbol">→</a> <a id="1502" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="1505" href="Overture.Operations.html#1483" class="Bound">A</a> <a id="1507" href="Overture.Operations.html#1470" class="Bound">I</a>
<a id="1509" href="Overture.Operations.html#1465" class="Function">π</a> <a id="1511" href="Overture.Operations.html#1511" class="Bound">i</a> <a id="1513" class="Symbol">=</a> <a id="1515" class="Symbol">λ</a> <a id="1517" href="Overture.Operations.html#1517" class="Bound">x</a> <a id="1519" class="Symbol">→</a> <a id="1521" href="Overture.Operations.html#1517" class="Bound">x</a> <a id="1523" href="Overture.Operations.html#1511" class="Bound">i</a>

</pre>

Occasionally we want to extract the arity of a given operation symbol.

<pre class="Agda">

<a id="1624" class="Comment">-- return the arity of a given operation symbol</a>
<a id="arity[_]"></a><a id="1672" href="Overture.Operations.html#1672" class="Function Operator">arity[_]</a> <a id="1681" class="Symbol">:</a> <a id="1683" class="Symbol">{</a><a id="1684" href="Overture.Operations.html#1684" class="Bound">I</a> <a id="1686" class="Symbol">:</a> <a id="1688" href="Overture.Operations.html#1088" class="Primitive">Type</a> <a id="1693" href="Overture.Operations.html#1182" class="Generalizable">𝓥</a><a id="1694" class="Symbol">}</a> <a id="1696" class="Symbol">{</a><a id="1697" href="Overture.Operations.html#1697" class="Bound">A</a> <a id="1699" class="Symbol">:</a> <a id="1701" href="Overture.Operations.html#1088" class="Primitive">Type</a> <a id="1706" href="Overture.Operations.html#1176" class="Generalizable">a</a> <a id="1708" class="Symbol">}</a> <a id="1710" class="Symbol">→</a> <a id="1712" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="1715" href="Overture.Operations.html#1697" class="Bound">A</a> <a id="1717" href="Overture.Operations.html#1684" class="Bound">I</a> <a id="1719" class="Symbol">→</a> <a id="1721" href="Overture.Operations.html#1088" class="Primitive">Type</a> <a id="1726" href="Overture.Operations.html#1182" class="Generalizable">𝓥</a>
<a id="1728" href="Overture.Operations.html#1672" class="Function Operator">arity[_]</a> <a id="1737" class="Symbol">{</a><a id="1738" class="Argument">I</a> <a id="1740" class="Symbol">=</a> <a id="1742" href="Overture.Operations.html#1742" class="Bound">I</a><a id="1743" class="Symbol">}</a> <a id="1745" href="Overture.Operations.html#1745" class="Bound">f</a> <a id="1747" class="Symbol">=</a> <a id="1749" href="Overture.Operations.html#1742" class="Bound">I</a>
</pre>

-----------

<span style="float:left;">[← Overture.Signatures](Overture.Signatures.html)</span>
<span style="float:right;">[Base →](Base.html)</span>


{% include UALib.Links.md %}

