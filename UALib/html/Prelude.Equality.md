---
layout: default
title : UALib.Prelude.Equality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="equality">Equality</a>

This section describes the [UALib.Prelude.Equality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="291" class="Symbol">{-#</a> <a id="295" class="Keyword">OPTIONS</a> <a id="303" class="Pragma">--without-K</a> <a id="315" class="Pragma">--exact-split</a> <a id="329" class="Pragma">--safe</a> <a id="336" class="Symbol">#-}</a>

<a id="341" class="Keyword">module</a> <a id="348" href="Prelude.Equality.html" class="Module">Prelude.Equality</a> <a id="365" class="Keyword">where</a>

<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="406" class="Keyword">public</a>

</pre>

#### <a id="definitional-equality">Definitional equality</a>

The type referred to as "reflexivity" or "refl" is a very basic but important one. It represents [definitional equality](https://ncatlab.org/nlab/show/equality#definitional_equality).

The `refl` type we use is a standard one. It is defined in the `Identity-Type` module of the [Type Topology][] library, but apart from syntax it is equivalent to the identity type used in most other Agda libraries.

We make `refl` available by importing it from the `Identity-Type` module.  However, we first repeat the definition here (inside a hidden submodule) for clarity. (See [the remark about hidden modules](Prelude.Equality.html#fn3) in the [third footnote](Prelude.Preliminaries.html#fn3).html#fn1) of the [Prelude.Preliminaries][] module.)

<pre class="Agda">

<a id="1239" class="Keyword">module</a> <a id="hide-refl"></a><a id="1246" href="Prelude.Equality.html#1246" class="Module">hide-refl</a> <a id="1256" class="Symbol">{</a><a id="1257" href="Prelude.Equality.html#1257" class="Bound">𝓤</a> <a id="1259" class="Symbol">:</a> <a id="1261" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1269" class="Symbol">}</a> <a id="1271" class="Keyword">where</a>

 <a id="1279" class="Keyword">data</a> <a id="hide-refl._≡_"></a><a id="1284" href="Prelude.Equality.html#1284" class="Datatype Operator">_≡_</a> <a id="1288" class="Symbol">{</a><a id="1289" href="Prelude.Equality.html#1289" class="Bound">𝓤</a><a id="1290" class="Symbol">}</a> <a id="1292" class="Symbol">{</a><a id="1293" href="Prelude.Equality.html#1293" class="Bound">A</a> <a id="1295" class="Symbol">:</a> <a id="1297" href="Prelude.Equality.html#1289" class="Bound">𝓤</a> <a id="1299" href="Universes.html#403" class="Function Operator">̇</a> <a id="1301" class="Symbol">}</a> <a id="1303" class="Symbol">:</a> <a id="1305" href="Prelude.Equality.html#1293" class="Bound">A</a> <a id="1307" class="Symbol">→</a> <a id="1309" href="Prelude.Equality.html#1293" class="Bound">A</a> <a id="1311" class="Symbol">→</a> <a id="1313" href="Prelude.Equality.html#1289" class="Bound">𝓤</a> <a id="1315" href="Universes.html#403" class="Function Operator">̇</a> <a id="1317" class="Keyword">where</a> <a id="hide-refl._≡_.refl"></a><a id="1323" href="Prelude.Equality.html#1323" class="InductiveConstructor">refl</a> <a id="1328" class="Symbol">:</a> <a id="1330" class="Symbol">{</a><a id="1331" href="Prelude.Equality.html#1331" class="Bound">x</a> <a id="1333" class="Symbol">:</a> <a id="1335" href="Prelude.Equality.html#1293" class="Bound">A</a><a id="1336" class="Symbol">}</a> <a id="1338" class="Symbol">→</a> <a id="1340" href="Prelude.Equality.html#1331" class="Bound">x</a> <a id="1342" href="Prelude.Equality.html#1284" class="Datatype Operator">≡</a> <a id="1344" href="Prelude.Equality.html#1331" class="Bound">x</a>

<a id="1347" class="Keyword">open</a> <a id="1352" class="Keyword">import</a> <a id="1359" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="1373" class="Keyword">renaming</a> <a id="1382" class="Symbol">(</a><a id="1383" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="1387" class="Symbol">to</a> <a id="1390" class="Keyword">infix</a> <a id="1396" class="Number">0</a> <a id="_≡_"></a><a id="1398" href="Prelude.Equality.html#1398" class="Datatype Operator">_≡_</a><a id="1401" class="Symbol">)</a> <a id="1403" class="Keyword">public</a>

</pre>

Thus, whenever we need to complete a proof by simply asserting that `x` is definitionally equal to itself, we can invoke `refl`.  If we need to make `x` explicit, we use `refl {x = x}`.

Of course `≡` is an equivalence relation and the formal proof of this fact is trivial. We don't even need to prove reflexivity since it is the defining property of `≡`.  Here are the (trivial) proofs of symmetry and transitivity of `≡`.

<pre class="Agda">

<a id="1862" class="Keyword">module</a> <a id="1869" href="Prelude.Equality.html#1869" class="Module">_</a>  <a id="1872" class="Symbol">{</a><a id="1873" href="Prelude.Equality.html#1873" class="Bound">𝓤</a> <a id="1875" class="Symbol">:</a> <a id="1877" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1885" class="Symbol">}{</a><a id="1887" href="Prelude.Equality.html#1887" class="Bound">A</a> <a id="1889" class="Symbol">:</a> <a id="1891" href="Prelude.Equality.html#1873" class="Bound">𝓤</a> <a id="1893" href="Universes.html#403" class="Function Operator">̇</a> <a id="1895" class="Symbol">}</a>  <a id="1898" class="Keyword">where</a>

 <a id="1906" href="Prelude.Equality.html#1906" class="Function">≡-symmetric</a> <a id="1918" class="Symbol">:</a> <a id="1920" class="Symbol">(</a><a id="1921" href="Prelude.Equality.html#1921" class="Bound">x</a> <a id="1923" href="Prelude.Equality.html#1923" class="Bound">y</a> <a id="1925" class="Symbol">:</a> <a id="1927" href="Prelude.Equality.html#1887" class="Bound">A</a><a id="1928" class="Symbol">)</a> <a id="1930" class="Symbol">→</a> <a id="1932" href="Prelude.Equality.html#1921" class="Bound">x</a> <a id="1934" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="1936" href="Prelude.Equality.html#1923" class="Bound">y</a> <a id="1938" class="Symbol">→</a> <a id="1940" href="Prelude.Equality.html#1923" class="Bound">y</a> <a id="1942" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="1944" href="Prelude.Equality.html#1921" class="Bound">x</a>
 <a id="1947" href="Prelude.Equality.html#1906" class="Function">≡-symmetric</a> <a id="1959" class="Symbol">_</a> <a id="1961" class="Symbol">_</a> <a id="1963" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="1968" class="Symbol">=</a> <a id="1970" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

 <a id="1977" href="Prelude.Equality.html#1977" class="Function">≡-sym</a> <a id="1983" class="Symbol">:</a> <a id="1985" class="Symbol">{</a><a id="1986" href="Prelude.Equality.html#1986" class="Bound">x</a> <a id="1988" href="Prelude.Equality.html#1988" class="Bound">y</a> <a id="1990" class="Symbol">:</a> <a id="1992" href="Prelude.Equality.html#1887" class="Bound">A</a><a id="1993" class="Symbol">}</a> <a id="1995" class="Symbol">→</a> <a id="1997" href="Prelude.Equality.html#1986" class="Bound">x</a> <a id="1999" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2001" href="Prelude.Equality.html#1988" class="Bound">y</a> <a id="2003" class="Symbol">→</a> <a id="2005" href="Prelude.Equality.html#1988" class="Bound">y</a> <a id="2007" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2009" href="Prelude.Equality.html#1986" class="Bound">x</a>
 <a id="2012" href="Prelude.Equality.html#1977" class="Function">≡-sym</a> <a id="2018" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2023" class="Symbol">=</a> <a id="2025" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

 <a id="2032" href="Prelude.Equality.html#2032" class="Function">≡-transitive</a> <a id="2045" class="Symbol">:</a> <a id="2047" class="Symbol">(</a><a id="2048" href="Prelude.Equality.html#2048" class="Bound">x</a> <a id="2050" href="Prelude.Equality.html#2050" class="Bound">y</a> <a id="2052" href="Prelude.Equality.html#2052" class="Bound">z</a> <a id="2054" class="Symbol">:</a> <a id="2056" href="Prelude.Equality.html#1887" class="Bound">A</a><a id="2057" class="Symbol">)</a> <a id="2059" class="Symbol">→</a> <a id="2061" href="Prelude.Equality.html#2048" class="Bound">x</a> <a id="2063" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2065" href="Prelude.Equality.html#2050" class="Bound">y</a> <a id="2067" class="Symbol">→</a> <a id="2069" href="Prelude.Equality.html#2050" class="Bound">y</a> <a id="2071" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2073" href="Prelude.Equality.html#2052" class="Bound">z</a> <a id="2075" class="Symbol">→</a> <a id="2077" href="Prelude.Equality.html#2048" class="Bound">x</a> <a id="2079" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2081" href="Prelude.Equality.html#2052" class="Bound">z</a>
 <a id="2084" href="Prelude.Equality.html#2032" class="Function">≡-transitive</a> <a id="2097" class="Symbol">_</a> <a id="2099" class="Symbol">_</a> <a id="2101" class="Symbol">_</a> <a id="2103" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2108" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2113" class="Symbol">=</a> <a id="2115" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

 <a id="2122" href="Prelude.Equality.html#2122" class="Function">≡-trans</a> <a id="2130" class="Symbol">:</a> <a id="2132" class="Symbol">{</a><a id="2133" href="Prelude.Equality.html#2133" class="Bound">x</a> <a id="2135" href="Prelude.Equality.html#2135" class="Bound">y</a> <a id="2137" href="Prelude.Equality.html#2137" class="Bound">z</a> <a id="2139" class="Symbol">:</a> <a id="2141" href="Prelude.Equality.html#1887" class="Bound">A</a><a id="2142" class="Symbol">}</a> <a id="2144" class="Symbol">→</a> <a id="2146" href="Prelude.Equality.html#2133" class="Bound">x</a> <a id="2148" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2150" href="Prelude.Equality.html#2135" class="Bound">y</a> <a id="2152" class="Symbol">→</a> <a id="2154" href="Prelude.Equality.html#2135" class="Bound">y</a> <a id="2156" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2158" href="Prelude.Equality.html#2137" class="Bound">z</a> <a id="2160" class="Symbol">→</a> <a id="2162" href="Prelude.Equality.html#2133" class="Bound">x</a> <a id="2164" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2166" href="Prelude.Equality.html#2137" class="Bound">z</a>
 <a id="2169" href="Prelude.Equality.html#2122" class="Function">≡-trans</a> <a id="2177" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2182" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2187" class="Symbol">=</a> <a id="2189" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

The only difference between `≡-symmetric` and `≡-sym` (respectively, `≡-transitive` and `≡-trans`) is that the latter has fewer explicit arguments, which is sometimes convenient.

Many proofs make abundant use of the symmetry of `_≡_`, and the following syntactic sugar can often improve the readability of such proofs.<sup>[1](Prelude.Equality.html#fn1)</sup>

<pre class="Agda">

<a id="2583" class="Keyword">module</a> <a id="hide-sym-trans"></a><a id="2590" href="Prelude.Equality.html#2590" class="Module">hide-sym-trans</a> <a id="2605" class="Symbol">{</a><a id="2606" href="Prelude.Equality.html#2606" class="Bound">𝓤</a> <a id="2608" class="Symbol">:</a> <a id="2610" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2618" class="Symbol">}</a> <a id="2620" class="Symbol">{</a><a id="2621" href="Prelude.Equality.html#2621" class="Bound">A</a> <a id="2623" class="Symbol">:</a> <a id="2625" href="Prelude.Equality.html#2606" class="Bound">𝓤</a> <a id="2627" href="Universes.html#403" class="Function Operator">̇</a> <a id="2629" class="Symbol">}</a> <a id="2631" class="Keyword">where</a>

 <a id="hide-sym-trans._⁻¹"></a><a id="2639" href="Prelude.Equality.html#2639" class="Function Operator">_⁻¹</a> <a id="2643" class="Symbol">:</a> <a id="2645" class="Symbol">{</a><a id="2646" href="Prelude.Equality.html#2646" class="Bound">x</a> <a id="2648" href="Prelude.Equality.html#2648" class="Bound">y</a> <a id="2650" class="Symbol">:</a> <a id="2652" href="Prelude.Equality.html#2621" class="Bound">A</a><a id="2653" class="Symbol">}</a> <a id="2655" class="Symbol">→</a> <a id="2657" href="Prelude.Equality.html#2646" class="Bound">x</a> <a id="2659" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2661" href="Prelude.Equality.html#2648" class="Bound">y</a> <a id="2663" class="Symbol">→</a> <a id="2665" href="Prelude.Equality.html#2648" class="Bound">y</a> <a id="2667" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2669" href="Prelude.Equality.html#2646" class="Bound">x</a>
 <a id="2672" href="Prelude.Equality.html#2672" class="Bound">p</a> <a id="2674" href="Prelude.Equality.html#2639" class="Function Operator">⁻¹</a> <a id="2677" class="Symbol">=</a> <a id="2679" href="Prelude.Equality.html#1977" class="Function">≡-sym</a> <a id="2685" href="Prelude.Equality.html#2672" class="Bound">p</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `≡-sym p` we can use the more intuitive `p ⁻¹` .

Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

 <a id="hide-sym-trans._∙_"></a><a id="2945" href="Prelude.Equality.html#2945" class="Function Operator">_∙_</a> <a id="2949" class="Symbol">:</a> <a id="2951" class="Symbol">{</a><a id="2952" href="Prelude.Equality.html#2952" class="Bound">x</a> <a id="2954" href="Prelude.Equality.html#2954" class="Bound">y</a> <a id="2956" href="Prelude.Equality.html#2956" class="Bound">z</a> <a id="2958" class="Symbol">:</a> <a id="2960" href="Prelude.Equality.html#2621" class="Bound">A</a><a id="2961" class="Symbol">}</a> <a id="2963" class="Symbol">→</a> <a id="2965" href="Prelude.Equality.html#2952" class="Bound">x</a> <a id="2967" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2969" href="Prelude.Equality.html#2954" class="Bound">y</a> <a id="2971" class="Symbol">→</a> <a id="2973" href="Prelude.Equality.html#2954" class="Bound">y</a> <a id="2975" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2977" href="Prelude.Equality.html#2956" class="Bound">z</a> <a id="2979" class="Symbol">→</a> <a id="2981" href="Prelude.Equality.html#2952" class="Bound">x</a> <a id="2983" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2985" href="Prelude.Equality.html#2956" class="Bound">z</a>
 <a id="2988" href="Prelude.Equality.html#2988" class="Bound">p</a> <a id="2990" href="Prelude.Equality.html#2945" class="Function Operator">∙</a> <a id="2992" href="Prelude.Equality.html#2992" class="Bound">q</a> <a id="2994" class="Symbol">=</a> <a id="2996" href="Prelude.Equality.html#2122" class="Function">≡-trans</a> <a id="3004" href="Prelude.Equality.html#2988" class="Bound">p</a> <a id="3006" href="Prelude.Equality.html#2992" class="Bound">q</a>

</pre>

As usual, we import the original definitions from the [Type Topology][] library.

<pre class="Agda">

<a id="3117" class="Keyword">open</a> <a id="3122" class="Keyword">import</a> <a id="3129" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="3138" class="Keyword">using</a> <a id="3144" class="Symbol">(</a><a id="3145" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="3148" class="Symbol">;</a> <a id="3150" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="3153" class="Symbol">)</a> <a id="3155" class="Keyword">public</a>

</pre>

#### <a id="transport">Transport</a>

Alonzo Church characterized equality by declaring two things equal iff no property (predicate) can distinguish them.<sup>[3](Prelude.Equality.html#fn3)</sup>  In other terms, `x` and `y` are equal iff for all `P` we have `P x → P y`.  One direction of this implication is sometimes called *substitution* or *transport* or *transport along an identity*.  It asserts that *if* two objects are equal and one of them satisfies a predicate, then so does the other. A type representing this notion is defined in the `MGS-MLTT` module of the [Type Topology][] library as follows.<sup>[2](Preliminaries.Equality.html#fn2)</sup>

<pre class="Agda">

<a id="3848" class="Keyword">module</a> <a id="hide-transport"></a><a id="3855" href="Prelude.Equality.html#3855" class="Module">hide-transport</a> <a id="3870" class="Symbol">{</a><a id="3871" href="Prelude.Equality.html#3871" class="Bound">𝓤</a> <a id="3873" href="Prelude.Equality.html#3873" class="Bound">𝓦</a> <a id="3875" class="Symbol">:</a> <a id="3877" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3885" class="Symbol">}</a> <a id="3887" class="Keyword">where</a>

 <a id="hide-transport.𝑖𝑑"></a><a id="3895" href="Prelude.Equality.html#3895" class="Function">𝑖𝑑</a> <a id="3898" class="Symbol">:</a> <a id="3900" class="Symbol">{</a><a id="3901" href="Prelude.Equality.html#3901" class="Bound">𝓧</a> <a id="3903" class="Symbol">:</a> <a id="3905" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3913" class="Symbol">}</a> <a id="3915" class="Symbol">(</a><a id="3916" href="Prelude.Equality.html#3916" class="Bound">X</a> <a id="3918" class="Symbol">:</a> <a id="3920" href="Prelude.Equality.html#3901" class="Bound">𝓧</a> <a id="3922" href="Universes.html#403" class="Function Operator">̇</a> <a id="3924" class="Symbol">)</a> <a id="3926" class="Symbol">→</a> <a id="3928" href="Prelude.Equality.html#3916" class="Bound">X</a> <a id="3930" class="Symbol">→</a> <a id="3932" href="Prelude.Equality.html#3916" class="Bound">X</a>
 <a id="3935" href="Prelude.Equality.html#3895" class="Function">𝑖𝑑</a> <a id="3938" href="Prelude.Equality.html#3938" class="Bound">X</a> <a id="3940" class="Symbol">=</a> <a id="3942" class="Symbol">λ</a> <a id="3944" href="Prelude.Equality.html#3944" class="Bound">x</a> <a id="3946" class="Symbol">→</a> <a id="3948" href="Prelude.Equality.html#3944" class="Bound">x</a>

 <a id="hide-transport.transport"></a><a id="3952" href="Prelude.Equality.html#3952" class="Function">transport</a> <a id="3962" class="Symbol">:</a> <a id="3964" class="Symbol">{</a><a id="3965" href="Prelude.Equality.html#3965" class="Bound">A</a> <a id="3967" class="Symbol">:</a> <a id="3969" href="Prelude.Equality.html#3871" class="Bound">𝓤</a> <a id="3971" href="Universes.html#403" class="Function Operator">̇</a> <a id="3973" class="Symbol">}</a> <a id="3975" class="Symbol">(</a><a id="3976" href="Prelude.Equality.html#3976" class="Bound">B</a> <a id="3978" class="Symbol">:</a> <a id="3980" href="Prelude.Equality.html#3965" class="Bound">A</a> <a id="3982" class="Symbol">→</a> <a id="3984" href="Prelude.Equality.html#3873" class="Bound">𝓦</a> <a id="3986" href="Universes.html#403" class="Function Operator">̇</a> <a id="3988" class="Symbol">)</a> <a id="3990" class="Symbol">{</a><a id="3991" href="Prelude.Equality.html#3991" class="Bound">x</a> <a id="3993" href="Prelude.Equality.html#3993" class="Bound">y</a> <a id="3995" class="Symbol">:</a> <a id="3997" href="Prelude.Equality.html#3965" class="Bound">A</a><a id="3998" class="Symbol">}</a> <a id="4000" class="Symbol">→</a> <a id="4002" href="Prelude.Equality.html#3991" class="Bound">x</a> <a id="4004" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4006" href="Prelude.Equality.html#3993" class="Bound">y</a> <a id="4008" class="Symbol">→</a> <a id="4010" href="Prelude.Equality.html#3976" class="Bound">B</a> <a id="4012" href="Prelude.Equality.html#3991" class="Bound">x</a> <a id="4014" class="Symbol">→</a> <a id="4016" href="Prelude.Equality.html#3976" class="Bound">B</a> <a id="4018" href="Prelude.Equality.html#3993" class="Bound">y</a>
 <a id="4021" href="Prelude.Equality.html#3952" class="Function">transport</a> <a id="4031" href="Prelude.Equality.html#4031" class="Bound">B</a> <a id="4033" class="Symbol">(</a><a id="4034" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4039" class="Symbol">{</a><a id="4040" class="Argument">x</a> <a id="4042" class="Symbol">=</a> <a id="4044" href="Prelude.Equality.html#4044" class="Bound">x</a><a id="4045" class="Symbol">})</a> <a id="4048" class="Symbol">=</a> <a id="4050" href="Prelude.Equality.html#3895" class="Function">𝑖𝑑</a> <a id="4053" class="Symbol">(</a><a id="4054" href="Prelude.Equality.html#4031" class="Bound">B</a> <a id="4056" href="Prelude.Equality.html#4044" class="Bound">x</a><a id="4057" class="Symbol">)</a>

<a id="4060" class="Keyword">open</a> <a id="4065" class="Keyword">import</a> <a id="4072" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="4081" class="Keyword">using</a> <a id="4087" class="Symbol">(</a><a id="4088" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="4090" class="Symbol">;</a> <a id="4092" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="4101" class="Symbol">)</a> <a id="4103" class="Keyword">public</a>

</pre>

As usual, we display `transport` in a hidden module and then imported the existing definition from [Type Topology][]. 

A function is well defined if and only if it maps equivalent elements to a single element and we often use this nature of functions in Agda proofs.  If we have a function `f : X → Y`, two elements `a b : X` of the domain, and an identity proof `p : a ≡ b`, then we obtain a proof of `f a ≡ f b` by simply applying the `ap` function like so, `ap f p : f a ≡ f b`. Escardó defines `ap` in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="4687" class="Keyword">module</a> <a id="hide-ap"></a><a id="4694" href="Prelude.Equality.html#4694" class="Module">hide-ap</a>  <a id="4703" class="Symbol">{</a><a id="4704" href="Prelude.Equality.html#4704" class="Bound">𝓤</a> <a id="4706" class="Symbol">:</a> <a id="4708" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4716" class="Symbol">}{</a><a id="4718" href="Prelude.Equality.html#4718" class="Bound">A</a> <a id="4720" class="Symbol">:</a> <a id="4722" href="Prelude.Equality.html#4704" class="Bound">𝓤</a> <a id="4724" href="Universes.html#403" class="Function Operator">̇</a><a id="4725" class="Symbol">}{</a><a id="4727" href="Prelude.Equality.html#4727" class="Bound">B</a> <a id="4729" class="Symbol">:</a> <a id="4731" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4733" href="Universes.html#403" class="Function Operator">̇</a><a id="4734" class="Symbol">}</a> <a id="4736" class="Keyword">where</a>

 <a id="hide-ap.ap"></a><a id="4744" href="Prelude.Equality.html#4744" class="Function">ap</a> <a id="4747" class="Symbol">:</a> <a id="4749" class="Symbol">(</a><a id="4750" href="Prelude.Equality.html#4750" class="Bound">f</a> <a id="4752" class="Symbol">:</a> <a id="4754" href="Prelude.Equality.html#4718" class="Bound">A</a> <a id="4756" class="Symbol">→</a> <a id="4758" href="Prelude.Equality.html#4727" class="Bound">B</a><a id="4759" class="Symbol">){</a><a id="4761" href="Prelude.Equality.html#4761" class="Bound">x</a> <a id="4763" href="Prelude.Equality.html#4763" class="Bound">y</a> <a id="4765" class="Symbol">:</a> <a id="4767" href="Prelude.Equality.html#4718" class="Bound">A</a><a id="4768" class="Symbol">}</a> <a id="4770" class="Symbol">→</a> <a id="4772" href="Prelude.Equality.html#4761" class="Bound">x</a> <a id="4774" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4776" href="Prelude.Equality.html#4763" class="Bound">y</a> <a id="4778" class="Symbol">→</a> <a id="4780" href="Prelude.Equality.html#4750" class="Bound">f</a> <a id="4782" href="Prelude.Equality.html#4761" class="Bound">x</a> <a id="4784" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4786" href="Prelude.Equality.html#4750" class="Bound">f</a> <a id="4788" href="Prelude.Equality.html#4763" class="Bound">y</a>
 <a id="4791" href="Prelude.Equality.html#4744" class="Function">ap</a> <a id="4794" href="Prelude.Equality.html#4794" class="Bound">f</a> <a id="4796" class="Symbol">{</a><a id="4797" href="Prelude.Equality.html#4797" class="Bound">x</a><a id="4798" class="Symbol">}</a> <a id="4800" href="Prelude.Equality.html#4800" class="Bound">p</a> <a id="4802" class="Symbol">=</a> <a id="4804" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="4814" class="Symbol">(λ</a> <a id="4817" href="Prelude.Equality.html#4817" class="Bound">-</a> <a id="4819" class="Symbol">→</a> <a id="4821" href="Prelude.Equality.html#4794" class="Bound">f</a> <a id="4823" href="Prelude.Equality.html#4797" class="Bound">x</a> <a id="4825" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4827" href="Prelude.Equality.html#4794" class="Bound">f</a> <a id="4829" href="Prelude.Equality.html#4817" class="Bound">-</a><a id="4830" class="Symbol">)</a> <a id="4832" href="Prelude.Equality.html#4800" class="Bound">p</a> <a id="4834" class="Symbol">(</a><a id="4835" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4840" class="Symbol">{</a><a id="4841" class="Argument">x</a> <a id="4843" class="Symbol">=</a> <a id="4845" href="Prelude.Equality.html#4794" class="Bound">f</a> <a id="4847" href="Prelude.Equality.html#4797" class="Bound">x</a><a id="4848" class="Symbol">})</a>

<a id="4852" class="Keyword">open</a> <a id="4857" class="Keyword">import</a> <a id="4864" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="4873" class="Keyword">using</a> <a id="4879" class="Symbol">(</a><a id="4880" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="4882" class="Symbol">)</a> <a id="4884" class="Keyword">public</a>

</pre>

We now define some variations of `ap` that are sometimes useful.

<pre class="Agda">

<a id="4984" class="Keyword">module</a> <a id="4991" href="Prelude.Equality.html#4991" class="Module">_</a> <a id="4993" class="Symbol">{</a><a id="4994" href="Prelude.Equality.html#4994" class="Bound">𝓤</a> <a id="4996" href="Prelude.Equality.html#4996" class="Bound">𝓦</a> <a id="4998" class="Symbol">:</a> <a id="5000" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5008" class="Symbol">}{</a><a id="5010" href="Prelude.Equality.html#5010" class="Bound">A</a> <a id="5012" class="Symbol">:</a> <a id="5014" href="Prelude.Equality.html#4994" class="Bound">𝓤</a> <a id="5016" href="Universes.html#403" class="Function Operator">̇</a><a id="5017" class="Symbol">}</a> <a id="5019" class="Keyword">where</a>

 <a id="5027" href="Prelude.Equality.html#5027" class="Function">ap-cong</a> <a id="5035" class="Symbol">:</a> <a id="5037" class="Symbol">{</a><a id="5038" href="Prelude.Equality.html#5038" class="Bound">B</a> <a id="5040" class="Symbol">:</a> <a id="5042" href="Prelude.Equality.html#4996" class="Bound">𝓦</a> <a id="5044" href="Universes.html#403" class="Function Operator">̇</a><a id="5045" class="Symbol">}{</a><a id="5047" href="Prelude.Equality.html#5047" class="Bound">f</a> <a id="5049" href="Prelude.Equality.html#5049" class="Bound">g</a> <a id="5051" class="Symbol">:</a> <a id="5053" href="Prelude.Equality.html#5010" class="Bound">A</a> <a id="5055" class="Symbol">→</a> <a id="5057" href="Prelude.Equality.html#5038" class="Bound">B</a><a id="5058" class="Symbol">}{</a><a id="5060" href="Prelude.Equality.html#5060" class="Bound">a</a> <a id="5062" href="Prelude.Equality.html#5062" class="Bound">b</a> <a id="5064" class="Symbol">:</a> <a id="5066" href="Prelude.Equality.html#5010" class="Bound">A</a><a id="5067" class="Symbol">}</a> <a id="5069" class="Symbol">→</a> <a id="5071" href="Prelude.Equality.html#5047" class="Bound">f</a> <a id="5073" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5075" href="Prelude.Equality.html#5049" class="Bound">g</a> <a id="5077" class="Symbol">→</a> <a id="5079" href="Prelude.Equality.html#5060" class="Bound">a</a> <a id="5081" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5083" href="Prelude.Equality.html#5062" class="Bound">b</a> <a id="5085" class="Symbol">→</a> <a id="5087" href="Prelude.Equality.html#5047" class="Bound">f</a> <a id="5089" href="Prelude.Equality.html#5060" class="Bound">a</a> <a id="5091" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5093" href="Prelude.Equality.html#5049" class="Bound">g</a> <a id="5095" href="Prelude.Equality.html#5062" class="Bound">b</a>
 <a id="5098" href="Prelude.Equality.html#5027" class="Function">ap-cong</a> <a id="5106" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5111" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5116" class="Symbol">=</a> <a id="5118" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

We sometimes need a version of this that works for [dependent types][], such as the following (which we borrow from the `Relation/Binary/Core.agda` module of the [Agda Standard Library][], transcribed into MHE/UALib notation of course):

<pre class="Agda">

 <a id="5389" href="Prelude.Equality.html#5389" class="Function">cong-app</a> <a id="5398" class="Symbol">:</a> <a id="5400" class="Symbol">{</a><a id="5401" href="Prelude.Equality.html#5401" class="Bound">B</a> <a id="5403" class="Symbol">:</a> <a id="5405" href="Prelude.Equality.html#5010" class="Bound">A</a> <a id="5407" class="Symbol">→</a> <a id="5409" href="Prelude.Equality.html#4996" class="Bound">𝓦</a> <a id="5411" href="Universes.html#403" class="Function Operator">̇</a><a id="5412" class="Symbol">}{</a><a id="5414" href="Prelude.Equality.html#5414" class="Bound">f</a> <a id="5416" href="Prelude.Equality.html#5416" class="Bound">g</a> <a id="5418" class="Symbol">:</a> <a id="5420" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5422" href="Prelude.Equality.html#5401" class="Bound">B</a><a id="5423" class="Symbol">}</a> <a id="5425" class="Symbol">→</a> <a id="5427" href="Prelude.Equality.html#5414" class="Bound">f</a> <a id="5429" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5431" href="Prelude.Equality.html#5416" class="Bound">g</a> <a id="5433" class="Symbol">→</a> <a id="5435" class="Symbol">∀</a> <a id="5437" href="Prelude.Equality.html#5437" class="Bound">x</a> <a id="5439" class="Symbol">→</a> <a id="5441" href="Prelude.Equality.html#5414" class="Bound">f</a> <a id="5443" href="Prelude.Equality.html#5437" class="Bound">x</a> <a id="5445" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5447" href="Prelude.Equality.html#5416" class="Bound">g</a> <a id="5449" href="Prelude.Equality.html#5437" class="Bound">x</a>
 <a id="5452" href="Prelude.Equality.html#5389" class="Function">cong-app</a> <a id="5461" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5466" class="Symbol">_</a> <a id="5468" class="Symbol">=</a> <a id="5470" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>




-------------------------------------


<sup>1</sup><span class="footnote" id="fn1"> **Unicode Hints**. In [agda2-mode][] type `⁻¹` as `\^-\^1`, type `𝑖𝑑` as `\Mii\Mid`, and type `∙` as `\.`. In general, to get information about a given unicode character (e.g., how to type it) place the cursor over that character and type `M-x describe-char` (or `M-x h d c`).</span>

<sup>2</sup><span class="footnote" id="fn2"> Alonzo Church, "A Formulation of the Simple Theory of Types," *Journal of Symbolic Logic*, (2)5:56--68, 1940 [JSOR link](http://www.jstor.org/stable/2266170). See also [this section](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#70309) of Escardó's [HoTT/UF in Agda notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html) for a discussion of transport; cf. [HoTT-Agda's definition](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda).<span>

<p></p>
<p></p>


[← Prelude.Preliminaries ](Prelude.Preliminaries.html)
<span style="float:right;">[Prelude.Extensionality →](Prelude.Extensionality.html)</span>

{% include UALib.Links.md %}


<!-- NO LONGER USED

#### <a id="≡-intro-and-≡-elim-for-nondependent-pairs">≡-intro and ≡-elim for nondependent pairs</a>

We conclude the Equality module with some occasionally useful introduction and elimination rules for the equality relation on (nondependent) pair types.

 ≡-elim-left : {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇} → (A₁ , B₁) ≡ (A₂ , B₂) → A₁ ≡ A₂
 ≡-elim-left e = ap fst e


 ≡-elim-right : {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇} → (A₁ , B₁) ≡ (A₂ , B₂) → B₁ ≡ B₂
 ≡-elim-right e = ap snd e


 ≡-×-intro : {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇} → A₁ ≡ A₂ → B₁ ≡ B₂ → (A₁ , B₁) ≡ (A₂ , B₂)
 ≡-×-intro refl refl = refl


 ≡-×-int : {A : 𝓤 ̇}{B : 𝓦 ̇}{a x : A}{b y : B} → a ≡ x → b ≡ y → (a , b) ≡ (x , y)
 ≡-×-int refl refl = refl

-->
