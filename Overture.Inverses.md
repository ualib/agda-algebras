---
layout: default
title : Overture.Inverses module
date : 2021-01-12
author: [agda-algebras development team][]
---

### Inverses

This is the [Overture.Inverses][] module of the [agda-algebras][] library.

<pre class="Agda">

<a id="224" class="Symbol">{-#</a> <a id="228" class="Keyword">OPTIONS</a> <a id="236" class="Pragma">--without-K</a> <a id="248" class="Pragma">--exact-split</a> <a id="262" class="Pragma">--safe</a> <a id="269" class="Symbol">#-}</a>


<a id="275" class="Keyword">module</a> <a id="282" href="Overture.Inverses.html" class="Module">Overture.Inverses</a> <a id="300" class="Keyword">where</a>

<a id="307" class="Comment">-- Imports from Agda and the Agda Standard Library</a>
<a id="358" class="Keyword">open</a> <a id="363" class="Keyword">import</a> <a id="370" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>              <a id="398" class="Keyword">using</a> <a id="404" class="Symbol">(</a> <a id="406" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="410" class="Symbol">;</a> <a id="412" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="417" class="Symbol">;</a> <a id="419" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="425" class="Symbol">)</a> <a id="427" class="Keyword">renaming</a> <a id="436" class="Symbol">(</a> <a id="438" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="442" class="Symbol">to</a> <a id="445" class="Primitive">Type</a> <a id="450" class="Symbol">)</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="Data.Product.html" class="Module">Data.Product</a>                <a id="492" class="Keyword">using</a> <a id="498" class="Symbol">(</a> <a id="500" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="504" class="Symbol">;</a> <a id="506" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="510" class="Symbol">;</a> <a id="512" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="514" class="Symbol">)</a>
<a id="516" class="Keyword">open</a> <a id="521" class="Keyword">import</a> <a id="528" href="Function.Base.html" class="Module">Function.Base</a>               <a id="556" class="Keyword">using</a> <a id="562" class="Symbol">(</a> <a id="564" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="568" class="Symbol">)</a>
<a id="570" class="Keyword">open</a> <a id="575" class="Keyword">import</a> <a id="582" href="Function.Definitions.html" class="Module">Function.Definitions</a>        <a id="610" class="Keyword">using</a> <a id="616" class="Symbol">(</a> <a id="618" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="628" class="Symbol">)</a>
<a id="630" class="Keyword">open</a> <a id="635" class="Keyword">import</a> <a id="642" href="Function.Bundles.html" class="Module">Function.Bundles</a>            <a id="670" class="Keyword">using</a> <a id="676" class="Symbol">(</a> <a id="678" href="Function.Bundles.html#8289" class="Function Operator">_↣_</a> <a id="682" class="Symbol">;</a> <a id="684" href="Function.Bundles.html#9178" class="Function">mk↣</a> <a id="688" class="Symbol">)</a>
<a id="690" class="Keyword">open</a> <a id="695" class="Keyword">import</a> <a id="702" href="Function.Construct.Identity.html" class="Module">Function.Construct.Identity</a> <a id="730" class="Keyword">using</a> <a id="736" class="Symbol">(</a> <a id="738" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="743" class="Symbol">)</a>
<a id="745" class="Keyword">open</a> <a id="750" class="Keyword">import</a> <a id="757" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                                        <a id="835" class="Keyword">using</a> <a id="841" class="Symbol">(</a> <a id="843" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="847" class="Symbol">;</a> <a id="849" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="854" class="Symbol">)</a>

<a id="857" class="Comment">-- Imports from agda-algebras</a>
<a id="887" class="Keyword">open</a> <a id="892" class="Keyword">import</a> <a id="899" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="922" class="Keyword">using</a> <a id="928" class="Symbol">(</a> <a id="930" href="Overture.Preliminaries.html#4859" class="Function Operator">_⁻¹</a> <a id="934" class="Symbol">)</a>

</pre>

We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

<pre class="Agda">

<a id="1069" class="Keyword">private</a> <a id="1077" class="Keyword">variable</a> <a id="1086" href="Overture.Inverses.html#1086" class="Generalizable">α</a> <a id="1088" href="Overture.Inverses.html#1088" class="Generalizable">β</a> <a id="1090" href="Overture.Inverses.html#1090" class="Generalizable">γ</a> <a id="1092" class="Symbol">:</a> <a id="1094" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="1101" class="Keyword">module</a> <a id="1108" href="Overture.Inverses.html#1108" class="Module">_</a> <a id="1110" class="Symbol">{</a><a id="1111" href="Overture.Inverses.html#1111" class="Bound">A</a> <a id="1113" class="Symbol">:</a> <a id="1115" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="1120" href="Overture.Inverses.html#1086" class="Generalizable">α</a> <a id="1122" class="Symbol">}{</a><a id="1124" href="Overture.Inverses.html#1124" class="Bound">B</a> <a id="1126" class="Symbol">:</a> <a id="1128" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="1133" href="Overture.Inverses.html#1088" class="Generalizable">β</a> <a id="1135" class="Symbol">}</a> <a id="1137" class="Keyword">where</a>

 <a id="1145" class="Keyword">data</a> <a id="1150" href="Overture.Inverses.html#1150" class="Datatype Operator">Image_∋_</a> <a id="1159" class="Symbol">(</a><a id="1160" href="Overture.Inverses.html#1160" class="Bound">f</a> <a id="1162" class="Symbol">:</a> <a id="1164" href="Overture.Inverses.html#1111" class="Bound">A</a> <a id="1166" class="Symbol">→</a> <a id="1168" href="Overture.Inverses.html#1124" class="Bound">B</a><a id="1169" class="Symbol">)</a> <a id="1171" class="Symbol">:</a> <a id="1173" href="Overture.Inverses.html#1124" class="Bound">B</a> <a id="1175" class="Symbol">→</a> <a id="1177" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="1182" class="Symbol">(</a><a id="1183" href="Overture.Inverses.html#1120" class="Bound">α</a> <a id="1185" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1187" href="Overture.Inverses.html#1133" class="Bound">β</a><a id="1188" class="Symbol">)</a> <a id="1190" class="Keyword">where</a>
  <a id="1198" href="Overture.Inverses.html#1198" class="InductiveConstructor">eq</a> <a id="1201" class="Symbol">:</a> <a id="1203" class="Symbol">{</a><a id="1204" href="Overture.Inverses.html#1204" class="Bound">b</a> <a id="1206" class="Symbol">:</a> <a id="1208" href="Overture.Inverses.html#1124" class="Bound">B</a><a id="1209" class="Symbol">}</a> <a id="1211" class="Symbol">→</a> <a id="1213" class="Symbol">(</a><a id="1214" href="Overture.Inverses.html#1214" class="Bound">a</a> <a id="1216" class="Symbol">:</a> <a id="1218" href="Overture.Inverses.html#1111" class="Bound">A</a><a id="1219" class="Symbol">)</a> <a id="1221" class="Symbol">→</a> <a id="1223" href="Overture.Inverses.html#1204" class="Bound">b</a> <a id="1225" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="1227" href="Overture.Inverses.html#1160" class="Bound">f</a> <a id="1229" href="Overture.Inverses.html#1214" class="Bound">a</a> <a id="1231" class="Symbol">→</a> <a id="1233" href="Overture.Inverses.html#1150" class="Datatype Operator">Image</a> <a id="1239" href="Overture.Inverses.html#1160" class="Bound">f</a> <a id="1241" href="Overture.Inverses.html#1150" class="Datatype Operator">∋</a> <a id="1243" href="Overture.Inverses.html#1204" class="Bound">b</a>

</pre>

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

<pre class="Agda">

 <a id="1750" href="Overture.Inverses.html#1750" class="Function">Inv</a> <a id="1754" class="Symbol">:</a> <a id="1756" class="Symbol">(</a><a id="1757" href="Overture.Inverses.html#1757" class="Bound">f</a> <a id="1759" class="Symbol">:</a> <a id="1761" href="Overture.Inverses.html#1111" class="Bound">A</a> <a id="1763" class="Symbol">→</a> <a id="1765" href="Overture.Inverses.html#1124" class="Bound">B</a><a id="1766" class="Symbol">){</a><a id="1768" href="Overture.Inverses.html#1768" class="Bound">b</a> <a id="1770" class="Symbol">:</a> <a id="1772" href="Overture.Inverses.html#1124" class="Bound">B</a><a id="1773" class="Symbol">}</a> <a id="1775" class="Symbol">→</a> <a id="1777" href="Overture.Inverses.html#1150" class="Datatype Operator">Image</a> <a id="1783" href="Overture.Inverses.html#1757" class="Bound">f</a> <a id="1785" href="Overture.Inverses.html#1150" class="Datatype Operator">∋</a> <a id="1787" href="Overture.Inverses.html#1768" class="Bound">b</a>  <a id="1790" class="Symbol">→</a>  <a id="1793" href="Overture.Inverses.html#1111" class="Bound">A</a>
 <a id="1796" href="Overture.Inverses.html#1750" class="Function">Inv</a> <a id="1800" href="Overture.Inverses.html#1800" class="Bound">f</a> <a id="1802" class="Symbol">(</a><a id="1803" href="Overture.Inverses.html#1198" class="InductiveConstructor">eq</a> <a id="1806" href="Overture.Inverses.html#1806" class="Bound">a</a> <a id="1808" class="Symbol">_)</a> <a id="1811" class="Symbol">=</a> <a id="1813" href="Overture.Inverses.html#1806" class="Bound">a</a>

</pre>

We can prove that `Inv f` is the *right-inverse* of `f`, as follows.

<pre class="Agda">

 <a id="1913" href="Overture.Inverses.html#1913" class="Function">InvIsInv</a> <a id="1922" class="Symbol">:</a> <a id="1924" class="Symbol">(</a><a id="1925" href="Overture.Inverses.html#1925" class="Bound">f</a> <a id="1927" class="Symbol">:</a> <a id="1929" href="Overture.Inverses.html#1111" class="Bound">A</a> <a id="1931" class="Symbol">→</a> <a id="1933" href="Overture.Inverses.html#1124" class="Bound">B</a><a id="1934" class="Symbol">){</a><a id="1936" href="Overture.Inverses.html#1936" class="Bound">b</a> <a id="1938" class="Symbol">:</a> <a id="1940" href="Overture.Inverses.html#1124" class="Bound">B</a><a id="1941" class="Symbol">}(</a><a id="1943" href="Overture.Inverses.html#1943" class="Bound">q</a> <a id="1945" class="Symbol">:</a> <a id="1947" href="Overture.Inverses.html#1150" class="Datatype Operator">Image</a> <a id="1953" href="Overture.Inverses.html#1925" class="Bound">f</a> <a id="1955" href="Overture.Inverses.html#1150" class="Datatype Operator">∋</a> <a id="1957" href="Overture.Inverses.html#1936" class="Bound">b</a><a id="1958" class="Symbol">)</a> <a id="1960" class="Symbol">→</a> <a id="1962" href="Overture.Inverses.html#1925" class="Bound">f</a><a id="1963" class="Symbol">(</a><a id="1964" href="Overture.Inverses.html#1750" class="Function">Inv</a> <a id="1968" href="Overture.Inverses.html#1925" class="Bound">f</a> <a id="1970" href="Overture.Inverses.html#1943" class="Bound">q</a><a id="1971" class="Symbol">)</a> <a id="1973" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="1975" href="Overture.Inverses.html#1936" class="Bound">b</a>
 <a id="1978" href="Overture.Inverses.html#1913" class="Function">InvIsInv</a> <a id="1987" href="Overture.Inverses.html#1987" class="Bound">f</a> <a id="1989" class="Symbol">(</a><a id="1990" href="Overture.Inverses.html#1198" class="InductiveConstructor">eq</a> <a id="1993" class="Symbol">_</a> <a id="1995" href="Overture.Inverses.html#1995" class="Bound">p</a><a id="1996" class="Symbol">)</a> <a id="1998" class="Symbol">=</a> <a id="2000" href="Overture.Inverses.html#1995" class="Bound">p</a> <a id="2002" href="Overture.Preliminaries.html#4859" class="Function Operator">⁻¹</a>

</pre>


#### <a id="injective-functions">Injective functions</a>

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following type manifests this property.

<pre class="Agda">

<a id="2289" class="Keyword">module</a> <a id="2296" href="Overture.Inverses.html#2296" class="Module">_</a> <a id="2298" class="Symbol">{</a><a id="2299" href="Overture.Inverses.html#2299" class="Bound">A</a> <a id="2301" class="Symbol">:</a> <a id="2303" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="2308" href="Overture.Inverses.html#1086" class="Generalizable">α</a><a id="2309" class="Symbol">}{</a><a id="2311" href="Overture.Inverses.html#2311" class="Bound">B</a> <a id="2313" class="Symbol">:</a> <a id="2315" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="2320" href="Overture.Inverses.html#1088" class="Generalizable">β</a><a id="2321" class="Symbol">}</a> <a id="2323" class="Keyword">where</a>

 <a id="2331" href="Overture.Inverses.html#2331" class="Function">IsInjective</a> <a id="2343" class="Symbol">:</a> <a id="2345" class="Symbol">(</a><a id="2346" href="Overture.Inverses.html#2299" class="Bound">A</a> <a id="2348" class="Symbol">→</a> <a id="2350" href="Overture.Inverses.html#2311" class="Bound">B</a><a id="2351" class="Symbol">)</a> <a id="2353" class="Symbol">→</a> <a id="2355" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="2360" class="Symbol">(</a><a id="2361" href="Overture.Inverses.html#2308" class="Bound">α</a> <a id="2363" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2365" href="Overture.Inverses.html#2320" class="Bound">β</a><a id="2366" class="Symbol">)</a>
 <a id="2369" href="Overture.Inverses.html#2331" class="Function">IsInjective</a> <a id="2381" href="Overture.Inverses.html#2381" class="Bound">f</a> <a id="2383" class="Symbol">=</a> <a id="2385" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="2395" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="2399" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="2403" href="Overture.Inverses.html#2381" class="Bound">f</a>

</pre>

Before moving on to discuss surjective functions, let us prove (the obvious facts) that the identity map is injective and that the composition of injectives is injective.

<pre class="Agda">

<a id="id-is-injective"></a><a id="2604" href="Overture.Inverses.html#2604" class="Function">id-is-injective</a> <a id="2620" class="Symbol">:</a> <a id="2622" class="Symbol">{</a><a id="2623" href="Overture.Inverses.html#2623" class="Bound">A</a> <a id="2625" class="Symbol">:</a> <a id="2627" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="2632" href="Overture.Inverses.html#1086" class="Generalizable">α</a><a id="2633" class="Symbol">}</a> <a id="2635" class="Symbol">→</a> <a id="2637" href="Overture.Inverses.html#2623" class="Bound">A</a> <a id="2639" href="Function.Bundles.html#8289" class="Function Operator">↣</a> <a id="2641" href="Overture.Inverses.html#2623" class="Bound">A</a>
<a id="2643" href="Overture.Inverses.html#2604" class="Function">id-is-injective</a> <a id="2659" class="Symbol">{</a><a id="2660" class="Argument">A</a> <a id="2662" class="Symbol">=</a> <a id="2664" href="Overture.Inverses.html#2664" class="Bound">A</a><a id="2665" class="Symbol">}</a> <a id="2667" class="Symbol">=</a> <a id="2669" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="2674" href="Overture.Inverses.html#2664" class="Bound">A</a>

<a id="∘-injective"></a><a id="2677" href="Overture.Inverses.html#2677" class="Function">∘-injective</a> <a id="2689" class="Symbol">:</a> <a id="2691" class="Symbol">{</a><a id="2692" href="Overture.Inverses.html#2692" class="Bound">A</a> <a id="2694" class="Symbol">:</a> <a id="2696" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="2701" href="Overture.Inverses.html#1086" class="Generalizable">α</a><a id="2702" class="Symbol">}{</a><a id="2704" href="Overture.Inverses.html#2704" class="Bound">B</a> <a id="2706" class="Symbol">:</a> <a id="2708" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="2713" href="Overture.Inverses.html#1088" class="Generalizable">β</a><a id="2714" class="Symbol">}{</a><a id="2716" href="Overture.Inverses.html#2716" class="Bound">C</a> <a id="2718" class="Symbol">:</a> <a id="2720" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="2725" href="Overture.Inverses.html#1090" class="Generalizable">γ</a><a id="2726" class="Symbol">}{</a><a id="2728" href="Overture.Inverses.html#2728" class="Bound">f</a> <a id="2730" class="Symbol">:</a> <a id="2732" href="Overture.Inverses.html#2692" class="Bound">A</a> <a id="2734" class="Symbol">→</a> <a id="2736" href="Overture.Inverses.html#2704" class="Bound">B</a><a id="2737" class="Symbol">}{</a><a id="2739" href="Overture.Inverses.html#2739" class="Bound">g</a> <a id="2741" class="Symbol">:</a> <a id="2743" href="Overture.Inverses.html#2704" class="Bound">B</a> <a id="2745" class="Symbol">→</a> <a id="2747" href="Overture.Inverses.html#2716" class="Bound">C</a><a id="2748" class="Symbol">}</a>
 <a id="2751" class="Symbol">→</a>            <a id="2764" href="Overture.Inverses.html#2331" class="Function">IsInjective</a> <a id="2776" href="Overture.Inverses.html#2728" class="Bound">f</a> <a id="2778" class="Symbol">→</a> <a id="2780" href="Overture.Inverses.html#2331" class="Function">IsInjective</a> <a id="2792" href="Overture.Inverses.html#2739" class="Bound">g</a> <a id="2794" class="Symbol">→</a> <a id="2796" href="Overture.Inverses.html#2331" class="Function">IsInjective</a> <a id="2808" class="Symbol">(</a><a id="2809" href="Overture.Inverses.html#2739" class="Bound">g</a> <a id="2811" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2813" href="Overture.Inverses.html#2728" class="Bound">f</a><a id="2814" class="Symbol">)</a>
<a id="2816" href="Overture.Inverses.html#2677" class="Function">∘-injective</a> <a id="2828" href="Overture.Inverses.html#2828" class="Bound">finj</a> <a id="2833" href="Overture.Inverses.html#2833" class="Bound">ginj</a> <a id="2838" class="Symbol">=</a> <a id="2840" class="Symbol">λ</a> <a id="2842" href="Overture.Inverses.html#2842" class="Bound">z</a> <a id="2844" class="Symbol">→</a> <a id="2846" href="Overture.Inverses.html#2828" class="Bound">finj</a> <a id="2851" class="Symbol">(</a><a id="2852" href="Overture.Inverses.html#2833" class="Bound">ginj</a> <a id="2857" href="Overture.Inverses.html#2842" class="Bound">z</a><a id="2858" class="Symbol">)</a>

</pre>


#### <a id="epics">Surjective functions</a>

A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types manifest this notion.

<pre class="Agda">

<a id="3165" class="Keyword">module</a> <a id="3172" href="Overture.Inverses.html#3172" class="Module">_</a> <a id="3174" class="Symbol">{</a><a id="3175" href="Overture.Inverses.html#3175" class="Bound">A</a> <a id="3177" class="Symbol">:</a> <a id="3179" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="3184" href="Overture.Inverses.html#1086" class="Generalizable">α</a><a id="3185" class="Symbol">}{</a><a id="3187" href="Overture.Inverses.html#3187" class="Bound">B</a> <a id="3189" class="Symbol">:</a> <a id="3191" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="3196" href="Overture.Inverses.html#1088" class="Generalizable">β</a><a id="3197" class="Symbol">}</a> <a id="3199" class="Keyword">where</a>
 <a id="3206" href="Overture.Inverses.html#3206" class="Function">IsSurjective</a> <a id="3219" class="Symbol">:</a> <a id="3221" class="Symbol">(</a><a id="3222" href="Overture.Inverses.html#3175" class="Bound">A</a> <a id="3224" class="Symbol">→</a> <a id="3226" href="Overture.Inverses.html#3187" class="Bound">B</a><a id="3227" class="Symbol">)</a> <a id="3229" class="Symbol">→</a>  <a id="3232" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="3237" class="Symbol">(</a><a id="3238" href="Overture.Inverses.html#3184" class="Bound">α</a> <a id="3240" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3242" href="Overture.Inverses.html#3196" class="Bound">β</a><a id="3243" class="Symbol">)</a>
 <a id="3246" href="Overture.Inverses.html#3206" class="Function">IsSurjective</a> <a id="3259" href="Overture.Inverses.html#3259" class="Bound">f</a> <a id="3261" class="Symbol">=</a> <a id="3263" class="Symbol">∀</a> <a id="3265" href="Overture.Inverses.html#3265" class="Bound">y</a> <a id="3267" class="Symbol">→</a> <a id="3269" href="Overture.Inverses.html#1150" class="Datatype Operator">Image</a> <a id="3275" href="Overture.Inverses.html#3259" class="Bound">f</a> <a id="3277" href="Overture.Inverses.html#1150" class="Datatype Operator">∋</a> <a id="3279" href="Overture.Inverses.html#3265" class="Bound">y</a>

 <a id="3283" href="Overture.Inverses.html#3283" class="Function">Surjective</a> <a id="3294" class="Symbol">:</a> <a id="3296" href="Overture.Inverses.html#445" class="Primitive">Type</a> <a id="3301" class="Symbol">(</a><a id="3302" href="Overture.Inverses.html#3184" class="Bound">α</a> <a id="3304" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3306" href="Overture.Inverses.html#3196" class="Bound">β</a><a id="3307" class="Symbol">)</a>
 <a id="3310" href="Overture.Inverses.html#3283" class="Function">Surjective</a> <a id="3321" class="Symbol">=</a> <a id="3323" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="3325" class="Symbol">(</a><a id="3326" href="Overture.Inverses.html#3175" class="Bound">A</a> <a id="3328" class="Symbol">→</a> <a id="3330" href="Overture.Inverses.html#3187" class="Bound">B</a><a id="3331" class="Symbol">)</a> <a id="3333" href="Overture.Inverses.html#3206" class="Function">IsSurjective</a>

</pre>

With the next definition, we can represent a *right-inverse* of a surjective function.

<pre class="Agda">

 <a id="3462" href="Overture.Inverses.html#3462" class="Function">SurjInv</a> <a id="3470" class="Symbol">:</a> <a id="3472" class="Symbol">(</a><a id="3473" href="Overture.Inverses.html#3473" class="Bound">f</a> <a id="3475" class="Symbol">:</a> <a id="3477" href="Overture.Inverses.html#3175" class="Bound">A</a> <a id="3479" class="Symbol">→</a> <a id="3481" href="Overture.Inverses.html#3187" class="Bound">B</a><a id="3482" class="Symbol">)</a> <a id="3484" class="Symbol">→</a> <a id="3486" href="Overture.Inverses.html#3206" class="Function">IsSurjective</a> <a id="3499" href="Overture.Inverses.html#3473" class="Bound">f</a> <a id="3501" class="Symbol">→</a> <a id="3503" href="Overture.Inverses.html#3187" class="Bound">B</a> <a id="3505" class="Symbol">→</a> <a id="3507" href="Overture.Inverses.html#3175" class="Bound">A</a>
 <a id="3510" href="Overture.Inverses.html#3462" class="Function">SurjInv</a> <a id="3518" href="Overture.Inverses.html#3518" class="Bound">f</a> <a id="3520" href="Overture.Inverses.html#3520" class="Bound">fE</a> <a id="3523" href="Overture.Inverses.html#3523" class="Bound">b</a> <a id="3525" class="Symbol">=</a> <a id="3527" href="Overture.Inverses.html#1750" class="Function">Inv</a> <a id="3531" href="Overture.Inverses.html#3518" class="Bound">f</a> <a id="3533" class="Symbol">(</a><a id="3534" href="Overture.Inverses.html#3520" class="Bound">fE</a> <a id="3537" href="Overture.Inverses.html#3523" class="Bound">b</a><a id="3538" class="Symbol">)</a>

</pre>

Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.  Later, we will prove that this does indeed give the right-inverse, but we postpone the proof since it requires function extensionality, a concept we take up in the [Relations.Extensionality][] module.



--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


