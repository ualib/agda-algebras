---
layout: default
title : Overture.Inverses module
date : 2021-01-12
author: [agda-algebras development team][]
---

### <a id="inverses">Inverses</a>

This is the [Overture.Inverses][] module of the [agda-algebras][] library.

<pre class="Agda">

<a id="245" class="Symbol">{-#</a> <a id="249" class="Keyword">OPTIONS</a> <a id="257" class="Pragma">--without-K</a> <a id="269" class="Pragma">--exact-split</a> <a id="283" class="Pragma">--safe</a> <a id="290" class="Symbol">#-}</a>


<a id="296" class="Keyword">module</a> <a id="303" href="Overture.Inverses.html" class="Module">Overture.Inverses</a> <a id="321" class="Keyword">where</a>

<a id="328" class="Comment">-- Imports from Agda and the Agda Standard Library</a>
<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>              <a id="419" class="Keyword">using</a> <a id="425" class="Symbol">(</a> <a id="427" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="431" class="Symbol">;</a> <a id="433" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="438" class="Symbol">;</a> <a id="440" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="446" class="Symbol">)</a> <a id="448" class="Keyword">renaming</a> <a id="457" class="Symbol">(</a> <a id="459" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="463" class="Symbol">to</a> <a id="466" class="Primitive">Type</a> <a id="471" class="Symbol">)</a>
<a id="473" class="Keyword">open</a> <a id="478" class="Keyword">import</a> <a id="485" href="Data.Product.html" class="Module">Data.Product</a>                <a id="513" class="Keyword">using</a> <a id="519" class="Symbol">(</a> <a id="521" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="525" class="Symbol">;</a> <a id="527" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="531" class="Symbol">;</a> <a id="533" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="535" class="Symbol">)</a>
<a id="537" class="Keyword">open</a> <a id="542" class="Keyword">import</a> <a id="549" href="Function.Base.html" class="Module">Function.Base</a>               <a id="577" class="Keyword">using</a> <a id="583" class="Symbol">(</a> <a id="585" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="589" class="Symbol">)</a>
<a id="591" class="Keyword">open</a> <a id="596" class="Keyword">import</a> <a id="603" href="Function.Definitions.html" class="Module">Function.Definitions</a>        <a id="631" class="Keyword">using</a> <a id="637" class="Symbol">(</a> <a id="639" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="649" class="Symbol">)</a>
<a id="651" class="Keyword">open</a> <a id="656" class="Keyword">import</a> <a id="663" href="Function.Bundles.html" class="Module">Function.Bundles</a>            <a id="691" class="Keyword">using</a> <a id="697" class="Symbol">(</a> <a id="699" href="Function.Bundles.html#8289" class="Function Operator">_↣_</a> <a id="703" class="Symbol">;</a> <a id="705" href="Function.Bundles.html#9178" class="Function">mk↣</a> <a id="709" class="Symbol">)</a>
<a id="711" class="Keyword">open</a> <a id="716" class="Keyword">import</a> <a id="723" href="Function.Construct.Identity.html" class="Module">Function.Construct.Identity</a> <a id="751" class="Keyword">using</a> <a id="757" class="Symbol">(</a> <a id="759" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="764" class="Symbol">)</a>
<a id="766" class="Keyword">open</a> <a id="771" class="Keyword">import</a> <a id="778" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                                        <a id="856" class="Keyword">using</a> <a id="862" class="Symbol">(</a> <a id="864" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="868" class="Symbol">;</a> <a id="870" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="875" class="Symbol">)</a>

<a id="878" class="Comment">-- Imports from agda-algebras</a>
<a id="908" class="Keyword">open</a> <a id="913" class="Keyword">import</a> <a id="920" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="943" class="Keyword">using</a> <a id="949" class="Symbol">(</a> <a id="951" href="Overture.Preliminaries.html#4949" class="Function Operator">_⁻¹</a> <a id="955" class="Symbol">)</a>

</pre>

We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

<pre class="Agda">

<a id="1090" class="Keyword">private</a> <a id="1098" class="Keyword">variable</a> <a id="1107" href="Overture.Inverses.html#1107" class="Generalizable">α</a> <a id="1109" href="Overture.Inverses.html#1109" class="Generalizable">β</a> <a id="1111" href="Overture.Inverses.html#1111" class="Generalizable">γ</a> <a id="1113" class="Symbol">:</a> <a id="1115" href="Agda.Primitive.html#597" class="Postulate">Level</a>

<a id="1122" class="Keyword">module</a> <a id="1129" href="Overture.Inverses.html#1129" class="Module">_</a> <a id="1131" class="Symbol">{</a><a id="1132" href="Overture.Inverses.html#1132" class="Bound">A</a> <a id="1134" class="Symbol">:</a> <a id="1136" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="1141" href="Overture.Inverses.html#1107" class="Generalizable">α</a> <a id="1143" class="Symbol">}{</a><a id="1145" href="Overture.Inverses.html#1145" class="Bound">B</a> <a id="1147" class="Symbol">:</a> <a id="1149" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="1154" href="Overture.Inverses.html#1109" class="Generalizable">β</a> <a id="1156" class="Symbol">}</a> <a id="1158" class="Keyword">where</a>

 <a id="1166" class="Keyword">data</a> <a id="1171" href="Overture.Inverses.html#1171" class="Datatype Operator">Image_∋_</a> <a id="1180" class="Symbol">(</a><a id="1181" href="Overture.Inverses.html#1181" class="Bound">f</a> <a id="1183" class="Symbol">:</a> <a id="1185" href="Overture.Inverses.html#1132" class="Bound">A</a> <a id="1187" class="Symbol">→</a> <a id="1189" href="Overture.Inverses.html#1145" class="Bound">B</a><a id="1190" class="Symbol">)</a> <a id="1192" class="Symbol">:</a> <a id="1194" href="Overture.Inverses.html#1145" class="Bound">B</a> <a id="1196" class="Symbol">→</a> <a id="1198" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="1203" class="Symbol">(</a><a id="1204" href="Overture.Inverses.html#1141" class="Bound">α</a> <a id="1206" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="1208" href="Overture.Inverses.html#1154" class="Bound">β</a><a id="1209" class="Symbol">)</a> <a id="1211" class="Keyword">where</a>
  <a id="1219" href="Overture.Inverses.html#1219" class="InductiveConstructor">eq</a> <a id="1222" class="Symbol">:</a> <a id="1224" class="Symbol">{</a><a id="1225" href="Overture.Inverses.html#1225" class="Bound">b</a> <a id="1227" class="Symbol">:</a> <a id="1229" href="Overture.Inverses.html#1145" class="Bound">B</a><a id="1230" class="Symbol">}</a> <a id="1232" class="Symbol">→</a> <a id="1234" class="Symbol">(</a><a id="1235" href="Overture.Inverses.html#1235" class="Bound">a</a> <a id="1237" class="Symbol">:</a> <a id="1239" href="Overture.Inverses.html#1132" class="Bound">A</a><a id="1240" class="Symbol">)</a> <a id="1242" class="Symbol">→</a> <a id="1244" href="Overture.Inverses.html#1225" class="Bound">b</a> <a id="1246" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="1248" href="Overture.Inverses.html#1181" class="Bound">f</a> <a id="1250" href="Overture.Inverses.html#1235" class="Bound">a</a> <a id="1252" class="Symbol">→</a> <a id="1254" href="Overture.Inverses.html#1171" class="Datatype Operator">Image</a> <a id="1260" href="Overture.Inverses.html#1181" class="Bound">f</a> <a id="1262" href="Overture.Inverses.html#1171" class="Datatype Operator">∋</a> <a id="1264" href="Overture.Inverses.html#1225" class="Bound">b</a>

</pre>

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

<pre class="Agda">

 <a id="1771" href="Overture.Inverses.html#1771" class="Function">Inv</a> <a id="1775" class="Symbol">:</a> <a id="1777" class="Symbol">(</a><a id="1778" href="Overture.Inverses.html#1778" class="Bound">f</a> <a id="1780" class="Symbol">:</a> <a id="1782" href="Overture.Inverses.html#1132" class="Bound">A</a> <a id="1784" class="Symbol">→</a> <a id="1786" href="Overture.Inverses.html#1145" class="Bound">B</a><a id="1787" class="Symbol">){</a><a id="1789" href="Overture.Inverses.html#1789" class="Bound">b</a> <a id="1791" class="Symbol">:</a> <a id="1793" href="Overture.Inverses.html#1145" class="Bound">B</a><a id="1794" class="Symbol">}</a> <a id="1796" class="Symbol">→</a> <a id="1798" href="Overture.Inverses.html#1171" class="Datatype Operator">Image</a> <a id="1804" href="Overture.Inverses.html#1778" class="Bound">f</a> <a id="1806" href="Overture.Inverses.html#1171" class="Datatype Operator">∋</a> <a id="1808" href="Overture.Inverses.html#1789" class="Bound">b</a>  <a id="1811" class="Symbol">→</a>  <a id="1814" href="Overture.Inverses.html#1132" class="Bound">A</a>
 <a id="1817" href="Overture.Inverses.html#1771" class="Function">Inv</a> <a id="1821" href="Overture.Inverses.html#1821" class="Bound">f</a> <a id="1823" class="Symbol">(</a><a id="1824" href="Overture.Inverses.html#1219" class="InductiveConstructor">eq</a> <a id="1827" href="Overture.Inverses.html#1827" class="Bound">a</a> <a id="1829" class="Symbol">_)</a> <a id="1832" class="Symbol">=</a> <a id="1834" href="Overture.Inverses.html#1827" class="Bound">a</a>

</pre>

We can prove that `Inv f` is the *right-inverse* of `f`, as follows.

<pre class="Agda">

 <a id="1934" href="Overture.Inverses.html#1934" class="Function">InvIsInv</a> <a id="1943" class="Symbol">:</a> <a id="1945" class="Symbol">(</a><a id="1946" href="Overture.Inverses.html#1946" class="Bound">f</a> <a id="1948" class="Symbol">:</a> <a id="1950" href="Overture.Inverses.html#1132" class="Bound">A</a> <a id="1952" class="Symbol">→</a> <a id="1954" href="Overture.Inverses.html#1145" class="Bound">B</a><a id="1955" class="Symbol">){</a><a id="1957" href="Overture.Inverses.html#1957" class="Bound">b</a> <a id="1959" class="Symbol">:</a> <a id="1961" href="Overture.Inverses.html#1145" class="Bound">B</a><a id="1962" class="Symbol">}(</a><a id="1964" href="Overture.Inverses.html#1964" class="Bound">q</a> <a id="1966" class="Symbol">:</a> <a id="1968" href="Overture.Inverses.html#1171" class="Datatype Operator">Image</a> <a id="1974" href="Overture.Inverses.html#1946" class="Bound">f</a> <a id="1976" href="Overture.Inverses.html#1171" class="Datatype Operator">∋</a> <a id="1978" href="Overture.Inverses.html#1957" class="Bound">b</a><a id="1979" class="Symbol">)</a> <a id="1981" class="Symbol">→</a> <a id="1983" href="Overture.Inverses.html#1946" class="Bound">f</a><a id="1984" class="Symbol">(</a><a id="1985" href="Overture.Inverses.html#1771" class="Function">Inv</a> <a id="1989" href="Overture.Inverses.html#1946" class="Bound">f</a> <a id="1991" href="Overture.Inverses.html#1964" class="Bound">q</a><a id="1992" class="Symbol">)</a> <a id="1994" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="1996" href="Overture.Inverses.html#1957" class="Bound">b</a>
 <a id="1999" href="Overture.Inverses.html#1934" class="Function">InvIsInv</a> <a id="2008" href="Overture.Inverses.html#2008" class="Bound">f</a> <a id="2010" class="Symbol">(</a><a id="2011" href="Overture.Inverses.html#1219" class="InductiveConstructor">eq</a> <a id="2014" class="Symbol">_</a> <a id="2016" href="Overture.Inverses.html#2016" class="Bound">p</a><a id="2017" class="Symbol">)</a> <a id="2019" class="Symbol">=</a> <a id="2021" href="Overture.Inverses.html#2016" class="Bound">p</a> <a id="2023" href="Overture.Preliminaries.html#4949" class="Function Operator">⁻¹</a>

</pre>


#### <a id="injective-functions">Injective functions</a>

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following type manifests this property.

<pre class="Agda">

<a id="2310" class="Keyword">module</a> <a id="2317" href="Overture.Inverses.html#2317" class="Module">_</a> <a id="2319" class="Symbol">{</a><a id="2320" href="Overture.Inverses.html#2320" class="Bound">A</a> <a id="2322" class="Symbol">:</a> <a id="2324" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="2329" href="Overture.Inverses.html#1107" class="Generalizable">α</a><a id="2330" class="Symbol">}{</a><a id="2332" href="Overture.Inverses.html#2332" class="Bound">B</a> <a id="2334" class="Symbol">:</a> <a id="2336" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="2341" href="Overture.Inverses.html#1109" class="Generalizable">β</a><a id="2342" class="Symbol">}</a> <a id="2344" class="Keyword">where</a>

 <a id="2352" href="Overture.Inverses.html#2352" class="Function">IsInjective</a> <a id="2364" class="Symbol">:</a> <a id="2366" class="Symbol">(</a><a id="2367" href="Overture.Inverses.html#2320" class="Bound">A</a> <a id="2369" class="Symbol">→</a> <a id="2371" href="Overture.Inverses.html#2332" class="Bound">B</a><a id="2372" class="Symbol">)</a> <a id="2374" class="Symbol">→</a> <a id="2376" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="2381" class="Symbol">(</a><a id="2382" href="Overture.Inverses.html#2329" class="Bound">α</a> <a id="2384" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2386" href="Overture.Inverses.html#2341" class="Bound">β</a><a id="2387" class="Symbol">)</a>
 <a id="2390" href="Overture.Inverses.html#2352" class="Function">IsInjective</a> <a id="2402" href="Overture.Inverses.html#2402" class="Bound">f</a> <a id="2404" class="Symbol">=</a> <a id="2406" href="Function.Definitions.html#889" class="Function">Injective</a> <a id="2416" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="2420" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="2424" href="Overture.Inverses.html#2402" class="Bound">f</a>

</pre>

Before moving on to discuss surjective functions, let us prove (the obvious facts) that the identity map is injective and that the composition of injectives is injective.

<pre class="Agda">

<a id="id-is-injective"></a><a id="2625" href="Overture.Inverses.html#2625" class="Function">id-is-injective</a> <a id="2641" class="Symbol">:</a> <a id="2643" class="Symbol">{</a><a id="2644" href="Overture.Inverses.html#2644" class="Bound">A</a> <a id="2646" class="Symbol">:</a> <a id="2648" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="2653" href="Overture.Inverses.html#1107" class="Generalizable">α</a><a id="2654" class="Symbol">}</a> <a id="2656" class="Symbol">→</a> <a id="2658" href="Overture.Inverses.html#2644" class="Bound">A</a> <a id="2660" href="Function.Bundles.html#8289" class="Function Operator">↣</a> <a id="2662" href="Overture.Inverses.html#2644" class="Bound">A</a>
<a id="2664" href="Overture.Inverses.html#2625" class="Function">id-is-injective</a> <a id="2680" class="Symbol">{</a><a id="2681" class="Argument">A</a> <a id="2683" class="Symbol">=</a> <a id="2685" href="Overture.Inverses.html#2685" class="Bound">A</a><a id="2686" class="Symbol">}</a> <a id="2688" class="Symbol">=</a> <a id="2690" href="Function.Construct.Identity.html#3966" class="Function">id-↣</a> <a id="2695" href="Overture.Inverses.html#2685" class="Bound">A</a>

<a id="∘-injective"></a><a id="2698" href="Overture.Inverses.html#2698" class="Function">∘-injective</a> <a id="2710" class="Symbol">:</a> <a id="2712" class="Symbol">{</a><a id="2713" href="Overture.Inverses.html#2713" class="Bound">A</a> <a id="2715" class="Symbol">:</a> <a id="2717" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="2722" href="Overture.Inverses.html#1107" class="Generalizable">α</a><a id="2723" class="Symbol">}{</a><a id="2725" href="Overture.Inverses.html#2725" class="Bound">B</a> <a id="2727" class="Symbol">:</a> <a id="2729" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="2734" href="Overture.Inverses.html#1109" class="Generalizable">β</a><a id="2735" class="Symbol">}{</a><a id="2737" href="Overture.Inverses.html#2737" class="Bound">C</a> <a id="2739" class="Symbol">:</a> <a id="2741" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="2746" href="Overture.Inverses.html#1111" class="Generalizable">γ</a><a id="2747" class="Symbol">}{</a><a id="2749" href="Overture.Inverses.html#2749" class="Bound">f</a> <a id="2751" class="Symbol">:</a> <a id="2753" href="Overture.Inverses.html#2713" class="Bound">A</a> <a id="2755" class="Symbol">→</a> <a id="2757" href="Overture.Inverses.html#2725" class="Bound">B</a><a id="2758" class="Symbol">}{</a><a id="2760" href="Overture.Inverses.html#2760" class="Bound">g</a> <a id="2762" class="Symbol">:</a> <a id="2764" href="Overture.Inverses.html#2725" class="Bound">B</a> <a id="2766" class="Symbol">→</a> <a id="2768" href="Overture.Inverses.html#2737" class="Bound">C</a><a id="2769" class="Symbol">}</a>
 <a id="2772" class="Symbol">→</a>            <a id="2785" href="Overture.Inverses.html#2352" class="Function">IsInjective</a> <a id="2797" href="Overture.Inverses.html#2749" class="Bound">f</a> <a id="2799" class="Symbol">→</a> <a id="2801" href="Overture.Inverses.html#2352" class="Function">IsInjective</a> <a id="2813" href="Overture.Inverses.html#2760" class="Bound">g</a> <a id="2815" class="Symbol">→</a> <a id="2817" href="Overture.Inverses.html#2352" class="Function">IsInjective</a> <a id="2829" class="Symbol">(</a><a id="2830" href="Overture.Inverses.html#2760" class="Bound">g</a> <a id="2832" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="2834" href="Overture.Inverses.html#2749" class="Bound">f</a><a id="2835" class="Symbol">)</a>
<a id="2837" href="Overture.Inverses.html#2698" class="Function">∘-injective</a> <a id="2849" href="Overture.Inverses.html#2849" class="Bound">finj</a> <a id="2854" href="Overture.Inverses.html#2854" class="Bound">ginj</a> <a id="2859" class="Symbol">=</a> <a id="2861" class="Symbol">λ</a> <a id="2863" href="Overture.Inverses.html#2863" class="Bound">z</a> <a id="2865" class="Symbol">→</a> <a id="2867" href="Overture.Inverses.html#2849" class="Bound">finj</a> <a id="2872" class="Symbol">(</a><a id="2873" href="Overture.Inverses.html#2854" class="Bound">ginj</a> <a id="2878" href="Overture.Inverses.html#2863" class="Bound">z</a><a id="2879" class="Symbol">)</a>

</pre>


#### <a id="epics">Surjective functions</a>

A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types manifest this notion.

<pre class="Agda">

<a id="3186" class="Keyword">module</a> <a id="3193" href="Overture.Inverses.html#3193" class="Module">_</a> <a id="3195" class="Symbol">{</a><a id="3196" href="Overture.Inverses.html#3196" class="Bound">A</a> <a id="3198" class="Symbol">:</a> <a id="3200" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="3205" href="Overture.Inverses.html#1107" class="Generalizable">α</a><a id="3206" class="Symbol">}{</a><a id="3208" href="Overture.Inverses.html#3208" class="Bound">B</a> <a id="3210" class="Symbol">:</a> <a id="3212" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="3217" href="Overture.Inverses.html#1109" class="Generalizable">β</a><a id="3218" class="Symbol">}</a> <a id="3220" class="Keyword">where</a>
 <a id="3227" href="Overture.Inverses.html#3227" class="Function">IsSurjective</a> <a id="3240" class="Symbol">:</a> <a id="3242" class="Symbol">(</a><a id="3243" href="Overture.Inverses.html#3196" class="Bound">A</a> <a id="3245" class="Symbol">→</a> <a id="3247" href="Overture.Inverses.html#3208" class="Bound">B</a><a id="3248" class="Symbol">)</a> <a id="3250" class="Symbol">→</a>  <a id="3253" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="3258" class="Symbol">(</a><a id="3259" href="Overture.Inverses.html#3205" class="Bound">α</a> <a id="3261" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3263" href="Overture.Inverses.html#3217" class="Bound">β</a><a id="3264" class="Symbol">)</a>
 <a id="3267" href="Overture.Inverses.html#3227" class="Function">IsSurjective</a> <a id="3280" href="Overture.Inverses.html#3280" class="Bound">f</a> <a id="3282" class="Symbol">=</a> <a id="3284" class="Symbol">∀</a> <a id="3286" href="Overture.Inverses.html#3286" class="Bound">y</a> <a id="3288" class="Symbol">→</a> <a id="3290" href="Overture.Inverses.html#1171" class="Datatype Operator">Image</a> <a id="3296" href="Overture.Inverses.html#3280" class="Bound">f</a> <a id="3298" href="Overture.Inverses.html#1171" class="Datatype Operator">∋</a> <a id="3300" href="Overture.Inverses.html#3286" class="Bound">y</a>

 <a id="3304" href="Overture.Inverses.html#3304" class="Function">Surjective</a> <a id="3315" class="Symbol">:</a> <a id="3317" href="Overture.Inverses.html#466" class="Primitive">Type</a> <a id="3322" class="Symbol">(</a><a id="3323" href="Overture.Inverses.html#3205" class="Bound">α</a> <a id="3325" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3327" href="Overture.Inverses.html#3217" class="Bound">β</a><a id="3328" class="Symbol">)</a>
 <a id="3331" href="Overture.Inverses.html#3304" class="Function">Surjective</a> <a id="3342" class="Symbol">=</a> <a id="3344" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a> <a id="3346" class="Symbol">(</a><a id="3347" href="Overture.Inverses.html#3196" class="Bound">A</a> <a id="3349" class="Symbol">→</a> <a id="3351" href="Overture.Inverses.html#3208" class="Bound">B</a><a id="3352" class="Symbol">)</a> <a id="3354" href="Overture.Inverses.html#3227" class="Function">IsSurjective</a>

</pre>

With the next definition, we can represent a *right-inverse* of a surjective function.

<pre class="Agda">

 <a id="3483" href="Overture.Inverses.html#3483" class="Function">SurjInv</a> <a id="3491" class="Symbol">:</a> <a id="3493" class="Symbol">(</a><a id="3494" href="Overture.Inverses.html#3494" class="Bound">f</a> <a id="3496" class="Symbol">:</a> <a id="3498" href="Overture.Inverses.html#3196" class="Bound">A</a> <a id="3500" class="Symbol">→</a> <a id="3502" href="Overture.Inverses.html#3208" class="Bound">B</a><a id="3503" class="Symbol">)</a> <a id="3505" class="Symbol">→</a> <a id="3507" href="Overture.Inverses.html#3227" class="Function">IsSurjective</a> <a id="3520" href="Overture.Inverses.html#3494" class="Bound">f</a> <a id="3522" class="Symbol">→</a> <a id="3524" href="Overture.Inverses.html#3208" class="Bound">B</a> <a id="3526" class="Symbol">→</a> <a id="3528" href="Overture.Inverses.html#3196" class="Bound">A</a>
 <a id="3531" href="Overture.Inverses.html#3483" class="Function">SurjInv</a> <a id="3539" href="Overture.Inverses.html#3539" class="Bound">f</a> <a id="3541" href="Overture.Inverses.html#3541" class="Bound">fE</a> <a id="3544" href="Overture.Inverses.html#3544" class="Bound">b</a> <a id="3546" class="Symbol">=</a> <a id="3548" href="Overture.Inverses.html#1771" class="Function">Inv</a> <a id="3552" href="Overture.Inverses.html#3539" class="Bound">f</a> <a id="3554" class="Symbol">(</a><a id="3555" href="Overture.Inverses.html#3541" class="Bound">fE</a> <a id="3558" href="Overture.Inverses.html#3544" class="Bound">b</a><a id="3559" class="Symbol">)</a>

</pre>

Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.  Later, we will prove that this does indeed give the right-inverse, but we postpone the proof since it requires function extensionality, a concept we take up in the [Relations.Extensionality][] module.



--------------------------------------

<br>
<br>

[← Overture.Preliminaries](Overture.Preliminaries.html)
<span style="float:right;">[Overture.Transformers →](Overture.Transformers.html)</span>


{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


