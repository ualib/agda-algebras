---
layout: default
title : UALib.Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebra-types">Algebra Types</a>

This section presents the [UALib.Algebras.Algebras][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="302" class="Symbol">{-#</a> <a id="306" class="Keyword">OPTIONS</a> <a id="314" class="Pragma">--without-K</a> <a id="326" class="Pragma">--exact-split</a> <a id="340" class="Pragma">--safe</a> <a id="347" class="Symbol">#-}</a>

<a id="352" class="Keyword">module</a> <a id="359" href="UALib.Algebras.Algebras.html" class="Module">UALib.Algebras.Algebras</a> <a id="383" class="Keyword">where</a>

<a id="390" class="Keyword">open</a> <a id="395" class="Keyword">import</a> <a id="402" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="428" class="Keyword">public</a>

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="476" class="Keyword">using</a> <a id="482" class="Symbol">(</a><a id="483" href="universes.html#504" class="Primitive">𝓤₀</a><a id="485" class="Symbol">;</a> <a id="487" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="488" class="Symbol">;</a> <a id="490" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="491" class="Symbol">)</a> <a id="493" class="Keyword">public</a>

</pre>

-------------------------------

#### <a id="algebra-types">Algebra types</a>

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe 𝓤, we define the type of **algebras in the signature** 𝑆 (or 𝑆-**algebras**) and with **domain** (or **carrier** or **universe**) `𝐴 : 𝓤 ̇` as follows

<pre class="Agda">

<a id="Algebra"></a><a id="813" href="UALib.Algebras.Algebras.html#813" class="Function">Algebra</a>   <a id="823" class="Comment">-- alias</a>
 <a id="∞-algebra"></a><a id="833" href="UALib.Algebras.Algebras.html#833" class="Function">∞-algebra</a> <a id="843" class="Symbol">:</a> <a id="845" class="Symbol">(</a><a id="846" href="UALib.Algebras.Algebras.html#846" class="Bound">𝓤</a> <a id="848" class="Symbol">:</a> <a id="850" href="universes.html#551" class="Postulate">Universe</a><a id="858" class="Symbol">)(</a><a id="860" href="UALib.Algebras.Algebras.html#860" class="Bound">𝑆</a> <a id="862" class="Symbol">:</a> <a id="864" href="UALib.Algebras.Signatures.html#1457" class="Function">Signature</a> <a id="874" href="universes.html#613" class="Generalizable">𝓞</a> <a id="876" href="universes.html#617" class="Generalizable">𝓥</a><a id="877" class="Symbol">)</a> <a id="879" class="Symbol">→</a>  <a id="882" href="universes.html#613" class="Generalizable">𝓞</a> <a id="884" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="886" href="universes.html#617" class="Generalizable">𝓥</a> <a id="888" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="890" href="UALib.Algebras.Algebras.html#846" class="Bound">𝓤</a> <a id="892" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="894" href="universes.html#758" class="Function Operator">̇</a>

<a id="897" href="UALib.Algebras.Algebras.html#833" class="Function">∞-algebra</a> <a id="907" href="UALib.Algebras.Algebras.html#907" class="Bound">𝓤</a>  <a id="910" href="UALib.Algebras.Algebras.html#910" class="Bound">𝑆</a> <a id="912" class="Symbol">=</a> <a id="914" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="916" href="UALib.Algebras.Algebras.html#916" class="Bound">A</a> <a id="918" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="920" href="UALib.Algebras.Algebras.html#907" class="Bound">𝓤</a> <a id="922" href="universes.html#758" class="Function Operator">̇</a> <a id="924" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="926" class="Symbol">((</a><a id="928" href="UALib.Algebras.Algebras.html#928" class="Bound">f</a> <a id="930" class="Symbol">:</a> <a id="932" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="934" href="UALib.Algebras.Algebras.html#910" class="Bound">𝑆</a> <a id="936" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="937" class="Symbol">)</a> <a id="939" class="Symbol">→</a> <a id="941" href="UALib.Algebras.Signatures.html#825" class="Function">Op</a> <a id="944" class="Symbol">(</a><a id="945" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="947" href="UALib.Algebras.Algebras.html#910" class="Bound">𝑆</a> <a id="949" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="951" href="UALib.Algebras.Algebras.html#928" class="Bound">f</a><a id="952" class="Symbol">)</a> <a id="954" href="UALib.Algebras.Algebras.html#916" class="Bound">A</a><a id="955" class="Symbol">)</a>
<a id="957" href="UALib.Algebras.Algebras.html#813" class="Function">Algebra</a> <a id="965" class="Symbol">=</a> <a id="967" href="UALib.Algebras.Algebras.html#833" class="Function">∞-algebra</a>

</pre>

We may refer to an inhabitant of this type as a "∞-algebra" because its domain can be an arbitrary type, say, `A : 𝓤 ̇` &nbsp;&nbsp; and need not be truncated at some level; in particular, `A` need to be a set. (See the [discussion of truncation and sets](UALib.Prelude.Preliminaries.html#truncation).)

We might take this opportunity to define the type of "0-algebras" (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, we will only need to know that the domains of our algebras are sets in a few places in the UALib, so it seems preferable to work with general ∞-algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.

---------------------------------------

#### <a id="algebras-as-record-types">Algebras as record types</a>

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

<pre class="Agda">

<a id="2007" class="Keyword">module</a> <a id="2014" href="UALib.Algebras.Algebras.html#2014" class="Module">_</a> <a id="2016" class="Symbol">{</a><a id="2017" href="UALib.Algebras.Algebras.html#2017" class="Bound">𝓞</a> <a id="2019" href="UALib.Algebras.Algebras.html#2019" class="Bound">𝓥</a> <a id="2021" class="Symbol">:</a> <a id="2023" href="universes.html#551" class="Postulate">Universe</a><a id="2031" class="Symbol">}</a> <a id="2033" class="Keyword">where</a>
 <a id="2040" class="Keyword">record</a> <a id="2047" href="UALib.Algebras.Algebras.html#2047" class="Record">algebra</a> <a id="2055" class="Symbol">(</a><a id="2056" href="UALib.Algebras.Algebras.html#2056" class="Bound">𝓤</a> <a id="2058" class="Symbol">:</a> <a id="2060" href="universes.html#551" class="Postulate">Universe</a><a id="2068" class="Symbol">)</a> <a id="2070" class="Symbol">(</a><a id="2071" href="UALib.Algebras.Algebras.html#2071" class="Bound">𝑆</a> <a id="2073" class="Symbol">:</a> <a id="2075" href="UALib.Algebras.Signatures.html#1457" class="Function">Signature</a> <a id="2085" href="UALib.Algebras.Algebras.html#2017" class="Bound">𝓞</a> <a id="2087" href="UALib.Algebras.Algebras.html#2019" class="Bound">𝓥</a><a id="2088" class="Symbol">)</a> <a id="2090" class="Symbol">:</a> <a id="2092" class="Symbol">(</a><a id="2093" href="UALib.Algebras.Algebras.html#2017" class="Bound">𝓞</a> <a id="2095" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2097" href="UALib.Algebras.Algebras.html#2019" class="Bound">𝓥</a> <a id="2099" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2101" href="UALib.Algebras.Algebras.html#2056" class="Bound">𝓤</a><a id="2102" class="Symbol">)</a> <a id="2104" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="2106" href="universes.html#758" class="Function Operator">̇</a> <a id="2108" class="Keyword">where</a>
  <a id="2116" class="Keyword">constructor</a> <a id="2128" href="UALib.Algebras.Algebras.html#2128" class="InductiveConstructor">mkalg</a>
  <a id="2136" class="Keyword">field</a>
   <a id="2145" href="UALib.Algebras.Algebras.html#2145" class="Field">univ</a> <a id="2150" class="Symbol">:</a> <a id="2152" href="UALib.Algebras.Algebras.html#2056" class="Bound">𝓤</a> <a id="2154" href="universes.html#758" class="Function Operator">̇</a>
   <a id="2159" href="UALib.Algebras.Algebras.html#2159" class="Field">op</a> <a id="2162" class="Symbol">:</a> <a id="2164" class="Symbol">(</a><a id="2165" href="UALib.Algebras.Algebras.html#2165" class="Bound">f</a> <a id="2167" class="Symbol">:</a> <a id="2169" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="2171" href="UALib.Algebras.Algebras.html#2071" class="Bound">𝑆</a> <a id="2173" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="2174" class="Symbol">)</a> <a id="2176" class="Symbol">→</a> <a id="2178" class="Symbol">((</a><a id="2180" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="2182" href="UALib.Algebras.Algebras.html#2071" class="Bound">𝑆</a> <a id="2184" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="2186" href="UALib.Algebras.Algebras.html#2165" class="Bound">f</a><a id="2187" class="Symbol">)</a> <a id="2189" class="Symbol">→</a> <a id="2191" href="UALib.Algebras.Algebras.html#2145" class="Field">univ</a><a id="2195" class="Symbol">)</a> <a id="2197" class="Symbol">→</a> <a id="2199" href="UALib.Algebras.Algebras.html#2145" class="Field">univ</a>


</pre>

(Recall, the type `Signature 𝓞 𝓥` is simply defined as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.)

Of course, we can go back and forth between the two representations of algebras, like so.

<pre class="Agda">

<a id="2429" class="Keyword">module</a> <a id="2436" href="UALib.Algebras.Algebras.html#2436" class="Module">_</a> <a id="2438" class="Symbol">{</a><a id="2439" href="UALib.Algebras.Algebras.html#2439" class="Bound">𝓤</a> <a id="2441" href="UALib.Algebras.Algebras.html#2441" class="Bound">𝓞</a> <a id="2443" href="UALib.Algebras.Algebras.html#2443" class="Bound">𝓥</a> <a id="2445" class="Symbol">:</a> <a id="2447" href="universes.html#551" class="Postulate">Universe</a><a id="2455" class="Symbol">}</a> <a id="2457" class="Symbol">{</a><a id="2458" href="UALib.Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="2460" class="Symbol">:</a> <a id="2462" href="UALib.Algebras.Signatures.html#1457" class="Function">Signature</a> <a id="2472" href="UALib.Algebras.Algebras.html#2441" class="Bound">𝓞</a> <a id="2474" href="UALib.Algebras.Algebras.html#2443" class="Bound">𝓥</a><a id="2475" class="Symbol">}</a> <a id="2477" class="Keyword">where</a>

 <a id="2485" class="Keyword">open</a> <a id="2490" href="UALib.Algebras.Algebras.html#2047" class="Module">algebra</a>

 <a id="2500" href="UALib.Algebras.Algebras.html#2500" class="Function">algebra→Algebra</a> <a id="2516" class="Symbol">:</a> <a id="2518" href="UALib.Algebras.Algebras.html#2047" class="Record">algebra</a> <a id="2526" href="UALib.Algebras.Algebras.html#2439" class="Bound">𝓤</a> <a id="2528" href="UALib.Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="2530" class="Symbol">→</a> <a id="2532" href="UALib.Algebras.Algebras.html#813" class="Function">Algebra</a> <a id="2540" href="UALib.Algebras.Algebras.html#2439" class="Bound">𝓤</a> <a id="2542" href="UALib.Algebras.Algebras.html#2458" class="Bound">𝑆</a>
 <a id="2545" href="UALib.Algebras.Algebras.html#2500" class="Function">algebra→Algebra</a> <a id="2561" href="UALib.Algebras.Algebras.html#2561" class="Bound">𝑨</a> <a id="2563" class="Symbol">=</a> <a id="2565" class="Symbol">(</a><a id="2566" href="UALib.Algebras.Algebras.html#2145" class="Field">univ</a> <a id="2571" href="UALib.Algebras.Algebras.html#2561" class="Bound">𝑨</a> <a id="2573" href="UALib.Prelude.Preliminaries.html#5763" class="InductiveConstructor Operator">,</a> <a id="2575" href="UALib.Algebras.Algebras.html#2159" class="Field">op</a> <a id="2578" href="UALib.Algebras.Algebras.html#2561" class="Bound">𝑨</a><a id="2579" class="Symbol">)</a>

 <a id="2583" href="UALib.Algebras.Algebras.html#2583" class="Function">Algebra→algebra</a> <a id="2599" class="Symbol">:</a> <a id="2601" href="UALib.Algebras.Algebras.html#813" class="Function">Algebra</a> <a id="2609" href="UALib.Algebras.Algebras.html#2439" class="Bound">𝓤</a> <a id="2611" href="UALib.Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="2613" class="Symbol">→</a> <a id="2615" href="UALib.Algebras.Algebras.html#2047" class="Record">algebra</a> <a id="2623" href="UALib.Algebras.Algebras.html#2439" class="Bound">𝓤</a> <a id="2625" href="UALib.Algebras.Algebras.html#2458" class="Bound">𝑆</a>
 <a id="2628" href="UALib.Algebras.Algebras.html#2583" class="Function">Algebra→algebra</a> <a id="2644" href="UALib.Algebras.Algebras.html#2644" class="Bound">𝑨</a> <a id="2646" class="Symbol">=</a> <a id="2648" href="UALib.Algebras.Algebras.html#2128" class="InductiveConstructor">mkalg</a> <a id="2654" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="2656" href="UALib.Algebras.Algebras.html#2644" class="Bound">𝑨</a> <a id="2658" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="2660" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="2662" href="UALib.Algebras.Algebras.html#2644" class="Bound">𝑨</a> <a id="2664" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a>

</pre>

----------------------------------------

#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We conclude this module by defining a convenient shorthand for the interpretation of an operation symbol that we will use often.  It looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with.

<pre class="Agda">

 <a id="3080" href="UALib.Algebras.Algebras.html#3080" class="Function Operator">_̂_</a> <a id="3084" class="Symbol">:</a> <a id="3086" class="Symbol">(</a><a id="3087" href="UALib.Algebras.Algebras.html#3087" class="Bound">f</a> <a id="3089" class="Symbol">:</a> <a id="3091" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3093" href="UALib.Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="3095" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="3096" class="Symbol">)(</a><a id="3098" href="UALib.Algebras.Algebras.html#3098" class="Bound">𝑨</a> <a id="3100" class="Symbol">:</a> <a id="3102" href="UALib.Algebras.Algebras.html#813" class="Function">Algebra</a> <a id="3110" href="UALib.Algebras.Algebras.html#2439" class="Bound">𝓤</a> <a id="3112" href="UALib.Algebras.Algebras.html#2458" class="Bound">𝑆</a><a id="3113" class="Symbol">)</a> <a id="3115" class="Symbol">→</a> <a id="3117" class="Symbol">(</a><a id="3118" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3120" href="UALib.Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="3122" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3124" href="UALib.Algebras.Algebras.html#3087" class="Bound">f</a>  <a id="3127" class="Symbol">→</a>  <a id="3130" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3132" href="UALib.Algebras.Algebras.html#3098" class="Bound">𝑨</a> <a id="3134" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="3135" class="Symbol">)</a> <a id="3137" class="Symbol">→</a> <a id="3139" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3141" href="UALib.Algebras.Algebras.html#3098" class="Bound">𝑨</a> <a id="3143" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a>

 <a id="3147" href="UALib.Algebras.Algebras.html#3147" class="Bound">f</a> <a id="3149" href="UALib.Algebras.Algebras.html#3080" class="Function Operator">̂</a> <a id="3151" href="UALib.Algebras.Algebras.html#3151" class="Bound">𝑨</a> <a id="3153" class="Symbol">=</a> <a id="3155" class="Symbol">λ</a> <a id="3157" href="UALib.Algebras.Algebras.html#3157" class="Bound">x</a> <a id="3159" class="Symbol">→</a> <a id="3161" class="Symbol">(</a><a id="3162" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3164" href="UALib.Algebras.Algebras.html#3151" class="Bound">𝑨</a> <a id="3166" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3168" href="UALib.Algebras.Algebras.html#3147" class="Bound">f</a><a id="3169" class="Symbol">)</a> <a id="3171" href="UALib.Algebras.Algebras.html#3157" class="Bound">x</a>

</pre>

#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

Finally, we will want to assume that we always have at our disposal an arbitrary collection \ab X of variable symbols such that, for every algebra \ab 𝑨, no matter the type of its domain, we have a surjective map \ab{h₀} \as : \ab X \as → \aiab{∣}{𝑨} from variables onto the domain of \ab 𝑨.

<pre class="Agda">

<a id="_↠_"></a><a id="3579" href="UALib.Algebras.Algebras.html#3579" class="Function Operator">_↠_</a> <a id="3583" class="Symbol">:</a> <a id="3585" class="Symbol">{</a><a id="3586" href="UALib.Algebras.Algebras.html#3586" class="Bound">𝑆</a> <a id="3588" class="Symbol">:</a> <a id="3590" href="UALib.Algebras.Signatures.html#1457" class="Function">Signature</a> <a id="3600" href="universes.html#613" class="Generalizable">𝓞</a> <a id="3602" href="universes.html#617" class="Generalizable">𝓥</a><a id="3603" class="Symbol">}{</a><a id="3605" href="UALib.Algebras.Algebras.html#3605" class="Bound">𝓤</a> <a id="3607" href="UALib.Algebras.Algebras.html#3607" class="Bound">𝓧</a> <a id="3609" class="Symbol">:</a> <a id="3611" href="universes.html#551" class="Postulate">Universe</a><a id="3619" class="Symbol">}</a> <a id="3621" class="Symbol">→</a> <a id="3623" href="UALib.Algebras.Algebras.html#3607" class="Bound">𝓧</a> <a id="3625" href="universes.html#758" class="Function Operator">̇</a> <a id="3627" class="Symbol">→</a> <a id="3629" href="UALib.Algebras.Algebras.html#813" class="Function">Algebra</a> <a id="3637" href="UALib.Algebras.Algebras.html#3605" class="Bound">𝓤</a> <a id="3639" href="UALib.Algebras.Algebras.html#3586" class="Bound">𝑆</a> <a id="3641" class="Symbol">→</a> <a id="3643" href="UALib.Algebras.Algebras.html#3607" class="Bound">𝓧</a> <a id="3645" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3647" href="UALib.Algebras.Algebras.html#3605" class="Bound">𝓤</a> <a id="3649" href="universes.html#758" class="Function Operator">̇</a>
<a id="3651" href="UALib.Algebras.Algebras.html#3651" class="Bound">X</a> <a id="3653" href="UALib.Algebras.Algebras.html#3579" class="Function Operator">↠</a> <a id="3655" href="UALib.Algebras.Algebras.html#3655" class="Bound">𝑨</a> <a id="3657" class="Symbol">=</a> <a id="3659" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3661" href="UALib.Algebras.Algebras.html#3661" class="Bound">h</a> <a id="3663" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3665" class="Symbol">(</a><a id="3666" href="UALib.Algebras.Algebras.html#3651" class="Bound">X</a> <a id="3668" class="Symbol">→</a> <a id="3670" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3672" href="UALib.Algebras.Algebras.html#3655" class="Bound">𝑨</a> <a id="3674" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="3675" class="Symbol">)</a> <a id="3677" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3679" href="UALib.Prelude.Inverses.html#2388" class="Function">Epic</a> <a id="3684" href="UALib.Algebras.Algebras.html#3661" class="Bound">h</a>

</pre>

-------------------------------------

[← UALib.Algebras.Signatures](UALib.Algebras.Signatures.html)
<span style="float:right;">[UALib.Algebras.Products →](UALib.Algebras.Products.html)</span>


{% include UALib.Links.md %}
