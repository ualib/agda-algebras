---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Extensionality</a>

This section describes the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="316" class="Symbol">{-#</a> <a id="320" class="Keyword">OPTIONS</a> <a id="328" class="Pragma">--without-K</a> <a id="340" class="Pragma">--exact-split</a> <a id="354" class="Pragma">--safe</a> <a id="361" class="Symbol">#-}</a>

<a id="366" class="Keyword">module</a> <a id="373" href="UALib.Prelude.Extensionality.html" class="Module">UALib.Prelude.Extensionality</a> <a id="402" class="Keyword">where</a>

<a id="409" class="Keyword">open</a> <a id="414" class="Keyword">import</a> <a id="421" href="UALib.Prelude.Inverses.html" class="Module">UALib.Prelude.Inverses</a> <a id="444" class="Keyword">public</a>
<a id="451" class="Keyword">open</a> <a id="456" class="Keyword">import</a> <a id="463" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="491" class="Keyword">using</a> <a id="497" class="Symbol">(</a><a id="498" href="MGS-MLTT.html#6747" class="Function Operator">_∼_</a><a id="501" class="Symbol">;</a> <a id="503" href="universes.html#580" class="Primitive">𝓤ω</a><a id="505" class="Symbol">;</a> <a id="507" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="508" class="Symbol">;</a> <a id="510" href="MGS-Powerset.html#2893" class="Function">Ω</a><a id="511" class="Symbol">;</a> <a id="513" href="MGS-Powerset.html#4551" class="Function">𝓟</a><a id="514" class="Symbol">;</a> <a id="516" href="MGS-Powerset.html#5497" class="Function">⊆-refl-consequence</a><a id="534" class="Symbol">;</a> <a id="536" href="UALib.Prelude.Preliminaries.html#6269" class="Function Operator">_∈₀_</a><a id="540" class="Symbol">;</a> <a id="542" href="UALib.Prelude.Preliminaries.html#6282" class="Function Operator">_⊆₀_</a><a id="546" class="Symbol">;</a> <a id="548" href="MGS-Powerset.html#2957" class="Function Operator">_holds</a><a id="554" class="Symbol">)</a> <a id="556" class="Keyword">public</a>

</pre>




#### <a id="function-extensionality">Function extensionality</a>

Extensional equality of functions, or function extensionality, means that any two point-wise equal functions are equal. As [MHE points out](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua), this is known to be not provable or disprovable in Martin-Löf type theory. It is an independent statement, which MHE abbreviates as `funext`.  Here is how this notion is given a type in the [Type Topology][] library

```agda
funext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g
```

For readability we occasionally use the following alias for the `funext` type.

<pre class="Agda">

<a id="extensionality"></a><a id="1296" href="UALib.Prelude.Extensionality.html#1296" class="Function">extensionality</a> <a id="1311" class="Symbol">:</a> <a id="1313" class="Symbol">∀</a> <a id="1315" href="UALib.Prelude.Extensionality.html#1315" class="Bound">𝓤</a> <a id="1317" href="UALib.Prelude.Extensionality.html#1317" class="Bound">𝓦</a>  <a id="1320" class="Symbol">→</a> <a id="1322" href="UALib.Prelude.Extensionality.html#1315" class="Bound">𝓤</a> <a id="1324" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1326" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1328" href="UALib.Prelude.Extensionality.html#1317" class="Bound">𝓦</a> <a id="1330" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="1332" href="universes.html#758" class="Function Operator">̇</a>
<a id="1334" href="UALib.Prelude.Extensionality.html#1296" class="Function">extensionality</a> <a id="1349" href="UALib.Prelude.Extensionality.html#1349" class="Bound">𝓤</a> <a id="1351" href="UALib.Prelude.Extensionality.html#1351" class="Bound">𝓦</a> <a id="1353" class="Symbol">=</a> <a id="1355" class="Symbol">{</a><a id="1356" href="UALib.Prelude.Extensionality.html#1356" class="Bound">A</a> <a id="1358" class="Symbol">:</a> <a id="1360" href="UALib.Prelude.Extensionality.html#1349" class="Bound">𝓤</a> <a id="1362" href="universes.html#758" class="Function Operator">̇</a> <a id="1364" class="Symbol">}</a> <a id="1366" class="Symbol">{</a><a id="1367" href="UALib.Prelude.Extensionality.html#1367" class="Bound">B</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="UALib.Prelude.Extensionality.html#1351" class="Bound">𝓦</a> <a id="1373" href="universes.html#758" class="Function Operator">̇</a> <a id="1375" class="Symbol">}</a> <a id="1377" class="Symbol">{</a><a id="1378" href="UALib.Prelude.Extensionality.html#1378" class="Bound">f</a> <a id="1380" href="UALib.Prelude.Extensionality.html#1380" class="Bound">g</a> <a id="1382" class="Symbol">:</a> <a id="1384" href="UALib.Prelude.Extensionality.html#1356" class="Bound">A</a> <a id="1386" class="Symbol">→</a> <a id="1388" href="UALib.Prelude.Extensionality.html#1367" class="Bound">B</a><a id="1389" class="Symbol">}</a> <a id="1391" class="Symbol">→</a> <a id="1393" href="UALib.Prelude.Extensionality.html#1378" class="Bound">f</a> <a id="1395" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="1397" href="UALib.Prelude.Extensionality.html#1380" class="Bound">g</a> <a id="1399" class="Symbol">→</a> <a id="1401" href="UALib.Prelude.Extensionality.html#1378" class="Bound">f</a> <a id="1403" href="UALib.Prelude.Preliminaries.html#5556" class="Datatype Operator">≡</a> <a id="1405" href="UALib.Prelude.Extensionality.html#1380" class="Bound">g</a>

</pre>

Pointwise equality of functions is typically what one means in informal settings when one says that two functions are equal.  Here is how MHE defines pointwise equality of (dependent) function in [Type Topology][].

```agda
_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x
infix 0 _∼_
```

In fact, if one assumes the [univalence axiom], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

<pre class="Agda">

<a id="dep-extensionality"></a><a id="2165" href="UALib.Prelude.Extensionality.html#2165" class="Function">dep-extensionality</a> <a id="2184" class="Symbol">:</a> <a id="2186" class="Symbol">∀</a> <a id="2188" href="UALib.Prelude.Extensionality.html#2188" class="Bound">𝓤</a> <a id="2190" href="UALib.Prelude.Extensionality.html#2190" class="Bound">𝓦</a> <a id="2192" class="Symbol">→</a> <a id="2194" href="UALib.Prelude.Extensionality.html#2188" class="Bound">𝓤</a> <a id="2196" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="2198" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2200" href="UALib.Prelude.Extensionality.html#2190" class="Bound">𝓦</a> <a id="2202" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="2204" href="universes.html#758" class="Function Operator">̇</a>
<a id="2206" href="UALib.Prelude.Extensionality.html#2165" class="Function">dep-extensionality</a> <a id="2225" href="UALib.Prelude.Extensionality.html#2225" class="Bound">𝓤</a> <a id="2227" href="UALib.Prelude.Extensionality.html#2227" class="Bound">𝓦</a> <a id="2229" class="Symbol">=</a> <a id="2231" class="Symbol">{</a><a id="2232" href="UALib.Prelude.Extensionality.html#2232" class="Bound">A</a> <a id="2234" class="Symbol">:</a> <a id="2236" href="UALib.Prelude.Extensionality.html#2225" class="Bound">𝓤</a> <a id="2238" href="universes.html#758" class="Function Operator">̇</a> <a id="2240" class="Symbol">}</a> <a id="2242" class="Symbol">{</a><a id="2243" href="UALib.Prelude.Extensionality.html#2243" class="Bound">B</a> <a id="2245" class="Symbol">:</a> <a id="2247" href="UALib.Prelude.Extensionality.html#2232" class="Bound">A</a> <a id="2249" class="Symbol">→</a> <a id="2251" href="UALib.Prelude.Extensionality.html#2227" class="Bound">𝓦</a> <a id="2253" href="universes.html#758" class="Function Operator">̇</a> <a id="2255" class="Symbol">}</a>
  <a id="2259" class="Symbol">{</a><a id="2260" href="UALib.Prelude.Extensionality.html#2260" class="Bound">f</a> <a id="2262" href="UALib.Prelude.Extensionality.html#2262" class="Bound">g</a> <a id="2264" class="Symbol">:</a> <a id="2266" class="Symbol">∀(</a><a id="2268" href="UALib.Prelude.Extensionality.html#2268" class="Bound">x</a> <a id="2270" class="Symbol">:</a> <a id="2272" href="UALib.Prelude.Extensionality.html#2232" class="Bound">A</a><a id="2273" class="Symbol">)</a> <a id="2275" class="Symbol">→</a> <a id="2277" href="UALib.Prelude.Extensionality.html#2243" class="Bound">B</a> <a id="2279" href="UALib.Prelude.Extensionality.html#2268" class="Bound">x</a><a id="2280" class="Symbol">}</a> <a id="2282" class="Symbol">→</a>  <a id="2285" href="UALib.Prelude.Extensionality.html#2260" class="Bound">f</a> <a id="2287" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="2289" href="UALib.Prelude.Extensionality.html#2262" class="Bound">g</a>  <a id="2292" class="Symbol">→</a>  <a id="2295" href="UALib.Prelude.Extensionality.html#2260" class="Bound">f</a> <a id="2297" href="UALib.Prelude.Preliminaries.html#5556" class="Datatype Operator">≡</a> <a id="2299" href="UALib.Prelude.Extensionality.html#2262" class="Bound">g</a>

</pre>

Sometimes we need extensionality principles that work at all universe levels, and Agda is capable of expressing such principles, which belong to the special 𝓤ω type, as follows:

<pre class="Agda">

<a id="∀-extensionality"></a><a id="2507" href="UALib.Prelude.Extensionality.html#2507" class="Function">∀-extensionality</a> <a id="2524" class="Symbol">:</a> <a id="2526" href="universes.html#580" class="Primitive">𝓤ω</a>
<a id="2529" href="UALib.Prelude.Extensionality.html#2507" class="Function">∀-extensionality</a> <a id="2546" class="Symbol">=</a> <a id="2548" class="Symbol">∀</a>  <a id="2551" class="Symbol">{</a><a id="2552" href="UALib.Prelude.Extensionality.html#2552" class="Bound">𝓤</a> <a id="2554" href="UALib.Prelude.Extensionality.html#2554" class="Bound">𝓥</a><a id="2555" class="Symbol">}</a> <a id="2557" class="Symbol">→</a> <a id="2559" href="UALib.Prelude.Extensionality.html#1296" class="Function">extensionality</a> <a id="2574" href="UALib.Prelude.Extensionality.html#2552" class="Bound">𝓤</a> <a id="2576" href="UALib.Prelude.Extensionality.html#2554" class="Bound">𝓥</a>

<a id="∀-dep-extensionality"></a><a id="2579" href="UALib.Prelude.Extensionality.html#2579" class="Function">∀-dep-extensionality</a> <a id="2600" class="Symbol">:</a> <a id="2602" href="universes.html#580" class="Primitive">𝓤ω</a>
<a id="2605" href="UALib.Prelude.Extensionality.html#2579" class="Function">∀-dep-extensionality</a> <a id="2626" class="Symbol">=</a> <a id="2628" class="Symbol">∀</a> <a id="2630" class="Symbol">{</a><a id="2631" href="UALib.Prelude.Extensionality.html#2631" class="Bound">𝓤</a> <a id="2633" href="UALib.Prelude.Extensionality.html#2633" class="Bound">𝓥</a><a id="2634" class="Symbol">}</a> <a id="2636" class="Symbol">→</a> <a id="2638" href="UALib.Prelude.Extensionality.html#2165" class="Function">dep-extensionality</a> <a id="2657" href="UALib.Prelude.Extensionality.html#2631" class="Bound">𝓤</a> <a id="2659" href="UALib.Prelude.Extensionality.html#2633" class="Bound">𝓥</a>

</pre>

More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


<pre class="Agda">

<a id="extensionality-lemma"></a><a id="2854" href="UALib.Prelude.Extensionality.html#2854" class="Function">extensionality-lemma</a> <a id="2875" class="Symbol">:</a> <a id="2877" class="Symbol">{</a><a id="2878" href="UALib.Prelude.Extensionality.html#2878" class="Bound">𝓘</a> <a id="2880" href="UALib.Prelude.Extensionality.html#2880" class="Bound">𝓤</a> <a id="2882" href="UALib.Prelude.Extensionality.html#2882" class="Bound">𝓥</a> <a id="2884" href="UALib.Prelude.Extensionality.html#2884" class="Bound">𝓣</a> <a id="2886" class="Symbol">:</a> <a id="2888" href="universes.html#551" class="Postulate">Universe</a><a id="2896" class="Symbol">}{</a><a id="2898" href="UALib.Prelude.Extensionality.html#2898" class="Bound">I</a> <a id="2900" class="Symbol">:</a> <a id="2902" href="UALib.Prelude.Extensionality.html#2878" class="Bound">𝓘</a> <a id="2904" href="universes.html#758" class="Function Operator">̇</a> <a id="2906" class="Symbol">}{</a><a id="2908" href="UALib.Prelude.Extensionality.html#2908" class="Bound">X</a> <a id="2910" class="Symbol">:</a> <a id="2912" href="UALib.Prelude.Extensionality.html#2880" class="Bound">𝓤</a> <a id="2914" href="universes.html#758" class="Function Operator">̇</a> <a id="2916" class="Symbol">}{</a><a id="2918" href="UALib.Prelude.Extensionality.html#2918" class="Bound">A</a> <a id="2920" class="Symbol">:</a> <a id="2922" href="UALib.Prelude.Extensionality.html#2898" class="Bound">I</a> <a id="2924" class="Symbol">→</a> <a id="2926" href="UALib.Prelude.Extensionality.html#2882" class="Bound">𝓥</a> <a id="2928" href="universes.html#758" class="Function Operator">̇</a> <a id="2930" class="Symbol">}</a>
                       <a id="2955" class="Symbol">(</a><a id="2956" href="UALib.Prelude.Extensionality.html#2956" class="Bound">p</a> <a id="2958" href="UALib.Prelude.Extensionality.html#2958" class="Bound">q</a> <a id="2960" class="Symbol">:</a> <a id="2962" class="Symbol">(</a><a id="2963" href="UALib.Prelude.Extensionality.html#2963" class="Bound">i</a> <a id="2965" class="Symbol">:</a> <a id="2967" href="UALib.Prelude.Extensionality.html#2898" class="Bound">I</a><a id="2968" class="Symbol">)</a> <a id="2970" class="Symbol">→</a> <a id="2972" class="Symbol">(</a><a id="2973" href="UALib.Prelude.Extensionality.html#2908" class="Bound">X</a> <a id="2975" class="Symbol">→</a> <a id="2977" href="UALib.Prelude.Extensionality.html#2918" class="Bound">A</a> <a id="2979" href="UALib.Prelude.Extensionality.html#2963" class="Bound">i</a><a id="2980" class="Symbol">)</a> <a id="2982" class="Symbol">→</a> <a id="2984" href="UALib.Prelude.Extensionality.html#2884" class="Bound">𝓣</a> <a id="2986" href="universes.html#758" class="Function Operator">̇</a> <a id="2988" class="Symbol">)(</a><a id="2990" href="UALib.Prelude.Extensionality.html#2990" class="Bound">args</a> <a id="2995" class="Symbol">:</a> <a id="2997" href="UALib.Prelude.Extensionality.html#2908" class="Bound">X</a> <a id="2999" class="Symbol">→</a> <a id="3001" class="Symbol">(</a><a id="3002" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3004" href="UALib.Prelude.Extensionality.html#2918" class="Bound">A</a><a id="3005" class="Symbol">))</a>
 <a id="3009" class="Symbol">→</a>                     <a id="3031" href="UALib.Prelude.Extensionality.html#2956" class="Bound">p</a> <a id="3033" href="UALib.Prelude.Preliminaries.html#5556" class="Datatype Operator">≡</a> <a id="3035" href="UALib.Prelude.Extensionality.html#2958" class="Bound">q</a>
                       <a id="3060" class="Comment">-------------------------------------------------------------</a>
 <a id="3123" class="Symbol">→</a>                     <a id="3145" class="Symbol">(λ</a> <a id="3148" href="UALib.Prelude.Extensionality.html#3148" class="Bound">i</a> <a id="3150" class="Symbol">→</a> <a id="3152" class="Symbol">(</a><a id="3153" href="UALib.Prelude.Extensionality.html#2956" class="Bound">p</a> <a id="3155" href="UALib.Prelude.Extensionality.html#3148" class="Bound">i</a><a id="3156" class="Symbol">)(λ</a> <a id="3160" href="UALib.Prelude.Extensionality.html#3160" class="Bound">x</a> <a id="3162" class="Symbol">→</a> <a id="3164" href="UALib.Prelude.Extensionality.html#2990" class="Bound">args</a> <a id="3169" href="UALib.Prelude.Extensionality.html#3160" class="Bound">x</a> <a id="3171" href="UALib.Prelude.Extensionality.html#3148" class="Bound">i</a><a id="3172" class="Symbol">))</a> <a id="3175" href="UALib.Prelude.Preliminaries.html#5556" class="Datatype Operator">≡</a> <a id="3177" class="Symbol">(λ</a> <a id="3180" href="UALib.Prelude.Extensionality.html#3180" class="Bound">i</a> <a id="3182" class="Symbol">→</a> <a id="3184" class="Symbol">(</a><a id="3185" href="UALib.Prelude.Extensionality.html#2958" class="Bound">q</a> <a id="3187" href="UALib.Prelude.Extensionality.html#3180" class="Bound">i</a><a id="3188" class="Symbol">)(λ</a> <a id="3192" href="UALib.Prelude.Extensionality.html#3192" class="Bound">x</a> <a id="3194" class="Symbol">→</a> <a id="3196" href="UALib.Prelude.Extensionality.html#2990" class="Bound">args</a> <a id="3201" href="UALib.Prelude.Extensionality.html#3192" class="Bound">x</a> <a id="3203" href="UALib.Prelude.Extensionality.html#3180" class="Bound">i</a><a id="3204" class="Symbol">))</a>

<a id="3208" href="UALib.Prelude.Extensionality.html#2854" class="Function">extensionality-lemma</a> <a id="3229" href="UALib.Prelude.Extensionality.html#3229" class="Bound">p</a> <a id="3231" href="UALib.Prelude.Extensionality.html#3231" class="Bound">q</a> <a id="3233" href="UALib.Prelude.Extensionality.html#3233" class="Bound">args</a> <a id="3238" href="UALib.Prelude.Extensionality.html#3238" class="Bound">p≡q</a> <a id="3242" class="Symbol">=</a> <a id="3244" href="MGS-MLTT.html#6613" class="Function">ap</a> <a id="3247" class="Symbol">(λ</a> <a id="3250" href="UALib.Prelude.Extensionality.html#3250" class="Bound">-</a> <a id="3252" class="Symbol">→</a> <a id="3254" class="Symbol">λ</a> <a id="3256" href="UALib.Prelude.Extensionality.html#3256" class="Bound">i</a> <a id="3258" class="Symbol">→</a> <a id="3260" class="Symbol">(</a><a id="3261" href="UALib.Prelude.Extensionality.html#3250" class="Bound">-</a> <a id="3263" href="UALib.Prelude.Extensionality.html#3256" class="Bound">i</a><a id="3264" class="Symbol">)</a> <a id="3266" class="Symbol">(λ</a> <a id="3269" href="UALib.Prelude.Extensionality.html#3269" class="Bound">x</a> <a id="3271" class="Symbol">→</a> <a id="3273" href="UALib.Prelude.Extensionality.html#3233" class="Bound">args</a> <a id="3278" href="UALib.Prelude.Extensionality.html#3269" class="Bound">x</a> <a id="3280" href="UALib.Prelude.Extensionality.html#3256" class="Bound">i</a><a id="3281" class="Symbol">))</a> <a id="3284" href="UALib.Prelude.Extensionality.html#3238" class="Bound">p≡q</a>

</pre>




#### <a id="function-intensionality">Function intensionality</a>

This is the opposite of function extensionality and is defined as follows.

<pre class="Agda">

<a id="intens"></a><a id="3460" href="UALib.Prelude.Extensionality.html#3460" class="Function">intens</a> <a id="3467" class="Comment">-- alias</a>
 <a id="intensionality"></a><a id="3477" href="UALib.Prelude.Extensionality.html#3477" class="Function">intensionality</a> <a id="3492" class="Symbol">:</a> <a id="3494" class="Symbol">{</a><a id="3495" href="UALib.Prelude.Extensionality.html#3495" class="Bound">𝓤</a> <a id="3497" href="UALib.Prelude.Extensionality.html#3497" class="Bound">𝓦</a> <a id="3499" class="Symbol">:</a> <a id="3501" href="universes.html#551" class="Postulate">Universe</a><a id="3509" class="Symbol">}{</a><a id="3511" href="UALib.Prelude.Extensionality.html#3511" class="Bound">A</a> <a id="3513" class="Symbol">:</a> <a id="3515" href="UALib.Prelude.Extensionality.html#3495" class="Bound">𝓤</a> <a id="3517" href="universes.html#758" class="Function Operator">̇</a><a id="3518" class="Symbol">}{</a><a id="3520" href="UALib.Prelude.Extensionality.html#3520" class="Bound">B</a> <a id="3522" class="Symbol">:</a> <a id="3524" href="UALib.Prelude.Extensionality.html#3497" class="Bound">𝓦</a> <a id="3526" href="universes.html#758" class="Function Operator">̇</a><a id="3527" class="Symbol">}{</a><a id="3529" href="UALib.Prelude.Extensionality.html#3529" class="Bound">f</a> <a id="3531" href="UALib.Prelude.Extensionality.html#3531" class="Bound">g</a> <a id="3533" class="Symbol">:</a> <a id="3535" href="UALib.Prelude.Extensionality.html#3511" class="Bound">A</a> <a id="3537" class="Symbol">→</a> <a id="3539" href="UALib.Prelude.Extensionality.html#3520" class="Bound">B</a><a id="3540" class="Symbol">}</a> <a id="3542" class="Symbol">→</a> <a id="3544" href="UALib.Prelude.Extensionality.html#3529" class="Bound">f</a> <a id="3546" href="UALib.Prelude.Preliminaries.html#5556" class="Datatype Operator">≡</a> <a id="3548" href="UALib.Prelude.Extensionality.html#3531" class="Bound">g</a>  <a id="3551" class="Symbol">→</a>  <a id="3554" href="UALib.Prelude.Extensionality.html#3529" class="Bound">f</a> <a id="3556" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3558" href="UALib.Prelude.Extensionality.html#3531" class="Bound">g</a>

<a id="3561" href="UALib.Prelude.Extensionality.html#3477" class="Function">intensionality</a> <a id="3576" href="UALib.Prelude.Preliminaries.html#5570" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="3581" class="Symbol">_</a>  <a id="3584" class="Symbol">=</a> <a id="3586" href="UALib.Prelude.Preliminaries.html#5570" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>
<a id="3591" href="UALib.Prelude.Extensionality.html#3460" class="Function">intens</a> <a id="3598" class="Symbol">=</a> <a id="3600" href="UALib.Prelude.Extensionality.html#3477" class="Function">intensionality</a>

</pre>

Of course, the intensionality principle has an analogue for dependent function types.

<pre class="Agda">

<a id="dintensionality"></a><a id="3729" href="UALib.Prelude.Extensionality.html#3729" class="Function">dintensionality</a> <a id="3745" class="Symbol">:</a> <a id="3747" class="Symbol">{</a><a id="3748" href="UALib.Prelude.Extensionality.html#3748" class="Bound">𝓤</a> <a id="3750" href="UALib.Prelude.Extensionality.html#3750" class="Bound">𝓦</a> <a id="3752" class="Symbol">:</a> <a id="3754" href="universes.html#551" class="Postulate">Universe</a><a id="3762" class="Symbol">}</a> <a id="3764" class="Symbol">{</a><a id="3765" href="UALib.Prelude.Extensionality.html#3765" class="Bound">A</a> <a id="3767" class="Symbol">:</a> <a id="3769" href="UALib.Prelude.Extensionality.html#3748" class="Bound">𝓤</a> <a id="3771" href="universes.html#758" class="Function Operator">̇</a> <a id="3773" class="Symbol">}</a> <a id="3775" class="Symbol">{</a><a id="3776" href="UALib.Prelude.Extensionality.html#3776" class="Bound">B</a> <a id="3778" class="Symbol">:</a> <a id="3780" href="UALib.Prelude.Extensionality.html#3765" class="Bound">A</a> <a id="3782" class="Symbol">→</a> <a id="3784" href="UALib.Prelude.Extensionality.html#3750" class="Bound">𝓦</a> <a id="3786" href="universes.html#758" class="Function Operator">̇</a> <a id="3788" class="Symbol">}</a> <a id="3790" class="Symbol">{</a><a id="3791" href="UALib.Prelude.Extensionality.html#3791" class="Bound">f</a> <a id="3793" href="UALib.Prelude.Extensionality.html#3793" class="Bound">g</a> <a id="3795" class="Symbol">:</a> <a id="3797" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="3799" href="UALib.Prelude.Extensionality.html#3776" class="Bound">B</a><a id="3800" class="Symbol">}</a> <a id="3802" class="Symbol">→</a> <a id="3804" href="UALib.Prelude.Extensionality.html#3791" class="Bound">f</a> <a id="3806" href="UALib.Prelude.Preliminaries.html#5556" class="Datatype Operator">≡</a> <a id="3808" href="UALib.Prelude.Extensionality.html#3793" class="Bound">g</a> <a id="3810" class="Symbol">→</a> <a id="3812" href="UALib.Prelude.Extensionality.html#3791" class="Bound">f</a> <a id="3814" href="MGS-MLTT.html#6747" class="Function Operator">∼</a> <a id="3816" href="UALib.Prelude.Extensionality.html#3793" class="Bound">g</a>

<a id="3819" href="UALib.Prelude.Extensionality.html#3729" class="Function">dintensionality</a> <a id="3835" href="UALib.Prelude.Preliminaries.html#5570" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a> <a id="3840" class="Symbol">_</a> <a id="3842" class="Symbol">=</a> <a id="3844" href="UALib.Prelude.Preliminaries.html#5570" class="InductiveConstructor">𝓇ℯ𝒻𝓁</a>

</pre>




-------------------------------------

[← UALib.Prelude.Inverses](UALib.Prelude.Inverses.html)
<span style="float:right;">[UALib.Algebras →](UALib.Algebras.html)</span>

{% include UALib.Links.md %}
