---
layout: default
title : UALib.Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebra-types">Algebra Types</a>

This section presents the [UALib.Algebras.Algebras] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="300" class="Symbol">{-#</a> <a id="304" class="Keyword">OPTIONS</a> <a id="312" class="Pragma">--without-K</a> <a id="324" class="Pragma">--exact-split</a> <a id="338" class="Pragma">--safe</a> <a id="345" class="Symbol">#-}</a>

<a id="350" class="Keyword">module</a> <a id="357" href="UALib.Algebras.Algebras.html" class="Module">UALib.Algebras.Algebras</a> <a id="381" class="Keyword">where</a>

<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="426" class="Keyword">public</a>

<a id="434" class="Keyword">open</a> <a id="439" class="Keyword">import</a> <a id="446" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="474" class="Keyword">using</a> <a id="480" class="Symbol">(</a><a id="481" href="universes.html#504" class="Primitive">𝓤₀</a><a id="483" class="Symbol">;</a> <a id="485" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="486" class="Symbol">;</a> <a id="488" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="489" class="Symbol">)</a> <a id="491" class="Keyword">public</a>

</pre>

-------------------------------

#### <a id="algebra-types">Algebra types</a>

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe 𝓤, we define the type of **algebras in the signature** 𝑆 (or 𝑆-**algebras**) and with **domain** (or **carrier** or **universe**) `𝐴 : 𝓤 ̇` as follows

<pre class="Agda">

<a id="Algebra"></a><a id="811" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a>   <a id="821" class="Comment">-- alias</a>
 <a id="∞-algebra"></a><a id="831" href="UALib.Algebras.Algebras.html#831" class="Function">∞-algebra</a> <a id="841" class="Symbol">:</a> <a id="843" class="Symbol">(</a><a id="844" href="UALib.Algebras.Algebras.html#844" class="Bound">𝓤</a> <a id="846" class="Symbol">:</a> <a id="848" href="universes.html#551" class="Postulate">Universe</a><a id="856" class="Symbol">)(</a><a id="858" href="UALib.Algebras.Algebras.html#858" class="Bound">𝑆</a> <a id="860" class="Symbol">:</a> <a id="862" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a> <a id="872" href="universes.html#613" class="Generalizable">𝓞</a> <a id="874" href="universes.html#617" class="Generalizable">𝓥</a><a id="875" class="Symbol">)</a> <a id="877" class="Symbol">→</a>  <a id="880" href="universes.html#613" class="Generalizable">𝓞</a> <a id="882" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="884" href="universes.html#617" class="Generalizable">𝓥</a> <a id="886" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="888" href="UALib.Algebras.Algebras.html#844" class="Bound">𝓤</a> <a id="890" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="892" href="universes.html#758" class="Function Operator">̇</a>

<a id="895" href="UALib.Algebras.Algebras.html#831" class="Function">∞-algebra</a> <a id="905" href="UALib.Algebras.Algebras.html#905" class="Bound">𝓤</a>  <a id="908" href="UALib.Algebras.Algebras.html#908" class="Bound">𝑆</a> <a id="910" class="Symbol">=</a> <a id="912" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="914" href="UALib.Algebras.Algebras.html#914" class="Bound">A</a> <a id="916" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="918" href="UALib.Algebras.Algebras.html#905" class="Bound">𝓤</a> <a id="920" href="universes.html#758" class="Function Operator">̇</a> <a id="922" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="924" class="Symbol">((</a><a id="926" href="UALib.Algebras.Algebras.html#926" class="Bound">f</a> <a id="928" class="Symbol">:</a> <a id="930" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="932" href="UALib.Algebras.Algebras.html#908" class="Bound">𝑆</a> <a id="934" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="935" class="Symbol">)</a> <a id="937" class="Symbol">→</a> <a id="939" href="UALib.Algebras.Signatures.html#820" class="Function">Op</a> <a id="942" class="Symbol">(</a><a id="943" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="945" href="UALib.Algebras.Algebras.html#908" class="Bound">𝑆</a> <a id="947" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="949" href="UALib.Algebras.Algebras.html#926" class="Bound">f</a><a id="950" class="Symbol">)</a> <a id="952" href="UALib.Algebras.Algebras.html#914" class="Bound">A</a><a id="953" class="Symbol">)</a>
<a id="955" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="963" class="Symbol">=</a> <a id="965" href="UALib.Algebras.Algebras.html#831" class="Function">∞-algebra</a>

</pre>

We may refer to an inhabitant of this type as a "∞-algebra" because its domain can be an arbitrary type, say, `A : 𝓤 ̇` &nbsp;&nbsp; and need not be truncated at some level; in particular, `A` need to be a set. (See the [discussion of truncation and sets](UALib.Prelude.Preliminaries.html#truncation).)

We might take this opportunity to define the type of "0-algebras" (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, we will only need to know that the domains of our algebras are sets in a few places in the UALib, so it seems preferable to work with general ∞-algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.

The type `Algebra 𝓤 𝑆` itself has a type; it is `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇`. This type appears so often in the UALib that we will define the following shorthand for its universe level.

```agda
OV : Universe → Universe
OV = λ 𝓤 → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
```

<!-- We can now write simply `Algebra 𝓤 𝑆 : OV 𝓤` in place of the laborious ``Algebra 𝓤 𝑆 : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`. -->

---------------------------------------

#### <a id="algebras-as-record-types">Algebras as record types</a>

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

<pre class="Agda">

<a id="2353" class="Keyword">module</a> <a id="2360" href="UALib.Algebras.Algebras.html#2360" class="Module">_</a> <a id="2362" class="Symbol">{</a><a id="2363" href="UALib.Algebras.Algebras.html#2363" class="Bound">𝓞</a> <a id="2365" href="UALib.Algebras.Algebras.html#2365" class="Bound">𝓥</a> <a id="2367" class="Symbol">:</a> <a id="2369" href="universes.html#551" class="Postulate">Universe</a><a id="2377" class="Symbol">}</a> <a id="2379" class="Keyword">where</a>
 <a id="2386" class="Keyword">record</a> <a id="2393" href="UALib.Algebras.Algebras.html#2393" class="Record">algebra</a> <a id="2401" class="Symbol">(</a><a id="2402" href="UALib.Algebras.Algebras.html#2402" class="Bound">𝓤</a> <a id="2404" class="Symbol">:</a> <a id="2406" href="universes.html#551" class="Postulate">Universe</a><a id="2414" class="Symbol">)</a> <a id="2416" class="Symbol">(</a><a id="2417" href="UALib.Algebras.Algebras.html#2417" class="Bound">𝑆</a> <a id="2419" class="Symbol">:</a> <a id="2421" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a> <a id="2431" href="UALib.Algebras.Algebras.html#2363" class="Bound">𝓞</a> <a id="2433" href="UALib.Algebras.Algebras.html#2365" class="Bound">𝓥</a><a id="2434" class="Symbol">)</a> <a id="2436" class="Symbol">:</a> <a id="2438" class="Symbol">(</a><a id="2439" href="UALib.Algebras.Algebras.html#2363" class="Bound">𝓞</a> <a id="2441" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2443" href="UALib.Algebras.Algebras.html#2365" class="Bound">𝓥</a> <a id="2445" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2447" href="UALib.Algebras.Algebras.html#2402" class="Bound">𝓤</a><a id="2448" class="Symbol">)</a> <a id="2450" href="universes.html#527" class="Primitive Operator">⁺</a> <a id="2452" href="universes.html#758" class="Function Operator">̇</a> <a id="2454" class="Keyword">where</a>
  <a id="2462" class="Keyword">constructor</a> <a id="2474" href="UALib.Algebras.Algebras.html#2474" class="InductiveConstructor">mkalg</a>
  <a id="2482" class="Keyword">field</a>
   <a id="2491" href="UALib.Algebras.Algebras.html#2491" class="Field">univ</a> <a id="2496" class="Symbol">:</a> <a id="2498" href="UALib.Algebras.Algebras.html#2402" class="Bound">𝓤</a> <a id="2500" href="universes.html#758" class="Function Operator">̇</a>
   <a id="2505" href="UALib.Algebras.Algebras.html#2505" class="Field">op</a> <a id="2508" class="Symbol">:</a> <a id="2510" class="Symbol">(</a><a id="2511" href="UALib.Algebras.Algebras.html#2511" class="Bound">f</a> <a id="2513" class="Symbol">:</a> <a id="2515" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="2517" href="UALib.Algebras.Algebras.html#2417" class="Bound">𝑆</a> <a id="2519" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="2520" class="Symbol">)</a> <a id="2522" class="Symbol">→</a> <a id="2524" class="Symbol">((</a><a id="2526" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="2528" href="UALib.Algebras.Algebras.html#2417" class="Bound">𝑆</a> <a id="2530" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="2532" href="UALib.Algebras.Algebras.html#2511" class="Bound">f</a><a id="2533" class="Symbol">)</a> <a id="2535" class="Symbol">→</a> <a id="2537" href="UALib.Algebras.Algebras.html#2491" class="Field">univ</a><a id="2541" class="Symbol">)</a> <a id="2543" class="Symbol">→</a> <a id="2545" href="UALib.Algebras.Algebras.html#2491" class="Field">univ</a>


</pre>

(Recall, the type `Signature 𝓞 𝓥` is simply defined as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.)

Of course, we can go back and forth between the two representations of algebras, like so.

<pre class="Agda">

<a id="2775" class="Keyword">module</a> <a id="2782" href="UALib.Algebras.Algebras.html#2782" class="Module">_</a> <a id="2784" class="Symbol">{</a><a id="2785" href="UALib.Algebras.Algebras.html#2785" class="Bound">𝓤</a> <a id="2787" href="UALib.Algebras.Algebras.html#2787" class="Bound">𝓞</a> <a id="2789" href="UALib.Algebras.Algebras.html#2789" class="Bound">𝓥</a> <a id="2791" class="Symbol">:</a> <a id="2793" href="universes.html#551" class="Postulate">Universe</a><a id="2801" class="Symbol">}</a> <a id="2803" class="Symbol">{</a><a id="2804" href="UALib.Algebras.Algebras.html#2804" class="Bound">𝑆</a> <a id="2806" class="Symbol">:</a> <a id="2808" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a> <a id="2818" href="UALib.Algebras.Algebras.html#2787" class="Bound">𝓞</a> <a id="2820" href="UALib.Algebras.Algebras.html#2789" class="Bound">𝓥</a><a id="2821" class="Symbol">}</a> <a id="2823" class="Keyword">where</a>

 <a id="2831" class="Keyword">open</a> <a id="2836" href="UALib.Algebras.Algebras.html#2393" class="Module">algebra</a>

 <a id="2846" href="UALib.Algebras.Algebras.html#2846" class="Function">algebra→Algebra</a> <a id="2862" class="Symbol">:</a> <a id="2864" href="UALib.Algebras.Algebras.html#2393" class="Record">algebra</a> <a id="2872" href="UALib.Algebras.Algebras.html#2785" class="Bound">𝓤</a> <a id="2874" href="UALib.Algebras.Algebras.html#2804" class="Bound">𝑆</a> <a id="2876" class="Symbol">→</a> <a id="2878" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="2886" href="UALib.Algebras.Algebras.html#2785" class="Bound">𝓤</a> <a id="2888" href="UALib.Algebras.Algebras.html#2804" class="Bound">𝑆</a>
 <a id="2891" href="UALib.Algebras.Algebras.html#2846" class="Function">algebra→Algebra</a> <a id="2907" href="UALib.Algebras.Algebras.html#2907" class="Bound">𝑨</a> <a id="2909" class="Symbol">=</a> <a id="2911" class="Symbol">(</a><a id="2912" href="UALib.Algebras.Algebras.html#2491" class="Field">univ</a> <a id="2917" href="UALib.Algebras.Algebras.html#2907" class="Bound">𝑨</a> <a id="2919" href="UALib.Prelude.Preliminaries.html#5763" class="InductiveConstructor Operator">,</a> <a id="2921" href="UALib.Algebras.Algebras.html#2505" class="Field">op</a> <a id="2924" href="UALib.Algebras.Algebras.html#2907" class="Bound">𝑨</a><a id="2925" class="Symbol">)</a>

 <a id="2929" href="UALib.Algebras.Algebras.html#2929" class="Function">Algebra→algebra</a> <a id="2945" class="Symbol">:</a> <a id="2947" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="2955" href="UALib.Algebras.Algebras.html#2785" class="Bound">𝓤</a> <a id="2957" href="UALib.Algebras.Algebras.html#2804" class="Bound">𝑆</a> <a id="2959" class="Symbol">→</a> <a id="2961" href="UALib.Algebras.Algebras.html#2393" class="Record">algebra</a> <a id="2969" href="UALib.Algebras.Algebras.html#2785" class="Bound">𝓤</a> <a id="2971" href="UALib.Algebras.Algebras.html#2804" class="Bound">𝑆</a>
 <a id="2974" href="UALib.Algebras.Algebras.html#2929" class="Function">Algebra→algebra</a> <a id="2990" href="UALib.Algebras.Algebras.html#2990" class="Bound">𝑨</a> <a id="2992" class="Symbol">=</a> <a id="2994" href="UALib.Algebras.Algebras.html#2474" class="InductiveConstructor">mkalg</a> <a id="3000" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3002" href="UALib.Algebras.Algebras.html#2990" class="Bound">𝑨</a> <a id="3004" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3006" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3008" href="UALib.Algebras.Algebras.html#2990" class="Bound">𝑨</a> <a id="3010" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a>

</pre>

----------------------------------------

#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We conclude this module by defining a convenient shorthand for the interpretation of an operation symbol that we will use often.  It looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with.

<pre class="Agda">

 <a id="3426" href="UALib.Algebras.Algebras.html#3426" class="Function Operator">_̂_</a> <a id="3430" class="Symbol">:</a> <a id="3432" class="Symbol">(</a><a id="3433" href="UALib.Algebras.Algebras.html#3433" class="Bound">f</a> <a id="3435" class="Symbol">:</a> <a id="3437" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3439" href="UALib.Algebras.Algebras.html#2804" class="Bound">𝑆</a> <a id="3441" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="3442" class="Symbol">)(</a><a id="3444" href="UALib.Algebras.Algebras.html#3444" class="Bound">𝑨</a> <a id="3446" class="Symbol">:</a> <a id="3448" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="3456" href="UALib.Algebras.Algebras.html#2785" class="Bound">𝓤</a> <a id="3458" href="UALib.Algebras.Algebras.html#2804" class="Bound">𝑆</a><a id="3459" class="Symbol">)</a> <a id="3461" class="Symbol">→</a> <a id="3463" class="Symbol">(</a><a id="3464" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3466" href="UALib.Algebras.Algebras.html#2804" class="Bound">𝑆</a> <a id="3468" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3470" href="UALib.Algebras.Algebras.html#3433" class="Bound">f</a>  <a id="3473" class="Symbol">→</a>  <a id="3476" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3478" href="UALib.Algebras.Algebras.html#3444" class="Bound">𝑨</a> <a id="3480" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="3481" class="Symbol">)</a> <a id="3483" class="Symbol">→</a> <a id="3485" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="3487" href="UALib.Algebras.Algebras.html#3444" class="Bound">𝑨</a> <a id="3489" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a>

 <a id="3493" href="UALib.Algebras.Algebras.html#3493" class="Bound">f</a> <a id="3495" href="UALib.Algebras.Algebras.html#3426" class="Function Operator">̂</a> <a id="3497" href="UALib.Algebras.Algebras.html#3497" class="Bound">𝑨</a> <a id="3499" class="Symbol">=</a> <a id="3501" class="Symbol">λ</a> <a id="3503" href="UALib.Algebras.Algebras.html#3503" class="Bound">x</a> <a id="3505" class="Symbol">→</a> <a id="3507" class="Symbol">(</a><a id="3508" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3510" href="UALib.Algebras.Algebras.html#3497" class="Bound">𝑨</a> <a id="3512" href="UALib.Prelude.Preliminaries.html#10452" class="Function Operator">∥</a> <a id="3514" href="UALib.Algebras.Algebras.html#3493" class="Bound">f</a><a id="3515" class="Symbol">)</a> <a id="3517" href="UALib.Algebras.Algebras.html#3503" class="Bound">x</a>

</pre>

#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

Finally, we will want to assume that we always have at our disposal an arbitrary collection \ab X of variable symbols such that, for every algebra \ab 𝑨, no matter the type of its domain, we have a surjective map \ab{h₀} \as : \ab X \as → \aiab{∣}{𝑨} from variables onto the domain of \ab 𝑨.

<pre class="Agda">

<a id="_↠_"></a><a id="3925" href="UALib.Algebras.Algebras.html#3925" class="Function Operator">_↠_</a> <a id="3929" class="Symbol">:</a> <a id="3931" class="Symbol">{</a><a id="3932" href="UALib.Algebras.Algebras.html#3932" class="Bound">𝑆</a> <a id="3934" class="Symbol">:</a> <a id="3936" href="UALib.Algebras.Signatures.html#1452" class="Function">Signature</a> <a id="3946" href="universes.html#613" class="Generalizable">𝓞</a> <a id="3948" href="universes.html#617" class="Generalizable">𝓥</a><a id="3949" class="Symbol">}{</a><a id="3951" href="UALib.Algebras.Algebras.html#3951" class="Bound">𝓤</a> <a id="3953" href="UALib.Algebras.Algebras.html#3953" class="Bound">𝓧</a> <a id="3955" class="Symbol">:</a> <a id="3957" href="universes.html#551" class="Postulate">Universe</a><a id="3965" class="Symbol">}</a> <a id="3967" class="Symbol">→</a> <a id="3969" href="UALib.Algebras.Algebras.html#3953" class="Bound">𝓧</a> <a id="3971" href="universes.html#758" class="Function Operator">̇</a> <a id="3973" class="Symbol">→</a> <a id="3975" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="3983" href="UALib.Algebras.Algebras.html#3951" class="Bound">𝓤</a> <a id="3985" href="UALib.Algebras.Algebras.html#3932" class="Bound">𝑆</a> <a id="3987" class="Symbol">→</a> <a id="3989" href="UALib.Algebras.Algebras.html#3953" class="Bound">𝓧</a> <a id="3991" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3993" href="UALib.Algebras.Algebras.html#3951" class="Bound">𝓤</a> <a id="3995" href="universes.html#758" class="Function Operator">̇</a>
<a id="3997" href="UALib.Algebras.Algebras.html#3997" class="Bound">X</a> <a id="3999" href="UALib.Algebras.Algebras.html#3925" class="Function Operator">↠</a> <a id="4001" href="UALib.Algebras.Algebras.html#4001" class="Bound">𝑨</a> <a id="4003" class="Symbol">=</a> <a id="4005" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4007" href="UALib.Algebras.Algebras.html#4007" class="Bound">h</a> <a id="4009" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4011" class="Symbol">(</a><a id="4012" href="UALib.Algebras.Algebras.html#3997" class="Bound">X</a> <a id="4014" class="Symbol">→</a> <a id="4016" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a> <a id="4018" href="UALib.Algebras.Algebras.html#4001" class="Bound">𝑨</a> <a id="4020" href="UALib.Prelude.Preliminaries.html#10371" class="Function Operator">∣</a><a id="4021" class="Symbol">)</a> <a id="4023" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4025" href="UALib.Prelude.Inverses.html#2377" class="Function">Epic</a> <a id="4030" href="UALib.Algebras.Algebras.html#4007" class="Bound">h</a>

</pre>

-------------------------------------

[← UALib.Algebras.Signatures](UALib.Algebras.Signatures.html)
<span style="float:right;">[UALib.Algebras.Products →](UALib.Algebras.Products.html)</span>


{% include UALib.Links.md %}
