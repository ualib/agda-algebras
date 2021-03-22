---
layout: default
title : Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebras">Algebras</a>

This section presents the [Algebras.Algebras][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="280" class="Symbol">{-#</a> <a id="284" class="Keyword">OPTIONS</a> <a id="292" class="Pragma">--without-K</a> <a id="304" class="Pragma">--exact-split</a> <a id="318" class="Pragma">--safe</a> <a id="325" class="Symbol">#-}</a>

<a id="330" class="Keyword">module</a> <a id="337" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="355" class="Keyword">where</a>

<a id="362" class="Keyword">open</a> <a id="367" class="Keyword">import</a> <a id="374" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="394" class="Keyword">public</a>

</pre>


#### <a id="algebra-types">Algebra types</a>

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe `𝓤`, we define the type of *algebras in the signature* 𝑆 (or 𝑆-*algebras*) and with *domain* (or *carrier* or *universe*) `𝐴 : 𝓤 ̇` as follows

<pre class="Agda">

<a id="Algebra"></a><a id="674" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="682" class="Symbol">:</a> <a id="684" class="Symbol">(</a><a id="685" href="Algebras.Algebras.html#685" class="Bound">𝓤</a> <a id="687" class="Symbol">:</a> <a id="689" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="697" class="Symbol">)(</a><a id="699" href="Algebras.Algebras.html#699" class="Bound">𝑆</a> <a id="701" class="Symbol">:</a> <a id="703" href="Algebras.Signatures.html#1266" class="Function">Signature</a> <a id="713" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="715" href="Universes.html#262" class="Generalizable">𝓥</a><a id="716" class="Symbol">)</a> <a id="718" class="Symbol">→</a>  <a id="721" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="723" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="725" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="727" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="729" href="Algebras.Algebras.html#685" class="Bound">𝓤</a> <a id="731" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="733" href="Universes.html#403" class="Function Operator">̇</a>
<a id="735" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="743" href="Algebras.Algebras.html#743" class="Bound">𝓤</a>  <a id="746" href="Algebras.Algebras.html#746" class="Bound">𝑆</a> <a id="748" class="Symbol">=</a> <a id="750" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="752" href="Algebras.Algebras.html#752" class="Bound">A</a> <a id="754" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="756" href="Algebras.Algebras.html#743" class="Bound">𝓤</a> <a id="758" href="Universes.html#403" class="Function Operator">̇</a> <a id="760" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="762" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="764" href="Algebras.Algebras.html#764" class="Bound">f</a> <a id="766" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="768" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="770" href="Algebras.Algebras.html#746" class="Bound">𝑆</a> <a id="772" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="774" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="776" href="Algebras.Signatures.html#668" class="Function">Op</a> <a id="779" class="Symbol">(</a><a id="780" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="782" href="Algebras.Algebras.html#746" class="Bound">𝑆</a> <a id="784" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="786" href="Algebras.Algebras.html#764" class="Bound">f</a><a id="787" class="Symbol">)</a> <a id="789" href="Algebras.Algebras.html#752" class="Bound">A</a>

</pre>

We could refer to an inhabitant of this type as a ∞-*algebra* because its domain can be an arbitrary type, say, `A : 𝓤 ̇` and need not be truncated at some level; in particular, `A` need to be a set. (See the [Prelude.Preliminaries.html#truncation](Prelude.Preliminaries.html#truncation).)

We might take this opportunity to define the type of 0-*algebras* (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, below we will only need to know that the domains of our algebras are sets in a few places in the [UALib][], so it seems preferable to work with general (∞-)algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.



#### <a id="algebras-as-record-types">Algebras as record types</a>

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

<pre class="Agda">

<a id="1781" class="Keyword">record</a> <a id="algebra"></a><a id="1788" href="Algebras.Algebras.html#1788" class="Record">algebra</a> <a id="1796" class="Symbol">(</a><a id="1797" href="Algebras.Algebras.html#1797" class="Bound">𝓤</a> <a id="1799" class="Symbol">:</a> <a id="1801" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1809" class="Symbol">)</a> <a id="1811" class="Symbol">(</a><a id="1812" href="Algebras.Algebras.html#1812" class="Bound">𝑆</a> <a id="1814" class="Symbol">:</a> <a id="1816" href="Algebras.Signatures.html#1266" class="Function">Signature</a> <a id="1826" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="1828" href="Universes.html#262" class="Generalizable">𝓥</a><a id="1829" class="Symbol">)</a> <a id="1831" class="Symbol">:</a> <a id="1833" class="Symbol">(</a><a id="1834" href="Algebras.Algebras.html#1826" class="Bound">𝓞</a> <a id="1836" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1838" href="Algebras.Algebras.html#1828" class="Bound">𝓥</a> <a id="1840" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1842" href="Algebras.Algebras.html#1797" class="Bound">𝓤</a><a id="1843" class="Symbol">)</a> <a id="1845" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1847" href="Universes.html#403" class="Function Operator">̇</a> <a id="1849" class="Keyword">where</a>
 <a id="1856" class="Keyword">constructor</a> <a id="mkalg"></a><a id="1868" href="Algebras.Algebras.html#1868" class="InductiveConstructor">mkalg</a>
 <a id="1875" class="Keyword">field</a>
  <a id="algebra.univ"></a><a id="1883" href="Algebras.Algebras.html#1883" class="Field">univ</a> <a id="1888" class="Symbol">:</a> <a id="1890" href="Algebras.Algebras.html#1797" class="Bound">𝓤</a> <a id="1892" href="Universes.html#403" class="Function Operator">̇</a>
  <a id="algebra.op"></a><a id="1896" href="Algebras.Algebras.html#1896" class="Field">op</a> <a id="1899" class="Symbol">:</a> <a id="1901" class="Symbol">(</a><a id="1902" href="Algebras.Algebras.html#1902" class="Bound">f</a> <a id="1904" class="Symbol">:</a> <a id="1906" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="1908" href="Algebras.Algebras.html#1812" class="Bound">𝑆</a> <a id="1910" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="1911" class="Symbol">)</a> <a id="1913" class="Symbol">→</a> <a id="1915" class="Symbol">((</a><a id="1917" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="1919" href="Algebras.Algebras.html#1812" class="Bound">𝑆</a> <a id="1921" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="1923" href="Algebras.Algebras.html#1902" class="Bound">f</a><a id="1924" class="Symbol">)</a> <a id="1926" class="Symbol">→</a> <a id="1928" href="Algebras.Algebras.html#1883" class="Field">univ</a><a id="1932" class="Symbol">)</a> <a id="1934" class="Symbol">→</a> <a id="1936" href="Algebras.Algebras.html#1883" class="Field">univ</a>


</pre>

Recall, the type `Signature 𝓞 𝓥` was defined in the [Algebras.Signature][] module as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.

If for some reason we want to use both representations of algebras and move back and forth between them, this is easily accomplished with the following functions.

<pre class="Agda">

<a id="2268" class="Keyword">module</a> <a id="2275" href="Algebras.Algebras.html#2275" class="Module">_</a> <a id="2277" class="Symbol">{</a><a id="2278" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="2280" class="Symbol">:</a> <a id="2282" href="Algebras.Signatures.html#1266" class="Function">Signature</a> <a id="2292" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="2294" href="Universes.html#262" class="Generalizable">𝓥</a><a id="2295" class="Symbol">}</a> <a id="2297" class="Keyword">where</a>

 <a id="2305" class="Keyword">open</a> <a id="2310" href="Algebras.Algebras.html#1788" class="Module">algebra</a>

 <a id="2320" href="Algebras.Algebras.html#2320" class="Function">algebra→Algebra</a> <a id="2336" class="Symbol">:</a> <a id="2338" href="Algebras.Algebras.html#1788" class="Record">algebra</a> <a id="2346" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2348" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="2350" class="Symbol">→</a> <a id="2352" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2360" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2362" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a>
 <a id="2365" href="Algebras.Algebras.html#2320" class="Function">algebra→Algebra</a> <a id="2381" href="Algebras.Algebras.html#2381" class="Bound">𝑨</a> <a id="2383" class="Symbol">=</a> <a id="2385" class="Symbol">(</a><a id="2386" href="Algebras.Algebras.html#1883" class="Field">univ</a> <a id="2391" href="Algebras.Algebras.html#2381" class="Bound">𝑨</a> <a id="2393" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="2395" href="Algebras.Algebras.html#1896" class="Field">op</a> <a id="2398" href="Algebras.Algebras.html#2381" class="Bound">𝑨</a><a id="2399" class="Symbol">)</a>

 <a id="2403" href="Algebras.Algebras.html#2403" class="Function">Algebra→algebra</a> <a id="2419" class="Symbol">:</a> <a id="2421" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2429" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2431" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="2433" class="Symbol">→</a> <a id="2435" href="Algebras.Algebras.html#1788" class="Record">algebra</a> <a id="2443" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2445" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a>
 <a id="2448" href="Algebras.Algebras.html#2403" class="Function">Algebra→algebra</a> <a id="2464" href="Algebras.Algebras.html#2464" class="Bound">𝑨</a> <a id="2466" class="Symbol">=</a> <a id="2468" href="Algebras.Algebras.html#1868" class="InductiveConstructor">mkalg</a> <a id="2474" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="2476" href="Algebras.Algebras.html#2464" class="Bound">𝑨</a> <a id="2478" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="2480" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="2482" href="Algebras.Algebras.html#2464" class="Bound">𝑨</a> <a id="2484" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a>

</pre>




#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with, so we will use this new notation almost exclusively in the remaining modules of the [UALib][].

<pre class="Agda">

 <a id="2912" href="Algebras.Algebras.html#2912" class="Function Operator">_̂_</a> <a id="2916" class="Symbol">:</a> <a id="2918" class="Symbol">(</a><a id="2919" href="Algebras.Algebras.html#2919" class="Bound">𝑓</a> <a id="2921" class="Symbol">:</a> <a id="2923" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="2925" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="2927" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="2928" class="Symbol">)(</a><a id="2930" href="Algebras.Algebras.html#2930" class="Bound">𝑨</a> <a id="2932" class="Symbol">:</a> <a id="2934" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2942" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2944" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a><a id="2945" class="Symbol">)</a> <a id="2947" class="Symbol">→</a> <a id="2949" class="Symbol">(</a><a id="2950" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="2952" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="2954" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="2956" href="Algebras.Algebras.html#2919" class="Bound">𝑓</a>  <a id="2959" class="Symbol">→</a>  <a id="2962" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="2964" href="Algebras.Algebras.html#2930" class="Bound">𝑨</a> <a id="2966" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="2967" class="Symbol">)</a> <a id="2969" class="Symbol">→</a> <a id="2971" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="2973" href="Algebras.Algebras.html#2930" class="Bound">𝑨</a> <a id="2975" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a>

 <a id="2979" href="Algebras.Algebras.html#2979" class="Bound">𝑓</a> <a id="2981" href="Algebras.Algebras.html#2912" class="Function Operator">̂</a> <a id="2983" href="Algebras.Algebras.html#2983" class="Bound">𝑨</a> <a id="2985" class="Symbol">=</a> <a id="2987" class="Symbol">λ</a> <a id="2989" href="Algebras.Algebras.html#2989" class="Bound">𝑎</a> <a id="2991" class="Symbol">→</a> <a id="2993" class="Symbol">(</a><a id="2994" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="2996" href="Algebras.Algebras.html#2983" class="Bound">𝑨</a> <a id="2998" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="3000" href="Algebras.Algebras.html#2979" class="Bound">𝑓</a><a id="3001" class="Symbol">)</a> <a id="3003" href="Algebras.Algebras.html#2989" class="Bound">𝑎</a>

</pre>

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.


#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

We sometimes want to assume that we have at our disposal an arbitrary collection `X` of variable symbols such that, for every algebra `𝑨`, no matter the type of its domain, we have a surjective map `h₀ : X → ∣ 𝑨 ∣` from variables onto the domain of `𝑨`.  We may use the following definition to express this assumption when we need it.

<pre class="Agda">

 <a id="3671" href="Algebras.Algebras.html#3671" class="Function Operator">_↠_</a> <a id="3675" class="Symbol">:</a> <a id="3677" class="Symbol">{</a><a id="3678" href="Algebras.Algebras.html#3678" class="Bound">𝓤</a> <a id="3680" href="Algebras.Algebras.html#3680" class="Bound">𝓧</a> <a id="3682" class="Symbol">:</a> <a id="3684" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3692" class="Symbol">}</a> <a id="3694" class="Symbol">→</a> <a id="3696" href="Algebras.Algebras.html#3680" class="Bound">𝓧</a> <a id="3698" href="Universes.html#403" class="Function Operator">̇</a> <a id="3700" class="Symbol">→</a> <a id="3702" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3710" href="Algebras.Algebras.html#3678" class="Bound">𝓤</a> <a id="3712" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="3714" class="Symbol">→</a> <a id="3716" href="Algebras.Algebras.html#3680" class="Bound">𝓧</a> <a id="3718" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3720" href="Algebras.Algebras.html#3678" class="Bound">𝓤</a> <a id="3722" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3725" href="Algebras.Algebras.html#3725" class="Bound">X</a> <a id="3727" href="Algebras.Algebras.html#3671" class="Function Operator">↠</a> <a id="3729" href="Algebras.Algebras.html#3729" class="Bound">𝑨</a> <a id="3731" class="Symbol">=</a> <a id="3733" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3735" href="Algebras.Algebras.html#3735" class="Bound">h</a> <a id="3737" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3739" class="Symbol">(</a><a id="3740" href="Algebras.Algebras.html#3725" class="Bound">X</a> <a id="3742" class="Symbol">→</a> <a id="3744" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="3746" href="Algebras.Algebras.html#3729" class="Bound">𝑨</a> <a id="3748" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="3749" class="Symbol">)</a> <a id="3751" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3753" href="Prelude.Inverses.html#2039" class="Function">Epic</a> <a id="3758" href="Algebras.Algebras.html#3735" class="Bound">h</a>

</pre>

Now we can assert, in a specific module, the existence of the surjective map described above by including the following line in that module's declaration, like so.

module _ {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨} where

Then fst(𝕏 𝑨) will denote the surjective map h₀ : X → ∣ 𝑨 ∣, and snd(𝕏 𝑨) will be a proof that h₀ is surjective.




#### <a id="lifts-of-algebras">Lifts of algebras</a>

Here we define some domain-specific lifting tools for our operation and algebra types.

<pre class="Agda">

 <a id="4286" class="Keyword">open</a> <a id="4291" href="Prelude.Lifts.html#2589" class="Module">Lift</a>

 <a id="4298" href="Algebras.Algebras.html#4298" class="Function">lift-op</a> <a id="4306" class="Symbol">:</a> <a id="4308" class="Symbol">{</a><a id="4309" href="Algebras.Algebras.html#4309" class="Bound">I</a> <a id="4311" class="Symbol">:</a> <a id="4313" href="Algebras.Algebras.html#2294" class="Bound">𝓥</a> <a id="4315" href="Universes.html#403" class="Function Operator">̇</a><a id="4316" class="Symbol">}{</a><a id="4318" href="Algebras.Algebras.html#4318" class="Bound">A</a> <a id="4320" class="Symbol">:</a> <a id="4322" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4324" href="Universes.html#403" class="Function Operator">̇</a><a id="4325" class="Symbol">}</a> <a id="4327" class="Symbol">→</a> <a id="4329" class="Symbol">((</a><a id="4331" href="Algebras.Algebras.html#4309" class="Bound">I</a> <a id="4333" class="Symbol">→</a> <a id="4335" href="Algebras.Algebras.html#4318" class="Bound">A</a><a id="4336" class="Symbol">)</a> <a id="4338" class="Symbol">→</a> <a id="4340" href="Algebras.Algebras.html#4318" class="Bound">A</a><a id="4341" class="Symbol">)</a> <a id="4343" class="Symbol">→</a> <a id="4345" class="Symbol">(</a><a id="4346" href="Algebras.Algebras.html#4346" class="Bound">𝓦</a> <a id="4348" class="Symbol">:</a> <a id="4350" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4358" class="Symbol">)</a>
  <a id="4362" class="Symbol">→</a>        <a id="4371" class="Symbol">((</a><a id="4373" href="Algebras.Algebras.html#4309" class="Bound">I</a> <a id="4375" class="Symbol">→</a> <a id="4377" href="Prelude.Lifts.html#2589" class="Record">Lift</a><a id="4381" class="Symbol">{</a><a id="4382" href="Algebras.Algebras.html#4346" class="Bound">𝓦</a><a id="4383" class="Symbol">}</a> <a id="4385" href="Algebras.Algebras.html#4318" class="Bound">A</a><a id="4386" class="Symbol">)</a> <a id="4388" class="Symbol">→</a> <a id="4390" href="Prelude.Lifts.html#2589" class="Record">Lift</a> <a id="4395" class="Symbol">{</a><a id="4396" href="Algebras.Algebras.html#4346" class="Bound">𝓦</a><a id="4397" class="Symbol">}</a> <a id="4399" href="Algebras.Algebras.html#4318" class="Bound">A</a><a id="4400" class="Symbol">)</a>

 <a id="4404" href="Algebras.Algebras.html#4298" class="Function">lift-op</a> <a id="4412" href="Algebras.Algebras.html#4412" class="Bound">f</a> <a id="4414" href="Algebras.Algebras.html#4414" class="Bound">𝓦</a> <a id="4416" class="Symbol">=</a> <a id="4418" class="Symbol">λ</a> <a id="4420" href="Algebras.Algebras.html#4420" class="Bound">x</a> <a id="4422" class="Symbol">→</a> <a id="4424" href="Prelude.Lifts.html#2651" class="InductiveConstructor">lift</a> <a id="4429" class="Symbol">(</a><a id="4430" href="Algebras.Algebras.html#4412" class="Bound">f</a> <a id="4432" class="Symbol">(λ</a> <a id="4435" href="Algebras.Algebras.html#4435" class="Bound">i</a> <a id="4437" class="Symbol">→</a> <a id="4439" href="Prelude.Lifts.html#2663" class="Field">lower</a> <a id="4445" class="Symbol">(</a><a id="4446" href="Algebras.Algebras.html#4420" class="Bound">x</a> <a id="4448" href="Algebras.Algebras.html#4435" class="Bound">i</a><a id="4449" class="Symbol">)))</a>

 <a id="4455" class="Keyword">open</a> <a id="4460" href="Algebras.Algebras.html#1788" class="Module">algebra</a>

 <a id="4470" href="Algebras.Algebras.html#4470" class="Function">lift-alg</a> <a id="4479" class="Symbol">:</a> <a id="4481" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4489" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4491" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="4493" class="Symbol">→</a> <a id="4495" class="Symbol">(</a><a id="4496" href="Algebras.Algebras.html#4496" class="Bound">𝓦</a> <a id="4498" class="Symbol">:</a> <a id="4500" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4508" class="Symbol">)</a> <a id="4510" class="Symbol">→</a> <a id="4512" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4520" class="Symbol">(</a><a id="4521" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4523" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4525" href="Algebras.Algebras.html#4496" class="Bound">𝓦</a><a id="4526" class="Symbol">)</a> <a id="4528" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a>
 <a id="4531" href="Algebras.Algebras.html#4470" class="Function">lift-alg</a> <a id="4540" href="Algebras.Algebras.html#4540" class="Bound">𝑨</a> <a id="4542" href="Algebras.Algebras.html#4542" class="Bound">𝓦</a> <a id="4544" class="Symbol">=</a> <a id="4546" href="Prelude.Lifts.html#2589" class="Record">Lift</a> <a id="4551" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4553" href="Algebras.Algebras.html#4540" class="Bound">𝑨</a> <a id="4555" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4557" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="4559" class="Symbol">(λ</a> <a id="4562" class="Symbol">(</a><a id="4563" href="Algebras.Algebras.html#4563" class="Bound">𝑓</a> <a id="4565" class="Symbol">:</a> <a id="4567" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4569" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="4571" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="4572" class="Symbol">)</a> <a id="4574" class="Symbol">→</a> <a id="4576" href="Algebras.Algebras.html#4298" class="Function">lift-op</a> <a id="4584" class="Symbol">(</a><a id="4585" href="Algebras.Algebras.html#4563" class="Bound">𝑓</a> <a id="4587" href="Algebras.Algebras.html#2912" class="Function Operator">̂</a> <a id="4589" href="Algebras.Algebras.html#4540" class="Bound">𝑨</a><a id="4590" class="Symbol">)</a> <a id="4592" href="Algebras.Algebras.html#4542" class="Bound">𝓦</a><a id="4593" class="Symbol">)</a>

 <a id="4597" href="Algebras.Algebras.html#4597" class="Function">lift-alg-record-type</a> <a id="4618" class="Symbol">:</a> <a id="4620" href="Algebras.Algebras.html#1788" class="Record">algebra</a> <a id="4628" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4630" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="4632" class="Symbol">→</a> <a id="4634" class="Symbol">(</a><a id="4635" href="Algebras.Algebras.html#4635" class="Bound">𝓦</a> <a id="4637" class="Symbol">:</a> <a id="4639" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4647" class="Symbol">)</a> <a id="4649" class="Symbol">→</a> <a id="4651" href="Algebras.Algebras.html#1788" class="Record">algebra</a> <a id="4659" class="Symbol">(</a><a id="4660" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4662" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4664" href="Algebras.Algebras.html#4635" class="Bound">𝓦</a><a id="4665" class="Symbol">)</a> <a id="4667" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a>
 <a id="4670" href="Algebras.Algebras.html#4597" class="Function">lift-alg-record-type</a> <a id="4691" href="Algebras.Algebras.html#4691" class="Bound">𝑨</a> <a id="4693" href="Algebras.Algebras.html#4693" class="Bound">𝓦</a> <a id="4695" class="Symbol">=</a> <a id="4697" href="Algebras.Algebras.html#1868" class="InductiveConstructor">mkalg</a> <a id="4703" class="Symbol">(</a><a id="4704" href="Prelude.Lifts.html#2589" class="Record">Lift</a> <a id="4709" class="Symbol">(</a><a id="4710" href="Algebras.Algebras.html#1883" class="Field">univ</a> <a id="4715" href="Algebras.Algebras.html#4691" class="Bound">𝑨</a><a id="4716" class="Symbol">))</a> <a id="4719" class="Symbol">(λ</a> <a id="4722" class="Symbol">(</a><a id="4723" href="Algebras.Algebras.html#4723" class="Bound">f</a> <a id="4725" class="Symbol">:</a> <a id="4727" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4729" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a> <a id="4731" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="4732" class="Symbol">)</a> <a id="4734" class="Symbol">→</a> <a id="4736" href="Algebras.Algebras.html#4298" class="Function">lift-op</a> <a id="4744" class="Symbol">((</a><a id="4746" href="Algebras.Algebras.html#1896" class="Field">op</a> <a id="4749" href="Algebras.Algebras.html#4691" class="Bound">𝑨</a><a id="4750" class="Symbol">)</a> <a id="4752" href="Algebras.Algebras.html#4723" class="Bound">f</a><a id="4753" class="Symbol">)</a> <a id="4755" href="Algebras.Algebras.html#4693" class="Bound">𝓦</a><a id="4756" class="Symbol">)</a>

</pre>

We use the function `lift-alg` to resolve errors that arise when working in Agda's noncummulative hierarchy of type universes. (See the discussion in [Prelude.Lifts][].)




#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

If `𝑨` is an algebra and `R` a binary relation, then `compatible 𝑨 R` will represents the assertion that `R` is *compatible* with all basic operations of `𝑨`. Recall, informally this means for every operation symbol `𝑓 : ∣ 𝑆 ∣` and all pairs `𝑎 𝑎' : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` of tuples from the domain of 𝑨, the following implication holds:

if `R (𝑎 i) (𝑎' i)` for all `i`, then  `R ((𝑓 ̂ 𝑨) 𝑎) ((𝑓 ̂ 𝑨) 𝑎')`.

The formal definition representing this notion of compatibility is easy to write down since we already have a type that does all the work.

<pre class="Agda">

 <a id="5589" href="Algebras.Algebras.html#5589" class="Function">compatible</a> <a id="5600" class="Symbol">:</a> <a id="5602" class="Symbol">(</a><a id="5603" href="Algebras.Algebras.html#5603" class="Bound">𝑨</a> <a id="5605" class="Symbol">:</a> <a id="5607" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5615" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5617" href="Algebras.Algebras.html#2278" class="Bound">𝑆</a><a id="5618" class="Symbol">)</a> <a id="5620" class="Symbol">→</a> <a id="5622" href="Relations.Discrete.html#7173" class="Function">Rel</a> <a id="5626" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="5628" href="Algebras.Algebras.html#5603" class="Bound">𝑨</a> <a id="5630" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="5632" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5634" class="Symbol">→</a> <a id="5636" href="Algebras.Algebras.html#2292" class="Bound">𝓞</a> <a id="5638" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5640" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5642" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5644" href="Algebras.Algebras.html#2294" class="Bound">𝓥</a> <a id="5646" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5648" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5650" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5653" href="Algebras.Algebras.html#5589" class="Function">compatible</a>  <a id="5665" href="Algebras.Algebras.html#5665" class="Bound">𝑨</a> <a id="5667" href="Algebras.Algebras.html#5667" class="Bound">R</a> <a id="5669" class="Symbol">=</a> <a id="5671" class="Symbol">∀</a> <a id="5673" href="Algebras.Algebras.html#5673" class="Bound">𝑓</a> <a id="5675" class="Symbol">→</a> <a id="5677" href="Relations.Discrete.html#10243" class="Function">compatible-fun</a> <a id="5692" class="Symbol">(</a><a id="5693" href="Algebras.Algebras.html#5673" class="Bound">𝑓</a> <a id="5695" href="Algebras.Algebras.html#2912" class="Function Operator">̂</a> <a id="5697" href="Algebras.Algebras.html#5665" class="Bound">𝑨</a><a id="5698" class="Symbol">)</a> <a id="5700" href="Algebras.Algebras.html#5667" class="Bound">R</a>

</pre>

Recall, the `compatible-fun` type was defined in [Relations.Discrete][] module.



---------------------------------------



#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations*</a>

This section presents the `continuous-compatibility` submodule of the [Algebras.Algebras][] module.<sup>[*](Algebras.Algebras.html#fn0)</sup>


Next we define a type that represents *compatibility of a continuous relation* with all operations of an algebra. We start by defining compatibility of a continuous relations with a single operation.

<pre class="Agda">

<a id="6295" class="Keyword">module</a> <a id="continuous-compatibility"></a><a id="6302" href="Algebras.Algebras.html#6302" class="Module">continuous-compatibility</a> <a id="6327" class="Symbol">{</a><a id="6328" href="Algebras.Algebras.html#6328" class="Bound">𝑆</a> <a id="6330" class="Symbol">:</a> <a id="6332" href="Algebras.Signatures.html#1266" class="Function">Signature</a> <a id="6342" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="6344" href="Universes.html#262" class="Generalizable">𝓥</a><a id="6345" class="Symbol">}</a> <a id="6347" class="Symbol">{</a><a id="6348" href="Algebras.Algebras.html#6348" class="Bound">𝑨</a> <a id="6350" class="Symbol">:</a> <a id="6352" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="6360" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6362" href="Algebras.Algebras.html#6328" class="Bound">𝑆</a><a id="6363" class="Symbol">}</a> <a id="6365" class="Symbol">{</a><a id="6366" href="Algebras.Algebras.html#6366" class="Bound">I</a> <a id="6368" class="Symbol">:</a> <a id="6370" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6372" href="Universes.html#403" class="Function Operator">̇</a><a id="6373" class="Symbol">}</a> <a id="6375" class="Keyword">where</a>

 <a id="6383" class="Keyword">open</a> <a id="6388" class="Keyword">import</a> <a id="6395" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="6416" class="Keyword">using</a> <a id="6422" class="Symbol">(</a><a id="6423" href="Relations.Continuous.html#3268" class="Function">ConRel</a><a id="6429" class="Symbol">;</a> <a id="6431" href="Relations.Continuous.html#3645" class="Function">lift-con-rel</a><a id="6443" class="Symbol">;</a> <a id="6445" href="Relations.Continuous.html#3747" class="Function">con-compatible-fun</a><a id="6463" class="Symbol">)</a>


 <a id="continuous-compatibility.con-compatible-op"></a><a id="6468" href="Algebras.Algebras.html#6468" class="Function">con-compatible-op</a> <a id="6486" class="Symbol">:</a> <a id="6488" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6490" href="Algebras.Algebras.html#6328" class="Bound">𝑆</a> <a id="6492" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6494" class="Symbol">→</a> <a id="6496" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="6503" href="Algebras.Algebras.html#6366" class="Bound">I</a> <a id="6505" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6507" href="Algebras.Algebras.html#6348" class="Bound">𝑨</a> <a id="6509" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6511" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6513" class="Symbol">→</a> <a id="6515" href="Algebras.Algebras.html#6360" class="Bound">𝓤</a> <a id="6517" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6519" href="Algebras.Algebras.html#6344" class="Bound">𝓥</a> <a id="6521" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6523" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6525" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6528" href="Algebras.Algebras.html#6468" class="Function">con-compatible-op</a> <a id="6546" href="Algebras.Algebras.html#6546" class="Bound">𝑓</a> <a id="6548" href="Algebras.Algebras.html#6548" class="Bound">R</a> <a id="6550" class="Symbol">=</a> <a id="6552" href="Relations.Continuous.html#3747" class="Function">con-compatible-fun</a> <a id="6571" class="Symbol">(λ</a> <a id="6574" href="Algebras.Algebras.html#6574" class="Bound">_</a> <a id="6576" class="Symbol">→</a> <a id="6578" class="Symbol">(</a><a id="6579" href="Algebras.Algebras.html#6546" class="Bound">𝑓</a> <a id="6581" href="Algebras.Algebras.html#2912" class="Function Operator">̂</a> <a id="6583" href="Algebras.Algebras.html#6348" class="Bound">𝑨</a><a id="6584" class="Symbol">))</a> <a id="6587" href="Algebras.Algebras.html#6548" class="Bound">R</a>

</pre>

In case it helps the reader understand `con-compatible-op`, we redefine it explicitly without the help of `con-compatible-fun`.

<pre class="Agda">

 <a id="continuous-compatibility.con-compatible-op&#39;"></a><a id="6746" href="Algebras.Algebras.html#6746" class="Function">con-compatible-op&#39;</a> <a id="6765" class="Symbol">:</a> <a id="6767" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6769" href="Algebras.Algebras.html#6328" class="Bound">𝑆</a> <a id="6771" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6773" class="Symbol">→</a> <a id="6775" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="6782" href="Algebras.Algebras.html#6366" class="Bound">I</a> <a id="6784" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6786" href="Algebras.Algebras.html#6348" class="Bound">𝑨</a> <a id="6788" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6790" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6792" class="Symbol">→</a> <a id="6794" href="Algebras.Algebras.html#6360" class="Bound">𝓤</a> <a id="6796" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6798" href="Algebras.Algebras.html#6344" class="Bound">𝓥</a> <a id="6800" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6802" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6804" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6807" href="Algebras.Algebras.html#6746" class="Function">con-compatible-op&#39;</a> <a id="6826" href="Algebras.Algebras.html#6826" class="Bound">𝑓</a> <a id="6828" href="Algebras.Algebras.html#6828" class="Bound">R</a> <a id="6830" class="Symbol">=</a> <a id="6832" class="Symbol">∀</a> <a id="6834" href="Algebras.Algebras.html#6834" class="Bound">𝕒</a> <a id="6836" class="Symbol">→</a> <a id="6838" class="Symbol">(</a><a id="6839" href="Relations.Continuous.html#3645" class="Function">lift-con-rel</a> <a id="6852" href="Algebras.Algebras.html#6828" class="Bound">R</a><a id="6853" class="Symbol">)</a> <a id="6855" href="Algebras.Algebras.html#6834" class="Bound">𝕒</a> <a id="6857" class="Symbol">→</a> <a id="6859" href="Algebras.Algebras.html#6828" class="Bound">R</a> <a id="6861" class="Symbol">(λ</a> <a id="6864" href="Algebras.Algebras.html#6864" class="Bound">i</a> <a id="6866" class="Symbol">→</a> <a id="6868" class="Symbol">(</a><a id="6869" href="Algebras.Algebras.html#6826" class="Bound">𝑓</a> <a id="6871" href="Algebras.Algebras.html#2912" class="Function Operator">̂</a> <a id="6873" href="Algebras.Algebras.html#6348" class="Bound">𝑨</a><a id="6874" class="Symbol">)</a> <a id="6876" class="Symbol">(</a><a id="6877" href="Algebras.Algebras.html#6834" class="Bound">𝕒</a> <a id="6879" href="Algebras.Algebras.html#6864" class="Bound">i</a><a id="6880" class="Symbol">))</a>

</pre>

where we have let Agda infer the type of `𝕒`, which is `(i : I) → ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`.

With `con-compatible-op` in hand, it is a trivial matter to define a type that represents *compatibility of a continuous relation with an algebra*.

<pre class="Agda">

 <a id="continuous-compatibility.con-compatible"></a><a id="7145" href="Algebras.Algebras.html#7145" class="Function">con-compatible</a> <a id="7160" class="Symbol">:</a> <a id="7162" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="7169" href="Algebras.Algebras.html#6366" class="Bound">I</a> <a id="7171" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="7173" href="Algebras.Algebras.html#6348" class="Bound">𝑨</a> <a id="7175" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="7177" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7179" class="Symbol">→</a> <a id="7181" href="Algebras.Algebras.html#6342" class="Bound">𝓞</a> <a id="7183" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7185" href="Algebras.Algebras.html#6360" class="Bound">𝓤</a> <a id="7187" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7189" href="Algebras.Algebras.html#6344" class="Bound">𝓥</a> <a id="7191" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7193" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7195" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7198" href="Algebras.Algebras.html#7145" class="Function">con-compatible</a> <a id="7213" href="Algebras.Algebras.html#7213" class="Bound">R</a> <a id="7215" class="Symbol">=</a> <a id="7217" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="7219" href="Algebras.Algebras.html#7219" class="Bound">𝑓</a> <a id="7221" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="7223" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="7225" href="Algebras.Algebras.html#6328" class="Bound">𝑆</a> <a id="7227" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="7229" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="7231" href="Algebras.Algebras.html#6468" class="Function">con-compatible-op</a> <a id="7249" href="Algebras.Algebras.html#7219" class="Bound">𝑓</a> <a id="7251" href="Algebras.Algebras.html#7213" class="Bound">R</a>

</pre>



--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>


[← Algebras.Signatures](Algebras.Signatures.html)
<span style="float:right;">[Algebras.Products →](Algebras.Products.html)</span>


{% include UALib.Links.md %}
