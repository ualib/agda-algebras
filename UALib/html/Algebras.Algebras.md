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

<a id="Algebra"></a><a id="674" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="682" class="Symbol">:</a> <a id="684" class="Symbol">(</a><a id="685" href="Algebras.Algebras.html#685" class="Bound">𝓤</a> <a id="687" class="Symbol">:</a> <a id="689" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="697" class="Symbol">)(</a><a id="699" href="Algebras.Algebras.html#699" class="Bound">𝑆</a> <a id="701" class="Symbol">:</a> <a id="703" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="713" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="715" href="Universes.html#262" class="Generalizable">𝓥</a><a id="716" class="Symbol">)</a> <a id="718" class="Symbol">→</a> <a id="720" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="722" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="724" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="726" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="728" href="Algebras.Algebras.html#685" class="Bound">𝓤</a> <a id="730" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="732" href="Universes.html#403" class="Function Operator">̇</a>

<a id="735" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="743" href="Algebras.Algebras.html#743" class="Bound">𝓤</a> <a id="745" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="747" class="Symbol">=</a> <a id="749" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="751" href="Algebras.Algebras.html#751" class="Bound">A</a> <a id="753" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="755" href="Algebras.Algebras.html#743" class="Bound">𝓤</a> <a id="757" href="Universes.html#403" class="Function Operator">̇</a> <a id="759" href="MGS-MLTT.html#3074" class="Function">,</a>                      <a id="782" class="Comment">-- the domain</a>
              <a id="810" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="812" href="Algebras.Algebras.html#812" class="Bound">f</a> <a id="814" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="816" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="818" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="820" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="822" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="824" href="Algebras.Signatures.html#639" class="Function">Op</a> <a id="827" class="Symbol">(</a><a id="828" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="830" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="832" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="834" href="Algebras.Algebras.html#812" class="Bound">f</a><a id="835" class="Symbol">)</a> <a id="837" href="Algebras.Algebras.html#751" class="Bound">A</a>    <a id="842" class="Comment">-- the basic operations</a>

</pre>

We could refer to an inhabitant of this type as a ∞-*algebra* because its domain can be an arbitrary type, say, `A : 𝓤 ̇` and need not be truncated at some level; in particular, `A` need to be a set. (See the [Prelude.Preliminaries.html#truncation](Prelude.Preliminaries.html#truncation).)

We might take this opportunity to define the type of 0-*algebras* (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, below we will only need to know that the domains of our algebras are sets in a few places in the [UALib][], so it seems preferable to work with general (∞-)algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.



#### <a id="algebras-as-record-types">Algebras as record types</a>

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

<pre class="Agda">

<a id="1856" class="Keyword">record</a> <a id="algebra"></a><a id="1863" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="1871" class="Symbol">(</a><a id="1872" href="Algebras.Algebras.html#1872" class="Bound">𝓤</a> <a id="1874" class="Symbol">:</a> <a id="1876" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1884" class="Symbol">)</a> <a id="1886" class="Symbol">(</a><a id="1887" href="Algebras.Algebras.html#1887" class="Bound">𝑆</a> <a id="1889" class="Symbol">:</a> <a id="1891" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="1901" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="1903" href="Universes.html#262" class="Generalizable">𝓥</a><a id="1904" class="Symbol">)</a> <a id="1906" class="Symbol">:</a> <a id="1908" class="Symbol">(</a><a id="1909" href="Algebras.Algebras.html#1901" class="Bound">𝓞</a> <a id="1911" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1913" href="Algebras.Algebras.html#1903" class="Bound">𝓥</a> <a id="1915" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1917" href="Algebras.Algebras.html#1872" class="Bound">𝓤</a><a id="1918" class="Symbol">)</a> <a id="1920" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1922" href="Universes.html#403" class="Function Operator">̇</a> <a id="1924" class="Keyword">where</a>
 <a id="1931" class="Keyword">constructor</a> <a id="mkalg"></a><a id="1943" href="Algebras.Algebras.html#1943" class="InductiveConstructor">mkalg</a>
 <a id="1950" class="Keyword">field</a>
  <a id="algebra.univ"></a><a id="1958" href="Algebras.Algebras.html#1958" class="Field">univ</a> <a id="1963" class="Symbol">:</a> <a id="1965" href="Algebras.Algebras.html#1872" class="Bound">𝓤</a> <a id="1967" href="Universes.html#403" class="Function Operator">̇</a>
  <a id="algebra.op"></a><a id="1971" href="Algebras.Algebras.html#1971" class="Field">op</a> <a id="1974" class="Symbol">:</a> <a id="1976" class="Symbol">(</a><a id="1977" href="Algebras.Algebras.html#1977" class="Bound">f</a> <a id="1979" class="Symbol">:</a> <a id="1981" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="1983" href="Algebras.Algebras.html#1887" class="Bound">𝑆</a> <a id="1985" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="1986" class="Symbol">)</a> <a id="1988" class="Symbol">→</a> <a id="1990" class="Symbol">((</a><a id="1992" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="1994" href="Algebras.Algebras.html#1887" class="Bound">𝑆</a> <a id="1996" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="1998" href="Algebras.Algebras.html#1977" class="Bound">f</a><a id="1999" class="Symbol">)</a> <a id="2001" class="Symbol">→</a> <a id="2003" href="Algebras.Algebras.html#1958" class="Field">univ</a><a id="2007" class="Symbol">)</a> <a id="2009" class="Symbol">→</a> <a id="2011" href="Algebras.Algebras.html#1958" class="Field">univ</a>


</pre>

Recall, the type `Signature 𝓞 𝓥` was defined in the [Algebras.Signature][] module as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.

If for some reason we want to use both representations of algebras and move back and forth between them, this is easily accomplished with the following functions.

<pre class="Agda">

<a id="2343" class="Keyword">module</a> <a id="2350" href="Algebras.Algebras.html#2350" class="Module">_</a> <a id="2352" class="Symbol">{</a><a id="2353" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a> <a id="2355" class="Symbol">:</a> <a id="2357" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="2367" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="2369" href="Universes.html#262" class="Generalizable">𝓥</a><a id="2370" class="Symbol">}</a> <a id="2372" class="Keyword">where</a>

 <a id="2380" class="Keyword">open</a> <a id="2385" href="Algebras.Algebras.html#1863" class="Module">algebra</a>

 <a id="2395" href="Algebras.Algebras.html#2395" class="Function">algebra→Algebra</a> <a id="2411" class="Symbol">:</a> <a id="2413" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="2421" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2423" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a> <a id="2425" class="Symbol">→</a> <a id="2427" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2435" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2437" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a>
 <a id="2440" href="Algebras.Algebras.html#2395" class="Function">algebra→Algebra</a> <a id="2456" href="Algebras.Algebras.html#2456" class="Bound">𝑨</a> <a id="2458" class="Symbol">=</a> <a id="2460" class="Symbol">(</a><a id="2461" href="Algebras.Algebras.html#1958" class="Field">univ</a> <a id="2466" href="Algebras.Algebras.html#2456" class="Bound">𝑨</a> <a id="2468" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="2470" href="Algebras.Algebras.html#1971" class="Field">op</a> <a id="2473" href="Algebras.Algebras.html#2456" class="Bound">𝑨</a><a id="2474" class="Symbol">)</a>

 <a id="2478" href="Algebras.Algebras.html#2478" class="Function">Algebra→algebra</a> <a id="2494" class="Symbol">:</a> <a id="2496" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2504" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2506" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a> <a id="2508" class="Symbol">→</a> <a id="2510" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="2518" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2520" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a>
 <a id="2523" href="Algebras.Algebras.html#2478" class="Function">Algebra→algebra</a> <a id="2539" href="Algebras.Algebras.html#2539" class="Bound">𝑨</a> <a id="2541" class="Symbol">=</a> <a id="2543" href="Algebras.Algebras.html#1943" class="InductiveConstructor">mkalg</a> <a id="2549" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="2551" href="Algebras.Algebras.html#2539" class="Bound">𝑨</a> <a id="2553" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="2555" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="2557" href="Algebras.Algebras.html#2539" class="Bound">𝑨</a> <a id="2559" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a>

</pre>




#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with, so we will use this new notation almost exclusively in the remaining modules of the [UALib][].

<pre class="Agda">

 <a id="2987" href="Algebras.Algebras.html#2987" class="Function Operator">_̂_</a> <a id="2991" class="Symbol">:</a> <a id="2993" class="Symbol">(</a><a id="2994" href="Algebras.Algebras.html#2994" class="Bound">𝑓</a> <a id="2996" class="Symbol">:</a> <a id="2998" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="3000" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a> <a id="3002" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="3003" class="Symbol">)(</a><a id="3005" href="Algebras.Algebras.html#3005" class="Bound">𝑨</a> <a id="3007" class="Symbol">:</a> <a id="3009" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3017" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3019" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a><a id="3020" class="Symbol">)</a> <a id="3022" class="Symbol">→</a> <a id="3024" class="Symbol">(</a><a id="3025" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="3027" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a> <a id="3029" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="3031" href="Algebras.Algebras.html#2994" class="Bound">𝑓</a>  <a id="3034" class="Symbol">→</a>  <a id="3037" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="3039" href="Algebras.Algebras.html#3005" class="Bound">𝑨</a> <a id="3041" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="3042" class="Symbol">)</a> <a id="3044" class="Symbol">→</a> <a id="3046" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="3048" href="Algebras.Algebras.html#3005" class="Bound">𝑨</a> <a id="3050" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a>

 <a id="3054" href="Algebras.Algebras.html#3054" class="Bound">𝑓</a> <a id="3056" href="Algebras.Algebras.html#2987" class="Function Operator">̂</a> <a id="3058" href="Algebras.Algebras.html#3058" class="Bound">𝑨</a> <a id="3060" class="Symbol">=</a> <a id="3062" class="Symbol">λ</a> <a id="3064" href="Algebras.Algebras.html#3064" class="Bound">𝑎</a> <a id="3066" class="Symbol">→</a> <a id="3068" class="Symbol">(</a><a id="3069" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="3071" href="Algebras.Algebras.html#3058" class="Bound">𝑨</a> <a id="3073" href="Prelude.Preliminaries.html#12455" class="Function Operator">∥</a> <a id="3075" href="Algebras.Algebras.html#3054" class="Bound">𝑓</a><a id="3076" class="Symbol">)</a> <a id="3078" href="Algebras.Algebras.html#3064" class="Bound">𝑎</a>

</pre>

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.


#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

We sometimes want to assume that we have at our disposal an arbitrary collection `X` of variable symbols such that, for every algebra `𝑨`, no matter the type of its domain, we have a surjective map of type `X → ∣ 𝑨 ∣`, from variable symbols onto the domain of `𝑨`.  We may use the following definition to express this assumption when we need it.

<pre class="Agda">

 <a id="3757" href="Algebras.Algebras.html#3757" class="Function Operator">_↠_</a> <a id="3761" class="Symbol">:</a> <a id="3763" class="Symbol">{</a><a id="3764" href="Algebras.Algebras.html#3764" class="Bound">𝓧</a> <a id="3766" class="Symbol">:</a> <a id="3768" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3776" class="Symbol">}</a> <a id="3778" class="Symbol">→</a> <a id="3780" href="Algebras.Algebras.html#3764" class="Bound">𝓧</a> <a id="3782" href="Universes.html#403" class="Function Operator">̇</a> <a id="3784" class="Symbol">→</a> <a id="3786" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3794" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3796" href="Algebras.Algebras.html#2353" class="Bound">𝑆</a> <a id="3798" class="Symbol">→</a> <a id="3800" href="Algebras.Algebras.html#3764" class="Bound">𝓧</a> <a id="3802" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3804" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3806" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3809" href="Algebras.Algebras.html#3809" class="Bound">X</a> <a id="3811" href="Algebras.Algebras.html#3757" class="Function Operator">↠</a> <a id="3813" href="Algebras.Algebras.html#3813" class="Bound">𝑨</a> <a id="3815" class="Symbol">=</a> <a id="3817" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3819" href="Algebras.Algebras.html#3819" class="Bound">h</a> <a id="3821" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3823" class="Symbol">(</a><a id="3824" href="Algebras.Algebras.html#3809" class="Bound">X</a> <a id="3826" class="Symbol">→</a> <a id="3828" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="3830" href="Algebras.Algebras.html#3813" class="Bound">𝑨</a> <a id="3832" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="3833" class="Symbol">)</a> <a id="3835" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3837" href="Prelude.Inverses.html#2039" class="Function">Epic</a> <a id="3842" href="Algebras.Algebras.html#3819" class="Bound">h</a>

</pre>

Now we can assert, in a specific module, the existence of the surjective map described above by including the following line in that module's declaration, like so.

<pre class="Agda">

<a id="4036" class="Keyword">module</a> <a id="4043" href="Algebras.Algebras.html#4043" class="Module">_</a> <a id="4045" class="Symbol">{</a><a id="4046" href="Algebras.Algebras.html#4046" class="Bound">𝓧</a> <a id="4048" class="Symbol">:</a> <a id="4050" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4058" class="Symbol">}{</a><a id="4060" href="Algebras.Algebras.html#4060" class="Bound">X</a> <a id="4062" class="Symbol">:</a> <a id="4064" href="Algebras.Algebras.html#4046" class="Bound">𝓧</a> <a id="4066" href="Universes.html#403" class="Function Operator">̇</a><a id="4067" class="Symbol">}{</a><a id="4069" href="Algebras.Algebras.html#4069" class="Bound">𝑆</a> <a id="4071" class="Symbol">:</a> <a id="4073" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="4083" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="4085" href="Universes.html#262" class="Generalizable">𝓥</a><a id="4086" class="Symbol">}</a>
         <a id="4097" class="Symbol">{</a><a id="4098" href="Algebras.Algebras.html#4098" class="Bound">𝕏</a> <a id="4100" class="Symbol">:</a> <a id="4102" class="Symbol">(</a><a id="4103" href="Algebras.Algebras.html#4103" class="Bound">𝑨</a> <a id="4105" class="Symbol">:</a> <a id="4107" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4115" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4117" href="Algebras.Algebras.html#4069" class="Bound">𝑆</a><a id="4118" class="Symbol">)</a> <a id="4120" class="Symbol">→</a> <a id="4122" href="Algebras.Algebras.html#4060" class="Bound">X</a> <a id="4124" href="Algebras.Algebras.html#3757" class="Function Operator">↠</a> <a id="4126" href="Algebras.Algebras.html#4103" class="Bound">𝑨</a><a id="4127" class="Symbol">}</a> <a id="4129" class="Keyword">where</a>

</pre>

Then fst(𝕏 𝑨) will denote the surjective map h₀ : X → ∣ 𝑨 ∣, and snd(𝕏 𝑨) will be a proof that h₀ is surjective.




#### <a id="lifts-of-algebras">Lifts of algebras</a>

Here we define some domain-specific lifting tools for our operation and algebra types.

<pre class="Agda">


<a id="4422" class="Keyword">module</a> <a id="4429" href="Algebras.Algebras.html#4429" class="Module">_</a> <a id="4431" class="Symbol">{</a><a id="4432" href="Algebras.Algebras.html#4432" class="Bound">I</a> <a id="4434" class="Symbol">:</a> <a id="4436" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4438" href="Universes.html#403" class="Function Operator">̇</a><a id="4439" class="Symbol">}{</a><a id="4441" href="Algebras.Algebras.html#4441" class="Bound">A</a> <a id="4443" class="Symbol">:</a> <a id="4445" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4447" href="Universes.html#403" class="Function Operator">̇</a><a id="4448" class="Symbol">}</a> <a id="4450" class="Keyword">where</a>

 <a id="4458" class="Keyword">open</a> <a id="4463" href="Prelude.Lifts.html#2589" class="Module">Lift</a>

 <a id="4470" href="Algebras.Algebras.html#4470" class="Function">lift-op</a> <a id="4478" class="Symbol">:</a> <a id="4480" class="Symbol">((</a><a id="4482" href="Algebras.Algebras.html#4432" class="Bound">I</a> <a id="4484" class="Symbol">→</a> <a id="4486" href="Algebras.Algebras.html#4441" class="Bound">A</a><a id="4487" class="Symbol">)</a> <a id="4489" class="Symbol">→</a> <a id="4491" href="Algebras.Algebras.html#4441" class="Bound">A</a><a id="4492" class="Symbol">)</a> <a id="4494" class="Symbol">→</a> <a id="4496" class="Symbol">(</a><a id="4497" href="Algebras.Algebras.html#4497" class="Bound">𝓦</a> <a id="4499" class="Symbol">:</a> <a id="4501" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4509" class="Symbol">)</a> <a id="4511" class="Symbol">→</a> <a id="4513" class="Symbol">((</a><a id="4515" href="Algebras.Algebras.html#4432" class="Bound">I</a> <a id="4517" class="Symbol">→</a> <a id="4519" href="Prelude.Lifts.html#2589" class="Record">Lift</a><a id="4523" class="Symbol">{</a><a id="4524" href="Algebras.Algebras.html#4497" class="Bound">𝓦</a><a id="4525" class="Symbol">}</a> <a id="4527" href="Algebras.Algebras.html#4441" class="Bound">A</a><a id="4528" class="Symbol">)</a> <a id="4530" class="Symbol">→</a> <a id="4532" href="Prelude.Lifts.html#2589" class="Record">Lift</a> <a id="4537" class="Symbol">{</a><a id="4538" href="Algebras.Algebras.html#4497" class="Bound">𝓦</a><a id="4539" class="Symbol">}</a> <a id="4541" href="Algebras.Algebras.html#4441" class="Bound">A</a><a id="4542" class="Symbol">)</a>
 <a id="4545" href="Algebras.Algebras.html#4470" class="Function">lift-op</a> <a id="4553" href="Algebras.Algebras.html#4553" class="Bound">f</a> <a id="4555" href="Algebras.Algebras.html#4555" class="Bound">𝓦</a> <a id="4557" class="Symbol">=</a> <a id="4559" class="Symbol">λ</a> <a id="4561" href="Algebras.Algebras.html#4561" class="Bound">x</a> <a id="4563" class="Symbol">→</a> <a id="4565" href="Prelude.Lifts.html#2651" class="InductiveConstructor">lift</a> <a id="4570" class="Symbol">(</a><a id="4571" href="Algebras.Algebras.html#4553" class="Bound">f</a> <a id="4573" class="Symbol">(λ</a> <a id="4576" href="Algebras.Algebras.html#4576" class="Bound">i</a> <a id="4578" class="Symbol">→</a> <a id="4580" href="Prelude.Lifts.html#2663" class="Field">lower</a> <a id="4586" class="Symbol">(</a><a id="4587" href="Algebras.Algebras.html#4561" class="Bound">x</a> <a id="4589" href="Algebras.Algebras.html#4576" class="Bound">i</a><a id="4590" class="Symbol">)))</a>

<a id="4595" class="Keyword">module</a> <a id="4602" href="Algebras.Algebras.html#4602" class="Module">_</a> <a id="4604" class="Symbol">{</a><a id="4605" href="Algebras.Algebras.html#4605" class="Bound">𝑆</a> <a id="4607" class="Symbol">:</a> <a id="4609" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="4619" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="4621" href="Universes.html#262" class="Generalizable">𝓥</a><a id="4622" class="Symbol">}</a>  <a id="4625" class="Keyword">where</a>

 <a id="4633" class="Keyword">open</a> <a id="4638" href="Algebras.Algebras.html#1863" class="Module">algebra</a>

 <a id="4648" href="Algebras.Algebras.html#4648" class="Function">lift-alg</a> <a id="4657" class="Symbol">:</a> <a id="4659" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4667" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4669" href="Algebras.Algebras.html#4605" class="Bound">𝑆</a> <a id="4671" class="Symbol">→</a> <a id="4673" class="Symbol">(</a><a id="4674" href="Algebras.Algebras.html#4674" class="Bound">𝓦</a> <a id="4676" class="Symbol">:</a> <a id="4678" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4686" class="Symbol">)</a> <a id="4688" class="Symbol">→</a> <a id="4690" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4698" class="Symbol">(</a><a id="4699" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4701" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4703" href="Algebras.Algebras.html#4674" class="Bound">𝓦</a><a id="4704" class="Symbol">)</a> <a id="4706" href="Algebras.Algebras.html#4605" class="Bound">𝑆</a>
 <a id="4709" href="Algebras.Algebras.html#4648" class="Function">lift-alg</a> <a id="4718" href="Algebras.Algebras.html#4718" class="Bound">𝑨</a> <a id="4720" href="Algebras.Algebras.html#4720" class="Bound">𝓦</a> <a id="4722" class="Symbol">=</a> <a id="4724" href="Prelude.Lifts.html#2589" class="Record">Lift</a> <a id="4729" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4731" href="Algebras.Algebras.html#4718" class="Bound">𝑨</a> <a id="4733" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4735" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a> <a id="4737" class="Symbol">(λ</a> <a id="4740" class="Symbol">(</a><a id="4741" href="Algebras.Algebras.html#4741" class="Bound">𝑓</a> <a id="4743" class="Symbol">:</a> <a id="4745" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4747" href="Algebras.Algebras.html#4605" class="Bound">𝑆</a> <a id="4749" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="4750" class="Symbol">)</a> <a id="4752" class="Symbol">→</a> <a id="4754" href="Algebras.Algebras.html#4470" class="Function">lift-op</a> <a id="4762" class="Symbol">(</a><a id="4763" href="Algebras.Algebras.html#4741" class="Bound">𝑓</a> <a id="4765" href="Algebras.Algebras.html#2987" class="Function Operator">̂</a> <a id="4767" href="Algebras.Algebras.html#4718" class="Bound">𝑨</a><a id="4768" class="Symbol">)</a> <a id="4770" href="Algebras.Algebras.html#4720" class="Bound">𝓦</a><a id="4771" class="Symbol">)</a>

 <a id="4775" href="Algebras.Algebras.html#4775" class="Function">lift-alg-record-type</a> <a id="4796" class="Symbol">:</a> <a id="4798" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="4806" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4808" href="Algebras.Algebras.html#4605" class="Bound">𝑆</a> <a id="4810" class="Symbol">→</a> <a id="4812" class="Symbol">(</a><a id="4813" href="Algebras.Algebras.html#4813" class="Bound">𝓦</a> <a id="4815" class="Symbol">:</a> <a id="4817" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4825" class="Symbol">)</a> <a id="4827" class="Symbol">→</a> <a id="4829" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="4837" class="Symbol">(</a><a id="4838" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4840" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4842" href="Algebras.Algebras.html#4813" class="Bound">𝓦</a><a id="4843" class="Symbol">)</a> <a id="4845" href="Algebras.Algebras.html#4605" class="Bound">𝑆</a>
 <a id="4848" href="Algebras.Algebras.html#4775" class="Function">lift-alg-record-type</a> <a id="4869" href="Algebras.Algebras.html#4869" class="Bound">𝑨</a> <a id="4871" href="Algebras.Algebras.html#4871" class="Bound">𝓦</a> <a id="4873" class="Symbol">=</a> <a id="4875" href="Algebras.Algebras.html#1943" class="InductiveConstructor">mkalg</a> <a id="4881" class="Symbol">(</a><a id="4882" href="Prelude.Lifts.html#2589" class="Record">Lift</a> <a id="4887" class="Symbol">(</a><a id="4888" href="Algebras.Algebras.html#1958" class="Field">univ</a> <a id="4893" href="Algebras.Algebras.html#4869" class="Bound">𝑨</a><a id="4894" class="Symbol">))</a> <a id="4897" class="Symbol">(λ</a> <a id="4900" class="Symbol">(</a><a id="4901" href="Algebras.Algebras.html#4901" class="Bound">f</a> <a id="4903" class="Symbol">:</a> <a id="4905" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4907" href="Algebras.Algebras.html#4605" class="Bound">𝑆</a> <a id="4909" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="4910" class="Symbol">)</a> <a id="4912" class="Symbol">→</a> <a id="4914" href="Algebras.Algebras.html#4470" class="Function">lift-op</a> <a id="4922" class="Symbol">((</a><a id="4924" href="Algebras.Algebras.html#1971" class="Field">op</a> <a id="4927" href="Algebras.Algebras.html#4869" class="Bound">𝑨</a><a id="4928" class="Symbol">)</a> <a id="4930" href="Algebras.Algebras.html#4901" class="Bound">f</a><a id="4931" class="Symbol">)</a> <a id="4933" href="Algebras.Algebras.html#4871" class="Bound">𝓦</a><a id="4934" class="Symbol">)</a>

</pre>

We use the function `lift-alg` to resolve errors that arise when working in Agda's noncummulative hierarchy of type universes. (See the discussion in [Prelude.Lifts][].)




#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

If `𝑨` is an algebra and `R` a binary relation, then `compatible 𝑨 R` will represents the assertion that `R` is *compatible* with all basic operations of `𝑨`. Recall, informally this means for every operation symbol `𝑓 : ∣ 𝑆 ∣` and all pairs `𝑎 𝑎' : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` of tuples from the domain of 𝑨, the following implication holds:

if `R (𝑎 i) (𝑎' i)` for all `i`, then  `R ((𝑓 ̂ 𝑨) 𝑎) ((𝑓 ̂ 𝑨) 𝑎')`.

The formal definition representing this notion of compatibility is easy to write down since we already have a type that does all the work.

<pre class="Agda">

 <a id="5767" href="Algebras.Algebras.html#5767" class="Function">compatible</a> <a id="5778" class="Symbol">:</a> <a id="5780" class="Symbol">(</a><a id="5781" href="Algebras.Algebras.html#5781" class="Bound">𝑨</a> <a id="5783" class="Symbol">:</a> <a id="5785" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5793" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5795" href="Algebras.Algebras.html#4605" class="Bound">𝑆</a><a id="5796" class="Symbol">)</a> <a id="5798" class="Symbol">→</a> <a id="5800" href="Relations.Discrete.html#7173" class="Function">Rel</a> <a id="5804" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="5806" href="Algebras.Algebras.html#5781" class="Bound">𝑨</a> <a id="5808" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="5810" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5812" class="Symbol">→</a> <a id="5814" href="Algebras.Algebras.html#4619" class="Bound">𝓞</a> <a id="5816" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5818" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5820" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5822" href="Algebras.Algebras.html#4621" class="Bound">𝓥</a> <a id="5824" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5826" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5828" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5831" href="Algebras.Algebras.html#5767" class="Function">compatible</a>  <a id="5843" href="Algebras.Algebras.html#5843" class="Bound">𝑨</a> <a id="5845" href="Algebras.Algebras.html#5845" class="Bound">R</a> <a id="5847" class="Symbol">=</a> <a id="5849" class="Symbol">∀</a> <a id="5851" href="Algebras.Algebras.html#5851" class="Bound">𝑓</a> <a id="5853" class="Symbol">→</a> <a id="5855" href="Relations.Discrete.html#10243" class="Function">compatible-fun</a> <a id="5870" class="Symbol">(</a><a id="5871" href="Algebras.Algebras.html#5851" class="Bound">𝑓</a> <a id="5873" href="Algebras.Algebras.html#2987" class="Function Operator">̂</a> <a id="5875" href="Algebras.Algebras.html#5843" class="Bound">𝑨</a><a id="5876" class="Symbol">)</a> <a id="5878" href="Algebras.Algebras.html#5845" class="Bound">R</a>

</pre>

Recall, the `compatible-fun` type was defined in [Relations.Discrete][] module.



---------------------------------------



#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations*</a>

This section presents the `continuous-compatibility` submodule of the [Algebras.Algebras][] module.<sup>[*](Algebras.Algebras.html#fn0)</sup>


Next we define a type that represents *compatibility of a continuous relation* with all operations of an algebra. We start by defining compatibility of a continuous relations with a single operation.

<pre class="Agda">

<a id="6473" class="Keyword">module</a> <a id="continuous-compatibility"></a><a id="6480" href="Algebras.Algebras.html#6480" class="Module">continuous-compatibility</a> <a id="6505" class="Symbol">{</a><a id="6506" href="Algebras.Algebras.html#6506" class="Bound">𝑆</a> <a id="6508" class="Symbol">:</a> <a id="6510" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="6520" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="6522" href="Universes.html#262" class="Generalizable">𝓥</a><a id="6523" class="Symbol">}</a> <a id="6525" class="Symbol">{</a><a id="6526" href="Algebras.Algebras.html#6526" class="Bound">𝑨</a> <a id="6528" class="Symbol">:</a> <a id="6530" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="6538" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6540" href="Algebras.Algebras.html#6506" class="Bound">𝑆</a><a id="6541" class="Symbol">}</a> <a id="6543" class="Symbol">{</a><a id="6544" href="Algebras.Algebras.html#6544" class="Bound">I</a> <a id="6546" class="Symbol">:</a> <a id="6548" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6550" href="Universes.html#403" class="Function Operator">̇</a><a id="6551" class="Symbol">}</a> <a id="6553" class="Keyword">where</a>

 <a id="6561" class="Keyword">open</a> <a id="6566" class="Keyword">import</a> <a id="6573" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="6594" class="Keyword">using</a> <a id="6600" class="Symbol">(</a><a id="6601" href="Relations.Continuous.html#3268" class="Function">ConRel</a><a id="6607" class="Symbol">;</a> <a id="6609" href="Relations.Continuous.html#3645" class="Function">lift-con-rel</a><a id="6621" class="Symbol">;</a> <a id="6623" href="Relations.Continuous.html#3747" class="Function">con-compatible-fun</a><a id="6641" class="Symbol">)</a>


 <a id="continuous-compatibility.con-compatible-op"></a><a id="6646" href="Algebras.Algebras.html#6646" class="Function">con-compatible-op</a> <a id="6664" class="Symbol">:</a> <a id="6666" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6668" href="Algebras.Algebras.html#6506" class="Bound">𝑆</a> <a id="6670" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6672" class="Symbol">→</a> <a id="6674" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="6681" href="Algebras.Algebras.html#6544" class="Bound">I</a> <a id="6683" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6685" href="Algebras.Algebras.html#6526" class="Bound">𝑨</a> <a id="6687" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6689" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6691" class="Symbol">→</a> <a id="6693" href="Algebras.Algebras.html#6538" class="Bound">𝓤</a> <a id="6695" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6697" href="Algebras.Algebras.html#6522" class="Bound">𝓥</a> <a id="6699" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6701" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6703" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6706" href="Algebras.Algebras.html#6646" class="Function">con-compatible-op</a> <a id="6724" href="Algebras.Algebras.html#6724" class="Bound">𝑓</a> <a id="6726" href="Algebras.Algebras.html#6726" class="Bound">R</a> <a id="6728" class="Symbol">=</a> <a id="6730" href="Relations.Continuous.html#3747" class="Function">con-compatible-fun</a> <a id="6749" class="Symbol">(λ</a> <a id="6752" href="Algebras.Algebras.html#6752" class="Bound">_</a> <a id="6754" class="Symbol">→</a> <a id="6756" class="Symbol">(</a><a id="6757" href="Algebras.Algebras.html#6724" class="Bound">𝑓</a> <a id="6759" href="Algebras.Algebras.html#2987" class="Function Operator">̂</a> <a id="6761" href="Algebras.Algebras.html#6526" class="Bound">𝑨</a><a id="6762" class="Symbol">))</a> <a id="6765" href="Algebras.Algebras.html#6726" class="Bound">R</a>

</pre>

In case it helps the reader understand `con-compatible-op`, we redefine it explicitly without the help of `con-compatible-fun`.

<pre class="Agda">

 <a id="continuous-compatibility.con-compatible-op&#39;"></a><a id="6924" href="Algebras.Algebras.html#6924" class="Function">con-compatible-op&#39;</a> <a id="6943" class="Symbol">:</a> <a id="6945" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6947" href="Algebras.Algebras.html#6506" class="Bound">𝑆</a> <a id="6949" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6951" class="Symbol">→</a> <a id="6953" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="6960" href="Algebras.Algebras.html#6544" class="Bound">I</a> <a id="6962" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6964" href="Algebras.Algebras.html#6526" class="Bound">𝑨</a> <a id="6966" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="6968" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6970" class="Symbol">→</a> <a id="6972" href="Algebras.Algebras.html#6538" class="Bound">𝓤</a> <a id="6974" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6976" href="Algebras.Algebras.html#6522" class="Bound">𝓥</a> <a id="6978" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6980" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6982" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6985" href="Algebras.Algebras.html#6924" class="Function">con-compatible-op&#39;</a> <a id="7004" href="Algebras.Algebras.html#7004" class="Bound">𝑓</a> <a id="7006" href="Algebras.Algebras.html#7006" class="Bound">R</a> <a id="7008" class="Symbol">=</a> <a id="7010" class="Symbol">∀</a> <a id="7012" href="Algebras.Algebras.html#7012" class="Bound">𝕒</a> <a id="7014" class="Symbol">→</a> <a id="7016" class="Symbol">(</a><a id="7017" href="Relations.Continuous.html#3645" class="Function">lift-con-rel</a> <a id="7030" href="Algebras.Algebras.html#7006" class="Bound">R</a><a id="7031" class="Symbol">)</a> <a id="7033" href="Algebras.Algebras.html#7012" class="Bound">𝕒</a> <a id="7035" class="Symbol">→</a> <a id="7037" href="Algebras.Algebras.html#7006" class="Bound">R</a> <a id="7039" class="Symbol">(λ</a> <a id="7042" href="Algebras.Algebras.html#7042" class="Bound">i</a> <a id="7044" class="Symbol">→</a> <a id="7046" class="Symbol">(</a><a id="7047" href="Algebras.Algebras.html#7004" class="Bound">𝑓</a> <a id="7049" href="Algebras.Algebras.html#2987" class="Function Operator">̂</a> <a id="7051" href="Algebras.Algebras.html#6526" class="Bound">𝑨</a><a id="7052" class="Symbol">)</a> <a id="7054" class="Symbol">(</a><a id="7055" href="Algebras.Algebras.html#7012" class="Bound">𝕒</a> <a id="7057" href="Algebras.Algebras.html#7042" class="Bound">i</a><a id="7058" class="Symbol">))</a>

</pre>

where we have let Agda infer the type of `𝕒`, which is `(i : I) → ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`.

With `con-compatible-op` in hand, it is a trivial matter to define a type that represents *compatibility of a continuous relation with an algebra*.

<pre class="Agda">

 <a id="continuous-compatibility.con-compatible"></a><a id="7323" href="Algebras.Algebras.html#7323" class="Function">con-compatible</a> <a id="7338" class="Symbol">:</a> <a id="7340" href="Relations.Continuous.html#3268" class="Function">ConRel</a> <a id="7347" href="Algebras.Algebras.html#6544" class="Bound">I</a> <a id="7349" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="7351" href="Algebras.Algebras.html#6526" class="Bound">𝑨</a> <a id="7353" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="7355" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7357" class="Symbol">→</a> <a id="7359" href="Algebras.Algebras.html#6520" class="Bound">𝓞</a> <a id="7361" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7363" href="Algebras.Algebras.html#6538" class="Bound">𝓤</a> <a id="7365" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7367" href="Algebras.Algebras.html#6522" class="Bound">𝓥</a> <a id="7369" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7371" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7373" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7376" href="Algebras.Algebras.html#7323" class="Function">con-compatible</a> <a id="7391" href="Algebras.Algebras.html#7391" class="Bound">R</a> <a id="7393" class="Symbol">=</a> <a id="7395" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="7397" href="Algebras.Algebras.html#7397" class="Bound">𝑓</a> <a id="7399" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="7401" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="7403" href="Algebras.Algebras.html#6506" class="Bound">𝑆</a> <a id="7405" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="7407" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="7409" href="Algebras.Algebras.html#6646" class="Function">con-compatible-op</a> <a id="7427" href="Algebras.Algebras.html#7397" class="Bound">𝑓</a> <a id="7429" href="Algebras.Algebras.html#7391" class="Bound">R</a>

</pre>



--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>


[← Algebras.Signatures](Algebras.Signatures.html)
<span style="float:right;">[Algebras.Products →](Algebras.Products.html)</span>


{% include UALib.Links.md %}
