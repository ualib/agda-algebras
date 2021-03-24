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

<a id="Algebra"></a><a id="674" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="682" class="Symbol">:</a> <a id="684" class="Symbol">(</a><a id="685" href="Algebras.Algebras.html#685" class="Bound">𝓤</a> <a id="687" class="Symbol">:</a> <a id="689" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="697" class="Symbol">)(</a><a id="699" href="Algebras.Algebras.html#699" class="Bound">𝑆</a> <a id="701" class="Symbol">:</a> <a id="703" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="713" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a> <a id="715" href="Universes.html#262" class="Generalizable">𝓥</a><a id="716" class="Symbol">)</a> <a id="718" class="Symbol">→</a> <a id="720" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a> <a id="722" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="724" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="726" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="728" href="Algebras.Algebras.html#685" class="Bound">𝓤</a> <a id="730" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="732" href="Universes.html#403" class="Function Operator">̇</a>

<a id="735" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="743" href="Algebras.Algebras.html#743" class="Bound">𝓤</a> <a id="745" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="747" class="Symbol">=</a> <a id="749" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="751" href="Algebras.Algebras.html#751" class="Bound">A</a> <a id="753" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="755" href="Algebras.Algebras.html#743" class="Bound">𝓤</a> <a id="757" href="Universes.html#403" class="Function Operator">̇</a> <a id="759" href="MGS-MLTT.html#3074" class="Function">,</a>                      <a id="782" class="Comment">-- the domain</a>
              <a id="810" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="812" href="Algebras.Algebras.html#812" class="Bound">f</a> <a id="814" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="816" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="818" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="820" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="822" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="824" href="Algebras.Signatures.html#627" class="Function">Op</a> <a id="827" class="Symbol">(</a><a id="828" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="830" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="832" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="834" href="Algebras.Algebras.html#812" class="Bound">f</a><a id="835" class="Symbol">)</a> <a id="837" href="Algebras.Algebras.html#751" class="Bound">A</a>    <a id="842" class="Comment">-- the basic operations</a>

</pre>

We could refer to an inhabitant of this type as a ∞-*algebra* because its domain can be an arbitrary type, say, `A : 𝓤 ̇` and need not be truncated at some level; in particular, `A` need to be a set. (See the [Overture.Preliminaries.html#truncation](Overture.Preliminaries.html#truncation).)

We might take this opportunity to define the type of 0-*algebras* (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, below we will only need to know that the domains of our algebras are sets in a few places in the [UALib][], so it seems preferable to work with general (∞-)algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.



#### <a id="algebras-as-record-types">Algebras as record types</a>

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

<pre class="Agda">

<a id="1858" class="Keyword">record</a> <a id="algebra"></a><a id="1865" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="1873" class="Symbol">(</a><a id="1874" href="Algebras.Algebras.html#1874" class="Bound">𝓤</a> <a id="1876" class="Symbol">:</a> <a id="1878" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1886" class="Symbol">)</a> <a id="1888" class="Symbol">(</a><a id="1889" href="Algebras.Algebras.html#1889" class="Bound">𝑆</a> <a id="1891" class="Symbol">:</a> <a id="1893" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="1903" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a> <a id="1905" href="Universes.html#262" class="Generalizable">𝓥</a><a id="1906" class="Symbol">)</a> <a id="1908" class="Symbol">:</a> <a id="1910" class="Symbol">(</a><a id="1911" href="Algebras.Algebras.html#1903" class="Bound">𝓞</a> <a id="1913" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1915" href="Algebras.Algebras.html#1905" class="Bound">𝓥</a> <a id="1917" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1919" href="Algebras.Algebras.html#1874" class="Bound">𝓤</a><a id="1920" class="Symbol">)</a> <a id="1922" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1924" href="Universes.html#403" class="Function Operator">̇</a> <a id="1926" class="Keyword">where</a>
 <a id="1933" class="Keyword">constructor</a> <a id="mkalg"></a><a id="1945" href="Algebras.Algebras.html#1945" class="InductiveConstructor">mkalg</a>
 <a id="1952" class="Keyword">field</a>
  <a id="algebra.univ"></a><a id="1960" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="1965" class="Symbol">:</a> <a id="1967" href="Algebras.Algebras.html#1874" class="Bound">𝓤</a> <a id="1969" href="Universes.html#403" class="Function Operator">̇</a>
  <a id="algebra.op"></a><a id="1973" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="1976" class="Symbol">:</a> <a id="1978" class="Symbol">(</a><a id="1979" href="Algebras.Algebras.html#1979" class="Bound">f</a> <a id="1981" class="Symbol">:</a> <a id="1983" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="1985" href="Algebras.Algebras.html#1889" class="Bound">𝑆</a> <a id="1987" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a><a id="1988" class="Symbol">)</a> <a id="1990" class="Symbol">→</a> <a id="1992" class="Symbol">((</a><a id="1994" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="1996" href="Algebras.Algebras.html#1889" class="Bound">𝑆</a> <a id="1998" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="2000" href="Algebras.Algebras.html#1979" class="Bound">f</a><a id="2001" class="Symbol">)</a> <a id="2003" class="Symbol">→</a> <a id="2005" href="Algebras.Algebras.html#1960" class="Field">univ</a><a id="2009" class="Symbol">)</a> <a id="2011" class="Symbol">→</a> <a id="2013" href="Algebras.Algebras.html#1960" class="Field">univ</a>


</pre>

Recall, the type `Signature 𝓞 𝓥` was defined in the [Algebras.Signature][] module as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.

If for some reason we want to use both representations of algebras and move back and forth between them, this is easily accomplished with the following functions.

<pre class="Agda">

<a id="2345" class="Keyword">module</a> <a id="2352" href="Algebras.Algebras.html#2352" class="Module">_</a> <a id="2354" class="Symbol">{</a><a id="2355" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="2357" class="Symbol">:</a> <a id="2359" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="2369" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a> <a id="2371" href="Universes.html#262" class="Generalizable">𝓥</a><a id="2372" class="Symbol">}</a> <a id="2374" class="Keyword">where</a>

 <a id="2382" class="Keyword">open</a> <a id="2387" href="Algebras.Algebras.html#1865" class="Module">algebra</a>

 <a id="2397" href="Algebras.Algebras.html#2397" class="Function">algebra→Algebra</a> <a id="2413" class="Symbol">:</a> <a id="2415" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="2423" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2425" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="2427" class="Symbol">→</a> <a id="2429" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2437" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2439" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a>
 <a id="2442" href="Algebras.Algebras.html#2397" class="Function">algebra→Algebra</a> <a id="2458" href="Algebras.Algebras.html#2458" class="Bound">𝑨</a> <a id="2460" class="Symbol">=</a> <a id="2462" class="Symbol">(</a><a id="2463" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="2468" href="Algebras.Algebras.html#2458" class="Bound">𝑨</a> <a id="2470" href="Overture.Preliminaries.html#11717" class="InductiveConstructor Operator">,</a> <a id="2472" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="2475" href="Algebras.Algebras.html#2458" class="Bound">𝑨</a><a id="2476" class="Symbol">)</a>

 <a id="2480" href="Algebras.Algebras.html#2480" class="Function">Algebra→algebra</a> <a id="2496" class="Symbol">:</a> <a id="2498" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2506" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2508" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="2510" class="Symbol">→</a> <a id="2512" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="2520" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2522" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a>
 <a id="2525" href="Algebras.Algebras.html#2480" class="Function">Algebra→algebra</a> <a id="2541" href="Algebras.Algebras.html#2541" class="Bound">𝑨</a> <a id="2543" class="Symbol">=</a> <a id="2545" href="Algebras.Algebras.html#1945" class="InductiveConstructor">mkalg</a> <a id="2551" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="2553" href="Algebras.Algebras.html#2541" class="Bound">𝑨</a> <a id="2555" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="2557" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="2559" href="Algebras.Algebras.html#2541" class="Bound">𝑨</a> <a id="2561" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a>

</pre>




#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with, so we will use this new notation almost exclusively in the remaining modules of the [UALib][].

<pre class="Agda">

 <a id="2989" href="Algebras.Algebras.html#2989" class="Function Operator">_̂_</a> <a id="2993" class="Symbol">:</a> <a id="2995" class="Symbol">(</a><a id="2996" href="Algebras.Algebras.html#2996" class="Bound">𝑓</a> <a id="2998" class="Symbol">:</a> <a id="3000" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="3002" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="3004" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a><a id="3005" class="Symbol">)(</a><a id="3007" href="Algebras.Algebras.html#3007" class="Bound">𝑨</a> <a id="3009" class="Symbol">:</a> <a id="3011" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3019" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3021" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a><a id="3022" class="Symbol">)</a> <a id="3024" class="Symbol">→</a> <a id="3026" class="Symbol">(</a><a id="3027" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="3029" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="3031" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="3033" href="Algebras.Algebras.html#2996" class="Bound">𝑓</a>  <a id="3036" class="Symbol">→</a>  <a id="3039" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="3041" href="Algebras.Algebras.html#3007" class="Bound">𝑨</a> <a id="3043" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a><a id="3044" class="Symbol">)</a> <a id="3046" class="Symbol">→</a> <a id="3048" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="3050" href="Algebras.Algebras.html#3007" class="Bound">𝑨</a> <a id="3052" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a>

 <a id="3056" href="Algebras.Algebras.html#3056" class="Bound">𝑓</a> <a id="3058" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="3060" href="Algebras.Algebras.html#3060" class="Bound">𝑨</a> <a id="3062" class="Symbol">=</a> <a id="3064" class="Symbol">λ</a> <a id="3066" href="Algebras.Algebras.html#3066" class="Bound">𝑎</a> <a id="3068" class="Symbol">→</a> <a id="3070" class="Symbol">(</a><a id="3071" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="3073" href="Algebras.Algebras.html#3060" class="Bound">𝑨</a> <a id="3075" href="Overture.Preliminaries.html#12465" class="Function Operator">∥</a> <a id="3077" href="Algebras.Algebras.html#3056" class="Bound">𝑓</a><a id="3078" class="Symbol">)</a> <a id="3080" href="Algebras.Algebras.html#3066" class="Bound">𝑎</a>

</pre>

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.


#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

We sometimes want to assume that we have at our disposal an arbitrary collection `X` of variable symbols such that, for every algebra `𝑨`, no matter the type of its domain, we have a surjective map of type `X → ∣ 𝑨 ∣`, from variable symbols onto the domain of `𝑨`.  We may use the following definition to express this assumption when we need it.

<pre class="Agda">

 <a id="3759" href="Algebras.Algebras.html#3759" class="Function Operator">_↠_</a> <a id="3763" class="Symbol">:</a> <a id="3765" class="Symbol">{</a><a id="3766" href="Algebras.Algebras.html#3766" class="Bound">𝓧</a> <a id="3768" class="Symbol">:</a> <a id="3770" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3778" class="Symbol">}</a> <a id="3780" class="Symbol">→</a> <a id="3782" href="Algebras.Algebras.html#3766" class="Bound">𝓧</a> <a id="3784" href="Universes.html#403" class="Function Operator">̇</a> <a id="3786" class="Symbol">→</a> <a id="3788" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3796" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3798" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="3800" class="Symbol">→</a> <a id="3802" href="Algebras.Algebras.html#3766" class="Bound">𝓧</a> <a id="3804" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3806" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3808" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3811" href="Algebras.Algebras.html#3811" class="Bound">X</a> <a id="3813" href="Algebras.Algebras.html#3759" class="Function Operator">↠</a> <a id="3815" href="Algebras.Algebras.html#3815" class="Bound">𝑨</a> <a id="3817" class="Symbol">=</a> <a id="3819" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3821" href="Algebras.Algebras.html#3821" class="Bound">h</a> <a id="3823" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3825" class="Symbol">(</a><a id="3826" href="Algebras.Algebras.html#3811" class="Bound">X</a> <a id="3828" class="Symbol">→</a> <a id="3830" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="3832" href="Algebras.Algebras.html#3815" class="Bound">𝑨</a> <a id="3834" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a><a id="3835" class="Symbol">)</a> <a id="3837" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3839" href="Overture.Inverses.html#2031" class="Function">Epic</a> <a id="3844" href="Algebras.Algebras.html#3821" class="Bound">h</a>

</pre>

Now we can assert, in a specific module, the existence of the surjective map described above by including the following line in that module's declaration, like so.

<pre class="Agda">

<a id="4038" class="Keyword">module</a> <a id="4045" href="Algebras.Algebras.html#4045" class="Module">_</a> <a id="4047" class="Symbol">{</a><a id="4048" href="Algebras.Algebras.html#4048" class="Bound">𝓧</a> <a id="4050" class="Symbol">:</a> <a id="4052" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4060" class="Symbol">}{</a><a id="4062" href="Algebras.Algebras.html#4062" class="Bound">X</a> <a id="4064" class="Symbol">:</a> <a id="4066" href="Algebras.Algebras.html#4048" class="Bound">𝓧</a> <a id="4068" href="Universes.html#403" class="Function Operator">̇</a><a id="4069" class="Symbol">}{</a><a id="4071" href="Algebras.Algebras.html#4071" class="Bound">𝑆</a> <a id="4073" class="Symbol">:</a> <a id="4075" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="4085" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a> <a id="4087" href="Universes.html#262" class="Generalizable">𝓥</a><a id="4088" class="Symbol">}</a>
         <a id="4099" class="Symbol">{</a><a id="4100" href="Algebras.Algebras.html#4100" class="Bound">𝕏</a> <a id="4102" class="Symbol">:</a> <a id="4104" class="Symbol">(</a><a id="4105" href="Algebras.Algebras.html#4105" class="Bound">𝑨</a> <a id="4107" class="Symbol">:</a> <a id="4109" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4117" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4119" href="Algebras.Algebras.html#4071" class="Bound">𝑆</a><a id="4120" class="Symbol">)</a> <a id="4122" class="Symbol">→</a> <a id="4124" href="Algebras.Algebras.html#4062" class="Bound">X</a> <a id="4126" href="Algebras.Algebras.html#3759" class="Function Operator">↠</a> <a id="4128" href="Algebras.Algebras.html#4105" class="Bound">𝑨</a><a id="4129" class="Symbol">}</a> <a id="4131" class="Keyword">where</a>

</pre>

Then fst(𝕏 𝑨) will denote the surjective map h₀ : X → ∣ 𝑨 ∣, and snd(𝕏 𝑨) will be a proof that h₀ is surjective.




#### <a id="lifts-of-algebras">Lifts of algebras</a>

Here we define some domain-specific lifting tools for our operation and algebra types.

<pre class="Agda">


<a id="4424" class="Keyword">module</a> <a id="4431" href="Algebras.Algebras.html#4431" class="Module">_</a> <a id="4433" class="Symbol">{</a><a id="4434" href="Algebras.Algebras.html#4434" class="Bound">I</a> <a id="4436" class="Symbol">:</a> <a id="4438" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4440" href="Universes.html#403" class="Function Operator">̇</a><a id="4441" class="Symbol">}{</a><a id="4443" href="Algebras.Algebras.html#4443" class="Bound">A</a> <a id="4445" class="Symbol">:</a> <a id="4447" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4449" href="Universes.html#403" class="Function Operator">̇</a><a id="4450" class="Symbol">}</a> <a id="4452" class="Keyword">where</a>

 <a id="4460" class="Keyword">open</a> <a id="4465" href="Overture.Lifts.html#2588" class="Module">Lift</a>

 <a id="4472" href="Algebras.Algebras.html#4472" class="Function">lift-op</a> <a id="4480" class="Symbol">:</a> <a id="4482" class="Symbol">((</a><a id="4484" href="Algebras.Algebras.html#4434" class="Bound">I</a> <a id="4486" class="Symbol">→</a> <a id="4488" href="Algebras.Algebras.html#4443" class="Bound">A</a><a id="4489" class="Symbol">)</a> <a id="4491" class="Symbol">→</a> <a id="4493" href="Algebras.Algebras.html#4443" class="Bound">A</a><a id="4494" class="Symbol">)</a> <a id="4496" class="Symbol">→</a> <a id="4498" class="Symbol">(</a><a id="4499" href="Algebras.Algebras.html#4499" class="Bound">𝓦</a> <a id="4501" class="Symbol">:</a> <a id="4503" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4511" class="Symbol">)</a> <a id="4513" class="Symbol">→</a> <a id="4515" class="Symbol">((</a><a id="4517" href="Algebras.Algebras.html#4434" class="Bound">I</a> <a id="4519" class="Symbol">→</a> <a id="4521" href="Overture.Lifts.html#2588" class="Record">Lift</a><a id="4525" class="Symbol">{</a><a id="4526" href="Algebras.Algebras.html#4499" class="Bound">𝓦</a><a id="4527" class="Symbol">}</a> <a id="4529" href="Algebras.Algebras.html#4443" class="Bound">A</a><a id="4530" class="Symbol">)</a> <a id="4532" class="Symbol">→</a> <a id="4534" href="Overture.Lifts.html#2588" class="Record">Lift</a> <a id="4539" class="Symbol">{</a><a id="4540" href="Algebras.Algebras.html#4499" class="Bound">𝓦</a><a id="4541" class="Symbol">}</a> <a id="4543" href="Algebras.Algebras.html#4443" class="Bound">A</a><a id="4544" class="Symbol">)</a>
 <a id="4547" href="Algebras.Algebras.html#4472" class="Function">lift-op</a> <a id="4555" href="Algebras.Algebras.html#4555" class="Bound">f</a> <a id="4557" href="Algebras.Algebras.html#4557" class="Bound">𝓦</a> <a id="4559" class="Symbol">=</a> <a id="4561" class="Symbol">λ</a> <a id="4563" href="Algebras.Algebras.html#4563" class="Bound">x</a> <a id="4565" class="Symbol">→</a> <a id="4567" href="Overture.Lifts.html#2650" class="InductiveConstructor">lift</a> <a id="4572" class="Symbol">(</a><a id="4573" href="Algebras.Algebras.html#4555" class="Bound">f</a> <a id="4575" class="Symbol">(λ</a> <a id="4578" href="Algebras.Algebras.html#4578" class="Bound">i</a> <a id="4580" class="Symbol">→</a> <a id="4582" href="Overture.Lifts.html#2662" class="Field">lower</a> <a id="4588" class="Symbol">(</a><a id="4589" href="Algebras.Algebras.html#4563" class="Bound">x</a> <a id="4591" href="Algebras.Algebras.html#4578" class="Bound">i</a><a id="4592" class="Symbol">)))</a>

<a id="4597" class="Keyword">module</a> <a id="4604" href="Algebras.Algebras.html#4604" class="Module">_</a> <a id="4606" class="Symbol">{</a><a id="4607" href="Algebras.Algebras.html#4607" class="Bound">𝑆</a> <a id="4609" class="Symbol">:</a> <a id="4611" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="4621" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a> <a id="4623" href="Universes.html#262" class="Generalizable">𝓥</a><a id="4624" class="Symbol">}</a>  <a id="4627" class="Keyword">where</a>

 <a id="4635" class="Keyword">open</a> <a id="4640" href="Algebras.Algebras.html#1865" class="Module">algebra</a>

 <a id="4650" href="Algebras.Algebras.html#4650" class="Function">lift-alg</a> <a id="4659" class="Symbol">:</a> <a id="4661" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4669" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4671" href="Algebras.Algebras.html#4607" class="Bound">𝑆</a> <a id="4673" class="Symbol">→</a> <a id="4675" class="Symbol">(</a><a id="4676" href="Algebras.Algebras.html#4676" class="Bound">𝓦</a> <a id="4678" class="Symbol">:</a> <a id="4680" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4688" class="Symbol">)</a> <a id="4690" class="Symbol">→</a> <a id="4692" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4700" class="Symbol">(</a><a id="4701" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4703" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4705" href="Algebras.Algebras.html#4676" class="Bound">𝓦</a><a id="4706" class="Symbol">)</a> <a id="4708" href="Algebras.Algebras.html#4607" class="Bound">𝑆</a>
 <a id="4711" href="Algebras.Algebras.html#4650" class="Function">lift-alg</a> <a id="4720" href="Algebras.Algebras.html#4720" class="Bound">𝑨</a> <a id="4722" href="Algebras.Algebras.html#4722" class="Bound">𝓦</a> <a id="4724" class="Symbol">=</a> <a id="4726" href="Overture.Lifts.html#2588" class="Record">Lift</a> <a id="4731" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="4733" href="Algebras.Algebras.html#4720" class="Bound">𝑨</a> <a id="4735" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="4737" href="Overture.Preliminaries.html#11717" class="InductiveConstructor Operator">,</a> <a id="4739" class="Symbol">(λ</a> <a id="4742" class="Symbol">(</a><a id="4743" href="Algebras.Algebras.html#4743" class="Bound">𝑓</a> <a id="4745" class="Symbol">:</a> <a id="4747" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="4749" href="Algebras.Algebras.html#4607" class="Bound">𝑆</a> <a id="4751" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a><a id="4752" class="Symbol">)</a> <a id="4754" class="Symbol">→</a> <a id="4756" href="Algebras.Algebras.html#4472" class="Function">lift-op</a> <a id="4764" class="Symbol">(</a><a id="4765" href="Algebras.Algebras.html#4743" class="Bound">𝑓</a> <a id="4767" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="4769" href="Algebras.Algebras.html#4720" class="Bound">𝑨</a><a id="4770" class="Symbol">)</a> <a id="4772" href="Algebras.Algebras.html#4722" class="Bound">𝓦</a><a id="4773" class="Symbol">)</a>

 <a id="4777" href="Algebras.Algebras.html#4777" class="Function">lift-alg-record-type</a> <a id="4798" class="Symbol">:</a> <a id="4800" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="4808" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4810" href="Algebras.Algebras.html#4607" class="Bound">𝑆</a> <a id="4812" class="Symbol">→</a> <a id="4814" class="Symbol">(</a><a id="4815" href="Algebras.Algebras.html#4815" class="Bound">𝓦</a> <a id="4817" class="Symbol">:</a> <a id="4819" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4827" class="Symbol">)</a> <a id="4829" class="Symbol">→</a> <a id="4831" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="4839" class="Symbol">(</a><a id="4840" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4842" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4844" href="Algebras.Algebras.html#4815" class="Bound">𝓦</a><a id="4845" class="Symbol">)</a> <a id="4847" href="Algebras.Algebras.html#4607" class="Bound">𝑆</a>
 <a id="4850" href="Algebras.Algebras.html#4777" class="Function">lift-alg-record-type</a> <a id="4871" href="Algebras.Algebras.html#4871" class="Bound">𝑨</a> <a id="4873" href="Algebras.Algebras.html#4873" class="Bound">𝓦</a> <a id="4875" class="Symbol">=</a> <a id="4877" href="Algebras.Algebras.html#1945" class="InductiveConstructor">mkalg</a> <a id="4883" class="Symbol">(</a><a id="4884" href="Overture.Lifts.html#2588" class="Record">Lift</a> <a id="4889" class="Symbol">(</a><a id="4890" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="4895" href="Algebras.Algebras.html#4871" class="Bound">𝑨</a><a id="4896" class="Symbol">))</a> <a id="4899" class="Symbol">(λ</a> <a id="4902" class="Symbol">(</a><a id="4903" href="Algebras.Algebras.html#4903" class="Bound">f</a> <a id="4905" class="Symbol">:</a> <a id="4907" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="4909" href="Algebras.Algebras.html#4607" class="Bound">𝑆</a> <a id="4911" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a><a id="4912" class="Symbol">)</a> <a id="4914" class="Symbol">→</a> <a id="4916" href="Algebras.Algebras.html#4472" class="Function">lift-op</a> <a id="4924" class="Symbol">((</a><a id="4926" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="4929" href="Algebras.Algebras.html#4871" class="Bound">𝑨</a><a id="4930" class="Symbol">)</a> <a id="4932" href="Algebras.Algebras.html#4903" class="Bound">f</a><a id="4933" class="Symbol">)</a> <a id="4935" href="Algebras.Algebras.html#4873" class="Bound">𝓦</a><a id="4936" class="Symbol">)</a>

</pre>

We use the function `lift-alg` to resolve errors that arise when working in Agda's noncummulative hierarchy of type universes. (See the discussion in [Overture.Lifts][].)




#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

If `𝑨` is an algebra and `R` a binary relation, then `compatible 𝑨 R` will represents the assertion that `R` is *compatible* with all basic operations of `𝑨`. Recall, informally this means for every operation symbol `𝑓 : ∣ 𝑆 ∣` and all pairs `𝑎 𝑎' : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` of tuples from the domain of 𝑨, the following implication holds:

if `R (𝑎 i) (𝑎' i)` for all `i`, then  `R ((𝑓 ̂ 𝑨) 𝑎) ((𝑓 ̂ 𝑨) 𝑎')`.

The formal definition representing this notion of compatibility is easy to write down since we already have a type that does all the work.

<pre class="Agda">

 <a id="5770" href="Algebras.Algebras.html#5770" class="Function">compatible</a> <a id="5781" class="Symbol">:</a> <a id="5783" class="Symbol">(</a><a id="5784" href="Algebras.Algebras.html#5784" class="Bound">𝑨</a> <a id="5786" class="Symbol">:</a> <a id="5788" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5796" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5798" href="Algebras.Algebras.html#4607" class="Bound">𝑆</a><a id="5799" class="Symbol">)</a> <a id="5801" class="Symbol">→</a> <a id="5803" href="Relations.Discrete.html#7168" class="Function">Rel</a> <a id="5807" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="5809" href="Algebras.Algebras.html#5784" class="Bound">𝑨</a> <a id="5811" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="5813" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5815" class="Symbol">→</a> <a id="5817" href="Algebras.Algebras.html#4621" class="Bound">𝓞</a> <a id="5819" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5821" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5823" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5825" href="Algebras.Algebras.html#4623" class="Bound">𝓥</a> <a id="5827" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5829" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="5831" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="5834" href="Algebras.Algebras.html#5770" class="Function">compatible</a>  <a id="5846" href="Algebras.Algebras.html#5846" class="Bound">𝑨</a> <a id="5848" href="Algebras.Algebras.html#5848" class="Bound">R</a> <a id="5850" class="Symbol">=</a> <a id="5852" class="Symbol">∀</a> <a id="5854" href="Algebras.Algebras.html#5854" class="Bound">𝑓</a> <a id="5856" class="Symbol">→</a> <a id="5858" href="Relations.Discrete.html#10239" class="Function">compatible-fun</a> <a id="5873" class="Symbol">(</a><a id="5874" href="Algebras.Algebras.html#5854" class="Bound">𝑓</a> <a id="5876" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="5878" href="Algebras.Algebras.html#5846" class="Bound">𝑨</a><a id="5879" class="Symbol">)</a> <a id="5881" href="Algebras.Algebras.html#5848" class="Bound">R</a>

</pre>

Recall, the `compatible-fun` type was defined in [Relations.Discrete][] module.



---------------------------------------



#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations*</a>

This section presents the `continuous-compatibility` submodule of the [Algebras.Algebras][] module.<sup>[*](Algebras.Algebras.html#fn0)</sup>


Next we define a type that represents *compatibility of a continuous relation* with all operations of an algebra. We start by defining compatibility of a continuous relations with a single operation.

<pre class="Agda">

<a id="6476" class="Keyword">module</a> <a id="continuous-compatibility"></a><a id="6483" href="Algebras.Algebras.html#6483" class="Module">continuous-compatibility</a> <a id="6508" class="Symbol">{</a><a id="6509" href="Algebras.Algebras.html#6509" class="Bound">𝑆</a> <a id="6511" class="Symbol">:</a> <a id="6513" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="6523" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a> <a id="6525" href="Universes.html#262" class="Generalizable">𝓥</a><a id="6526" class="Symbol">}</a> <a id="6528" class="Symbol">{</a><a id="6529" href="Algebras.Algebras.html#6529" class="Bound">𝑨</a> <a id="6531" class="Symbol">:</a> <a id="6533" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="6541" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6543" href="Algebras.Algebras.html#6509" class="Bound">𝑆</a><a id="6544" class="Symbol">}</a> <a id="6546" class="Symbol">{</a><a id="6547" href="Algebras.Algebras.html#6547" class="Bound">I</a> <a id="6549" class="Symbol">:</a> <a id="6551" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6553" href="Universes.html#403" class="Function Operator">̇</a><a id="6554" class="Symbol">}</a> <a id="6556" class="Keyword">where</a>

 <a id="6564" class="Keyword">open</a> <a id="6569" class="Keyword">import</a> <a id="6576" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="6597" class="Keyword">using</a> <a id="6603" class="Symbol">(</a><a id="6604" href="Relations.Continuous.html#3256" class="Function">ConRel</a><a id="6610" class="Symbol">;</a> <a id="6612" href="Relations.Continuous.html#3633" class="Function">lift-con-rel</a><a id="6624" class="Symbol">;</a> <a id="6626" href="Relations.Continuous.html#3735" class="Function">con-compatible-fun</a><a id="6644" class="Symbol">)</a>


 <a id="continuous-compatibility.con-compatible-op"></a><a id="6649" href="Algebras.Algebras.html#6649" class="Function">con-compatible-op</a> <a id="6667" class="Symbol">:</a> <a id="6669" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="6671" href="Algebras.Algebras.html#6509" class="Bound">𝑆</a> <a id="6673" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="6675" class="Symbol">→</a> <a id="6677" href="Relations.Continuous.html#3256" class="Function">ConRel</a> <a id="6684" href="Algebras.Algebras.html#6547" class="Bound">I</a> <a id="6686" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="6688" href="Algebras.Algebras.html#6529" class="Bound">𝑨</a> <a id="6690" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="6692" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6694" class="Symbol">→</a> <a id="6696" href="Algebras.Algebras.html#6541" class="Bound">𝓤</a> <a id="6698" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6700" href="Algebras.Algebras.html#6525" class="Bound">𝓥</a> <a id="6702" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6704" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6706" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6709" href="Algebras.Algebras.html#6649" class="Function">con-compatible-op</a> <a id="6727" href="Algebras.Algebras.html#6727" class="Bound">𝑓</a> <a id="6729" href="Algebras.Algebras.html#6729" class="Bound">R</a> <a id="6731" class="Symbol">=</a> <a id="6733" href="Relations.Continuous.html#3735" class="Function">con-compatible-fun</a> <a id="6752" class="Symbol">(λ</a> <a id="6755" href="Algebras.Algebras.html#6755" class="Bound">_</a> <a id="6757" class="Symbol">→</a> <a id="6759" class="Symbol">(</a><a id="6760" href="Algebras.Algebras.html#6727" class="Bound">𝑓</a> <a id="6762" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="6764" href="Algebras.Algebras.html#6529" class="Bound">𝑨</a><a id="6765" class="Symbol">))</a> <a id="6768" href="Algebras.Algebras.html#6729" class="Bound">R</a>

</pre>

In case it helps the reader understand `con-compatible-op`, we redefine it explicitly without the help of `con-compatible-fun`.

<pre class="Agda">

 <a id="continuous-compatibility.con-compatible-op&#39;"></a><a id="6927" href="Algebras.Algebras.html#6927" class="Function">con-compatible-op&#39;</a> <a id="6946" class="Symbol">:</a> <a id="6948" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="6950" href="Algebras.Algebras.html#6509" class="Bound">𝑆</a> <a id="6952" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="6954" class="Symbol">→</a> <a id="6956" href="Relations.Continuous.html#3256" class="Function">ConRel</a> <a id="6963" href="Algebras.Algebras.html#6547" class="Bound">I</a> <a id="6965" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="6967" href="Algebras.Algebras.html#6529" class="Bound">𝑨</a> <a id="6969" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="6971" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6973" class="Symbol">→</a> <a id="6975" href="Algebras.Algebras.html#6541" class="Bound">𝓤</a> <a id="6977" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6979" href="Algebras.Algebras.html#6525" class="Bound">𝓥</a> <a id="6981" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6983" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6985" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6988" href="Algebras.Algebras.html#6927" class="Function">con-compatible-op&#39;</a> <a id="7007" href="Algebras.Algebras.html#7007" class="Bound">𝑓</a> <a id="7009" href="Algebras.Algebras.html#7009" class="Bound">R</a> <a id="7011" class="Symbol">=</a> <a id="7013" class="Symbol">∀</a> <a id="7015" href="Algebras.Algebras.html#7015" class="Bound">𝕒</a> <a id="7017" class="Symbol">→</a> <a id="7019" class="Symbol">(</a><a id="7020" href="Relations.Continuous.html#3633" class="Function">lift-con-rel</a> <a id="7033" href="Algebras.Algebras.html#7009" class="Bound">R</a><a id="7034" class="Symbol">)</a> <a id="7036" href="Algebras.Algebras.html#7015" class="Bound">𝕒</a> <a id="7038" class="Symbol">→</a> <a id="7040" href="Algebras.Algebras.html#7009" class="Bound">R</a> <a id="7042" class="Symbol">(λ</a> <a id="7045" href="Algebras.Algebras.html#7045" class="Bound">i</a> <a id="7047" class="Symbol">→</a> <a id="7049" class="Symbol">(</a><a id="7050" href="Algebras.Algebras.html#7007" class="Bound">𝑓</a> <a id="7052" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="7054" href="Algebras.Algebras.html#6529" class="Bound">𝑨</a><a id="7055" class="Symbol">)</a> <a id="7057" class="Symbol">(</a><a id="7058" href="Algebras.Algebras.html#7015" class="Bound">𝕒</a> <a id="7060" href="Algebras.Algebras.html#7045" class="Bound">i</a><a id="7061" class="Symbol">))</a>

</pre>

where we have let Agda infer the type of `𝕒`, which is `(i : I) → ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`.

With `con-compatible-op` in hand, it is a trivial matter to define a type that represents *compatibility of a continuous relation with an algebra*.

<pre class="Agda">

 <a id="continuous-compatibility.con-compatible"></a><a id="7326" href="Algebras.Algebras.html#7326" class="Function">con-compatible</a> <a id="7341" class="Symbol">:</a> <a id="7343" href="Relations.Continuous.html#3256" class="Function">ConRel</a> <a id="7350" href="Algebras.Algebras.html#6547" class="Bound">I</a> <a id="7352" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="7354" href="Algebras.Algebras.html#6529" class="Bound">𝑨</a> <a id="7356" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="7358" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7360" class="Symbol">→</a> <a id="7362" href="Algebras.Algebras.html#6523" class="Bound">𝓞</a> <a id="7364" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7366" href="Algebras.Algebras.html#6541" class="Bound">𝓤</a> <a id="7368" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7370" href="Algebras.Algebras.html#6525" class="Bound">𝓥</a> <a id="7372" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7374" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7376" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7379" href="Algebras.Algebras.html#7326" class="Function">con-compatible</a> <a id="7394" href="Algebras.Algebras.html#7394" class="Bound">R</a> <a id="7396" class="Symbol">=</a> <a id="7398" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="7400" href="Algebras.Algebras.html#7400" class="Bound">𝑓</a> <a id="7402" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="7404" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="7406" href="Algebras.Algebras.html#6509" class="Bound">𝑆</a> <a id="7408" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="7410" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="7412" href="Algebras.Algebras.html#6649" class="Function">con-compatible-op</a> <a id="7430" href="Algebras.Algebras.html#7400" class="Bound">𝑓</a> <a id="7432" href="Algebras.Algebras.html#7394" class="Bound">R</a>

</pre>



--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>


[← Algebras.Signatures](Algebras.Signatures.html)
<span style="float:right;">[Algebras.Products →](Algebras.Products.html)</span>


{% include UALib.Links.md %}
