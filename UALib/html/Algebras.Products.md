---
layout: default
title : UALib.Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="product-algebras">Product Algebras</a>

This section presents the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

Notice that we begin this module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

**NOTATION**.  From now on, the remaining modules of the [UALib][] will assume universes 𝓞 and 𝓥, and a fixed signature type `𝑆 : Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="587" class="Symbol">{-#</a> <a id="591" class="Keyword">OPTIONS</a> <a id="599" class="Pragma">--without-K</a> <a id="611" class="Pragma">--exact-split</a> <a id="625" class="Pragma">--safe</a> <a id="632" class="Symbol">#-}</a>

<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="669" class="Keyword">using</a> <a id="675" class="Symbol">(</a><a id="676" href="Algebras.Signatures.html#1251" class="Function">Signature</a><a id="685" class="Symbol">;</a> <a id="687" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a><a id="688" class="Symbol">;</a> <a id="690" href="Universes.html#262" class="Generalizable">𝓥</a><a id="691" class="Symbol">)</a>

<a id="694" class="Keyword">module</a> <a id="701" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="719" class="Symbol">{</a><a id="720" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="722" class="Symbol">:</a> <a id="724" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="734" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="736" href="Universes.html#262" class="Generalizable">𝓥</a><a id="737" class="Symbol">}</a> <a id="739" class="Keyword">where</a>

<a id="746" class="Keyword">open</a> <a id="751" class="Keyword">import</a> <a id="758" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="776" class="Keyword">hiding</a> <a id="783" class="Symbol">(</a><a id="784" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a><a id="785" class="Symbol">;</a> <a id="787" href="Universes.html#262" class="Generalizable">𝓥</a><a id="788" class="Symbol">)</a> <a id="790" class="Keyword">public</a>

</pre>

We must import the `Signature` type from the [Algebras.Signatures][] module first, before the `module` line, so that we may use it to declare the signature `𝑆` as a parameter of the [Algebras.Products][] module.

In the [UALib][] a \defn{product of} \ab 𝑆-\defn{algebras} is represented by the following type.

<pre class="Agda">

<a id="1135" class="Keyword">module</a> <a id="1142" href="Algebras.Products.html#1142" class="Module">_</a> <a id="1144" class="Symbol">{</a><a id="1145" href="Algebras.Products.html#1145" class="Bound">𝓤</a> <a id="1147" href="Algebras.Products.html#1147" class="Bound">𝓘</a> <a id="1149" class="Symbol">:</a> <a id="1151" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1159" class="Symbol">}{</a><a id="1161" href="Algebras.Products.html#1161" class="Bound">I</a> <a id="1163" class="Symbol">:</a> <a id="1165" href="Algebras.Products.html#1147" class="Bound">𝓘</a> <a id="1167" href="Universes.html#403" class="Function Operator">̇</a> <a id="1169" class="Symbol">}</a> <a id="1171" class="Keyword">where</a>

 <a id="1179" href="Algebras.Products.html#1179" class="Function">⨅</a> <a id="1181" class="Symbol">:</a> <a id="1183" class="Symbol">(</a><a id="1184" href="Algebras.Products.html#1184" class="Bound">𝒜</a> <a id="1186" class="Symbol">:</a> <a id="1188" href="Algebras.Products.html#1161" class="Bound">I</a> <a id="1190" class="Symbol">→</a> <a id="1192" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1200" href="Algebras.Products.html#1145" class="Bound">𝓤</a> <a id="1202" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="1204" class="Symbol">)</a> <a id="1206" class="Symbol">→</a> <a id="1208" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1216" class="Symbol">(</a><a id="1217" href="Algebras.Products.html#1147" class="Bound">𝓘</a> <a id="1219" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1221" href="Algebras.Products.html#1145" class="Bound">𝓤</a><a id="1222" class="Symbol">)</a> <a id="1224" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="1228" href="Algebras.Products.html#1179" class="Function">⨅</a> <a id="1230" href="Algebras.Products.html#1230" class="Bound">𝒜</a> <a id="1232" class="Symbol">=</a> <a id="1234" class="Symbol">(</a><a id="1235" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="1237" href="Algebras.Products.html#1237" class="Bound">i</a> <a id="1239" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="1241" href="Algebras.Products.html#1161" class="Bound">I</a> <a id="1243" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="1245" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="1247" href="Algebras.Products.html#1230" class="Bound">𝒜</a> <a id="1249" href="Algebras.Products.html#1237" class="Bound">i</a> <a id="1251" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="1252" class="Symbol">)</a> <a id="1254" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a>               <a id="1270" class="Comment">-- domain of the product algebra</a>
       <a id="1310" class="Symbol">λ</a> <a id="1312" href="Algebras.Products.html#1312" class="Bound">𝑓</a> <a id="1314" href="Algebras.Products.html#1314" class="Bound">𝑎</a> <a id="1316" href="Algebras.Products.html#1316" class="Bound">i</a> <a id="1318" class="Symbol">→</a> <a id="1320" class="Symbol">(</a><a id="1321" href="Algebras.Products.html#1312" class="Bound">𝑓</a> <a id="1323" href="Algebras.Algebras.html#2987" class="Function Operator">̂</a> <a id="1325" href="Algebras.Products.html#1230" class="Bound">𝒜</a> <a id="1327" href="Algebras.Products.html#1316" class="Bound">i</a><a id="1328" class="Symbol">)</a> <a id="1330" class="Symbol">λ</a> <a id="1332" href="Algebras.Products.html#1332" class="Bound">x</a> <a id="1334" class="Symbol">→</a> <a id="1336" href="Algebras.Products.html#1314" class="Bound">𝑎</a> <a id="1338" href="Algebras.Products.html#1332" class="Bound">x</a> <a id="1340" href="Algebras.Products.html#1316" class="Bound">i</a>   <a id="1344" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

Other modules of the [UALib][] will use the foregoing product type exclusively.  However, for completeness, we now demonstrate how one would construct product algebras when the factors are defined using records.

<pre class="Agda">

<a id="1712" class="Keyword">open</a> <a id="1717" href="Algebras.Algebras.html#1863" class="Module">algebra</a>

<a id="1726" class="Comment">-- product for algebras of record type</a>
<a id="⨅&#39;"></a><a id="1765" href="Algebras.Products.html#1765" class="Function">⨅&#39;</a> <a id="1768" class="Symbol">:</a> <a id="1770" class="Symbol">{</a><a id="1771" href="Algebras.Products.html#1771" class="Bound">𝓤</a> <a id="1773" href="Algebras.Products.html#1773" class="Bound">𝓘</a> <a id="1775" class="Symbol">:</a> <a id="1777" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1785" class="Symbol">}{</a><a id="1787" href="Algebras.Products.html#1787" class="Bound">I</a> <a id="1789" class="Symbol">:</a> <a id="1791" href="Algebras.Products.html#1773" class="Bound">𝓘</a> <a id="1793" href="Universes.html#403" class="Function Operator">̇</a> <a id="1795" class="Symbol">}(</a><a id="1797" href="Algebras.Products.html#1797" class="Bound">𝒜</a> <a id="1799" class="Symbol">:</a> <a id="1801" href="Algebras.Products.html#1787" class="Bound">I</a> <a id="1803" class="Symbol">→</a> <a id="1805" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="1813" href="Algebras.Products.html#1771" class="Bound">𝓤</a> <a id="1815" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="1816" class="Symbol">)</a> <a id="1818" class="Symbol">→</a> <a id="1820" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="1828" class="Symbol">(</a><a id="1829" href="Algebras.Products.html#1773" class="Bound">𝓘</a> <a id="1831" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1833" href="Algebras.Products.html#1771" class="Bound">𝓤</a><a id="1834" class="Symbol">)</a> <a id="1836" href="Algebras.Products.html#720" class="Bound">𝑆</a>

<a id="1839" href="Algebras.Products.html#1765" class="Function">⨅&#39;</a> <a id="1842" href="Algebras.Products.html#1842" class="Bound">𝒜</a> <a id="1844" class="Symbol">=</a> <a id="1846" class="Keyword">record</a> <a id="1853" class="Symbol">{</a> <a id="1855" href="Algebras.Algebras.html#1958" class="Field">univ</a> <a id="1860" class="Symbol">=</a> <a id="1862" class="Symbol">∀</a> <a id="1864" href="Algebras.Products.html#1864" class="Bound">i</a> <a id="1866" class="Symbol">→</a> <a id="1868" href="Algebras.Algebras.html#1958" class="Field">univ</a> <a id="1873" class="Symbol">(</a><a id="1874" href="Algebras.Products.html#1842" class="Bound">𝒜</a> <a id="1876" href="Algebras.Products.html#1864" class="Bound">i</a><a id="1877" class="Symbol">)</a>                 <a id="1895" class="Comment">-- domain</a>
              <a id="1919" class="Symbol">;</a> <a id="1921" href="Algebras.Algebras.html#1971" class="Field">op</a> <a id="1924" class="Symbol">=</a> <a id="1926" class="Symbol">λ</a> <a id="1928" href="Algebras.Products.html#1928" class="Bound">𝑓</a> <a id="1930" href="Algebras.Products.html#1930" class="Bound">𝑎</a> <a id="1932" href="Algebras.Products.html#1932" class="Bound">i</a> <a id="1934" class="Symbol">→</a> <a id="1936" class="Symbol">(</a><a id="1937" href="Algebras.Algebras.html#1971" class="Field">op</a> <a id="1940" class="Symbol">(</a><a id="1941" href="Algebras.Products.html#1842" class="Bound">𝒜</a> <a id="1943" href="Algebras.Products.html#1932" class="Bound">i</a><a id="1944" class="Symbol">))</a> <a id="1947" href="Algebras.Products.html#1928" class="Bound">𝑓</a> <a id="1949" class="Symbol">λ</a> <a id="1951" href="Algebras.Products.html#1951" class="Bound">x</a> <a id="1953" class="Symbol">→</a> <a id="1955" href="Algebras.Products.html#1930" class="Bound">𝑎</a> <a id="1957" href="Algebras.Products.html#1951" class="Bound">x</a> <a id="1959" href="Algebras.Products.html#1932" class="Bound">i</a> <a id="1961" class="Comment">-- basic operations</a>
              <a id="1995" class="Symbol">}</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that it is worthwhile to define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2252" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="2255" class="Symbol">:</a> <a id="2257" href="Agda.Primitive.html#423" class="Postulate">Universe</a> <a id="2266" class="Symbol">→</a> <a id="2268" href="Agda.Primitive.html#423" class="Postulate">Universe</a>
<a id="2277" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="2280" href="Algebras.Products.html#2280" class="Bound">𝓤</a> <a id="2282" class="Symbol">=</a> <a id="2284" href="Algebras.Products.html#734" class="Bound">𝓞</a> <a id="2286" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2288" href="Algebras.Products.html#736" class="Bound">𝓥</a> <a id="2290" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2292" href="Algebras.Products.html#2280" class="Bound">𝓤</a> <a id="2294" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra 𝓤 𝑆`, for some universe level `𝓤` and signature `𝑆`. That is, `𝒦 : Pred (Algebra 𝓤 𝑆) \_`.<sup>[1](Algebras.Products.html#fn1)</sup>

Later we will formally state and prove that, given an arbitrary class `𝒦` of algebras, the product of all subalgebras of algebras in the class belongs to the class  `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise. In fact, it is not even immediately clear (at least not to this author) how to merely express the product of an entire class of algebras as a dependent type. (We urge you, dear *UALiber*, to take a moment and try it before moving on.)

After some concentratation, meditation, and a few failed attempts, eventually the right type reveals itself and, as is often the case, the thing we sought seems almost obvious once we lay our hands on it.<sup>[2](Algebras.Products.html#fn2)</sup>

The solution we propose in the \agdaualib is the \af{class-product'} type whose construction is the main goal of this section.

orm of the `class-product` whose construction is the main goal of this section.

First, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">

<a id="3712" class="Keyword">module</a> <a id="3719" href="Algebras.Products.html#3719" class="Module">_</a> <a id="3721" class="Symbol">{</a><a id="3722" href="Algebras.Products.html#3722" class="Bound">𝓤</a> <a id="3724" href="Algebras.Products.html#3724" class="Bound">𝓧</a> <a id="3726" class="Symbol">:</a> <a id="3728" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3736" class="Symbol">}{</a><a id="3738" href="Algebras.Products.html#3738" class="Bound">X</a> <a id="3740" class="Symbol">:</a> <a id="3742" href="Algebras.Products.html#3724" class="Bound">𝓧</a> <a id="3744" href="Universes.html#403" class="Function Operator">̇</a><a id="3745" class="Symbol">}</a> <a id="3747" class="Keyword">where</a>

 <a id="3755" href="Algebras.Products.html#3755" class="Function">ℑ</a> <a id="3757" class="Symbol">:</a> <a id="3759" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="3764" class="Symbol">(</a><a id="3765" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3773" href="Algebras.Products.html#3722" class="Bound">𝓤</a> <a id="3775" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="3776" class="Symbol">)(</a><a id="3778" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="3781" href="Algebras.Products.html#3722" class="Bound">𝓤</a><a id="3782" class="Symbol">)</a> <a id="3784" class="Symbol">→</a> <a id="3786" class="Symbol">(</a><a id="3787" href="Algebras.Products.html#3724" class="Bound">𝓧</a> <a id="3789" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3791" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="3794" href="Algebras.Products.html#3722" class="Bound">𝓤</a><a id="3795" class="Symbol">)</a> <a id="3797" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3800" href="Algebras.Products.html#3755" class="Function">ℑ</a> <a id="3802" href="Algebras.Products.html#3802" class="Bound">𝒦</a> <a id="3804" class="Symbol">=</a> <a id="3806" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3808" href="Algebras.Products.html#3808" class="Bound">𝑨</a> <a id="3810" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3812" class="Symbol">(</a><a id="3813" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3821" href="Algebras.Products.html#3722" class="Bound">𝓤</a> <a id="3823" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="3824" class="Symbol">)</a> <a id="3826" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3828" class="Symbol">(</a><a id="3829" href="Algebras.Products.html#3808" class="Bound">𝑨</a> <a id="3831" href="Relations.Discrete.html#2499" class="Function Operator">∈</a> <a id="3833" href="Algebras.Products.html#3802" class="Bound">𝒦</a><a id="3834" class="Symbol">)</a> <a id="3836" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="3838" class="Symbol">(</a><a id="3839" href="Algebras.Products.html#3738" class="Bound">X</a> <a id="3841" class="Symbol">→</a> <a id="3843" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="3845" href="Algebras.Products.html#3808" class="Bound">𝑨</a> <a id="3847" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="3848" class="Symbol">)</a>

</pre>

Notice that the second component of this dependent pair type is  `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`. In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`, until we realized that adding the type `X → ∣ 𝑨 ∣` is quite useful. Later we will see exactly why, but for now suffice it to say that a map of type `X → ∣ 𝑨 ∣` may be viewed abstractly as an *ambient context*, or more concretely, as an assignment of *values* in `∣ 𝑨 ∣` to *variable symbols* in `X`.  When computing with or reasoning about products, while we don't want to rigidly impose a context in advance, want do want to lay our hands on whatever context is ultimately assumed.  Including the "context map" inside the index type `ℑ` of the product turns out to be a convenient way to achieve this flexibility.


Taking the product over the index type ℑ requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra 𝓤 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="4984" href="Algebras.Products.html#4984" class="Function">𝔄</a> <a id="4986" class="Symbol">:</a> <a id="4988" class="Symbol">(</a><a id="4989" href="Algebras.Products.html#4989" class="Bound">𝒦</a> <a id="4991" class="Symbol">:</a> <a id="4993" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="4998" class="Symbol">(</a><a id="4999" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5007" href="Algebras.Products.html#3722" class="Bound">𝓤</a> <a id="5009" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="5010" class="Symbol">)(</a><a id="5012" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="5015" href="Algebras.Products.html#3722" class="Bound">𝓤</a><a id="5016" class="Symbol">))</a> <a id="5019" class="Symbol">→</a> <a id="5021" href="Algebras.Products.html#3755" class="Function">ℑ</a> <a id="5023" href="Algebras.Products.html#4989" class="Bound">𝒦</a> <a id="5025" class="Symbol">→</a> <a id="5027" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5035" href="Algebras.Products.html#3722" class="Bound">𝓤</a> <a id="5037" href="Algebras.Products.html#720" class="Bound">𝑆</a>
 <a id="5040" href="Algebras.Products.html#4984" class="Function">𝔄</a> <a id="5042" href="Algebras.Products.html#5042" class="Bound">𝒦</a> <a id="5044" class="Symbol">=</a> <a id="5046" class="Symbol">λ</a> <a id="5048" class="Symbol">(</a><a id="5049" href="Algebras.Products.html#5049" class="Bound">i</a> <a id="5051" class="Symbol">:</a> <a id="5053" class="Symbol">(</a><a id="5054" href="Algebras.Products.html#3755" class="Function">ℑ</a> <a id="5056" href="Algebras.Products.html#5042" class="Bound">𝒦</a><a id="5057" class="Symbol">))</a> <a id="5060" class="Symbol">→</a> <a id="5062" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="5064" href="Algebras.Products.html#5049" class="Bound">i</a> <a id="5066" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="5182" href="Algebras.Products.html#5182" class="Function">class-product</a> <a id="5196" class="Symbol">:</a> <a id="5198" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="5203" class="Symbol">(</a><a id="5204" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5212" href="Algebras.Products.html#3722" class="Bound">𝓤</a> <a id="5214" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="5215" class="Symbol">)(</a><a id="5217" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="5220" href="Algebras.Products.html#3722" class="Bound">𝓤</a><a id="5221" class="Symbol">)</a> <a id="5223" class="Symbol">→</a> <a id="5225" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5233" class="Symbol">(</a><a id="5234" href="Algebras.Products.html#3724" class="Bound">𝓧</a> <a id="5236" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5238" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="5241" href="Algebras.Products.html#3722" class="Bound">𝓤</a><a id="5242" class="Symbol">)</a> <a id="5244" href="Algebras.Products.html#720" class="Bound">𝑆</a>
 <a id="5247" href="Algebras.Products.html#5182" class="Function">class-product</a> <a id="5261" href="Algebras.Products.html#5261" class="Bound">𝒦</a> <a id="5263" class="Symbol">=</a> <a id="5265" href="Algebras.Products.html#1179" class="Function">⨅</a> <a id="5267" class="Symbol">(</a> <a id="5269" href="Algebras.Products.html#4984" class="Function">𝔄</a> <a id="5271" href="Algebras.Products.html#5261" class="Bound">𝒦</a> <a id="5273" class="Symbol">)</a>

</pre>

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

<pre class="Agda">

 <a id="5413" href="Algebras.Products.html#5413" class="Function">class-product&#39;</a> <a id="5428" class="Symbol">:</a> <a id="5430" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="5435" class="Symbol">(</a><a id="5436" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5444" href="Algebras.Products.html#3722" class="Bound">𝓤</a> <a id="5446" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="5447" class="Symbol">)(</a><a id="5449" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="5452" href="Algebras.Products.html#3722" class="Bound">𝓤</a><a id="5453" class="Symbol">)</a> <a id="5455" class="Symbol">→</a> <a id="5457" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5465" class="Symbol">(</a><a id="5466" href="Algebras.Products.html#3724" class="Bound">𝓧</a> <a id="5468" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5470" href="Algebras.Products.html#2252" class="Function">ov</a> <a id="5473" href="Algebras.Products.html#3722" class="Bound">𝓤</a><a id="5474" class="Symbol">)</a> <a id="5476" href="Algebras.Products.html#720" class="Bound">𝑆</a>
 <a id="5479" href="Algebras.Products.html#5413" class="Function">class-product&#39;</a> <a id="5494" href="Algebras.Products.html#5494" class="Bound">𝒦</a> <a id="5496" class="Symbol">=</a> <a id="5498" href="Algebras.Products.html#1179" class="Function">⨅</a> <a id="5500" class="Symbol">λ</a> <a id="5502" class="Symbol">(</a><a id="5503" href="Algebras.Products.html#5503" class="Bound">i</a> <a id="5505" class="Symbol">:</a> <a id="5507" class="Symbol">(</a><a id="5508" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="5510" href="Algebras.Products.html#5510" class="Bound">𝑨</a> <a id="5512" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="5514" class="Symbol">(</a><a id="5515" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5523" href="Algebras.Products.html#3722" class="Bound">𝓤</a> <a id="5525" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="5526" class="Symbol">)</a> <a id="5528" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="5530" class="Symbol">(</a><a id="5531" href="Algebras.Products.html#5510" class="Bound">𝑨</a> <a id="5533" href="Relations.Discrete.html#2499" class="Function Operator">∈</a> <a id="5535" href="Algebras.Products.html#5494" class="Bound">𝒦</a><a id="5536" class="Symbol">)</a> <a id="5538" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="5540" class="Symbol">(</a><a id="5541" href="Algebras.Products.html#3738" class="Bound">X</a> <a id="5543" class="Symbol">→</a> <a id="5545" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="5547" href="Algebras.Products.html#5510" class="Bound">𝑨</a> <a id="5549" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="5550" class="Symbol">)))</a> <a id="5554" class="Symbol">→</a> <a id="5556" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="5558" href="Algebras.Products.html#5503" class="Bound">i</a> <a id="5560" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a>

</pre>

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the triple `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.





-----------------------

<sup>1</sup><span class="footnote" id="fn1"> The underscore is merely a placeholder for the universe of the predicate type and needn't concern us here.</span>

<sup>2</sup><span class="footnote" id="fn2"> This was our own experience, but readers are encouraged to try to derive for themselves a type that represents the product of all things satisfying a given predicate (e.g., over a type like \AgdaFunction{Algebra}\AgdaSpace{}\AgdaBound{𝓤}\AgdaSpace{}\AgdaBound{𝑆}, or over an arbitrary type). It is a good exercise.</span>

<br>
<br>

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
