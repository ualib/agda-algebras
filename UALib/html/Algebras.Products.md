---
layout: default
title : Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="product-algebras">Product Algebras</a>

This is the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

Notice that we begin this module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

<pre class="Agda">

<a id="420" class="Symbol">{-#</a> <a id="424" class="Keyword">OPTIONS</a> <a id="432" class="Pragma">--without-K</a> <a id="444" class="Pragma">--exact-split</a> <a id="458" class="Pragma">--safe</a> <a id="465" class="Symbol">#-}</a>

<a id="470" class="Keyword">open</a> <a id="475" class="Keyword">import</a> <a id="482" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="502" class="Keyword">using</a> <a id="508" class="Symbol">(</a><a id="509" href="Algebras.Signatures.html#626" class="Function">Signature</a><a id="518" class="Symbol">;</a> <a id="520" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a><a id="521" class="Symbol">;</a> <a id="523" href="Universes.html#262" class="Generalizable">𝓥</a><a id="524" class="Symbol">)</a>

<a id="527" class="Keyword">module</a> <a id="534" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="552" class="Symbol">{</a><a id="553" href="Algebras.Products.html#553" class="Bound">𝑆</a> <a id="555" class="Symbol">:</a> <a id="557" href="Algebras.Signatures.html#626" class="Function">Signature</a> <a id="567" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="569" href="Universes.html#262" class="Generalizable">𝓥</a><a id="570" class="Symbol">}</a> <a id="572" class="Keyword">where</a>

<a id="579" class="Keyword">open</a> <a id="584" class="Keyword">import</a> <a id="591" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="609" class="Keyword">hiding</a> <a id="616" class="Symbol">(</a><a id="617" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a><a id="618" class="Symbol">;</a> <a id="620" href="Universes.html#262" class="Generalizable">𝓥</a><a id="621" class="Symbol">)</a> <a id="623" class="Keyword">public</a>

</pre>

From now on, the modules of the [UALib][] will assume a fixed signature `𝑆 : Signature 𝓞 𝓥`.  Notice that we have to import the `Signature` type from [Algebras.Signatures][] before the `module` line so that we may declare the signature `𝑆` as a parameter of the [Algebras.Products][] module.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I : 𝓘 ̇` and a family `𝒜 : I → Algebra 𝓤 𝑆`, the *product* `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In the [UALib][] a *product of* 𝑆-*algebras* is represented by the following type.

<pre class="Agda">

<a id="1548" class="Keyword">module</a> <a id="1555" href="Algebras.Products.html#1555" class="Module">_</a> <a id="1557" class="Symbol">{</a><a id="1558" href="Algebras.Products.html#1558" class="Bound">𝓤</a> <a id="1560" href="Algebras.Products.html#1560" class="Bound">𝓘</a> <a id="1562" class="Symbol">:</a> <a id="1564" href="Universes.html#205" class="Postulate">Universe</a><a id="1572" class="Symbol">}{</a><a id="1574" href="Algebras.Products.html#1574" class="Bound">I</a> <a id="1576" class="Symbol">:</a> <a id="1578" href="Algebras.Products.html#1560" class="Bound">𝓘</a> <a id="1580" href="Universes.html#403" class="Function Operator">̇</a> <a id="1582" class="Symbol">}</a> <a id="1584" class="Keyword">where</a>

 <a id="1592" href="Algebras.Products.html#1592" class="Function">⨅</a> <a id="1594" class="Symbol">:</a> <a id="1596" class="Symbol">(</a><a id="1597" href="Algebras.Products.html#1597" class="Bound">𝒜</a> <a id="1599" class="Symbol">:</a> <a id="1601" href="Algebras.Products.html#1574" class="Bound">I</a> <a id="1603" class="Symbol">→</a> <a id="1605" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="1613" href="Algebras.Products.html#1558" class="Bound">𝓤</a> <a id="1615" href="Algebras.Products.html#553" class="Bound">𝑆</a> <a id="1617" class="Symbol">)</a> <a id="1619" class="Symbol">→</a> <a id="1621" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="1629" class="Symbol">(</a><a id="1630" href="Algebras.Products.html#1560" class="Bound">𝓘</a> <a id="1632" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1634" href="Algebras.Products.html#1558" class="Bound">𝓤</a><a id="1635" class="Symbol">)</a> <a id="1637" href="Algebras.Products.html#553" class="Bound">𝑆</a>

 <a id="1641" href="Algebras.Products.html#1592" class="Function">⨅</a> <a id="1643" href="Algebras.Products.html#1643" class="Bound">𝒜</a> <a id="1645" class="Symbol">=</a> <a id="1647" class="Symbol">(</a><a id="1648" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="1650" href="Algebras.Products.html#1650" class="Bound">i</a> <a id="1652" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="1654" href="Algebras.Products.html#1574" class="Bound">I</a> <a id="1656" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="1658" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="1660" href="Algebras.Products.html#1643" class="Bound">𝒜</a> <a id="1662" href="Algebras.Products.html#1650" class="Bound">i</a> <a id="1664" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a><a id="1665" class="Symbol">)</a> <a id="1667" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a>            <a id="1680" class="Comment">-- domain of the product algebra</a>
       <a id="1720" class="Symbol">λ</a> <a id="1722" href="Algebras.Products.html#1722" class="Bound">𝑓</a> <a id="1724" href="Algebras.Products.html#1724" class="Bound">𝑎</a> <a id="1726" href="Algebras.Products.html#1726" class="Bound">i</a> <a id="1728" class="Symbol">→</a> <a id="1730" class="Symbol">(</a><a id="1731" href="Algebras.Products.html#1722" class="Bound">𝑓</a> <a id="1733" href="Algebras.Algebras.html#3080" class="Function Operator">̂</a> <a id="1735" href="Algebras.Products.html#1643" class="Bound">𝒜</a> <a id="1737" href="Algebras.Products.html#1726" class="Bound">i</a><a id="1738" class="Symbol">)</a> <a id="1740" class="Symbol">λ</a> <a id="1742" href="Algebras.Products.html#1742" class="Bound">x</a> <a id="1744" class="Symbol">→</a> <a id="1746" href="Algebras.Products.html#1724" class="Bound">𝑎</a> <a id="1748" href="Algebras.Products.html#1742" class="Bound">x</a> <a id="1750" href="Algebras.Products.html#1726" class="Bound">i</a>   <a id="1754" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UALib][] whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

 <a id="2229" class="Keyword">open</a> <a id="2234" href="Algebras.Algebras.html#2059" class="Module">algebra</a>

 <a id="2244" href="Algebras.Products.html#2244" class="Function">⨅&#39;</a> <a id="2247" class="Symbol">:</a> <a id="2249" class="Symbol">(</a><a id="2250" href="Algebras.Products.html#2250" class="Bound">𝒜</a> <a id="2252" class="Symbol">:</a> <a id="2254" href="Algebras.Products.html#1574" class="Bound">I</a> <a id="2256" class="Symbol">→</a> <a id="2258" href="Algebras.Algebras.html#2059" class="Record">algebra</a> <a id="2266" href="Algebras.Products.html#1558" class="Bound">𝓤</a> <a id="2268" href="Algebras.Products.html#553" class="Bound">𝑆</a><a id="2269" class="Symbol">)</a> <a id="2271" class="Symbol">→</a> <a id="2273" href="Algebras.Algebras.html#2059" class="Record">algebra</a> <a id="2281" class="Symbol">(</a><a id="2282" href="Algebras.Products.html#1560" class="Bound">𝓘</a> <a id="2284" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2286" href="Algebras.Products.html#1558" class="Bound">𝓤</a><a id="2287" class="Symbol">)</a> <a id="2289" href="Algebras.Products.html#553" class="Bound">𝑆</a>

 <a id="2293" href="Algebras.Products.html#2244" class="Function">⨅&#39;</a> <a id="2296" href="Algebras.Products.html#2296" class="Bound">𝒜</a> <a id="2298" class="Symbol">=</a> <a id="2300" class="Keyword">record</a> <a id="2307" class="Symbol">{</a> <a id="2309" href="Algebras.Algebras.html#2154" class="Field">univ</a> <a id="2314" class="Symbol">=</a> <a id="2316" class="Symbol">∀</a> <a id="2318" href="Algebras.Products.html#2318" class="Bound">i</a> <a id="2320" class="Symbol">→</a> <a id="2322" href="Algebras.Algebras.html#2154" class="Field">univ</a> <a id="2327" class="Symbol">(</a><a id="2328" href="Algebras.Products.html#2296" class="Bound">𝒜</a> <a id="2330" href="Algebras.Products.html#2318" class="Bound">i</a><a id="2331" class="Symbol">)</a> <a id="2333" class="Symbol">;</a>                 <a id="2351" class="Comment">-- domain</a>
                 <a id="2378" href="Algebras.Algebras.html#2167" class="Field">op</a> <a id="2381" class="Symbol">=</a> <a id="2383" class="Symbol">λ</a> <a id="2385" href="Algebras.Products.html#2385" class="Bound">𝑓</a> <a id="2387" href="Algebras.Products.html#2387" class="Bound">𝑎</a> <a id="2389" href="Algebras.Products.html#2389" class="Bound">i</a> <a id="2391" class="Symbol">→</a> <a id="2393" class="Symbol">(</a><a id="2394" href="Algebras.Algebras.html#2167" class="Field">op</a> <a id="2397" class="Symbol">(</a><a id="2398" href="Algebras.Products.html#2296" class="Bound">𝒜</a> <a id="2400" href="Algebras.Products.html#2389" class="Bound">i</a><a id="2401" class="Symbol">))</a> <a id="2404" href="Algebras.Products.html#2385" class="Bound">𝑓</a> <a id="2406" class="Symbol">λ</a> <a id="2408" href="Algebras.Products.html#2408" class="Bound">x</a> <a id="2410" class="Symbol">→</a> <a id="2412" href="Algebras.Products.html#2387" class="Bound">𝑎</a> <a id="2414" href="Algebras.Products.html#2408" class="Bound">x</a> <a id="2416" href="Algebras.Products.html#2389" class="Bound">i</a> <a id="2418" class="Symbol">}</a> <a id="2420" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2678" href="Algebras.Products.html#2678" class="Function">ov</a> <a id="2681" class="Symbol">:</a> <a id="2683" href="Universes.html#205" class="Postulate">Universe</a> <a id="2692" class="Symbol">→</a> <a id="2694" href="Universes.html#205" class="Postulate">Universe</a>
<a id="2703" href="Algebras.Products.html#2678" class="Function">ov</a> <a id="2706" href="Algebras.Products.html#2706" class="Bound">𝓤</a> <a id="2708" class="Symbol">=</a> <a id="2710" href="Algebras.Products.html#567" class="Bound">𝓞</a> <a id="2712" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2714" href="Algebras.Products.html#569" class="Bound">𝓥</a> <a id="2716" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2718" href="Algebras.Products.html#2706" class="Bound">𝓤</a> <a id="2720" href="Universes.html#181" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra 𝓤 𝑆`, for some universe level `𝓤` and signature `𝑆`. That is, `𝒦 : Pred (Algebra 𝓤 𝑆) 𝓦`, for some type `𝓦`. Later we will formally state and prove that the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary (nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is definitely *not* what we want.  To see why, recall that `Pred (Algebra 𝓤 𝑆) 𝓦`, is just an alias for the function type `Algebra 𝓤 𝑆 → 𝓦 ̇`. We interpret the latter semantically by taking `𝒦 𝑨` (and `𝑨 ∈ 𝒦`) to denote the assertion that `𝒦 𝑨` belongs to `𝒦`. Therefore, by definition, we have

`Π 𝒦 = Π 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝒦 𝑨` &nbsp; &nbsp; `=` &nbsp; &nbsp; `Π 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦`.

Semantically, this is the assertion that *every algebra of type* `Algebra 𝓤 𝑆` *belongs to* `𝒦`, and this bears little resemblance to the product of algebras that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of type `(Algebra 𝓤 𝑆) → 𝓦 ̇`) and the type `Algebra 𝓤 𝑆` seems rather nebulous in that there is no natural indexing class with which to "enumerate" all inhabitants of `Algebra 𝓤 𝑆` belonging to `𝒦`.<sup>[1](Algebras.Product.html#fn1)</sup>

The solution is to essentially take `𝒦` itself to be the indexing type, at least heuristically that is how one can view the type `ℑ` that we now define.<sup>[2](Algebras.Product.html#fn2)</sup>

<pre class="Agda">

<a id="4575" class="Keyword">module</a> <a id="class-products"></a><a id="4582" href="Algebras.Products.html#4582" class="Module">class-products</a> <a id="4597" class="Symbol">{</a><a id="4598" href="Algebras.Products.html#4598" class="Bound">𝓤</a> <a id="4600" class="Symbol">:</a> <a id="4602" href="Universes.html#205" class="Postulate">Universe</a><a id="4610" class="Symbol">}</a> <a id="4612" class="Symbol">(</a><a id="4613" href="Algebras.Products.html#4613" class="Bound">𝒦</a> <a id="4615" class="Symbol">:</a> <a id="4617" href="Relations.Discrete.html#1094" class="Function">Pred</a> <a id="4622" class="Symbol">(</a><a id="4623" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="4631" href="Algebras.Products.html#4598" class="Bound">𝓤</a> <a id="4633" href="Algebras.Products.html#553" class="Bound">𝑆</a><a id="4634" class="Symbol">)(</a><a id="4636" href="Algebras.Products.html#2678" class="Function">ov</a> <a id="4639" href="Algebras.Products.html#4598" class="Bound">𝓤</a><a id="4640" class="Symbol">))</a> <a id="4643" class="Keyword">where</a>

 <a id="class-products.ℑ"></a><a id="4651" href="Algebras.Products.html#4651" class="Function">ℑ</a> <a id="4653" class="Symbol">:</a> <a id="4655" href="Algebras.Products.html#2678" class="Function">ov</a> <a id="4658" href="Algebras.Products.html#4598" class="Bound">𝓤</a> <a id="4660" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4663" href="Algebras.Products.html#4651" class="Function">ℑ</a> <a id="4665" class="Symbol">=</a> <a id="4667" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4669" href="Algebras.Products.html#4669" class="Bound">𝑨</a> <a id="4671" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4673" class="Symbol">(</a><a id="4674" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="4682" href="Algebras.Products.html#4598" class="Bound">𝓤</a> <a id="4684" href="Algebras.Products.html#553" class="Bound">𝑆</a><a id="4685" class="Symbol">)</a> <a id="4687" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4689" class="Symbol">(</a><a id="4690" href="Algebras.Products.html#4669" class="Bound">𝑨</a> <a id="4692" href="Relations.Discrete.html#1962" class="Function Operator">∈</a> <a id="4694" href="Algebras.Products.html#4613" class="Bound">𝒦</a><a id="4695" class="Symbol">)</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="class-products.𝔄"></a><a id="5044" href="Algebras.Products.html#5044" class="Function">𝔄</a> <a id="5046" class="Symbol">:</a> <a id="5048" href="Algebras.Products.html#4651" class="Function">ℑ</a> <a id="5050" class="Symbol">→</a> <a id="5052" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="5060" href="Algebras.Products.html#4598" class="Bound">𝓤</a> <a id="5062" href="Algebras.Products.html#553" class="Bound">𝑆</a>
 <a id="5065" href="Algebras.Products.html#5044" class="Function">𝔄</a> <a id="5067" href="Algebras.Products.html#5067" class="Bound">i</a> <a id="5069" class="Symbol">=</a> <a id="5071" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="5073" href="Algebras.Products.html#5067" class="Bound">i</a> <a id="5075" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="class-products.class-product"></a><a id="5191" href="Algebras.Products.html#5191" class="Function">class-product</a> <a id="5205" class="Symbol">:</a> <a id="5207" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="5215" class="Symbol">(</a><a id="5216" href="Algebras.Products.html#2678" class="Function">ov</a> <a id="5219" href="Algebras.Products.html#4598" class="Bound">𝓤</a><a id="5220" class="Symbol">)</a> <a id="5222" href="Algebras.Products.html#553" class="Bound">𝑆</a>
 <a id="5225" href="Algebras.Products.html#5191" class="Function">class-product</a> <a id="5239" class="Symbol">=</a> <a id="5241" href="Algebras.Products.html#1592" class="Function">⨅</a> <a id="5243" href="Algebras.Products.html#5044" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> If you haven't already seen this before, give it some thought and see if the correct type comes to you organically.</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. Some of our types are denoted with with Gothic ("mathfrak") symbols. To produce them in [agda2-mode][], type `\Mf` followed by a letter. For example, `\MfI` ↝ `ℑ`.</span>

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

<!--

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

 class-product' : Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (𝓧 ⊔ ov 𝓤) 𝑆
 class-product' 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣))) → ∣ i ∣

-->

