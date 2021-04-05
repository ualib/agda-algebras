---
layout: default
title : Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="product-algebras">Product Algebras</a>

This is the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

Notice that we begin this module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

**NOTATION**.  From now on, the remaining modules of the [UALib][] will assume universes 𝓞 and 𝓥, and a fixed signature type `𝑆 : Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="567" class="Symbol">{-#</a> <a id="571" class="Keyword">OPTIONS</a> <a id="579" class="Pragma">--without-K</a> <a id="591" class="Pragma">--exact-split</a> <a id="605" class="Pragma">--safe</a> <a id="612" class="Symbol">#-}</a>

<a id="617" class="Keyword">open</a> <a id="622" class="Keyword">import</a> <a id="629" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="649" class="Keyword">using</a> <a id="655" class="Symbol">(</a><a id="656" href="Algebras.Signatures.html#1238" class="Function">Signature</a><a id="665" class="Symbol">;</a> <a id="667" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a><a id="668" class="Symbol">;</a> <a id="670" href="Universes.html#262" class="Generalizable">𝓥</a><a id="671" class="Symbol">)</a>

<a id="674" class="Keyword">module</a> <a id="681" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="699" class="Symbol">{</a><a id="700" href="Algebras.Products.html#700" class="Bound">𝑆</a> <a id="702" class="Symbol">:</a> <a id="704" href="Algebras.Signatures.html#1238" class="Function">Signature</a> <a id="714" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="716" href="Universes.html#262" class="Generalizable">𝓥</a><a id="717" class="Symbol">}</a> <a id="719" class="Keyword">where</a>

<a id="726" class="Keyword">open</a> <a id="731" class="Keyword">import</a> <a id="738" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="756" class="Keyword">hiding</a> <a id="763" class="Symbol">(</a><a id="764" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a><a id="765" class="Symbol">;</a> <a id="767" href="Universes.html#262" class="Generalizable">𝓥</a><a id="768" class="Symbol">)</a> <a id="770" class="Keyword">public</a>

</pre>

We must import the `Signature` type from the [Algebras.Signatures][] module first, before the `module` line, so that we may use it to declare the signature `𝑆` as a parameter of the [Algebras.Products][] module.

In the [UALib][] a *product of* 𝑆-*algebras* is represented by the following type.

<pre class="Agda">

<a id="1101" class="Keyword">module</a> <a id="1108" href="Algebras.Products.html#1108" class="Module">_</a> <a id="1110" class="Symbol">{</a><a id="1111" href="Algebras.Products.html#1111" class="Bound">𝓤</a> <a id="1113" href="Algebras.Products.html#1113" class="Bound">𝓘</a> <a id="1115" class="Symbol">:</a> <a id="1117" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1125" class="Symbol">}{</a><a id="1127" href="Algebras.Products.html#1127" class="Bound">I</a> <a id="1129" class="Symbol">:</a> <a id="1131" href="Algebras.Products.html#1113" class="Bound">𝓘</a> <a id="1133" href="Universes.html#403" class="Function Operator">̇</a> <a id="1135" class="Symbol">}</a> <a id="1137" class="Keyword">where</a>

 <a id="1145" href="Algebras.Products.html#1145" class="Function">⨅</a> <a id="1147" class="Symbol">:</a> <a id="1149" class="Symbol">(</a><a id="1150" href="Algebras.Products.html#1150" class="Bound">𝒜</a> <a id="1152" class="Symbol">:</a> <a id="1154" href="Algebras.Products.html#1127" class="Bound">I</a> <a id="1156" class="Symbol">→</a> <a id="1158" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="1166" href="Algebras.Products.html#1111" class="Bound">𝓤</a> <a id="1168" href="Algebras.Products.html#700" class="Bound">𝑆</a> <a id="1170" class="Symbol">)</a> <a id="1172" class="Symbol">→</a> <a id="1174" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="1182" class="Symbol">(</a><a id="1183" href="Algebras.Products.html#1113" class="Bound">𝓘</a> <a id="1185" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1187" href="Algebras.Products.html#1111" class="Bound">𝓤</a><a id="1188" class="Symbol">)</a> <a id="1190" href="Algebras.Products.html#700" class="Bound">𝑆</a>

 <a id="1194" href="Algebras.Products.html#1145" class="Function">⨅</a> <a id="1196" href="Algebras.Products.html#1196" class="Bound">𝒜</a> <a id="1198" class="Symbol">=</a> <a id="1200" class="Symbol">(</a><a id="1201" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="1203" href="Algebras.Products.html#1203" class="Bound">i</a> <a id="1205" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="1207" href="Algebras.Products.html#1127" class="Bound">I</a> <a id="1209" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="1211" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="1213" href="Algebras.Products.html#1196" class="Bound">𝒜</a> <a id="1215" href="Algebras.Products.html#1203" class="Bound">i</a> <a id="1217" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a><a id="1218" class="Symbol">)</a> <a id="1220" href="Overture.Preliminaries.html#13136" class="InductiveConstructor Operator">,</a>            <a id="1233" class="Comment">-- domain of the product algebra</a>
       <a id="1273" class="Symbol">λ</a> <a id="1275" href="Algebras.Products.html#1275" class="Bound">𝑓</a> <a id="1277" href="Algebras.Products.html#1277" class="Bound">𝑎</a> <a id="1279" href="Algebras.Products.html#1279" class="Bound">i</a> <a id="1281" class="Symbol">→</a> <a id="1283" class="Symbol">(</a><a id="1284" href="Algebras.Products.html#1275" class="Bound">𝑓</a> <a id="1286" href="Algebras.Algebras.html#3080" class="Function Operator">̂</a> <a id="1288" href="Algebras.Products.html#1196" class="Bound">𝒜</a> <a id="1290" href="Algebras.Products.html#1279" class="Bound">i</a><a id="1291" class="Symbol">)</a> <a id="1293" class="Symbol">λ</a> <a id="1295" href="Algebras.Products.html#1295" class="Bound">x</a> <a id="1297" class="Symbol">→</a> <a id="1299" href="Algebras.Products.html#1277" class="Bound">𝑎</a> <a id="1301" href="Algebras.Products.html#1295" class="Bound">x</a> <a id="1303" href="Algebras.Products.html#1279" class="Bound">i</a>   <a id="1307" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UALib][] whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

 <a id="1782" class="Keyword">open</a> <a id="1787" href="Algebras.Algebras.html#2059" class="Module">algebra</a>

 <a id="1797" href="Algebras.Products.html#1797" class="Function">⨅&#39;</a> <a id="1800" class="Symbol">:</a> <a id="1802" class="Symbol">(</a><a id="1803" href="Algebras.Products.html#1803" class="Bound">𝒜</a> <a id="1805" class="Symbol">:</a> <a id="1807" href="Algebras.Products.html#1127" class="Bound">I</a> <a id="1809" class="Symbol">→</a> <a id="1811" href="Algebras.Algebras.html#2059" class="Record">algebra</a> <a id="1819" href="Algebras.Products.html#1111" class="Bound">𝓤</a> <a id="1821" href="Algebras.Products.html#700" class="Bound">𝑆</a><a id="1822" class="Symbol">)</a> <a id="1824" class="Symbol">→</a> <a id="1826" href="Algebras.Algebras.html#2059" class="Record">algebra</a> <a id="1834" class="Symbol">(</a><a id="1835" href="Algebras.Products.html#1113" class="Bound">𝓘</a> <a id="1837" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1839" href="Algebras.Products.html#1111" class="Bound">𝓤</a><a id="1840" class="Symbol">)</a> <a id="1842" href="Algebras.Products.html#700" class="Bound">𝑆</a>

 <a id="1846" href="Algebras.Products.html#1797" class="Function">⨅&#39;</a> <a id="1849" href="Algebras.Products.html#1849" class="Bound">𝒜</a> <a id="1851" class="Symbol">=</a> <a id="1853" class="Keyword">record</a> <a id="1860" class="Symbol">{</a> <a id="1862" href="Algebras.Algebras.html#2154" class="Field">univ</a> <a id="1867" class="Symbol">=</a> <a id="1869" class="Symbol">∀</a> <a id="1871" href="Algebras.Products.html#1871" class="Bound">i</a> <a id="1873" class="Symbol">→</a> <a id="1875" href="Algebras.Algebras.html#2154" class="Field">univ</a> <a id="1880" class="Symbol">(</a><a id="1881" href="Algebras.Products.html#1849" class="Bound">𝒜</a> <a id="1883" href="Algebras.Products.html#1871" class="Bound">i</a><a id="1884" class="Symbol">)</a> <a id="1886" class="Symbol">;</a>                 <a id="1904" class="Comment">-- domain</a>
                 <a id="1931" href="Algebras.Algebras.html#2167" class="Field">op</a> <a id="1934" class="Symbol">=</a> <a id="1936" class="Symbol">λ</a> <a id="1938" href="Algebras.Products.html#1938" class="Bound">𝑓</a> <a id="1940" href="Algebras.Products.html#1940" class="Bound">𝑎</a> <a id="1942" href="Algebras.Products.html#1942" class="Bound">i</a> <a id="1944" class="Symbol">→</a> <a id="1946" class="Symbol">(</a><a id="1947" href="Algebras.Algebras.html#2167" class="Field">op</a> <a id="1950" class="Symbol">(</a><a id="1951" href="Algebras.Products.html#1849" class="Bound">𝒜</a> <a id="1953" href="Algebras.Products.html#1942" class="Bound">i</a><a id="1954" class="Symbol">))</a> <a id="1957" href="Algebras.Products.html#1938" class="Bound">𝑓</a> <a id="1959" class="Symbol">λ</a> <a id="1961" href="Algebras.Products.html#1961" class="Bound">x</a> <a id="1963" class="Symbol">→</a> <a id="1965" href="Algebras.Products.html#1940" class="Bound">𝑎</a> <a id="1967" href="Algebras.Products.html#1961" class="Bound">x</a> <a id="1969" href="Algebras.Products.html#1942" class="Bound">i</a> <a id="1971" class="Symbol">}</a> <a id="1973" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that we define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2231" href="Algebras.Products.html#2231" class="Function">ov</a> <a id="2234" class="Symbol">:</a> <a id="2236" href="Agda.Primitive.html#423" class="Postulate">Universe</a> <a id="2245" class="Symbol">→</a> <a id="2247" href="Agda.Primitive.html#423" class="Postulate">Universe</a>
<a id="2256" href="Algebras.Products.html#2231" class="Function">ov</a> <a id="2259" href="Algebras.Products.html#2259" class="Bound">𝓤</a> <a id="2261" class="Symbol">=</a> <a id="2263" href="Algebras.Products.html#714" class="Bound">𝓞</a> <a id="2265" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2267" href="Algebras.Products.html#716" class="Bound">𝓥</a> <a id="2269" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2271" href="Algebras.Products.html#2259" class="Bound">𝓤</a> <a id="2273" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra 𝓤 𝑆`, for some universe level `𝓤` and signature `𝑆`. That is, `𝒦 : Pred (Algebra 𝓤 𝑆) 𝓦`, for some type `𝓦`. Later we will formally state and prove that the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary (nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is definitely *not* what we want.  To see why, recall that `Pred (Algebra 𝓤 𝑆) 𝓦`, is just an alias for the function type `Algebra 𝓤 𝑆 → 𝓦 ̇`. We interpret the latter semantically by taking `𝒦 𝑨` (and `𝑨 ∈ 𝒦`) to denote the assertion that `𝒦 𝑨` belongs to `𝒦`. Therefore, by definition, we have

`Π 𝒦 = Π 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝒦 𝑨` &nbsp; &nbsp; `=` &nbsp; &nbsp; `Π 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦`.

Semantically, this is the assertion that *every algebra of type* `Algebra 𝓤 𝑆` *belongs to* `𝒦`, and this bears little resemblance to the product of algebras that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of type `(Algebra 𝓤 𝑆) → 𝓦 ̇`) and the type `Algebra 𝓤 𝑆` seems rather nebulous in that there is no natural indexing class with which to "enumerate" all inhabitants of `Algebra 𝓤 𝑆` belonging to `𝒦`.<sup>[1](Algebras.Product.html#fn1)</sup>

The solution is to essentially take `𝒦` itself to be the indexing type, at least heuristically that is how one can view the type `ℑ` that we now define.<sup>[2](Algebras.Product.html#fn2)</sup>

<pre class="Agda">

<a id="4128" class="Keyword">module</a> <a id="class-products"></a><a id="4135" href="Algebras.Products.html#4135" class="Module">class-products</a> <a id="4150" class="Symbol">{</a><a id="4151" href="Algebras.Products.html#4151" class="Bound">𝓤</a> <a id="4153" class="Symbol">:</a> <a id="4155" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4163" class="Symbol">}</a> <a id="4165" class="Symbol">(</a><a id="4166" href="Algebras.Products.html#4166" class="Bound">𝒦</a> <a id="4168" class="Symbol">:</a> <a id="4170" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="4175" class="Symbol">(</a><a id="4176" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="4184" href="Algebras.Products.html#4151" class="Bound">𝓤</a> <a id="4186" href="Algebras.Products.html#700" class="Bound">𝑆</a><a id="4187" class="Symbol">)(</a><a id="4189" href="Algebras.Products.html#2231" class="Function">ov</a> <a id="4192" href="Algebras.Products.html#4151" class="Bound">𝓤</a><a id="4193" class="Symbol">))</a> <a id="4196" class="Keyword">where</a>

 <a id="class-products.ℑ"></a><a id="4204" href="Algebras.Products.html#4204" class="Function">ℑ</a> <a id="4206" class="Symbol">:</a> <a id="4208" href="Algebras.Products.html#2231" class="Function">ov</a> <a id="4211" href="Algebras.Products.html#4151" class="Bound">𝓤</a> <a id="4213" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4216" href="Algebras.Products.html#4204" class="Function">ℑ</a> <a id="4218" class="Symbol">=</a> <a id="4220" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4222" href="Algebras.Products.html#4222" class="Bound">𝑨</a> <a id="4224" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4226" class="Symbol">(</a><a id="4227" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="4235" href="Algebras.Products.html#4151" class="Bound">𝓤</a> <a id="4237" href="Algebras.Products.html#700" class="Bound">𝑆</a><a id="4238" class="Symbol">)</a> <a id="4240" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4242" class="Symbol">(</a><a id="4243" href="Algebras.Products.html#4222" class="Bound">𝑨</a> <a id="4245" href="Relations.Discrete.html#2402" class="Function Operator">∈</a> <a id="4247" href="Algebras.Products.html#4166" class="Bound">𝒦</a><a id="4248" class="Symbol">)</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="class-products.𝔄"></a><a id="4597" href="Algebras.Products.html#4597" class="Function">𝔄</a> <a id="4599" class="Symbol">:</a> <a id="4601" href="Algebras.Products.html#4204" class="Function">ℑ</a> <a id="4603" class="Symbol">→</a> <a id="4605" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="4613" href="Algebras.Products.html#4151" class="Bound">𝓤</a> <a id="4615" href="Algebras.Products.html#700" class="Bound">𝑆</a>
 <a id="4618" href="Algebras.Products.html#4597" class="Function">𝔄</a> <a id="4620" class="Symbol">=</a> <a id="4622" class="Symbol">λ</a> <a id="4624" class="Symbol">(</a><a id="4625" href="Algebras.Products.html#4625" class="Bound">i</a> <a id="4627" class="Symbol">:</a> <a id="4629" href="Algebras.Products.html#4204" class="Function">ℑ</a><a id="4630" class="Symbol">)</a> <a id="4632" class="Symbol">→</a> <a id="4634" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a> <a id="4636" href="Algebras.Products.html#4625" class="Bound">i</a> <a id="4638" href="Overture.Preliminaries.html#13832" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="class-products.class-product"></a><a id="4754" href="Algebras.Products.html#4754" class="Function">class-product</a> <a id="4768" class="Symbol">:</a> <a id="4770" href="Algebras.Algebras.html#844" class="Function">Algebra</a> <a id="4778" class="Symbol">(</a><a id="4779" href="Algebras.Products.html#2231" class="Function">ov</a> <a id="4782" href="Algebras.Products.html#4151" class="Bound">𝓤</a><a id="4783" class="Symbol">)</a> <a id="4785" href="Algebras.Products.html#700" class="Bound">𝑆</a>
 <a id="4788" href="Algebras.Products.html#4754" class="Function">class-product</a> <a id="4802" class="Symbol">=</a> <a id="4804" href="Algebras.Products.html#1145" class="Function">⨅</a> <a id="4806" href="Algebras.Products.html#4597" class="Function">𝔄</a>

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

