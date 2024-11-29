---
layout: default
title : "Base.Relations.Continuous module (The Agda Universal Algebra Library)"
date : "2021-02-28"
author: "[agda-algebras development team][]"
---

### <a id="continuous-relations">Continuous Relations</a>

This is the [Base.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="337" class="Symbol">{-#</a> <a id="341" class="Keyword">OPTIONS</a> <a id="349" class="Pragma">--without-K</a> <a id="361" class="Pragma">--exact-split</a> <a id="375" class="Pragma">--safe</a> <a id="382" class="Symbol">#-}</a>

<a id="387" class="Keyword">module</a> <a id="394" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a> <a id="420" class="Keyword">where</a>

<a id="427" class="Comment">-- Imports from Agda and the Agda Standard Library -------------------------------</a>
<a id="510" class="Keyword">open</a> <a id="515" class="Keyword">import</a> <a id="522" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="538" class="Keyword">using</a> <a id="544" class="Symbol">()</a> <a id="547" class="Keyword">renaming</a> <a id="556" class="Symbol">(</a> <a id="558" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="562" class="Symbol">to</a> <a id="565" class="Primitive">Type</a> <a id="570" class="Symbol">)</a>
<a id="572" class="Keyword">open</a> <a id="577" class="Keyword">import</a> <a id="584" href="Level.html" class="Module">Level</a>           <a id="600" class="Keyword">using</a> <a id="606" class="Symbol">(</a> <a id="608" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a> <a id="612" class="Symbol">;</a> <a id="614" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="618" class="Symbol">;</a> <a id="620" href="Agda.Primitive.html#742" class="Postulate">Level</a>  <a id="627" class="Symbol">)</a>

<a id="630" class="Comment">-- Imports from agda-algebras ----------------------------------------------------</a>
<a id="713" class="Keyword">open</a> <a id="718" class="Keyword">import</a> <a id="725" href="Overture.html" class="Module">Overture</a>        <a id="741" class="Keyword">using</a> <a id="747" class="Symbol">(</a> <a id="749" href="Overture.Basic.html#5930" class="Function">Π</a> <a id="751" class="Symbol">;</a> <a id="753" href="Overture.Basic.html#6010" class="Function">Π-syntax</a> <a id="762" class="Symbol">;</a> <a id="764" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="767" class="Symbol">;</a> <a id="769" href="Overture.Operations.html#1672" class="Function Operator">arity[_]</a> <a id="778" class="Symbol">)</a>

<a id="781" class="Keyword">private</a> <a id="789" class="Keyword">variable</a> <a id="798" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="800" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a> <a id="802" class="Symbol">:</a> <a id="804" href="Agda.Primitive.html#742" class="Postulate">Level</a>

</pre>

#### <a id="motivation">Motivation</a>

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → Type β` (for some universe β).

To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.

It's easier and more general to instead define an arity type `I : Type 𝓥`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → Type β`.

Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we define `Rel` to be the type `(I → A) → Type β` and we call this the type of *continuous relations*.  This generalizes "discrete" relations (i.e., relations of finite arity---unary, binary, etc), defined in the standard library since inhabitants of the continuous relation type can have arbitrary arity.

The relations of type `Rel` not completely general, however, since they are defined over a single type. Said another way, they are *single-sorted* relations. We will remove this limitation when we define the type of *dependent continuous relations* later in the module.

Just as `Rel A β` is the single-sorted special case of the multisorted `REL A B β` in the standard library, so too is our continuous version, `Rel I A β`, the single-sorted special case of a completely general type of relations.

The latter represents relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

Concretely, given an arbitrary family `A : I → Type a` of types, we may have a relation from `A i` to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be enumerable.

We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.

The `REL` type that we define [below](Base.Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.

**Warning**! The type of binary relations in the standard library's `Relation.Binary` module is also called `Rel`.  Therefore, to use both the discrete binary relation from the standard library, and our continuous relation type, we recommend renaming the former when importing with a line like this

`open import Relation.Binary  renaming ( REL to BinREL ; Rel to BinRel )`


#### <a id="continuous-and-dependent-relations">Continuous and dependent relations</a>

Here we define the types `Rel` and `REL`. The first of these represents predicates of arbitrary arity over a single type `A`. As noted above, we call these *continuous relations*.

The definition of `REL` goes even further and exploits the full power of dependent types resulting in a completely general relation type, which we call the type of *dependent relations*.

Here, the tuples of a relation of type `REL I 𝒜 β` inhabit the dependent function type `𝒜 : I → Type a` (where the codomain may depend on the input coordinate `i : I` of the domain).

Heuristically, we can think of an inhabitant of type `REL I 𝒜 β` as a relation from `𝒜 i` to `𝒜 j` to `𝒜 k` to ….

(This is only a rough heuristic since `I` could denote an uncountable collection.)  See the discussion below for a more detailed explanation.

<pre class="Agda">

<a id="4343" class="Keyword">module</a> <a id="4350" href="Base.Relations.Continuous.html#4350" class="Module">_</a> <a id="4352" class="Symbol">{</a><a id="4353" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="4355" class="Symbol">:</a> <a id="4357" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4362" class="Symbol">}</a> <a id="4364" class="Keyword">where</a>
 <a id="4371" href="Base.Relations.Continuous.html#4371" class="Function">ar</a> <a id="4374" class="Symbol">:</a> <a id="4376" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4381" class="Symbol">(</a><a id="4382" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="4386" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a><a id="4387" class="Symbol">)</a>
 <a id="4390" href="Base.Relations.Continuous.html#4371" class="Function">ar</a> <a id="4393" class="Symbol">=</a> <a id="4395" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4400" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a>

<a id="4403" class="Comment">-- Relations of arbitrary arity over a single sort.</a>
 <a id="4456" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="4460" class="Symbol">:</a> <a id="4462" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4467" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="4469" class="Symbol">→</a> <a id="4471" href="Base.Relations.Continuous.html#4371" class="Function">ar</a> <a id="4474" class="Symbol">→</a> <a id="4476" class="Symbol">{</a><a id="4477" href="Base.Relations.Continuous.html#4477" class="Bound">ρ</a> <a id="4479" class="Symbol">:</a> <a id="4481" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4486" class="Symbol">}</a> <a id="4488" class="Symbol">→</a> <a id="4490" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4495" class="Symbol">(</a><a id="4496" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="4498" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4500" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="4502" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4504" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="4508" href="Base.Relations.Continuous.html#4477" class="Bound">ρ</a><a id="4509" class="Symbol">)</a>
 <a id="4512" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="4516" href="Base.Relations.Continuous.html#4516" class="Bound">A</a> <a id="4518" href="Base.Relations.Continuous.html#4518" class="Bound">I</a> <a id="4520" class="Symbol">{</a><a id="4521" href="Base.Relations.Continuous.html#4521" class="Bound">ρ</a><a id="4522" class="Symbol">}</a> <a id="4524" class="Symbol">=</a> <a id="4526" class="Symbol">(</a><a id="4527" href="Base.Relations.Continuous.html#4518" class="Bound">I</a> <a id="4529" class="Symbol">→</a> <a id="4531" href="Base.Relations.Continuous.html#4516" class="Bound">A</a><a id="4532" class="Symbol">)</a> <a id="4534" class="Symbol">→</a> <a id="4536" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4541" href="Base.Relations.Continuous.html#4521" class="Bound">ρ</a>

 <a id="4545" href="Base.Relations.Continuous.html#4545" class="Function">Rel-syntax</a> <a id="4556" class="Symbol">:</a> <a id="4558" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4563" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="4565" class="Symbol">→</a> <a id="4567" href="Base.Relations.Continuous.html#4371" class="Function">ar</a> <a id="4570" class="Symbol">→</a> <a id="4572" class="Symbol">(</a><a id="4573" href="Base.Relations.Continuous.html#4573" class="Bound">ρ</a> <a id="4575" class="Symbol">:</a> <a id="4577" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4582" class="Symbol">)</a> <a id="4584" class="Symbol">→</a> <a id="4586" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4591" class="Symbol">(</a><a id="4592" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="4594" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4596" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="4598" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4600" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="4604" href="Base.Relations.Continuous.html#4573" class="Bound">ρ</a><a id="4605" class="Symbol">)</a>
 <a id="4608" href="Base.Relations.Continuous.html#4545" class="Function">Rel-syntax</a> <a id="4619" href="Base.Relations.Continuous.html#4619" class="Bound">A</a> <a id="4621" href="Base.Relations.Continuous.html#4621" class="Bound">I</a> <a id="4623" href="Base.Relations.Continuous.html#4623" class="Bound">ρ</a> <a id="4625" class="Symbol">=</a> <a id="4627" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="4631" href="Base.Relations.Continuous.html#4619" class="Bound">A</a> <a id="4633" href="Base.Relations.Continuous.html#4621" class="Bound">I</a> <a id="4635" class="Symbol">{</a><a id="4636" href="Base.Relations.Continuous.html#4623" class="Bound">ρ</a><a id="4637" class="Symbol">}</a>

 <a id="4641" class="Keyword">syntax</a> <a id="4648" href="Base.Relations.Continuous.html#4545" class="Function">Rel-syntax</a> <a id="4659" class="Bound">A</a> <a id="4661" class="Bound">I</a> <a id="4663" class="Bound">ρ</a> <a id="4665" class="Symbol">=</a> <a id="4667" class="Function">Rel[</a> <a id="4672" class="Bound">A</a> <a id="4674" class="Function">^</a> <a id="4676" class="Bound">I</a> <a id="4678" class="Function">]</a> <a id="4680" class="Bound">ρ</a>
 <a id="4683" class="Keyword">infix</a> <a id="4689" class="Number">6</a> <a id="4691" href="Base.Relations.Continuous.html#4545" class="Function">Rel-syntax</a>

 <a id="4704" class="Comment">-- The type of arbitrarily multisorted relations of arbitrary arity</a>
 <a id="4773" href="Base.Relations.Continuous.html#4773" class="Function">REL</a> <a id="4777" class="Symbol">:</a> <a id="4779" class="Symbol">(</a><a id="4780" href="Base.Relations.Continuous.html#4780" class="Bound">I</a> <a id="4782" class="Symbol">:</a> <a id="4784" href="Base.Relations.Continuous.html#4371" class="Function">ar</a><a id="4786" class="Symbol">)</a> <a id="4788" class="Symbol">→</a> <a id="4790" class="Symbol">(</a><a id="4791" href="Base.Relations.Continuous.html#4780" class="Bound">I</a> <a id="4793" class="Symbol">→</a> <a id="4795" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4800" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a><a id="4801" class="Symbol">)</a> <a id="4803" class="Symbol">→</a> <a id="4805" class="Symbol">{</a><a id="4806" href="Base.Relations.Continuous.html#4806" class="Bound">ρ</a> <a id="4808" class="Symbol">:</a> <a id="4810" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4815" class="Symbol">}</a> <a id="4817" class="Symbol">→</a> <a id="4819" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4824" class="Symbol">(</a><a id="4825" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="4827" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4829" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="4831" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4833" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="4837" href="Base.Relations.Continuous.html#4806" class="Bound">ρ</a><a id="4838" class="Symbol">)</a>
 <a id="4841" href="Base.Relations.Continuous.html#4773" class="Function">REL</a> <a id="4845" href="Base.Relations.Continuous.html#4845" class="Bound">I</a> <a id="4847" href="Base.Relations.Continuous.html#4847" class="Bound">𝒜</a> <a id="4849" class="Symbol">{</a><a id="4850" href="Base.Relations.Continuous.html#4850" class="Bound">ρ</a><a id="4851" class="Symbol">}</a> <a id="4853" class="Symbol">=</a> <a id="4855" class="Symbol">((</a><a id="4857" href="Base.Relations.Continuous.html#4857" class="Bound">i</a> <a id="4859" class="Symbol">:</a> <a id="4861" href="Base.Relations.Continuous.html#4845" class="Bound">I</a><a id="4862" class="Symbol">)</a> <a id="4864" class="Symbol">→</a> <a id="4866" href="Base.Relations.Continuous.html#4847" class="Bound">𝒜</a> <a id="4868" href="Base.Relations.Continuous.html#4857" class="Bound">i</a><a id="4869" class="Symbol">)</a> <a id="4871" class="Symbol">→</a> <a id="4873" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4878" href="Base.Relations.Continuous.html#4850" class="Bound">ρ</a>

 <a id="4882" href="Base.Relations.Continuous.html#4882" class="Function">REL-syntax</a> <a id="4893" class="Symbol">:</a> <a id="4895" class="Symbol">(</a><a id="4896" href="Base.Relations.Continuous.html#4896" class="Bound">I</a> <a id="4898" class="Symbol">:</a> <a id="4900" href="Base.Relations.Continuous.html#4371" class="Function">ar</a><a id="4902" class="Symbol">)</a> <a id="4904" class="Symbol">→</a> <a id="4906" class="Symbol">(</a><a id="4907" href="Base.Relations.Continuous.html#4896" class="Bound">I</a> <a id="4909" class="Symbol">→</a> <a id="4911" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4916" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a><a id="4917" class="Symbol">)</a> <a id="4919" class="Symbol">→</a> <a id="4921" class="Symbol">{</a><a id="4922" href="Base.Relations.Continuous.html#4922" class="Bound">ρ</a> <a id="4924" class="Symbol">:</a> <a id="4926" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4931" class="Symbol">}</a> <a id="4933" class="Symbol">→</a> <a id="4935" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="4940" class="Symbol">(</a><a id="4941" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="4943" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4945" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="4947" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4949" href="Agda.Primitive.html#931" class="Primitive">suc</a> <a id="4953" href="Base.Relations.Continuous.html#4922" class="Bound">ρ</a><a id="4954" class="Symbol">)</a>
 <a id="4957" href="Base.Relations.Continuous.html#4882" class="Function">REL-syntax</a> <a id="4968" href="Base.Relations.Continuous.html#4968" class="Bound">I</a> <a id="4970" href="Base.Relations.Continuous.html#4970" class="Bound">𝒜</a> <a id="4972" class="Symbol">{</a><a id="4973" href="Base.Relations.Continuous.html#4973" class="Bound">ρ</a><a id="4974" class="Symbol">}</a> <a id="4976" class="Symbol">=</a> <a id="4978" href="Base.Relations.Continuous.html#4773" class="Function">REL</a> <a id="4982" href="Base.Relations.Continuous.html#4968" class="Bound">I</a> <a id="4984" href="Base.Relations.Continuous.html#4970" class="Bound">𝒜</a> <a id="4986" class="Symbol">{</a><a id="4987" href="Base.Relations.Continuous.html#4973" class="Bound">ρ</a><a id="4988" class="Symbol">}</a>

 <a id="4992" class="Keyword">syntax</a> <a id="4999" href="Base.Relations.Continuous.html#4882" class="Function">REL-syntax</a> <a id="5010" class="Bound">I</a> <a id="5012" class="Symbol">(λ</a> <a id="5015" class="Bound">i</a> <a id="5017" class="Symbol">→</a> <a id="5019" class="Bound">𝒜</a><a id="5020" class="Symbol">)</a> <a id="5022" class="Symbol">=</a> <a id="5024" class="Function">REL[</a> <a id="5029" class="Bound">i</a> <a id="5031" class="Function">∈</a> <a id="5033" class="Bound">I</a> <a id="5035" class="Function">]</a> <a id="5037" class="Bound">𝒜</a>
 <a id="5040" class="Keyword">infix</a> <a id="5046" class="Number">6</a> <a id="5048" href="Base.Relations.Continuous.html#4882" class="Function">REL-syntax</a>

</pre>

#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

<pre class="Agda">

 <a id="5179" class="Comment">-- Lift a relation of tuples up to a relation on tuples of tuples.</a>
 <a id="5247" href="Base.Relations.Continuous.html#5247" class="Function">eval-Rel</a> <a id="5256" class="Symbol">:</a> <a id="5258" class="Symbol">{</a><a id="5259" href="Base.Relations.Continuous.html#5259" class="Bound">I</a> <a id="5261" class="Symbol">:</a> <a id="5263" href="Base.Relations.Continuous.html#4371" class="Function">ar</a><a id="5265" class="Symbol">}{</a><a id="5267" href="Base.Relations.Continuous.html#5267" class="Bound">A</a> <a id="5269" class="Symbol">:</a> <a id="5271" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="5276" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a><a id="5277" class="Symbol">}</a> <a id="5279" class="Symbol">→</a> <a id="5281" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="5285" href="Base.Relations.Continuous.html#5267" class="Bound">A</a> <a id="5287" href="Base.Relations.Continuous.html#5259" class="Bound">I</a><a id="5288" class="Symbol">{</a><a id="5289" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a><a id="5290" class="Symbol">}</a> <a id="5292" class="Symbol">→</a> <a id="5294" class="Symbol">(</a><a id="5295" href="Base.Relations.Continuous.html#5295" class="Bound">J</a> <a id="5297" class="Symbol">:</a> <a id="5299" href="Base.Relations.Continuous.html#4371" class="Function">ar</a><a id="5301" class="Symbol">)</a> <a id="5303" class="Symbol">→</a> <a id="5305" class="Symbol">(</a><a id="5306" href="Base.Relations.Continuous.html#5259" class="Bound">I</a> <a id="5308" class="Symbol">→</a> <a id="5310" href="Base.Relations.Continuous.html#5295" class="Bound">J</a> <a id="5312" class="Symbol">→</a> <a id="5314" href="Base.Relations.Continuous.html#5267" class="Bound">A</a><a id="5315" class="Symbol">)</a> <a id="5317" class="Symbol">→</a> <a id="5319" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="5324" class="Symbol">(</a><a id="5325" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="5327" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="5329" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a><a id="5330" class="Symbol">)</a>
 <a id="5333" href="Base.Relations.Continuous.html#5247" class="Function">eval-Rel</a> <a id="5342" href="Base.Relations.Continuous.html#5342" class="Bound">R</a> <a id="5344" href="Base.Relations.Continuous.html#5344" class="Bound">J</a> <a id="5346" href="Base.Relations.Continuous.html#5346" class="Bound">t</a> <a id="5348" class="Symbol">=</a> <a id="5350" class="Symbol">∀</a> <a id="5352" class="Symbol">(</a><a id="5353" href="Base.Relations.Continuous.html#5353" class="Bound">j</a> <a id="5355" class="Symbol">:</a> <a id="5357" href="Base.Relations.Continuous.html#5344" class="Bound">J</a><a id="5358" class="Symbol">)</a> <a id="5360" class="Symbol">→</a> <a id="5362" href="Base.Relations.Continuous.html#5342" class="Bound">R</a> <a id="5364" class="Symbol">λ</a> <a id="5366" href="Base.Relations.Continuous.html#5366" class="Bound">i</a> <a id="5368" class="Symbol">→</a> <a id="5370" href="Base.Relations.Continuous.html#5346" class="Bound">t</a> <a id="5372" href="Base.Relations.Continuous.html#5366" class="Bound">i</a> <a id="5374" href="Base.Relations.Continuous.html#5353" class="Bound">j</a>

</pre>

A relation `R` is compatible with an operation `f` if for every tuple `t` of tuples
belonging to `R`, the tuple whose elements are the result of applying `f` to
sections of `t` also belongs to `R`.

<pre class="Agda">

 <a id="5603" href="Base.Relations.Continuous.html#5603" class="Function">compatible-Rel</a> <a id="5618" class="Symbol">:</a> <a id="5620" class="Symbol">{</a><a id="5621" href="Base.Relations.Continuous.html#5621" class="Bound">I</a> <a id="5623" href="Base.Relations.Continuous.html#5623" class="Bound">J</a> <a id="5625" class="Symbol">:</a> <a id="5627" href="Base.Relations.Continuous.html#4371" class="Function">ar</a><a id="5629" class="Symbol">}{</a><a id="5631" href="Base.Relations.Continuous.html#5631" class="Bound">A</a> <a id="5633" class="Symbol">:</a> <a id="5635" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="5640" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a><a id="5641" class="Symbol">}</a> <a id="5643" class="Symbol">→</a> <a id="5645" href="Overture.Operations.html#1235" class="Function">Op</a><a id="5647" class="Symbol">(</a><a id="5648" href="Base.Relations.Continuous.html#5631" class="Bound">A</a><a id="5649" class="Symbol">)</a> <a id="5651" href="Base.Relations.Continuous.html#5623" class="Bound">J</a> <a id="5653" class="Symbol">→</a> <a id="5655" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="5659" href="Base.Relations.Continuous.html#5631" class="Bound">A</a> <a id="5661" href="Base.Relations.Continuous.html#5621" class="Bound">I</a><a id="5662" class="Symbol">{</a><a id="5663" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a><a id="5664" class="Symbol">}</a> <a id="5666" class="Symbol">→</a> <a id="5668" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="5673" class="Symbol">(</a><a id="5674" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="5676" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="5678" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="5680" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="5682" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a><a id="5683" class="Symbol">)</a>
 <a id="5686" href="Base.Relations.Continuous.html#5603" class="Function">compatible-Rel</a> <a id="5701" href="Base.Relations.Continuous.html#5701" class="Bound">f</a> <a id="5703" href="Base.Relations.Continuous.html#5703" class="Bound">R</a>  <a id="5706" class="Symbol">=</a> <a id="5708" class="Symbol">∀</a> <a id="5710" href="Base.Relations.Continuous.html#5710" class="Bound">t</a> <a id="5712" class="Symbol">→</a> <a id="5714" href="Base.Relations.Continuous.html#5247" class="Function">eval-Rel</a> <a id="5723" href="Base.Relations.Continuous.html#5703" class="Bound">R</a> <a id="5725" href="Overture.Operations.html#1672" class="Function Operator">arity[</a> <a id="5732" href="Base.Relations.Continuous.html#5701" class="Bound">f</a> <a id="5734" href="Overture.Operations.html#1672" class="Function Operator">]</a> <a id="5736" href="Base.Relations.Continuous.html#5710" class="Bound">t</a> <a id="5738" class="Symbol">→</a> <a id="5740" href="Base.Relations.Continuous.html#5703" class="Bound">R</a> <a id="5742" class="Symbol">λ</a> <a id="5744" href="Base.Relations.Continuous.html#5744" class="Bound">i</a> <a id="5746" class="Symbol">→</a> <a id="5748" href="Base.Relations.Continuous.html#5701" class="Bound">f</a> <a id="5750" class="Symbol">(</a><a id="5751" href="Base.Relations.Continuous.html#5710" class="Bound">t</a> <a id="5753" href="Base.Relations.Continuous.html#5744" class="Bound">i</a><a id="5754" class="Symbol">)</a>
 <a id="5757" class="Comment">-- (inferred type of t is I → J → A)</a>

</pre>


#### <a id="compatibility-of-operations-with-dependent-relations">Compatibility of operations with dependent relations</a>

<pre class="Agda">

 <a id="5947" href="Base.Relations.Continuous.html#5947" class="Function">eval-REL</a> <a id="5956" class="Symbol">:</a>  <a id="5959" class="Symbol">{</a><a id="5960" href="Base.Relations.Continuous.html#5960" class="Bound">I</a> <a id="5962" href="Base.Relations.Continuous.html#5962" class="Bound">J</a> <a id="5964" class="Symbol">:</a> <a id="5966" href="Base.Relations.Continuous.html#4371" class="Function">ar</a><a id="5968" class="Symbol">}{</a><a id="5970" href="Base.Relations.Continuous.html#5970" class="Bound">𝒜</a> <a id="5972" class="Symbol">:</a> <a id="5974" href="Base.Relations.Continuous.html#5960" class="Bound">I</a> <a id="5976" class="Symbol">→</a> <a id="5978" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="5983" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a><a id="5984" class="Symbol">}</a>
  <a id="5988" class="Symbol">→</a>          <a id="5999" href="Base.Relations.Continuous.html#4773" class="Function">REL</a> <a id="6003" href="Base.Relations.Continuous.html#5960" class="Bound">I</a> <a id="6005" href="Base.Relations.Continuous.html#5970" class="Bound">𝒜</a> <a id="6007" class="Symbol">{</a><a id="6008" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a><a id="6009" class="Symbol">}</a>          <a id="6020" class="Comment">-- the relation type: subsets of Π[ i ∈ I ] 𝒜 i</a>
                                  <a id="6102" class="Comment">-- (where Π[ i ∈ I ] 𝒜 i is a type of dependent functions or &quot;tuples&quot;)</a>
  <a id="6175" class="Symbol">→</a>          <a id="6186" class="Symbol">((</a><a id="6188" href="Base.Relations.Continuous.html#6188" class="Bound">i</a> <a id="6190" class="Symbol">:</a> <a id="6192" href="Base.Relations.Continuous.html#5960" class="Bound">I</a><a id="6193" class="Symbol">)</a> <a id="6195" class="Symbol">→</a> <a id="6197" href="Base.Relations.Continuous.html#5962" class="Bound">J</a> <a id="6199" class="Symbol">→</a> <a id="6201" href="Base.Relations.Continuous.html#5970" class="Bound">𝒜</a> <a id="6203" href="Base.Relations.Continuous.html#6188" class="Bound">i</a><a id="6204" class="Symbol">)</a>  <a id="6207" class="Comment">-- an I-tuple of (𝒥 i)-tuples</a>
  <a id="6239" class="Symbol">→</a>          <a id="6250" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="6255" class="Symbol">(</a><a id="6256" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="6258" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="6260" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a><a id="6261" class="Symbol">)</a>

 <a id="6265" href="Base.Relations.Continuous.html#5947" class="Function">eval-REL</a><a id="6273" class="Symbol">{</a><a id="6274" class="Argument">I</a> <a id="6276" class="Symbol">=</a> <a id="6278" href="Base.Relations.Continuous.html#6278" class="Bound">I</a><a id="6279" class="Symbol">}{</a><a id="6281" href="Base.Relations.Continuous.html#6281" class="Bound">J</a><a id="6282" class="Symbol">}{</a><a id="6284" href="Base.Relations.Continuous.html#6284" class="Bound">𝒜</a><a id="6285" class="Symbol">}</a> <a id="6287" href="Base.Relations.Continuous.html#6287" class="Bound">R</a> <a id="6289" href="Base.Relations.Continuous.html#6289" class="Bound">t</a> <a id="6291" class="Symbol">=</a> <a id="6293" class="Symbol">∀</a> <a id="6295" href="Base.Relations.Continuous.html#6295" class="Bound">j</a> <a id="6297" class="Symbol">→</a> <a id="6299" href="Base.Relations.Continuous.html#6287" class="Bound">R</a> <a id="6301" class="Symbol">λ</a> <a id="6303" href="Base.Relations.Continuous.html#6303" class="Bound">i</a> <a id="6305" class="Symbol">→</a> <a id="6307" class="Symbol">(</a><a id="6308" href="Base.Relations.Continuous.html#6289" class="Bound">t</a> <a id="6310" href="Base.Relations.Continuous.html#6303" class="Bound">i</a><a id="6311" class="Symbol">)</a> <a id="6313" href="Base.Relations.Continuous.html#6295" class="Bound">j</a>

 <a id="6317" href="Base.Relations.Continuous.html#6317" class="Function">compatible-REL</a> <a id="6332" class="Symbol">:</a>  <a id="6335" class="Symbol">{</a><a id="6336" href="Base.Relations.Continuous.html#6336" class="Bound">I</a> <a id="6338" href="Base.Relations.Continuous.html#6338" class="Bound">J</a> <a id="6340" class="Symbol">:</a> <a id="6342" href="Base.Relations.Continuous.html#4371" class="Function">ar</a><a id="6344" class="Symbol">}{</a><a id="6346" href="Base.Relations.Continuous.html#6346" class="Bound">𝒜</a> <a id="6348" class="Symbol">:</a> <a id="6350" href="Base.Relations.Continuous.html#6336" class="Bound">I</a> <a id="6352" class="Symbol">→</a> <a id="6354" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="6359" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a><a id="6360" class="Symbol">}</a>
  <a id="6364" class="Symbol">→</a>                <a id="6381" class="Symbol">(∀</a> <a id="6384" href="Base.Relations.Continuous.html#6384" class="Bound">i</a> <a id="6386" class="Symbol">→</a> <a id="6388" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="6391" class="Symbol">(</a><a id="6392" href="Base.Relations.Continuous.html#6346" class="Bound">𝒜</a> <a id="6394" href="Base.Relations.Continuous.html#6384" class="Bound">i</a><a id="6395" class="Symbol">)</a> <a id="6397" href="Base.Relations.Continuous.html#6338" class="Bound">J</a><a id="6398" class="Symbol">)</a>  <a id="6401" class="Comment">-- for each i : I, an operation of type  Op(𝒜 i){J} = (J → 𝒜 i) → 𝒜 i</a>
  <a id="6473" class="Symbol">→</a>                <a id="6490" href="Base.Relations.Continuous.html#4773" class="Function">REL</a> <a id="6494" href="Base.Relations.Continuous.html#6336" class="Bound">I</a> <a id="6496" href="Base.Relations.Continuous.html#6346" class="Bound">𝒜</a> <a id="6498" class="Symbol">{</a><a id="6499" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a><a id="6500" class="Symbol">}</a>         <a id="6510" class="Comment">-- a subset of Π[ i ∈ I ] 𝒜 i</a>
                                       <a id="6579" class="Comment">-- (where Π[ i ∈ I ] 𝒜 i is a type of dependent functions or &quot;tuples&quot;)</a>
  <a id="6652" class="Symbol">→</a>                <a id="6669" href="Base.Relations.Continuous.html#565" class="Primitive">Type</a> <a id="6674" class="Symbol">(</a><a id="6675" href="Base.Relations.Continuous.html#4353" class="Bound">𝓥</a> <a id="6677" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="6679" href="Base.Relations.Continuous.html#798" class="Generalizable">a</a> <a id="6681" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="6683" href="Base.Relations.Continuous.html#800" class="Generalizable">ρ</a><a id="6684" class="Symbol">)</a>
 <a id="6687" href="Base.Relations.Continuous.html#6317" class="Function">compatible-REL</a> <a id="6702" class="Symbol">{</a><a id="6703" class="Argument">I</a> <a id="6705" class="Symbol">=</a> <a id="6707" href="Base.Relations.Continuous.html#6707" class="Bound">I</a><a id="6708" class="Symbol">}{</a><a id="6710" href="Base.Relations.Continuous.html#6710" class="Bound">J</a><a id="6711" class="Symbol">}{</a><a id="6713" href="Base.Relations.Continuous.html#6713" class="Bound">𝒜</a><a id="6714" class="Symbol">}</a> <a id="6716" href="Base.Relations.Continuous.html#6716" class="Bound">𝑓</a> <a id="6718" href="Base.Relations.Continuous.html#6718" class="Bound">R</a>  <a id="6721" class="Symbol">=</a> <a id="6723" href="Overture.Basic.html#6010" class="Function">Π[</a> <a id="6726" href="Base.Relations.Continuous.html#6726" class="Bound">t</a> <a id="6728" href="Overture.Basic.html#6010" class="Function">∈</a> <a id="6730" class="Symbol">((</a><a id="6732" href="Base.Relations.Continuous.html#6732" class="Bound">i</a> <a id="6734" class="Symbol">:</a> <a id="6736" href="Base.Relations.Continuous.html#6707" class="Bound">I</a><a id="6737" class="Symbol">)</a> <a id="6739" class="Symbol">→</a> <a id="6741" href="Base.Relations.Continuous.html#6710" class="Bound">J</a> <a id="6743" class="Symbol">→</a> <a id="6745" href="Base.Relations.Continuous.html#6713" class="Bound">𝒜</a> <a id="6747" href="Base.Relations.Continuous.html#6732" class="Bound">i</a><a id="6748" class="Symbol">)</a> <a id="6750" href="Overture.Basic.html#6010" class="Function">]</a> <a id="6752" href="Base.Relations.Continuous.html#5947" class="Function">eval-REL</a> <a id="6761" href="Base.Relations.Continuous.html#6718" class="Bound">R</a> <a id="6763" href="Base.Relations.Continuous.html#6726" class="Bound">t</a>

</pre>

The definition `eval-REL` denotes an *evaluation* function which lifts an `I`-ary relation to an `(I → J)`-ary relation.

The lifted relation will relate an `I`-tuple of `J`-tuples when the `I`-slices (or rows) of the `J`-tuples belong
to the original relation.

The second definition, compatible-REL,  denotes compatibility of an operation with a continuous relation.


#### <a id="detailed-explanation-of-the-dependent-relation-type">Detailed explanation of the dependent relation type</a>

The last two definitions above may be hard to comprehend at first, so perhaps a more detailed explanation of the semantics of these deifnitions would help.

First, one should internalize the fact that `𝒶 : I → J → A` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`.

Next, recall that a continuous relation `R` denotes a certain collection of `I`-tuples (if `x : I → A`, then `R x` asserts that `x` belongs to `R`).

For such `R`, the type `eval-REL R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the tuples `𝒶 : I → J → A` for which `eval-REL R 𝒶` holds.

For simplicity, pretend for a moment that `J` is a finite set, say, `{1, 2, ..., J}`, so that we can write down a couple of the `J`-tuples as columns.

For example, here are the i-th and k-th columns (for some `i k : I`).

```
𝒶 i 1      𝒶 k 1
𝒶 i 2      𝒶 k 2  <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝒶 i J      𝒶 k J
```

Now `eval-REL R 𝒶` is defined by `∀ j → R (λ i → 𝒶 i j)` which asserts that each row of the `I` columns shown above belongs to the original relation `R`.

Finally, `compatible-REL` takes

*  an `I`-tuple (`λ i → (𝑓 i)`) of `J`-ary operations, where for each i the type of `𝑓 i` is `(J → 𝒜 i) → 𝒜 i`, and
*  an `I`-tuple (`𝒶 : I → J → A`) of `J`-tuples

and determines whether the `I`-tuple `λ i → (𝑓 i) (𝑎 i)` belongs to `R`.

--------------------------------------

<span style="float:left;">[← Base.Relations.Discrete](Base.Relations.Discrete.html)</span>
<span style="float:right;">[Base.Relations.Properties →](Base.Relations.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
