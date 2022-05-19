> Main questions:
> ---------------
> 

1.  > > Our initial proof attempt was very similar to what the referee is
    > > suggesting
    > > However, we switched to the approach based on Setoids and requires Abel’s ⊢ _ ▹ _≈
    > > relation because, using the former approach, we could not seem to avoid introducing the
    > > inconsistency described in ¶3 of the introduction
    > 
    > You can find attached an alternative version of your formalisation
    > (based on commit d279db15afd304a0bb4f),
    > where F[X] is defined as the image factorisation (or epi/mono
    > factorisation) of T[X] -> \prod_(A algebra in K, f : X -> U[A]) A.
    > Obviously, F[X] is in S (P K), and therefore I find the proof in
    > section 6.2 easier with this definition.
    > However, it avoids Abel's inductive relation. Do you think it is
    > inconsistent and why? If not, I don't mean to impose my version, but
    > you could at least mentioning this alternative
    > definition and proof, which has the benefit of requiring a reduced
    > number of definitions (as you can see by diffing).
    
    Author Response: 
    
    We considered the simplified version of the proof proposed by the referee, and we agree that it results
    in a clearer argument that requires fewer formal definition; we gladly and gratefully adopt the suggested 
    modifications.  Moreover, we expand the discussion of the inconsistency and make it concrete in §7 (see
    Item 2 below). We are confident that neither the previous version of the proof, nor the new and improved
    proof incorporating the suggestions of the referee, suffers from this defect.


2.  > > Second, an inconsistency could be contrived by taking the
    > > type X, representing an arbitrary collection of variable symbols, to be the two element type.

    > I think that this inconsistency deserves more details (or a link to an agda file where it is derived
    > if you have it). With this short description, it is not clear why the new formalisation doesn't have 
    > the same issue. As far as I know, inconsistencies arise by postulating an inconsistent set of axioms. 
    > Was it the case?
   
    Author Response:
   
    While we did not postulate an inconsistent set of axioms, the defect was that we were not careful to 
    restrict the type X of variable symbols, leaving it arbitrary.  This makes the proof incorrect, since 
    it is not valid for all X, but only those for which there exists surjections onto the algebras in the
    class under consideration.  We have included a more detailed discussion of this oversight in §7.
    Moreover, we now include a link to a formal derivation of the contradiction
    (see https://github.com/ualib/agda-algebras/blob/master/src/Demos/ContraX.lagda).
   


> Other comments:
> ---------------

A. > > The file src/Demos/HSP.lagda mentioned above
   > > includes the full proof

   > It would be safer to link to the exact commit that corresponds to the
   > paper in the final version (rather than master).
   
   XXXX YET TO DO XXXX


B. > > The term algebra T X is the absolutely free (or initial) S-algebra.

   > This wording doesn't fit with what follows because it does not mention X explicitly: T Y is also *the* 
   > absolutely free S-algebra according to your wording, while it doesn't have the property that is 
   > introduced afterwards, which talks about X. I suggest calling it the absolutely free S-algebra *on X* 
   > to follow the usual terminology "free S-algebra on X",

   > Besides, I am not sure that the adjective initial is adequate here. As far as I know, what is called 
   > the initial S-algebra is T 0, where 0 is the empty collection.
   
   AUTHOR RESPONSE:
   
   We removed "initial" and changed it to "The term algebra 𝑻 X is the *absolutely free* 𝑆-algebra over X."

C. > > Let C be the product of all algebras in S K, so C ∈ P (S K).

   > With this sentence, we expect C to be defined as \prod_A\in S K, A, but it turns out this is not
   > the case. Moreover, it could be that C does not "contain" all these algebras. For example, in some 
   > cases, it may not contain the empty algebra, if it exists (e.g., when there is no constant in the 
   > signature), because there is no environment for it. Therefore I suggest removing the word 'all' here, 
   > as it is misleading.

   XXXX YET TO DO XXXX

