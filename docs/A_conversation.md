# Appendix A: Conversation

This appendix mainly serves as a snapshot of conversation between me and Randall Holmes. Starting from below, **M** stands for me and **R** stands for Randall Holmes.

**M**
> How should I know the difference, practically, between propositional functions and propositions? By which there are several aspects:
> - (p.93) All assertions in PM are on propositional functions, and `*1.1` is used on a few exceptions. What will be the exceptions?
> - After chapter 12, PM is starting to introduce the (order's) hierarchy of propositions and propositional functions. Since `*1.1` is generally unused, can I consider the hierarchy of propositions(not functions) is also generally useless? How should it be used?

**R**
> If you are faced with a piece of propositional notation, it stands for a propositional function if it has a circumflexed variable in it.  If it has a free variable or free variables in it (phi(x) or phi(x,y)) the phi denotes a propositional function.
> It is as simple (or as complicated) as that.
> 
> Notice that it is important to require that in (forall x:phi) for example, the variable x must actually appear in phi.  This is an eccentril (in the modern view) but perfectly formalizable feature of PM.
> 
> I would simply formalize things to ignore things like 1.1 and 1.11.  The usual rule of modus ponens subsumes both of these cases.  Russell is confused about the difference between propositions and rules.  I think that in a computer formalization you simply cannot follow him in this regard.
> 
> A more charitable way to say this is that Russell is trying to formalize the usual *rule* (not proposition) of modus ponens, which is in fact valid in his system.   I would really not try to formalize 1.1 or 1.11.  
> 
> One does have to be careful with the formal rule of modus ponens itself, because of systematic ambiguity.  If P is a theorem, and P->Q is a theorem, it does not necessarily follow that all interpretations of Q are theorems.
> It follows that all interpretations of Q which are typed in such a way that they can be embedded in P->Q are theorems.
> 
> I can actually give an example.  It is a theorem of PM with reducibility that aleph_one exists.  Any element of aleph-one is uncountable.  So if aleph_one exists, there is an uncountable set.   Modus ponens appears to allow us to conclude by modus ponens that there is an uncountable set.  But this (stated ambiguously) is not a theorem of PM:  it is consistent with PM that the type of individuals is countable, so a certain typed version of "There is no uncountable set" is possible,
> and so "There is an uncountable set" cannot be a theorem in full generality.
> 
> P:  aleph_one exists
> 
> P->Q:  if aleph_one exists, there is an uncountable set [namely, any of its elements]
> 
> *Q:  there is an uncountable set
> 
> The problem is that the type of the witness to P->Q is constrained implicitly by the logical form of P->Q in a way that it is not when Q is stated by itself.
> 
> A neat formal solution would be to require in the rule that all types appearing in P also appear in Q [it is probably sufficient to require that minimal types appearing in P also appear in Q].  You would still be able to prove the theorem above and in a correct form, by adding features to Q which made the types more specific.
> 
> aleph_one is a set of sets of objects of unspecified type.  The object shown to be uncountable is an element of aleph_one, so a set of objects of unspecified type.
> 
> P: aleph_one exists
> 
> aleph_one is defined as the cardinality of the collection of isomorphism types of countable well-orderings.  Notice that this forces its type quite high.
> 
> If aleph_one exists (which it does), there is an uncountable set (namely any of its elements) but more concretely, there is an uncountable set of sets of binary relations.
> 
> The conclusion that there is an uncountable set of sets of binary relations is valid, because it mentions all the types mentioned in the hypothesis.
> 
> Note that the cases described in 1.1 and 1.11 meet the formal condition for application of modus ponens that I describe.
