# Audit Report
Every formal verification project comes with an audit report, and our analogue starts from below.

## The evaluation
Assessment for each of the chapter is based on the following questions:
1. Anatomy: What are the new symbols/ideas being brought up?
2. Feasibility: Are they easy to be implemented in Rocq?
3. Coverage: How much % of propositions can we formalize, and what is missing?

Anatomy on ideas(1) is performed in [mechanics](./3_mechanics.md). We start straight into the commentaries without reviewing them.

### Basic setups
**Symbol definitions.** We didn't express the *compositional* and *inheriting* nature of Principia. "Registering" new meanings to already defined theorems seems to suggest practical utilization of concepts in programming languages: typeclasses, interfaces, perhaps even monads.

On the other hand, Rocq's *notation system* has been very useful for expressing the new symbols in each of the chapter: see [chapter 14](../pm/ch14.v), [20](../pm/ch20.v) and beyond. 

I believe that both the compositional nature and the notational system are useful ideas, but they are scattered around, not being utilized to their maximum strength in our project. We will make a clearer distinction between them in the future.

**Citations.** Citations in general only cover the most important theorems and ignore the rest chores. Their orders to apply might differ from the possible ways perform the deduction[CITATION: ch14.v]. Constructing the proofs based only on the citations cannot be automated.

**Types.** Although we won't implement the typing algorithm immediately, there are still worthy comments to be made. We are aware that

1. PM doesn't have `->` type, and the typing algorithm seems to have struggled to type the functions.
2. PM also struggles at defining proposition's type: while same order propositions generalized from different types of arguments will not have the same type(p.162), it is supposed to be "practically ignored"(p.162).
3. On the very other hand, individuals, potentially being instantiated as propositions different order, all share the same type. The type for these individuals is good enough, with the consideration that individuals are, actually, the *lowest order entity for an expression*, but it is not clearly stated in the text whether individuals can have different orders in the same proposition.

**Informal propositions.** For informal propositions through the chapters, we are generally assuming that they are not implemented, as the implementation of most of them rely on a complete typing algorithm for PM.

### Chapter 1 - 5
**Coverage: 100%**

**General.** The informal propositions through chapter 1 - 5 are only the `Pp`s in chapter 1 and a special inference rule in chapter 3. For the implementation we're currently merge everything into a universal `MP` tactic.

### Chapter 9
**Coverage: 100%**

**General.** Currently we're using the default `forall`, `\/`, `~` in Rocq to model everything, making the primitive propositions not a necessity while pertaining the availability for `setoid_rewrite`.

The typing algorithm is being demonstrated, but is wrongly interpreted and will not be used anywhere.

\*9.13, the generalization assumption, according to the text, is to be performed without `MP`. Our current design is modeling this assumption by a `->`, leading to unnecessary `MP`s on `n9_13`.

**Functions.** For our soft embedding, the matrices are being constructed by just using the default lambda terms in Rocq. They works perfectly in this chapter, but later chapters will expose higher expectations on functions and matrices: should they typed in Rocq with `Prop -> Prop`, or should it be something else? Can we have an automatic way to lift functions to higher order(ch12)? The list of questions extends as we will proceed and have higher requirements.

### Chapter 10
**Coverage: 99% = ((x-1)/x)**. 

**\*X(number of the unprovable theorem)** TODO: explain why it is unprovable

**General.** Chapter 10 is doing essentially the same as chapter 9, except the alternative definitions for `forall` and `exists`. We didn't find any difficulties formalizing this chapter.

### Chapter 11
**Coverage: 100%**

**General.** Chapter 11 is doing essentially the same as chapter 10, except expanding `forall` and `exists` from one variable to multiple vars. There isn't a lot of difficulties formalizing this chapter.

The *of the same type* proposition in chapter 11 is unexamined. It will gain awareness when we're considering the typing algorithm.

**Quantified propositions.** As we're using the default `forall` in Rocq, it doesn't make a clear distinction between `forall x, forall y` and `forall x y`. We will leave it in the future, assuming such distinction is generally negligible.

### Chapter 12
**Coverage: 100%**

**General.** Axiom of Reducibility has been subjected to tons of criticisms. [Hilbert(p.33)](https://www.andrew.cmu.edu/user/avigad/Students/berkelhammer.pdf) thinks the `exists` for AoR is useless, and we can always write down the 1-st order equivalent manually - or find another way to generate such an equivalent - for an arbitrary n-order function. In our practice we find it hard to use either, and there is a plan to develop other forms of AoR to make a nicer conversion.

### Chapter 13
**Coverage: x** to be calculated; state failed proofs

**General.** This is the first chapter where we have to design `_pred` variants for previous theorems. We find lifting theorems to higher orders tedious and has to be performed manually. 

### Chapter 14
**Coverage: x** to be calculated; n13_15; ADDITIONAL THEOREMS MISSED AND NEEDED;

how n12_01 applies is mentioned in the text but unclear in the code;

**General.** As the definition of chapter 14 more complicated than any definitions in previous chapters, we are realizing that symbol definitions through `Df` should be best implemented with the notation system in Rocq. TODO: example showing that function doesn't necessarily quantify over all individuals of a same kind at once; 

**Interpretation of iota.** TODO: `iota` can have different interpretation, and the default notation in PM didn't make a clear distinction. Despite its seemingly negligible nature, some incomplete proof still stuck exactly because of it

### Chapter 20
**Coverage: WORKING IN PROGRESS**

**General.** TODO: types has become complicated... refer to Randall's work, discuss how should we consider the types
