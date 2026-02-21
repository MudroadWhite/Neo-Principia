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

Critics above suggest there might be freedom for us to design a different type system that is closer to Rocq type system.

**Informal propositions.** For informal propositions through the chapters, we are generally assuming that they are not implemented, as the implementation of most of them rely on a complete typing algorithm for PM.

**Sheffer strokes and other updates for 2nd edition.** We are aware that 2nd edition is a ["patched" version](https://www.andrew.cmu.edu/user/avigad/Students/berkelhammer.pdf) of Principia and Russell has tried to simplify the primitive ideas further down, with one of which being the Sheffer stroke `|` to further denote `~` and `\/`, in a hidden chapter 8. We are aware that Russell eventually realized that the distinction between real and apparent variable might not be necessary. We still prefer to ignore most of the *Introduction* chapter and proceed with what has written in the most of the chapters, as this is the easiest way to maintain most of the flavor in the proofs.

### Chapter 1 - 5
**Coverage: 100%**

**General.** The informal propositions through chapter 1 - 5 are only the `Pp`s in chapter 1 and a special inference rule in chapter 3. As explained in [tactics](4_tactics.md), we have made several simplification on the primitive propositions.

### Chapter 9
**Coverage: 100%**

**General.** Currently we're using the default `forall`, `\/`, `~` in Rocq to model everything, making the primitive propositions not a necessity while pertaining the availability for `setoid_rewrite`.

We have implemented the typing algorithm, but it is wrongly interpreted and will not be used anywhere.

\*9.13, the generalization assumption, according to the text, is to be performed without `MP`. Our current design is modeling this assumption by a `->`, leading to unnecessary `MP`s on `n9_13`.

**Functions.** For our soft embedding, the matrices are being constructed by just using the default lambda terms in Rocq. They works perfectly in this chapter, but later chapters will expose higher expectations on functions and matrices: should they typed in Rocq with `Prop -> Prop`, or should it be something else? Can we have an automatic way to lift functions to higher order(ch12)? The list of questions extends as we will proceed and have higher requirements.

### Chapter 10
**Coverage: 98.2% = 55/56.**
- **\*10.57.** 3rd step of the proof is unprovable.

**General.** Chapter 10 is doing essentially the same as chapter 9, except the alternative definitions for `forall` and `exists`. We didn't find any difficulties formalizing this chapter. Same to chapter 9, generalization in this chapter is not designed as Ltac.

### Chapter 11
**Coverage: 100%**

**General.** Chapter 11 is doing essentially the same as chapter 10, except expanding `forall` and `exists` from one variable to multiple vars. There isn't a lot of difficulties formalizing this chapter. Same to chapter 9, generalization in this chapter is not designed as Ltac.

The *of the same type* proposition in chapter 11 is unexamined. It will gain awareness when we're considering the typing algorithm.

**Quantified propositions.** As we're using the default `forall` in Rocq, it doesn't make a clear distinction between `forall x, forall y` and `forall x y`. We will leave it in the future, assuming such distinction is generally negligible.

### Chapter 12
**Coverage: 100%(?)**

**General.** Axiom of Reducibility has been subjected to tons of criticisms. [Hilbert(p.33)](https://www.andrew.cmu.edu/user/avigad/Students/berkelhammer.pdf) thinks the `exists` for AoR is useless, and we can always write down the 1-st order equivalent manually - or find another way to generate such an equivalent - for an arbitrary n-order function. In our practice we find it hard to use either, and there is a plan to develop other forms of AoR to make a nicer conversion.

### Chapter 13
**Coverage: 92.9% = 26/28.**
- **\*13.11, \*13.12.** Both of the theorems have used \*1.7 during the proof, which seems to be confusing. We think \*1.7 shouldn't be used explicitly and there should be some workaround for these proofs.

**General.** This is the first chapter where we have to design `_pred` variants for previous theorems. We find lifting theorems to higher orders tedious and has to be performed manually. In the future we plan to automate such lifting.

### Chapter 14
**Coverage: 84.61% = 44/52.**
- **\*14.12.** From the 2nd step of `n14_12` we discovered a step where for a individual `X`, the utilization of `n11_11` has demonstrated a generalization procedure for multiple variables neglected the assumption that generalization abstracts away all occurrences for an individual once at a time, which seems to be against what [Randall Holme's type system model](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT) is suggesting.
- **\*14.121, \*14.17, \*14.171, \*14.201.** Multiple theorems steps involving \*13.15 has been revealed beyond the power of the deduction. \*13.15 is defined `|- X = X`, and these theorems tries to use \*13.15 to imply that they can immediately obtain things like `A /\ (X = X)` to `A`, i.e. `X = X` is supposed to mean "true". We think there should be some extra theorems for \*13.15 to be patched up and make it actually useable.
- **\*14.142.** The last 2 steps of this theorem are both unprovable, and we suspect there is a typo happening in these two steps.
- **\*14.272, \*14.32.** The failing steps in the proof is revealing a crucial difference on the iota notation. In Principia, it is suggested that for an expression of the form of `ι x <-> ι y`, we can interpret using either `ι2` or single `ι`. It turns out that `ι2`  generates different expression from applying single `ι` twice, but PM has been mutually using them during developing the proof, and their equality has been explicitly suggested in the text.

**General.** As the definition of chapter 14 more complicated than any definitions in previous chapters, we are realizing that symbol definitions through `Df` should be best implemented with the notation system in Rocq. TODO: example showing that function doesn't necessarily quantify over all individuals of a same kind at once; 

TODO: 
- recheck n14_272
- recheck iota interpretation

### Chapter 20
**Coverage: WORKING IN PROGRESS**

**General.** TODO: types has become complicated... refer to Randall's work, discuss how should we consider the types
