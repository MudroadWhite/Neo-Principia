# Audit Report
We're aware that: 
- Checking types in Principia is **unavailable**.
- Expressing "types(orders) for a function's parameters" is **on plan**.
- Distinguishing between `∀ x y, P x y` and `∀ x, ∀ y, P x y` is currently **on plan**.
- Completely translate primitive propositions written in natural language, into Rocq proof as a demonstration, is **on plan**.
- More to come...

Every formal verification project comes with an audit report, and our analogue starts from below.

## The evaluation
Assessment for each of the chapter is based on the following questions:
1. Anatomy: What are the new ideas being brought up?
2. Feasibility: Are they easy to be expressed in Rocq?
3. Coverage: How much % of propositions can we formalize, and what is missing?

Anatomy on ideas(1) is performed in [mechanics](./3_mechanics.md). We start straight into the commentaries without reviewing them.

### Basic setups
**Definitions.** We didn't express the *compositional* and *inheriting* nature of Principia. "Registering" new meanings to already defined theorems seems to suggest practical utilization of concepts in programming languages: typeclasses, interfaces, perhaps even monads.

**Citations.** Citations in general only cover the most important theorems and ignore the rest chores. Their orders to apply might differ from the possible ways perform the deduction. Constructing the proofs based only on the citations cannot be automated.

**Types.** We won't check the types within the proofs, because we didn't find a way to correctly restrict the types for the terms. Currently I'm thinking of using functions as tags to label the type level of a parameter/term, as `Definition Predicate_1 (X : Prop) := Prop`, but beyond that I don't have a better clue. Proofs of chapters in this project **will not have their type checked**.

### Chapter 9
**Coverage: 100%**, without informal parts

**General.** There are two sets of theorems in this chapter: the formal and the informal one. We can completely express the formal parts in Rocq. We demonstrated how the informal parts should be expressed in Rocq, but they won't be used anywhere in the rest of the project.

**Functions.** The new feature being introduced into this chapter is *functions*, and quantified/formal propositions(`forall`, `exists`) that are built upon them. (TODO: MOVE THIS SENTENCE INTO MECHANICS, LEAVING ONLY CRITICS)For our soft embedding, we use a different approach to construct the function, which is just the default lambda terms in Rocq. They works perfectly in this chapter, but later chapters will expose higher expectations on them: should they come with a type of `Prop -> Prop`, or should it be something else? Can we have an automatic way to convert one kind of functions into another kind(ch12)? The list of questions extends as we will proceed and have higher requirements.
TODO: setoid_rewrite is being introduced exactly because of the difficulty on writing on forall/exists and functions

### Chapter 10
**Coverage: 100%**

**General.** Chapter 10 is doing essentially the same as chapter 9, except the alternative definitions for `forall` and `exists`. We didn't find any difficulties formalizing this chapter.

### Chapter 11
**Coverage: 100%**

**General.** Chapter 11 is doing essentially the same as chapter 10, except expanding `forall` and `exists` from one variable to multiple vars. We didn't find any difficulties formalizing this chapter.

**Quantified propositions.**TODO: forall takes 1 params at a time... for multiple variables, a rigorous distinction between Ax Ay and Axy has been ignored, assuming they wouldnt affect the proof very much

### Chapter 12
**Coverage: 100%**

**General.** TODO: only a few theorems; but they might subject to changes bc we don't know how exactly they works

### Chapter 13
**Coverage: x** to be calculated; state failed proofs

**General.** TODO: use theorem variants, might have something to be done with ch12; Are the `!` functions untyped, or they come strictly with a `Predicate` type??

### Chapter 14
**Coverage: x** to be calculated; n13_15; ADDITIONAL THEOREMS MISSED AND NEEDED;

**General.** TODO: higher requirements for notations; discuss how Dfs in Principia might share the same nature as Rocq notations; how n12_01 applies is mentioned in the text but unclear in the code; exmaple showing that function doesn't necessarily quantify over all individuals of a same kind at once
