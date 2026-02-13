# Audit Report
We're aware that: 
- Distinguishing between `∀ x y, P x y` and `∀ x, ∀ y, P x y` is currently **on plan**.
- Limiting parameter's "type"(orders)s for a function is currently **partially supported**, by only writing them as a header in each of the chapters.
- Checking their types is currently **unavailable**.
- Designing functions that accepts arbitrary length is currently **unavailable**.
- Constructing "types" for every propositions in Principia is **on plan**.
- Expressing "types(orders) for a function's parameters" is **on plan**.
- Completely translate primitive propositions written in natural language, into formalized Rocq proof, is **on plan**.
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

**General.** There are two sets of theorems in this chapter: the formal and the informal one. We can completely express the formal parts in Rocq. We have tried to demonstrate how the informal parts should be expressed in Rocq, but currently these code won't be used anywhere in the rest of the project.

**Functions.** The new feature being introduced into this chapter is *functions*, and quantified/formal propositions(`forall`, `exists`) that are built upon them. Rather than following how Principia builds the function, we just use the normal lambda abstraction in Rocq. Although lambda works nicely in this chapter, later chapters expose higher expectations on functions: should they come with a type of `Prop -> Prop`, or should it be something else? Can we have an automatic way to convert one kind of functions into another kind(ch12)? The list of questions extends as we will proceed and have higher requirements.

### Chapter 10
**Coverage: 100%**

**General.** Chapter 10 is doing essentially the same as chapter 9, except the alternative definitions for `forall` and `exists`. We don't find any difficulty in formalizing this chapter.

### Chapter 11
**Coverage: 100%**

**General.** TODO: write something

TODO:
- chapter 9, ... chapter 11: all proofs are nice
- chapter 13 14: higher requirements for notations; discuss how Dfs in Principia might share the same nature as Rocq notations; ADDITIONAL THEOREMS MISSED AND NEEDED;
- chapter 13: technically doesn't have support for quantifiers, but is required in later chapters
- chapter 14: how n12_01 applies is mentioned in the text but unclear in the code; exmaple showing that function doesn't necessarily quantify over all individuals of a same kind at once
