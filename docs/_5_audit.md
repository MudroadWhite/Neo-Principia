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

TODO - all this below should be filled after ch14 is formalized:

### Chapter 9
**General.** 
- Completeness: nice
- formal parts: formalized all the theorems but they are useless
- Informal parts: can be formalized but cannot be used

**Tech detail: functions.** The introduction of function in this chapter allows construction for `forall` and `exists`. We discover that
TODO: 
- types for lhs parameters: haven't examined seriously
- functions can be abstracted in more than one way(ch14), therefore abstraction cannot be automated 
- which further rejects Rocq to automatically instantiate theorems

### Chapter 10
TODO:
- chapter 9, ... chapter 11: nice
- chapter 13 14: can be verified with larger tweaks; notation is annoying
- chapter 13: technically doesn't have support for quantifiers, but is required in later chapters
