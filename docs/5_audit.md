# Audit Report
Every formal verification project comes with an audit report, and our analogue starts from below.

## The evaluation
Assessment for each of the chapter is based on the following questions:
1. Anatomy: What are the new symbols/ideas being brought up?
2. Feasibility: Are they easy to be implemented in Rocq?
3. Coverage: How much % of propositions can we formalize, and what is missing?

Anatomy on ideas(1) is performed in [mechanics](./3_mechanics.md). We start straight into the commentaries without reviewing them.

### Basic setups
**Symbol definitions.** We didn't express the *compositional* and *inheriting* nature of Principia. "Registering" new meanings to already defined theorems seems to suggest practical utilization of concepts in programming languages: typeclasses, interfaces, perhaps even monads. On the other hand, Rocq's *notation system* has been very useful for expressing the new symbols in each of the chapter: see [chapter 14](../pm/ch14.v), [20](../pm/ch20.v) and beyond. I believe that how to utilize both the compositional nature and the notational system is still unclear under current implementation, and we will make a clearer distinction between them in the future.

The core of symbol definition, *definitional equality*, is undefined, as discussed in [mechanics](./3_mechanics.md) and [tactics](./4_tactics.md). 

**Citations.** Aka. references as PM call it. Citations in general only cover the most important theorems and ignore the rest chores. There are several reasons why automatically using citations to prove theorems seems to be a fruitless expectation:
- The orders to apply citations might differ from the right way to deduce(see `n14_33` and beyond)
- Our implementation have to ignore unnecessary citations and utilize unmentioned trivial citations
- Cited propositions might be a mixture of both expressions and `Ltac`
- And more generally, cited theorems might have different context to interpret

**Types.** Although we won't implement the typing algorithm immediately, there are still worthy comments to be made. We are aware that
1. PM doesn't have `→` type, and the typing algorithm seems to have struggled to type the functions.
2. PM also struggles at defining proposition's type: while same order propositions generalized from different types of arguments will not have the same type(p.162), it is supposed to be "practically ignored"(p.162).
3. On the very other hand, individuals, potentially being instantiated as propositions different order, all share the same type. The type for these individuals is good enough, with the consideration that individuals are, actually, the *lowest order entity for an expression*, but it is not clearly stated in the text whether individuals can have different orders in the same proposition.

Critics above suggest there might be freedom for us to design a different type system that is closer to Rocq type system.

**Informal propositions.** For informal propositions through the chapters, we are generally assuming that they are not implemented, as the implementation of most of them rely on a complete typing algorithm for PM.

**Sheffer strokes and other updates for 2nd edition.** We are aware that 2nd edition is a ["patched" version](https://www.andrew.cmu.edu/user/avigad/Students/berkelhammer.pdf) of Principia and Russell has tried to simplify the primitive ideas further down, with one of which being the Sheffer stroke `|` to further denote `¬` and `∨`, in a hidden chapter 8. We are aware that Russell eventually realized that the distinction between real and apparent variable might not be necessary. We still prefer to ignore most of the *Introduction* chapter and proceed with what has written in the most of the chapters, as this is the easiest way to maintain most of the flavor in the proofs.

### Chapter 1 - 5
**Coverage: 100%**

**General.** The informal propositions through chapter 1 - 5 are only the `Pp`s in chapter 1 and a special inference rule in chapter 3. As explained in [tactics](4_tactics.md), we have made several simplifications over primitive propositions.

### Chapter 9
**Coverage: 100%**

**General.** Currently we're using the default `∀`, `∨`, `¬` in Rocq to model everything, making the primitive propositions not a necessity while pertaining the availability for `setoid_rewrite`.

We have implemented the typing algorithm, but it is wrongly interpreted and will not be used anywhere.

\*9.13, the generalization assumption, according to the text, is to be performed without `MP`. Our current design is modeling this assumption with a `→`, leading to unnecessary `MP`s on `n9_13`. Note that `if...then` written in natural language in PM is not something the same as `→`, in that `→` is defined through `∨` and `¬`.

**Functions.** For our soft embedding, both elementary and 1st order functions are constructed by just using the default lambda terms in Rocq. They works perfectly in this chapter, but later chapters will reveal higher expectations on newly defined functions and matrices: should they typed in Rocq with `Prop → Prop`, or should it be something else? Can we have an automatic way to lift functions to higher order(ch12)? The list of questions extends as we move on.

**Do 1-order proposition operators and "buffed" elementary proposition operators have the same type?** In chapter 9, `¬` and `∨` are clearly stated to be the elementary proposition version, so that "we can obtain first order propositions just from e-prop operators". Then, they are allowed to "break the rules" and take one 1-order proposition in one of its positions for operands. In chapter 10, `¬` and `∨` can take any 1-order propositions in their operands, because they are already the first-order version. There seems to be a confusion on the elementary proposition version to "not to break the type": we are assuming enough to see them as their 1-order version, so what is the difference between directly defining how they can be defined by directly using 1-order operators? The assumptions on these e-prop operators already break the type of them severely. If we would adapt to use 1-order operators in chapter 9, the correct statement for the chapter will not be "constructing 1-order propositions *just* using e-props", but "constructing 1-order propositions using 1-order operators on e-props", which also seems more natural in today's aspect.

### Chapter 10
**Coverage: 98.2% = 55/56.**
- **\*10.57.** 3rd step of the proof is unprovable, simply because the theorem it uses cannot be instantiated with correct parameters.

**General.** Chapter 10 is doing essentially the same as chapter 9, except the alternative definitions for `∀` and `∃`. We didn't find any difficulties formalizing this chapter. Same to chapter 9, generalization in this chapter is not designed as Ltac.

### Chapter 11
**Coverage: 100%**

**General.** Chapter 11 is doing essentially the same as chapter 10, except expanding `∀` and `∃` from one variable to multiple vars. Same to chapter 9, generalization in this chapter is not designed as Ltac.

The *of the same type* proposition in chapter 11 is unexamined. It will gain awareness when we're considering the typing algorithm.

**Quantified propositions.** As we're using the default `∀` in Rocq, it doesn't make a clear distinction between `∀ x, ∀ y` and `∀ x y`. We will leave it in the future, assuming such distinction is generally negligible.

### Chapter 12
**Coverage: 100%(?)**

**General.** Axiom of Reducibility has been subjected to tons of criticism per history. Hilbert thinks the `∃` for AoR is [useless(p.33)](https://www.andrew.cmu.edu/user/avigad/Students/berkelhammer.pdf), and we can always write down the 1-st order equivalent manually - or find another way to generate such an equivalent - for an arbitrary n-order function. In our implementation we find it indeed hard to use, and there is a plan to develop other forms of AoR to make a nicer conversion.

On its first citation in \*13.101, it has been considered that AoR not only express the *predicative* functions but also the *non-predicative* ones, and a strict enforcement should lead to different degrees on identity. Currently our design on both AoR and proof of \*13.101 are not aware of such technical details, and there seems to be a lot of work to do in the future.

### Chapter 13
**Coverage: 92.9% = 26/28.**
- **\*13.101.** Russell stated in the text that the proof for \*13.101, \*13.15-17 should be "taken as a primitive idea"(p.169). We do find odds that blocks this proof, but it comes from a completely different reason, and a complete proof can still be given. Our proof involves using a Rocq `destruct` to get out of the routine. What the simplification we made here, inherently, is to assume we can have `(∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)`, by which PM doesn't make a theorem for unfortunately. The "distribution law" on `∃` seems to be the problem for several cases, sometimes leading to solid failure in proof; see **\*14.32** below.
- **\*13.11, \*13.12.** Both of the theorems have used \*1.7 during the proof, which seems to be confusing. The reason that \*1.7 comes into use seems to have something to deal with a meta question: when can we substitute the individuals of a deduced proposition into something else? Should we allow such substitution? Under our current design of proof, we think \*1.7 shouldn't be used explicitly and there should be some workaround.

**General.** This is the first chapter where we have to design `_pred` variants for previous theorems. We find lifting theorems to higher orders tedious and has to be performed manually. In the future we plan to automate such lifting.

### Chapter 14
**Coverage: 84.61% = 44/52.**
- **\*14.12.** From the 2nd step of `n14_12` we discovered a step where for a individual `X`, the utilization of `n11_11` has demonstrated a generalization procedure for multiple variables neglected the assumption that generalization abstracts away all occurrences for an individual once at a time, which seems to be against what [Randall Holme's type system model](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT) is suggesting.
- **\*14.121, \*14.17, \*14.171, \*14.201.** Multiple theorems steps involving \*13.15 has been revealed beyond the power of the deduction. \*13.15 is defined `⊦ X = X`, and these theorems tries to use \*13.15 to imply that they can immediately obtain things like `A ∧ (X = X)` to `A`, i.e. `X = X` is supposed to mean "true". We think there should be some extra theorems for \*13.15 to be patched up and make it actually useable.
- **\*14.142.** The last 2 steps of this theorem are both unprovable, and we suspect there is a typo happening in these two steps.
- **\*14.272.** The citation of \*10.414 seems to be invalid, because it is deducing in the other direction. We think this theorem is unprovable.
- **\*14.32.** It has been assumed that \*14.32 is undergoing proof with same style as \*14.31, besides the fact that \*14.32 is bidirectional(using `↔`). The reverse direction involves using \*14.21(as the only way provided) and \*14.1. \*14.21 is taking a whole single `ιφ` as its premise; the hypothesis of our goal however, in our representation, is `([ι φ | ιφ => ¬ χ ιφ]) ↔ ¬ ([ι φ | ιφ => χ ιφ])` which involves two `ι`. Therefore we need to have a way to transform the two `ι`s into a single `ι`. What will be required beneath the re-scoping is a theorem of `(∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)`, which is even intuitively not always true. We conclude the reverse direction of this theorem unprovable. TODO: we might still be able to fix the proof in the future and eliminame the `admit`

**General.** As the definition of chapter 14 more complicated than any definitions in previous chapters, we are realizing that symbol definitions through `Df` should be best implemented with the `Notation` system in Rocq.

### Chapter 20
**Coverage: WORKING IN PROGRESS**

**General.** TODO: types has become complicated... refer to Randall's work, discuss how should we consider the types
