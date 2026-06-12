# Audit Report
Every formal verification project comes with an audit report, and our analogue starts from below.

## The evaluation
Assessment for each of the chapter is based on the following questions:
1. Anatomy: What are the new symbols/ideas being brought up?
2. Feasibility: Are they easy to be implemented in Rocq?
3. Coverage: How much % of propositions can we formalize, and what is missing?

Anatomy on ideas(1) is performed in [mechanics](./3_mechanics.md). For the below sections, we first make a short summary of major issues we have found.

### The Defects
Defects arisen in Principia come either from the lacking of proper implementation of our project, or directly from the Principia Mathematica itself. After stating these issues, we will expand every details we have found by each chapters.

**D1: Typing.** We didn't design a proper system to type every PM propositions. The very root of this defect originates from [lacking of definition](./B_proposition.md). The result is also a massive chain effect:
- **D1.1** We cannot distinguish between predicative and impredicative props/functions
- **D1.2** We cannot implement Axiom of Reducibility
- **D1.3** Several propositions that are relying on AoR cannot be properly implemented at all

**D2: Inheritance/internalization.** Problems under this topic usually involves with our inability to automate the related mechanics. They either because the text is missing their support, or we just haven't designed the correct abstraction yet. They include:
- **D2.1** Scoping for incomplete symbols
- **D2.2** Polymorphism on hierarchies
- **D2.3** And even a level down, there might be case where interpretation on a theorem is ambiguous. This is mostly a chapter-20 specific, where distinction between PM's language and interpretation starts to matter.

**D3: setoid_rewrite.** `setoid_rewrite` is a nice tactic, but it still changes by version updates. When updating Rocq to `9.0` or beyond, every `setoid_rewrite` starts to go wrong and we have to manually re-specify the index for `setoid_rewrite` to focus on. While this doesn't affect the proof in general, it prevents us to make our proof compatible for most of Coq/Rocq versions.

**D4: Tactics support.** We have identified 3 separate ways for PM to perform rewrite, while implementation-wise, we have only designed a `MP` tactic. Missing tactics for generalization and instantiation leaves our design not as "symmetric" as it should be. This is merely an aesthetical issue that hardly affect the interpretation quality of our formalization.

**D5: Unknown application of theorems.**
During formalizing the proof, we have observed several theorems being applied in unnatural way that is not just using simply deduction. We cannot identify why they are present.

### Basic setups
**Symbol definitions.** We didn't express the *compositional* and *inheriting* nature of Principia. "Registering" new meanings to already defined theorems seems to suggest practical utilization of concepts in programming languages: typeclasses, interfaces, perhaps even monads. On the other hand, Rocq's *notation system* has been very useful for expressing the new symbols in each of the chapter: see [chapter 14](../pm/ch14.v), [20](../pm/ch20.v) and beyond. I believe that how to utilize both the compositional nature and the notational system is still unclear under current implementation, and we will make a clearer distinction between them in the future.

The core of symbol definition, *definitional equality*, is undefined, as discussed in [mechanics](./3_mechanics.md) and [tactics](./4_tactics.md). 

**Citations.** Aka. references as PM call it. Citations in general only cover the most important theorems and ignore the rest chores. There are several reasons why automatically using citations to prove theorems seems to be a fruitless expectation:
- The orders to apply citations might differ from the right way to deduce(see `n14_33` and beyond)
- Our implementation have to ignore unnecessary citations and utilize unmentioned trivial citations
- Cited propositions might be a mixture of both expressions and `Ltac`
- And more generally, cited theorems might have different context to interpret

**Types.** Although we won't implement the typing algorithm immediately, there are still worthy comments to be made. We are aware that
1. PM doesn't have a notion for typing, also being mentioned by [Randall](https://randall-holmes.github.io/Drafts/pmsemantics.pdf).
2. For functions, Rocq's `→` type can apparently simulate PM's function type assuming we never apply the parameters partially.
3. For propositions: while same order propositions generalized from different types of arguments will not have the same type(p.162), it is supposed to be "practically ignored"(p.162). We can change the definition into the following to fix such unnecessary distinction: proposition's type is the returned order of the proposition from a completely instantiated function.
4. (p.128)Starting from chapter 9, it has been stated that "real variables can be untyped and can be applied on any propositions". Typing has been already hard for us, while this seems to be an important feature to address with, we didn't investigate anywhere deeper in situations where real variables should be typed.

**Orders**. We have the orders in our implementation, but currently it is severely wrongly interpreted and doesn't stand for the correct representation of a nth order proposition. It mostly works like a tag and doesn't involve actual typechecking. One can easily check its strength by giving the following goal a try:
```coq
Goal Order 0 = Order 1.
```

**Sheffer strokes and other updates for 2nd edition.** We are aware that 2nd edition is a ["patched" version](https://www.andrew.cmu.edu/user/avigad/Students/berkelhammer.pdf) of Principia and Russell has tried to simplify the primitive ideas further down, with one of which being the Sheffer stroke `|` to further denote `¬` and `∨`, in a hidden chapter 8. We are aware that Russell eventually realized that the distinction between real and apparent variable might not be necessary. We still prefer to ignore most of the *Introduction* chapter and proceed with what has written in the most of the chapters, as this is the easiest way to maintain most of the flavor in the proofs.

### Chapter 1 - 5
**Coverage: 100%**

**General.** The informal propositions through chapter 1 - 5 are only the `Pp`s in chapter 1 and a special inference rule in chapter 3. As explained in [tactics](4_tactics.md), we have made several simplifications over primitive propositions.

For *modus ponens*, and *syllogism* etc. in the later chapters, we are directly inheriting the tactics designed by [Landon](https://github.com/LogicalAtomist/principia). By using tactics for deductions, we can make a clear distinction between what are being performed through *modus ponens* and what are not.

### Chapter 9
**Coverage: 100%**

**General.** We first give a criticism on chapter 9's idea for performing the proof. Chapter 9 proves chapter 1 theorems can be "lifted" to 1-order versions, given assumed 1-order constructors `forall` and `exists` being able to applying on elementary `~` and `\/`s. If we are normally designing a language in functional language or Rocq, we would expect `~` or `\/`'s type can be automatically inferred from types of operand, or the other way around; here, PM seems more like to brutally associate elementary operators with first order operands, without ensuring us that we can uniquely infer the types. The proper way seems to be asserting that *first order* - rather than *elementary* ones - `~` and `\/` exists, then we can eventually deduce the first order equivalent of chapter 1 theorems.

Implementation-wise, we're using the default `∀`, `∨`, `¬` in Rocq to model everything, making the primitive propositions not a necessity while pertaining the availability for `setoid_rewrite`.

We have implemented the typing algorithm in chapter 9, but it is wrongly interpreted and will not be used anywhere.

**Functions.** This is the first chapter for our soft embedding to consider functions, and how to rewrite on functions. For our implementation, both elementary and 1st order functions are constructed by just using the default lambda terms in Rocq. They works perfectly in this chapter, but later chapters will reveal higher expectations on newly defined functions and matrices: should they typed in Rocq with `Prop → Prop`, or should it be something else? Can we have an automatic way to lift functions to higher order(ch12)? The list of questions extends as we move on.

**setoid_rewrite.** The tactic `setoid_rewrite` is completely introduced into our implementation to simplify the proofs. While it has been convenient to rewrite on subparts of a proposition correctly, it will hide away some of the citation for the proof. Similar issue apply to `destruct`, but it's underlying citation is clear: namely the `Simp` theorems.

We have received feedback that `setoid_rewrite` in Rocq >9.0 in seems to adopt to a different way to recognize the subparts. So far as I can see, this should be the only factor that will break version compatability.

### Chapter 10
**Coverage: 98.2% = 55/56.**
- **\*10.57.** 3rd step of the proof is unprovable, simply because the theorem it uses cannot be instantiated with correct parameters.
- **\*10.23, alternative proof.** In the 5th step of the proof, the proposition has used variable name `x` twice referring to two different actual variables. Although the proof is generally unaffected when we give it the right renaming, this is still a rare case of bad text.

**General.** Chapter 10 is doing essentially the same as chapter 9, except the alternative definitions for `∀` and `∃`. We didn't find any difficulties formalizing this chapter. Same to chapter 9, generalization in this chapter is not designed as Ltac.

### Chapter 11
**Coverage: 100%**

**General.** Chapter 11 is doing essentially the same as chapter 10, except expanding `∀` and `∃` from one variable to multiple vars. Same to chapter 9, generalization in this chapter is not designed as Ltac.

The *of the same type* proposition in chapter 11 is unexamined. It will gain awareness when we're considering the typing algorithm.

**Quantified propositions.** As we're using the default `∀` in Rocq, it doesn't make a clear distinction between `∀ x, ∀ y` and `∀ x y`. We will leave it in the future, assuming such distinction is generally negligible.

### Chapter 12
**Coverage: 0%(?)**

**General.** Axiom of Reducibility has been subjected to tons of criticism per history. Hilbert thinks the `∃` for AoR is [useless(p.33)](https://www.andrew.cmu.edu/user/avigad/Students/berkelhammer.pdf), and we can always write down the 1-st order equivalent manually - or find another way to generate such an equivalent - for an arbitrary n-order function. In our implementation we find it indeed hard to use, and there is a plan to develop other forms of AoR to make a nicer conversion.

Dependency on AoR generally matters with the utilization of `!` that also comes to (sometimes, critical)significance after chapter 12, denoting predicates from untyped functions. Inherently speaking, it requires us to design a useable small type system to distinguish between untyped functions and predicates. Our current implementation does not support `!`, because we don't strictly differentiate untyped and predicative functions. 

Lacking of the type system results in AoR not strictly implemented in chapter 12. While it doesn't generally matter in chapter 13 - 14, chapter 20 brings its necessity to the surface. 

### Chapter 13
**Coverage: 92.9% = 26/28.**
- **\*13.101.** Russell stated in the text that the proof for \*13.101, \*13.15-17 should be "taken as a primitive idea"(p.169). We do find odds that blocks this proof, but it comes from a completely different reason, and a complete proof can still be given. Our proof involves using a Rocq `destruct` to get out of the routine. What the simplification we made here, inherently, is to assume we can have `(∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)`, by which PM doesn't make a theorem for unfortunately. The "distribution law" on `∃` seems to be the problem for several cases, sometimes leading to solid failure in proof; see **\*14.32** below.
- **\*13.11, \*13.12.** Both of the theorems have used \*1.7 during the proof, which seems to be confusing. The reason that \*1.7 comes into use seems to have something to deal with a meta question: when can we substitute the individuals of a deduced proposition into something else? Should we allow such substitution? Under our current design of proof, we think \*1.7 shouldn't be used explicitly and there should be some workaround.

**General.** This is the first chapter where we have to design `_pred` variants for previous theorems, as the *variant* mechanic in [tactics](./4_tactics.md).

**Definition of identity.** In PM, it has been considered that AoR not only express the *predicative* functions but also the *non-predicative* ones, and a strict enforcement should lead to different degrees on identity, maybe even implying giving `=` different types depending of types of its operands. It is worthwhile to note that we are directly using Rocq's default `=` as the symbol for identity, leading to several facts below:
- All operands of `=` are having Rocq's type, not the types in PM
- Because of this issue, Rocq's `=` is hiding the necessity for Axiom of Reducibility.

### Chapter 14
**Coverage: 84.61% = 44/52.**
- **\*14.12.** From the 2nd step of `n14_12` we discovered a step where for a individual `X`, the utilization of `n11_11` has demonstrated a generalization procedure for multiple variables neglected the assumption that generalization abstracts away all occurrences for an individual once at a time, which seems to be against what [Randall's](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT) is suggesting.
- **\*14.121, \*14.17, \*14.171, \*14.201.** Multiple theorems steps involving \*13.15 has been revealed beyond the power of the deduction. \*13.15 is defined `⊦ X = X`, and these theorems tries to use \*13.15 to imply that they can immediately obtain things like `A ∧ (X = X)` to `A`, i.e. `X = X` is supposed to mean "true". We think there should be some extra theorems for \*13.15 to be patched up and make it actually useable.
- **\*14.142.** The last 2 steps of this theorem are both unprovable, and we suspect there is a typo happening in these two steps.
- **\*14.272.** The citation of \*10.414 seems to be invalid, because it is deducing in the other direction. We think this theorem is unprovable.
- **\*14.32.** It has been assumed that \*14.32 is undergoing proof with same style as \*14.31, besides the fact that \*14.32 is bidirectional(using `↔`). The reverse direction involves using \*14.21(as the only way provided) and \*14.1. \*14.21 is taking a whole single `ιφ` as its premise; the hypothesis of our goal however, in our self-defined notation, is `([ι φ | ιφ => ¬ χ ιφ]) ↔ ¬ ([ι φ | ιφ => χ ιφ])` which involves two `ι` scopes. Therefore we need to have a way to merge scopes of the two `ι`s into a single `ι` at a large scope. What will be required beneath the re-scoping is a theorem of `(∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)`, which is even intuitively not always true. We conclude the reverse direction of this theorem unprovable. 

**General.** This is the first chapter where we have to define an "incomplete" symbol, one feature of which is coming with a scope. We eventually find an elegant way to express such symbol: we want to define something almost like `λ (x : A) => ...`. `λ` here provides just the idea for a scope; `(x : A)` while seemingly assigning `x` to a type, can also assign `x` to some specification. Doing so involves our first symbol implementation in Rocq defined using a `Notation`, and the definition's difficulty has been eliminated once and for all. It seems like a general treatment for incomplete symbols in the whole PM.

**Symbol definitions.** While generally functions only use types like `Prop -> Prop`, our symbol definition will relax the type to `A -> Prop` for polymorphic type `A`, as our design principle "polymorphic symbol" requires in [tactics](./4_tactics.md). By [mechanics](./3_mechanics.md/#chapter-14), `ιx` does not necessarily only serve for propositional variables; in chapter 20, the variable's type will be type for classes. This leads to a distinction in our implementation: polymorphic for symbol definitions, but monomorphic for theorems; and by the dependency of theorems, such polymorphism is strictly required.

**Scopes.** When it involves more than one `ι` for a sub term, it turns out that the order of different `ι`s matters. While this is stated in the theorems in chapter 14, it is only *assumed* in chapter 20, and will involve adding axioms for such equivalence. Being implementation specific, for each `ι` term, our notation designed a variable to refer to the description, and these variables have to come with an extra axiom to make them order-unrelated, resulting in the extra `iota2_arg_comm`.

### Chapter 20
**Coverage: %= ?/61.**

**General.** Designing proofs in this chapter has been increasingly harder. As analyzed in [mechanics](./3_mechanics.md/#chapter-20), our current design is still not at its perfection. 

Our implementation eventually arrive at a conclusion where, although not explicitly required in the text, a hierarchy for class, and a association mechanic for classes' underlying function is needed. Another issue blocking most of the proofs is *scoping*, which also seems to be below proper treatment for PM.

**Scopes.** A major part of theorems are unprovable, because of the scoping issue. Consider two expressions `e1 := Phi x` and `e2 := ~ Psi x /\ x`, and assert `x`s' scopes are limited to the whole expression. PM tends to set the default scope for such an `x` to be the *minimal sub expression* except itself; but if we instantiate `Phi` such that `Phi := (fun y => ~ Psi y /\ y)`, the scopes for `x` in e2, if without any treatments, still remains to be the whole expression, while it should be for `Psi x` and `..... /\ x` separately.

On surface, it suggests that PM is lacking a lot of axioms to specify how the scope converts. But we have found a possible solution, which might be better to eliminate such problems, once implemented. We have proposed an experimental feature, only be outlined under `experiment/draft.v`. We find out that there can be a fixed set of tactics to shrink the scopes, or maybe design the correct representation closer to PM's original syntax, such that the scope can be automatically given during parsing the expression. This is, yet, left to be a draft, and we plan to terminate the development before it is put into use.
