# Mechanics of Principia Mathematica
We are building: 
- [x] Chapter 9 - A demonstration set of theorems to show chapter 1 - 5 can be extended to quantified propositions(with single "apparent variable"). Basic demonstration for a predicate called "IsSameType". Support for instantiating individuals.
- [x] Chapter 10 - The real and practical alternative to chapter 9, being used in later chapters. Material implications converted to formal implications. Notation supports for `→` and `↔` with single apparent variable.
- [x] Chapter 11 - Quantified propositions extended to more than one variables. Similarly, extended notation supports for `→` and `↔`.
- [x] Chapter 12 - Axiom of reducibility, and its conceptual support, the `Predicate` predicate.
- [x] Chapter 13 - Propositional equality(different from definitional equality). Support for instantiating predicative functions. 
- [x] Chapter 14 - Notation `ι` of the descriptions. Theorems on them.
- [ ] \[WIP\]Chapter 20 - Notation on class, and theorems of classes.

We now proceed to explain how everything is built up, bottom-up, in Principia.

## How does Principia define everything?
Different from most of the textbooks, Principia defines its concepts in a **compositional way**. In contrast to *`~ a` should be defined as something*, chapter 9 demonstrates, immediately, things like *`~` applied on an `∃` proposition should be defined as something*. It's a common practice to fix an operator and assign a function for its interpretation, but Principia usually involves 2 operators at a time. 

Principia also defines in an **inheriting way**. That means:
1. Some early chapters define rough ideas and propose their theorems. For example, we define what is an *animal*, and write down theorems about it.
2. Later chapters refine the rough idea and split for different cases. We divide *animal*s into *dog*s and *cat*s.
3. To prove a theorem in splitted cases, we might directly reuse the old theorems without any modifications. We directly use *animal* theorems instead of reinventing their analogues in *dog*s and *cat*s.

## How does Principia proof theorems?
Principia designs its theorems in a **"practical way"**. Theorems in chapter 10 are being proposed, because they are needed in later chapters, not because they address important properties for first order logic, such as soundness and completeness. ~~We really don't need `1+1=2` in a lot of places.~~

Principia performs everything **one step at a time**. This automatically means functions in Principia are always "small-step". We don't need to concern things like free vs bounded variables to eliminate the ambiguity, because deduction takes one step at a time, and only when a guaranteed/hand-crafted candidate exist. Functions don't come with a scope, and an ad-hoc "scope" is defined for auxiliary purpose orthogonal to functions. See chapter 14 below.

During each steps of the proof, Principia **cites** the theorems and previous steps to perform the next deduction. They usually appeared in the form of `[*n1.m1 . *n2.m2]`. 

TODO: check ch1, 1.7....

----------------

UNFINISHED PIECES for chapter 1 - 5

(Ch1 - 5)

For every theorem, we have two ways to use it. One is we refer to it just like a "function", and another one is prove the theorem by inference.

When we *refer* to the theorems, we are allowed to substitute every single literals with some new propositions, just like what you see in theorem provers.

When we want to prove them, we start with a set of individuals like `P`, `Q`, `R`. They are not propositions(as stated in Principia), cannot be further splitted and substituted. **New individuals that are not presented in the theorems though, is allowed to be introduced** - in the middle of proving, we might occur to a new individual like `S`.

(TODO: are individuals able to be changed in any time? )
(TODO: refer to `architecture` chapter, and maybe update the corresponded part)

how PM is different from modern type theories:
1. individuals are not propositions(???)
2. individuals can be substituted with more complex terms by infinite times(?TODO: check if there is some severe bug in formalization)

TODO: the mechanics of registration: if we have proven something is safe to use, we're supposed to extend the original symbols to new field, e.g. definition of ¬ and ∨


Elementary propositions are simple propositions connected with `¬` and `∨`.

TODO: polish as below
1. Fundamentally we have a set of individuals like `P`, `Q`, `R`. They are not propositions, and they cannot be further splited.
2. Elementary propositions are simple propositions connected with `¬` and `∨`. (Put it in another way, these `¬` and `∨`s are defined on elementary propositions)

----------------

### Chapter 1

### Chapter 2

### Chapter 3

### Chapter 4

### Chapter 5

### Chapter 9
This chapter starts to bring awareness to *matrices* and *functions*, where both of them are quite not the same to what people will acknowledge nowadays. The typical "lambda-calculus-like" functions in PM is called a *matrix*, but we don't even have the `lambda x` part to figure out what are the parameters. (TODO: citation to page in ch12, and find other occurences in intro & chapter 1-5) has demonstrated varied examples on matrices, taking different types of variables as their arguments.

*Functions* on the other hand, are these matrices themselves, *plus* their quantified(`forall`, `exists`) version. In chapter 9, there has been a notation for matrices, but never used anywhere else(TODO: check if this is actually correct): the hat operator `^` denoting exactly turning a proposition into a matrix. 

- **Matrices**(the actual "functions") are built on **propositions of a given type**
- **Quantified propositions** are built on **matrices**
- (Propositional)**functions** are built on **matrices and quantified propositions**

Formal propositions are built on matrices, without matrices, there will be no formal props 
TODO: recheck everywhere of functions and see if they should be actually matrix
TODO: check when will matrix be turned into a proposition/definition for a proposition

### Chapter 10
TODO: actual alternative;

### Chapter 11
TODO: generalize formal props

### Chapter 12
TODO: discuss the volatility for formalization; discuss how a function can be interpreted with different meanings

### Chapter 13
TODO: just an identity; discuss how it might use definition in ch12; state the utilization of `pred` variants

### Chapter 14
TODO: this is the last chapter where actual mechanics matters: the first chapter where we introduce *contextual definitions*, modeled with *notations* in Rocq. all future concept might be built either on normal or on contextual definitions, and they should be never interfere with the fundamentals for the rewriting system; but maybe in the future we might regard all the definitions as a whole and make a clearer distinction between the rewriting system, maybe until the presence of natural numbers

### Chapter 20
TODO: ambiguity on the interpretation for `Phi ! x` where we don't know if `!` stands for predicate or just the function as the focus
