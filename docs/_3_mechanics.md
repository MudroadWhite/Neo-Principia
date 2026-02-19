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

## Basic setups
### How does Principia define symbols?
Different from most of the textbooks, Principia defines its symbols in a **compositional way**. In contrast to *`~ a` should be defined as something*, chapter 9 demonstrates, immediately, things like *`~` applied on an `∃` proposition should be defined as something*. It's a common practice to fix one symbol and assign a function for its interpretation, but Principia usually involves 2 operators at a time. 

Principia also defines symbols in an **inheriting way**. That means:
1. Some early chapters define rough ideas and propose their theorems. For example, we define what is an *animal*, and write down theorems about it.
2. Later chapters refine the rough idea and split for different cases. We divide *animal*s into *dog*s and *cat*s.
3. To prove a theorem in splitted cases, we might directly reuse the old theorems without any modifications. We directly use *animal* theorems instead of reinventing their analogues in *dog*s and *cat*s.

### How does Principia proof theorems?
Principia designs its theorems in a "**practical way**". Theorems in chapter 10 are being proposed, because they are needed in later chapters, not because they address important properties for first order logic, such as soundness and completeness. ~~We really don't need `1+1=2` in a lot of places.~~

Principia performs everything **one step at a time**. This automatically means functions in Principia are always "small-step". We don't need to concern things like free vs bounded variables to eliminate the ambiguity, because deduction takes one step at a time, and only when a guaranteed/hand-crafted candidate exist. Functions don't come with a scope, and an ad-hoc "scope" is defined for auxiliary purpose orthogonal to functions. See chapter 14 below.

During each steps of the proof, Principia **cites** the theorems and previous steps to perform the next deduction. They usually appeared in the form of `[*n1.m1 . *n2.m2]`. 

Theorems, like symbol definitions, have its **inheriting** nature. The way for a theorem to be proven and to be used *varies* between chapters. See [chapter 1](./3_mechanics.md/#chapter-1) for case in chapter 1 - 5, [chapter 9](./3_mechanics.md/#chapter-9) for case in chapter 9 - 11, and [chapter 12](./3_mechanics.md/#chapter-12) for chapter 12 and beyond.

We now start explaining what new ideas are being introduced into each of the chapters.

## Chapters
### Chapter 1
Principia has 3 types of theorems: `Pp`(primitive proposition), `Df`(definitions, usually definitions for new symbols) and `Thm`s(ordinary theorems). Chapter 1 presents some basic `Pp`s to set everything up, and practically speaking, we find it out that `Pp`s usually suggest something just as meta in the Rocq system: for PM's *modus ponens* to work, we will have to implement a *MP* tactic in Rocq - currently with their parameter types unchecked because we didn't implement it yet.

The way *we prove theorems* in this chapter is basically just what `Pp`s says:
- Having something in our proof window means it has been asserted/implied true
- Asserting `H1 : P` means asserting `P` as an **elementary proposition**
- Asserting `H2 : P -> Q` means asserting `P` can successfully imply `Q`
- (\*1.1)If `H1` and `H2` are asserted true, we are allowed to assert `H3 : Q`

In chapter 1 we also have a rough idea on how to denote a (elementary) *propositional function*. Such kind of simple denotation will be changed into something else in later chapters. In chapter 1-5, most propositional functions don't come barely themselves - their values for variables are somehow "fixed" already during all the inference, where `Phi X` and `Phi Y` does not mean the same thing(p.19).

```Rocq
(* This is an elementary proposition *)
Example example_ch1_proposition (X : Prop) := X.

(* This is an asserted elementary function value *)
Example example_ch1_prop_function_1 (Phi : Prop) (X : Prop) := Phi X.

(* This is the actual way to write the function, but we won't use it *)
Example example_ch1_prop_function_2 (Phi : Prop) := fun (X : Prop) => Phi X.
```
- Asserting an (elementary) **propositional function** means asserting `H1 : Phi X`.
- (\*1.2)If `H2 : Phi X -> Psi X` can be implied, then we are allowed to imply `H3 : Psi X`.

To be exact, `H1 : Phi X` above should refer to something like `H1: (fun x => x /\ x) X` in the proof window, but this doesn't appear in our implementation as we will mostly have simplified it away. By asserting a function, we don't assert `Phi` solely(p.92) and we're still asserting a proposition. In practice, we have designed a unified `MP` to perform both kind of the *modus ponens*.

- (p.94)Definitional equality is undefined in PM
- **elementary propositions** are closed under `¬` and `∨`
- **elementary functions** are closed under `¬` and `∨`

(p.92)Note: not to confuse "not-p" in the "(2) Elementary propositional functions" with `¬ p`, where `¬` is symbolic negation and "not" is a made-up predicate in natural language.

### Chapter 2

### Chapter 3

### Chapter 4

### Chapter 5

### Chapter 9
This chapter starts to bring awareness to *matrices* and *functions*, where both of them are quite not the same to what people will acknowledge nowadays. Although they are being considered, their full definitions start from chapter 12, so our explanation will also cite the text in chapter 12 for reference.

```Rocq
(* This is a function with 2 real variables. It's also a matrix *)
Example example_matrix (X Y : Prop) := X /\ Y.

(* This is a function with 1 real variable and 1 apparent variable. It's not a matrix *)
Example example_function (X : Prop) := forall (y : Prop), X /\ y.

(* This is a proposition with 2 apparent variables. It is *not* a function anymore *)
Example example_proposition := forall (x y : Prop), x /\ y.
```

- **Matrices**(the actual "functions") are exactly **predicative functions**(p.164 defined as synonym).
- **Matrices** are built on **propositions** of a 1-level lower order(TODO: make a clear distinction between types). See [chapter 12](./3_mechanics.md/#chapter-12) below for a serious consideration on orders
- **Functions** are built on **matrices**, with *not all* of its variables quantified
- **Propositions** are built on **matrices**, with *all* possible variables quantified

The examples above should have already shown clearly what in PM called a *matrix*(p.50). Appearing in the text though, it is slightly less obvious how they are "functions" of a kind - they don't have the `lambda x` part(aka the parameter list) to explicitly state what are the parameters: the `example_matrix` above will just be written as `x /\ y`. For a matrix, all greek/english letters appeared are parameters.

(Propositional) *functions*(p.14) include matrices themselves, *plus* some(not all) of the variables of a matrix quantified(`forall`, `exists`). In chapter 9, there has been a notation for matrices, but never used anywhere else(TODO: check if this is actually correct and cite the part): the hat operator `^` denoting exactly turning a proposition into a matrix. 

There is another way to understand the difference between a matrix and a proposition, by identifying their apparent and real variables(p.18). Their difference have been discussed clearer in original text. Is it real that *there are no propositions containing real variables*, as [Wittgenstein](https://wittgensteinproject.org/w/index.php/Notes_on_Logic) have said? We don't really know, but let's just turn back to the our examples to vibe it off. One crucial difference between real and apparent variables(p.128), though, is that real variables are not given types in PM while apparent variables are given types.

Examples of *matrices* are given in \[CITATION NEEDED: cite page in ch12, and find other occurrences in intro & chapter 1-5 \], taking different types of variables as their arguments. 

Proving theorems in chapter 9 - 11 is under the following assumptions, which I personally call *order-1 context*:

- Parameters for a theorem are all the letters appeared in the theorem, similar to how a function is expressed(TODO: MOVE TO CH1)
- Only the case where parameters for theorems are individuals (plus elementary matrices just as the common sense "functions") is taken into consideration
- If such a elementary proposition/first order "proposition"(TODO: check if this is written correctly) can be proven true, we conclude the truth of such a theorem(TODO: maybe check theorems in chapter 1)
- When we want to use a proven theorem somewhere, we are allowed to replace individuals or matrices with arbitrary elementary propositions or elementary matrices

Chapter 9's theorems are furthermore splitted into 2 parts for different purposes:
- Theorems expressed as formulae have the purpose to *demonstrate* how theorems in chapter 1 - 5 can be extended to cases with quantifiers, *assuming that we can already use those quantifiers*
- Theorems expressed as natural language define the meta theory to legitimate the actual important properties: what is a type, how to extend a function to quantified propositions, when to derive them, and eventually, why can we extend to quantifiers without breaking the types.

TODO: 
- Check chapter II's discussion on "different meaning for ~ applying on forall and exists"
- the mechanics of registration: if we have proven something is safe to use, we're supposed to extend the original symbols to new field, e.g. definition of `¬` and `∨`
- check how PM uses different sets of symbols/letters to represent constants, matrices, etc..


TODO:

- Can propositions be taken as parameters, since (p.163) matrixes only take individuals/matrices as params?

~p.49:
- We can construct a function taking 2 arguments, and return either a function of function or a function of individual. 
It turns out that the return type is untyped. To enforce the return type with a fixed type, we have to enforce arguments
of a function taking the same type

~p.52:
- `!` notation also seems to be used only when the function is being considered as a variable(at rhs)? And for all other cases, they are 
  supposed to be fixed(at rhs)?
- `!`'s summary: this is not a notation just for first order functions, but it's more like a notation for function being identified as 
  a variable at rhs

### Chapter 10
TODO: actual alternative;

### Chapter 11
TODO: generalize formal props

### Chapter 12
Starting from chapter 12, a rigorous hierarchy of *orders* begins to be taken into consideration, and this is also the first chapter that we're going to think something like "so these theorems have more than one ways to use them"\[CITATION NEEDED\].

TODO:
- *context: order-n*
- Theorems in chapter 1 - 11 can be reused by replacing individuals into some n-order-matrices and elementary matrices into some n+1-order matrices
- discuss the volatility for formalization of AoR
- discuss the `!` operator: it doesn't consider the absolute order level but it fixes the relative level to +1; for convenience should we only start with individuals?
- a individual can have a 2nd order function - discuss how should we understand a function of +n types to a parameter
- [Hilbert](https://www.andrew.cmu.edu/user/avigad/Students/berkelhammer.pdf)(p.33) thinks the `exists` for AoR is a useless shit, and we can always write down the 1-st order equivalent manually - or find another way to generate such an equivalent - for an arbitrary n-order function.

### Chapter 13
TODO: 
- just an identity 
- discuss how it might use definition in ch12; state the utilization of `pred` variants
- (p.57)exaplained a proof of identity `=` informally, only to be complete with the support of axiom of reducibility


### Chapter 14
TODO: this is the last chapter where actual mechanics matters: the first chapter where we introduce *contextual definitions*/"incomplete symbol", modeled with *notations* in Rocq. all future concept might be built either on normal or on "incomplete symbols", and they should be never interfere with the fundamentals for the rewriting system; but maybe in the future we might regard all the definitions as a whole and make a clearer distinction between the rewriting system, maybe until the presence of natural numbers

### Chapter 20
TODO: ambiguity on the interpretation for `Phi ! x` where we don't know if `!` stands for predicate or just the function as the focus

DRAFTS
~p.17:
- descriptive funstion: a special kind of propositional function, including examples like `x is blue`
- `~` is not a primitive idea. It is supposed to have a different definition on different types of proposition. 
For example, we might define `~` a typeclass, and `∀` propositions has an instance of implementation for 
this operator

~p.20: 
- (Ax, Px → Q x) → (Ax, Px) → (Ax, Qx) requires that P Q takes arguments "of the same type". TODO: → p.49
- formal implication: the `→` wrapped up in `∀`s. It bypassed the problem that `P → Q = ~P ∨ Q`, and restrict that we have to 
know `∀ x, P x → Q x` and `P X` to get `Q X`.

~p.22:
(TODO)`=` is not defined until chapter 13, and this is being explained in chapter 2/chapter II.

~p.40:
- a nice counterexample to test a function P is well typed is to see if `P P` can be formed
- `P P` is also an example that `P` is *impossible* to be a value of `P`
- P with "all possible values" are called `significant`. Significant = "well typed"

~p.47, beginning of chapter II:
- `∀ x, Phi x` is considered as a function with `Phi` as one argument
- for `∀`, `Phi` can be a parameter but an individual `X` cannot be a parameter
- it is necesssary to make a distinction between passing in a `X` and passing in a `Phi`

~p.51:
- predicate: first order functions. Only takes individuals as parameters
- "Individual" is the best thing to instantiate a function's parameters
- (TODO)They are designed to be not propositions. Why?
- (TODO)Why we have to design the hierarchy for "functions" and "propositions " separately?

~p.127:
- Chapter II has explained that ~ and ∨ should have different meaning on different propositions. Guess: we cannot define a
negation on "all" propositions attributing to Russell's paradox

~p.128:
- Goal of ch9: focus on definition of `~` and `∨` defined in *1 - *5 limited to eprops. Extend their definitions to 1st orde props
- The support of `∀` and `∃` seems to be only for demonstration purpose - if we take them as primitive ideas, we can 
  conclude "upgraded" versions of propositions "just as in" ch1-5.
- the important parts seems to be *1.2 - *1.6; A new way is used for analogue of 1.7 - 1.72
- Real variables doesn't have types(??), and can be instantiated with any proposition of any orders???
- Summary:
  - elementary propositions are initially admitted, along with their types
  - definition of `~` and `∨` depends on proposition types
  - definition of function depends on type of `~` and `∨`
  - order of a proposition depends on its parameter's types

~p.138:
- Ch9 enables us to take `∀` propositions as parameters
- therefore we can have a better goal(?)
- Goal of ch10: focus on deducing 1-var functions from 
- "for example", `∃` is no longer a primitive idea which is different from ch9  
- several ch9 theorems are only taken because of their ability to reason for quantified propositions

~p.162:
- (TODO) propositions is defined in p.43. They are supposed to be incomplete symbols, but individuals are complete 
  so they are not propositions
- starting from chapter 12, all variables are either matrixes or individuals


## See Also
- https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html
- https://plato.stanford.edu/entries/pm-notation/
- https://en.wikipedia.org/wiki/Glossary_of_Principia_Mathematica
- https://randall-holmes.github.io/Drafts/notesonpm.pdf
- https://www.religion-online.org/article/the-axiomatic-matrix-of-whiteheads-process-and-reality/
- https://nap.nationalacademies.org/read/10866/chapter/66
- https://mathoverflow.net/questions/27793/russell-and-whiteheads-types-ramified-and-unramified