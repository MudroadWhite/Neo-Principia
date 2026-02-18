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

The way that a theorem is being proven and being used are different between each of the chapters. See \[Chapter 1\](TODO: CORRECT HYPERLINK) for how they are used in chapter 1 - 5, \[Chapter 9\] for how they are used in chapter 9 - 11, and \[Chapter 12\] for how they are used from chapter 12 and beyond.

### Chapter 1
TODO: 
- check why the statement is true: individuals are not propositions- 
- the mechanics of registration: if we have proven something is safe to use, we're supposed to extend the original symbols to new field, e.g. definition of ¬ and ∨
- TODO: find a place to write in chapter 1: *elementary propositions* are simple propositions connected with `¬` and `∨`; relate elementary propositions to those in chapter 9 - chapter 9 adds *matrices* in addition of e-props for substitutions
- TODO: check how PM uses different sets of symbols/letters to represent constants, matrices, etc..

### Chapter 2

### Chapter 3

### Chapter 4

### Chapter 5

### Chapter 9
```Rocq
(* This is a matrix with 2 real variables. It is also a function *)
Definition example_matrix (X Y : Prop) := X /\ Y.

(* This is a function with 1 real variable and 1 apparent variable *)
Definition example_function (X : Prop) := forall (y : Prop), X /\ y.

(* This is a proposition with 2 apparent variables. It is *not* a function anymore *)
Definition example_proposition := forall (x y : Prop), x /\ y.
```

- **Matrices**(the actual "functions") are exactly **predicative functions**.
- **Matrices** are built on **propositions** with a 1-level lower order(TODO: make a clear distinction between types). See \[chapter 12\] below for a serious consideration on orders
- (Propositional) **functions** are built on **matrices**, with *some*(but not all) of its variables quantified
- (Quantified) **propositions** are built on **matrices**, with *all* possible variables quantified

This chapter starts to bring awareness to *matrices* and *functions*, where both of them are quite not the same to what people will acknowledge nowadays. Although they are coming to consideration, their full definition starts from chapter 12, so our explanation will also cite the text in chapter 12 for reference.

The typical "lambda-calculus-like" functions in PM is called a *matrix*, but we don't even have the `lambda x` part(aka the parameter list) to figure out what are the parameters. For a matrix, all greek/english letters appeared are parameters. There is a synonym for matrix: *predicative functions*(p.164).

*Functions* are matrices themselves, *plus* some(not all) of the variables of a matrix quantified(`forall`, `exists`). In chapter 9, there has been a notation for matrices, but never used anywhere else(TODO: check if this is actually correct and cite the part): the hat operator `^` denoting exactly turning a proposition into a matrix. 

There is another way to understand the difference between a matrix and a proposition, by identifying their apparent and real variables, being explained way more clearer in the original text. *Is it real that the distinction between apparent and real variables are unnecessary*, as Wittgenstein said\[CITATION NEEDED\]? We don't really know, but just see the example at the beginning of this section.

Examples of *matrices* are given in \[CITATION NEEDED: cite ch12, and find other occurences in intro & chapter 1-5 \], taking different types of variables as their arguments. 

Theorems from chapter 9 to chapter 11 are proven in a different way against theorems starting from chapter 12 and beyond. For the general case, see [chapter 12] below. By proving a theorem, we mean(TDO: refine the statement):

- Parameters for a theorem are all the letters appeared in the theorem, similar to how a function is expressed
- We only prove the case where parameters for theorems are individuals (plus elementary matrices just as the "normal functions" of people's common sense)
- If such a elementary proposition/first order "proposition"(TODO: check if this is written correctly) can be proven true, we conclude the truth of such a theorem
- When we want to use a theorem somewhere, we are allowed to replace the individuals or the matrices with arbitrary elementary propositions or elementary matrices

### Chapter 10
TODO: actual alternative;

### Chapter 11
TODO: generalize formal props

### Chapter 12
Starting from chapter 12, a rigorous hierarchy of *orders* begins to be taken into consideration, and this is also the first chapter that we're going to think something like "so these theorems have more than one ways to use them"\[CITATION NEEDED\].

TODO:
- Theorems in chapter 1 - 11 can be reused by replacing individuals into some n-order-matrices and elementary matrices into some n+1-order matrices
- discuss the volatility for formalization of AoR
- discuss the `!` operator: it doesn't consider the absolute order level but it fixes the relative level to +1; for convinience should we only start with individuals?
- a individual can have a 2nd order function - discuss how should we understand a function of +n types to a parameter

### Chapter 13
TODO: just an identity; discuss how it might use definition in ch12; state the utilization of `pred` variants

### Chapter 14
TODO: this is the last chapter where actual mechanics matters: the first chapter where we introduce *contextual definitions*, modeled with *notations* in Rocq. all future concept might be built either on normal or on contextual definitions, and they should be never interfere with the fundamentals for the rewriting system; but maybe in the future we might regard all the definitions as a whole and make a clearer distinction between the rewriting system, maybe until the presence of natural numbers

### Chapter 20
TODO: ambiguity on the interpretation for `Phi ! x` where we don't know if `!` stands for predicate or just the function as the focus
