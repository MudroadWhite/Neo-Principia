# Mechanics of Principia Mathematica
## Basic setups
### How many types of statements are there in Principia?
Principia has 3 types(not mathematical type) of statements: `Pp`(primitive propositions), `Df`(definitions, usually definitions for new symbols) and `Thm`s(ordinary theorems). 

There are 3 hidden trait of statements in Principia, being written mostly in natural language. Some of these typing rules are `Pp`; while some of them might be `Thm`, being derived from some previous typing rules. Only some exceptions don't belong to these 3 traits, presented in chapter 1.
1. Typing a specific symbol, extending to more general cases
2. Extending *modus ponens* for a specific symbol
3. Extending *generalization* or *instantiation* for a specific symbol

### How to read the propositions in Principia?
Principia Mathematica uses Peano's *dot notation* just to eliminate the brackets. There are a lot of materials explaining how to understand the dot notation. In practice, Principia also sets up the indentation for propositions that have to be splitted into multiple lines, and their hints on priority, surprisingly, never go wrong. One can easily guess the priority, without knowing much about the dot notation.

Each proposition in PM is supposed to come with a type within a type hierarchy. Still, PM doesn't have a notion for types, nor will it explicitly label the hierarchy. PM proposes its typing algorithm as theorems of "what different terms can be considered *of the same type*". Such "of the same type" style definitions have been scattered into all the chapters.

### How does Principia define symbols?
Different from most of the textbooks, Principia defines its symbols in a **compositional way**. In contrast to *`¬ a` should be defined as something*, chapter 9 demonstrates, immediately, things like *`¬` applied on an `∃` proposition should be defined as something*. It's a common practice to fix one symbol and assign a function for its interpretation, but Principia usually involves 2 operators at a time. 

While not presented in this project, later chapters might suggest further complexities of such "composition". For example, Gregory Landini's [Note on Principia's *38 on Operations](https://mulpress.mcmaster.ca/russelljournal/article/download/5046/4059/17479) discusses a "female" symbol that abstract previous PM symbols at meta-level.

Principia also defines symbols in an **inheriting way**, as there are many hierarchies in PM system. From our limited knowledge prior to chapter 20, there are already 3 hierarchies existing in the text, plus 2 ad-hoc context from chapter 1 - 9 for easy definition. If one read from beginning to the end, he will occur to a lot of situation that "we can use our previous theorems in another way".

Above 2 natures of PM's definitions has a deep influence in our [tactics](./4_tactics.md)' design.

### How does Principia prove theorems?
Principia designs its theorems in a "**practical way**". Theorems in chapter 10 are being proposed, because they are needed in later chapters, not because they address important properties for first order logic, such as soundness and completeness. ~~We really don't need `1+1=2` in a lot of places.~~

Principia performs everything **one step at a time**. This automatically means functions in Principia are always "small-step". We don't need to concern things like free vs bounded variables to eliminate the ambiguity, because deduction takes one step at a time, and only when a guaranteed/hand-crafted candidate exist. Functions don't come with a scope, and an ad-hoc "scope" is defined for auxiliary purpose orthogonal to functions. See chapter 14 below.

During each steps of the proof, Principia **cites** the theorems and previous steps to perform the next deduction. They usually appeared in the form of `[*n1.m1 . *n2.m2]`. 

Context to prove theorems, like symbol definitions, have its **inheriting** nature. Theorems are proven in different context between different chapters. See [chapter 1](./3_mechanics.md/#chapter-1) for case in chapter 1 - 5, [chapter 9](./3_mechanics.md/#chapter-9) for case in chapter 9 - 11, [chapter 12](./3_mechanics.md/#chapter-12) for chapter 12 - 14, [chapter 20](./3_mechanics.md/#chapter-20) for beyond.

We now start exploring the main ideas for each chapters.

## Chapters
> "Still, considering the difficulty of the medium, some of the jokes are very good."
> -- [The final paragraph of G.H. Hardy's epic review of Russell & Whitehead's Principia Mathematica](https://x.com/davidbessis/status/1993059561381744863)

### Chapter 1
Principia Mathematica has made a pretty ambiguous description on what are *elementary propositions* and *elementary propositional functions*, so we still cannot define them. A detailed discussion of our attempt has been made in [propositions](./B_proposition.md).

Chapter 1 also presents some fundamental `Pp`s to set everything up, and we find `Pp`s usually suggest something just as meta in the Rocq system.

Implementation-wise, here are some ideas for definitions in chapter 1:
- Having something in our proof window means it has been asserted/implied true
- Asserting `H1 : P` means asserting `P` as an **elementary proposition**
- (\*1.1)If there is a rule saying that "if we can assert `H1` then we can assert `H2 : Q`", we are allowed to obtain `H2 : Q` in such a style. It could be happen if we are getting situations like `(|- P) → (|- Q)`(p.92), which doesn't occur within formulae in PM.
- Asserting an **elementary propositional function** means asserting `H1 : φ X`. It's strictly "not asserting a proposition"(p.18), but practically the same.
- (\*1.11)If `H2 : φ X → ψ X` can be implied, then we are allowed to imply `H3 : ψ X`.

Being the actual *modus ponens*, \*1.11 is said to be used almost everywhere, and \*1.1 is generally not used(p.93). For our implementation, we abstract all them away into a single tactic `MP`.

By proving a theorem, we mean:

|           Property          |      Limitation        |
|-----------------------------|------------------------|
| Highest proposition order   | Elementary proposition |
| Modus Ponens theorem        | Only \*1.11            |
| Generalization              | Not allowed            |
| Functions                   | Not allowed            |
| Introducing fresh variables | Not allowed            |
| Theorem variants\[\*\]      | Not allowed            |
| Function type               | Elementary function    |
| Function parameters         | Only E-propositions    |

\[\*\]: For the meaning of variants, see [tactics](./4_tactics.md/#polymorphism-and-the-variant-mechanic)

**Table 3.1: Proving context for chapter 1 - 5**

Note:
- (p.92)Not to confuse "not-p" in the "(2) Elementary propositional functions" with `¬ p`, where `¬` is symbolic negation and "not" is a made-up predicate in natural language
- (p.94)Definitional equality is undefined in PM
- Elementary functions are closed under `¬` and `∨`

### Chapter 2
While everything in chapter 1 are primitive propositions, chapter 2 starts to use them to construct some basic results. 

- For general rules on citation, see related paragraphs in [How does Principia prove theorems?](./3_mechanics.md/#how-does-principia-prove-theorems).
- In particular, `[(x)]` is a *citation* to a definition/primitive proposition*. `[x]` is a *citation* to a *theorem*. We can also cite previous steps.
- (p.103)For each proof stepping in the form of `[S1 . S2 . S3]`, it is suggested to somehow construct a sequence of modus ponens with `MP`s
- (p.105)For each citation chained up in the style of `|- P ([S1] →) Q ([S2 →] R ...)`, it is suggested to use syllogism to chain everything up with a syllogism tactic `Syll`
- Citations for modus ponens and syllogism will generally be omitted, and in our implementation we allow them to be alternate freely

### Chapter 3
Chapter 3 focuses on theorems about `∧`, which is constructed on `¬` and `∨`. 

### Chapter 4
Chapter 4 focuses on theorems about `↔`, turning most theorems bidirectional. They are useful in our implementation in that we can `rewrite` on them; see [tactics][4].

### Chapter 5
This chapter collects miscellaneous theorems of operators appeared in previous chapters, and is mostly provided because they are useful.

### Chapter 9
- **elementary functions** are dependent on **elementary propositions** (by generalizing individuals in them) and **elementary logical connectives**
- **1st order propositions** are dependent on **elementary functions** (by quantifying all of the function variables)

There's a lot of things happened in this chapter, making it significantly different from all the previous chapters. This is the first chapter where extra variables can appear during the proof, and we thereby introduce the `Intro` mechanic in [tactics][4] to patch up. 

To understand what chapter 9 does, we first look back at \*1.3:

```Rocq
Theorem Add1_3 (P Q : Prop) : Q → P ∨ Q.
```

In chapter 9, it is corresponded to the following cases:

```Rocq
Theorem n9_32 (φ : Prop → Prop) (Q : Prop) : Q → (∀ x, φ x) ∨ Q.
Theorem n9_33 (φ : Prop → Prop) (Q : Prop) : Q → (∃ x, φ x) ∨ Q.
Theorem n9_34 (φ : Prop → Prop) (P : Prop) : (∀ x, φ x) → P ∨ (∀ x, φ x).
Theorem n9_35 (φ : Prop → Prop) (P : Prop) : (∃ x, φ x) → P ∨ (∃ x, φ x).
```

Theorems in chapter 9 wants to prove that we can replace a *subpart* of a theorem in *chapter 1* to its `∀`/`∃` version. It is brutally performed without using mathematical induction, since it is not allowed yet. It further constitutes to the following reasoning:

- (p.128)If our *elementary* operators `¬` and `∨` is "enhanced"(p.128) to allow to take one 1-order proposition as its operand
- Then we can deduce 1-order theorems for chapter 1
- Therefore, we are allowed to have first-order `¬` and `∨`s.

Which is why in chapter 10, we can use first-order operators by default.

Propositions in chapter 9 starts to make a rough distinction between *elementary proposition*s and *1st order proposition*s, and the transition is being made through
- Generalization: the main technique to turn a *propositional function* into an *proposition* of higher order
- Instantiation: the reverse transformation of generalization
- *Individual*s: a placeholder, a very specific value, an unnamed constant, for a propositional function to be generalized into a proposition, or vice versa; they might themselves be functions when lifted to higher order.

Every `∀ x` is naturally taking just a `x`, not something like `∀ (x ∧ x)`. In this sense we are saying that `∀`, `∃` and more generally all *propositions*, *apparent variable*s only take *individual*s(the sole `x`) as their possible values(p.52, p.162), which is a useful and natural feature that is still considered in later chapters.

\*9.131, which I call it "of the same type algorithm", is a mixture of multiple aspects. It contains a [polymorphic typing algorithm](https://randall-holmes.github.io/Drafts/pm-no-compromise.pdf), plus a convention for individuals. All individuals in a theorem, which are not propositions(cannot be asserted and can only appear just like variables) nor functions(p.51, p.132), *will have the same (lowest possible)propositional order* within a theorem, and to be more exact, *have exactly the same proposition type*. 

The rest of the text is the typing algorithm for propositions and functions. Note that this typing algorithm can prevent constructions such as `P P`(p.40):
|          Notion          | Type name | Arguments                    | Identification rule                            |
|--------------------------|-----------|------------------------------|------------------------------------------------|
| Elementary proposition   | EProp     | None                         | All elementary propositions                    |
| Elementary function      | EFunc     | Types of function parameters | Connectives on same functions                  |
| Proposition of nth order | Prop n    | Type of the function\[\*\]   | `¬` on same type propositions; generalization on same type functions of 1 argument; generalization on 2nd argument of same type functions of 2 argument |
| Others                   | _         | _                            | Scattered through each chapters. e.g. \*11.311 |

**Table 3.2: "of the same type" algorithm from chapter 9**

- \[\*\] Functions of same order can have different types, thus propositions of same order can have different types. However, this is "practically ignored"(p.162). If we want to meet the practice, we can fix the definition to "returning order of the function".
- Additionally, several clarifications on terms: 
  - connectives : `¬` and `∨`
  - same: same propositions/functions are same in number of argument, and each argument have the same type on that index; additionally, they are usually 1-order lower to the proposition/function being constructed
  - other typing rules: usually consist of varied aspects to type on: how to type a new symbol; how to type a function with more arguments from function with less arguments, and so on

By proving a theorem in chapter 9 - 11, we mean:
|           Property          |          Limitation         |
|-----------------------------|-----------------------------|
| Highest proposition order   | 1st order proposition\[\*\] |
| Modus Ponens theorem        | Arbitrary(p.128)            |
| Generalization              | Allowed for E-props         |
| Functions                   | 1st order                   |
| Introducing fresh variables | Allowed for E-props         |
| Theorem variants            | Not allowed                 |
| Function type               | Untyped\[\*\*\]             |
| Function parameters         | <= 1 order propositions     |

**Table 3.3: Proving context for chapter 9 - 11**

- **\[\*\]**: Several propositions in the beginning of chapter 9 is still limited to elementary propositions(also see chapter II of the book). All real variables in the theorems can be given arbitrary orders after chapter 11(p.127, p.128, discussion on typing `¬` and `∨`)
- **\[\*\*\]**: Whether it is typed depends on how they are used in later chapter, and I'm still not sure about this

### Chapter 10
In contrast to "what will be when `∨` is applied to different propositions", `∀` and `∃` are immediately allowed to be appeared in any positions of these two logic connectives(1-order only). The primitive proposition for `∀` and `∃` is therefore only one primitive proposition, stating how `∃` is defined(p.138), and the `∨` and `¬` in this chapter is e-prop version anymore, but the actual 1-order propositions. With different primitive propositions assumed, some of chapter 10 theorems are actually deriving the chapter 9 primitive propositions as theorems, for example, \*10.12. Similarly, the `of same type` statement in chapter 10 is being obtained by showing the strength of the new primitive proposition is just the same as the chapter 9 ones.(\*10.221)

### Chapter 11
Chapter 11's main purpose is extending functions with 1 variables to 2 variables, and by repeating such construction, we can get functions of arbitrary variables. This chapter also provides its own version of *modus ponens* for functions with 2 arguments.

### Chapter 12
Chapter 12 starts to bring awareness to the rigorous and complete hierarchy of *orders* and this is also the first chapter that we're going to think something like "so these theorems have more than one ways to use them"(p.163, "It *will* be seen that..."). 

The consideration for the hierarchy starts with *matrices* for generating *functions*, where the *function*'s definition has been changed(and both the old and new meaning of "function" is used mutually in the text!) - they become what expressions generated by a matrix. (p.164)1-order matrix retains the complete power as an elementary function under this hierarchy.

```Rocq
(* (p.163)This is a matrix with 2 real variables. It's also a function, and it's even predicative. *lhs* parameter of this definition is now in serious consideration *)
Example example_matrix (X : Prop) (φ : Prop → Prop) := φ X.

(* This is a function with 1 real variable and 1 apparent variable. It's not a matrix *)
Example example_function_1 (φ : Prop → Prop) := ∀ (x : Prop), φ x.

(* This is another function with 1 real variable and 1 apparent variable. It has a different type from the previous function *)
Example example_function_2 (X : Prop) := ∀ (φ : Prop → Prop), φ X.

(* This is a proposition with 2 apparent variables. It is *not* a function anymore *)
Example example_proposition := ∀ (x : Prop) (φ : Prop → Prop), φ x.
```

- **Predicative function** is synonym to **matrices**(p.164), after this chapter. Predicative function of `a` where `a`'s order is n, though, strictly refers to a matrix of order n+1.
- **Matrices** are built on **matrices** of a 1-level lower order.
- **Functions** are built on **matrices**, with *not all* of its variables generalized(p.14)
- **Propositions** are built on **matrices**, with *all* possible variables generalized

Several comments on matrices and functions:
1. (p.52)Same the the treatment in [chapter 9](./3_mechanics.md/#chapter-9), matrix only takes matrices or individuals as variables
2. Order of functions are not dependent on order of arguments(p.164, also p.49 for difference between `fun x => φ x` and `fun x => ∀ φ, φ x`)
3. It appears that any `∀`s and any `∃`, under this hierarchy, cannot be produced by directly instantiating some functions; we have to start from completely constructing a matrix, then obtain all the quantifiers through generalizing individuals/other matrices with a controlled scope. Sometimes it will block us from, for example, perform generalization by instantiating on a *function* - which is not a *matrix*. Also see [tactics][4] and the 4th comment below.
4. (p.163) has given functions that we can generate from a matrix, of which including 2-order-higher function corresponded to a variable `x`. These examples are not derived from certain specific theorems, and are just demonstrated as eligible candidates. But in short, if we can construct a n-order matrix related to a variable `x`, we can almost immediately obtain a n-order function for variable `x`.

There is another way to understand the difference between a matrix and a proposition, by identifying their apparent and real variables(p.18). One crucial difference between real and apparent variables, is that real variables are not given types(p.128, "in practical purpose") while apparent variables are given types.

*Axiom of Reducibility* is introduced in this chapter for 2 reasons:
1. (p.49)When we define `x = y` as `∀ φ, φ x → φ y`, assuming it is untyped, we might still have `φ := fun x => (∀ φ, φ x → φ y)` or `φ := fun y => ∀ φ, φ x → φ y`. In other words for `fun x => φ x`, `fun x => (∀ φ, φ x → φ a)` has been a value that needs to be avoided. 
2. On the other hand, sometimes we want to speak of as "many" functions as we can. It turns out that, while we cannot precisely say all functions of a parameter `a`, but we can say all `n`-order functions of a parameter `a` and set `n` to infinity.

For 2 above, axiom of reducibility says that: when we want to have a very large "all" function `fun a => φ a` with `φ` of order `n`, we can simulate with a predicate function `fun a => ψ a`. The predicativity of `ψ` here means it is just 1-order higher than `a`, and we are assuming *this `ψ` exists*. In the context of [chapter 13](./3_mechanics.md/#chapter-13), we can have a more intuitive understanding.

Chapter 12 also brings the symbol `!` to awareness, and will be frequently used in later chapters. `!` has several different meanings all within the same time:
1. Emphasize(p.163, the second "It will be seen that...") that we might consider both the function and its parameter as variables for an expression. The purpose is to make functions as variables easier for people to recognize.
2. Indicate that the function is a *predicative function*, not a random untyped one.

By proving a theorem, we mean,
|           Property          |                Limitation             |
|-----------------------------|---------------------------------------|
| Highest proposition order   | Arbitrary                             |
| Modus Ponens theorem        | Arbitrary                             |
| Generalization              | Predicative functions(p.165)          |
| Functions                   | Arbitrary                             |
| Introducing fresh variables | Arbitrary                             |
| Theorem variants            | Arbitrary                             |
| Function type               | Can be untyped\[\*\]                  |
| Function parameters         | Only individuals and matrices\[\*\*\] |

- **\[\*\]**: Untyped functions take a parameter and return a proposition of *unknown* order.
- **\[\*\*\]**: See (p.52, 162, 163, 164).

**Table 3.4: Proving context for chapter 12 - 14**

- Not all symbols in an expression needs to be identified as variables. They can be **constants**(p.164). However we utilize the convenience of Rocq to ignore such requirement.
- For the hierarchy in this chapter, we have implemented a `Order` type. See [tactics](./4_tactics.md/#polymorphism-and-the-variant-mechanic).

### Chapter 13
In Rocq, we have different types for `=`. We can have `=` on propositions, `=` on `=` between propositions, `=` on `=`... and so on. Russell realized that he should give the `=` a similar treatment, but the hierarchy is slightly different: `=` is itself treated as a propositional function, and `=` can be an identity on 1st order, second order, ... arbitrary order functions. The first citation of chapter 12's axiom of reducibility appears at \*13.101, and with which applied to \*13.101, the order of `=` has been generally collapsed off. 

The identity has to be defined at such a late chapter(p.22), because:
1. Identity is built on functions
2. Functions comes with different types within the hierarchy defined in chapter 12
3. Axiom of Reducibility has to be used in the proof, also because of the hierarchy. Also see (p.57) for a informal reasoning on why it needs to be used

### Chapter 14
This chapter begins with a significantly complicated symbol `(ιx)(φx)` to denote a *description*. Here are the reasons why this symbol is such complicated:
- `(ιx)` means the descriptions should be treated as the same type of a `x`. In chapter 20, `x` will be lifted to some random `α` denoting classes
- `(φx)` means the description should describe a thing just like `φx`

This "incomplete symbol"(p.67) comes with an explicit "scope" notion, also implicitly required for symbols later chapters. For the scope, we find Rocq's *lambda calculus* the perfect candidate for such a restriction. Since `ι` will also apply to new symbols in later chapters such as *class* in chapter 20, we design `ι`, and in general symbols defined with `Notation` to be *polymorphic*. See related parts in [chapter 20](./3_mechanics.md/#chapter-20) and [tactics](./4_tactics.md/#polymorphism-and-the-variant-mechanic).

### Chapter 20
Definition of class in this chapter, at first glance, appears to be pretty obscure. It is not being stated clearly like a structure, and instead, how is it defined is written *in the middle of the text*. An extra difficulty at understanding its definition is its similarity to the definition of a function `Psi x^`. Both class and function(actually, its first appearance at \*20.59) have been presented in this chapter's theorems.

Next, we are taking some canonical theorems in chapter 20 to address several important points to help understanding this chapter. First we unfold the definition of \*20.02(p.188). 
1. `x∈(z^φz)` is a function of `φ`
2. If we pick this function as the `f` in \*20.01, we obtain `x∈(z^ψz) = ∃φ, φ z <[- z -]> ψ z ∧ (x ∈ φ)`. The `x` at the rightmost cannot be renamed into anything else because it is the `x` defined in the "function" we are using.
3. In this form, we "patch" the expression with \*20.02, matching exactly the rightmost sub expression, and rewriting the whole expression into `x∈(z^ψz) = ∃φ, φ z <[- z -]> ψ z ∧ φ x`, and then make a slight reordering.

Analyzing on how this proof applies also reveals more insights on how should we design PM symbols in Rocq: we don't just want a valid representation of `Class` as `^z => Phi z`, we also want it to work with all other necessary symbols smoothly. This resulted into several **failed** attempts previously made to define the type for `Class`. Suppose we want to build class on a function `A → Prop`, below are failed attempts:
- Define `Class` only using functions
- Define `Class` as `(A, Phi)`
- Define `Class` as inductive type. 

In practice, defining `Class` with record can make the function it holds *implicit*, while exposing and extracting `A` peacefully. Our current definition resulted in theorems demanding `let` clause at the beginning of the proof; but soon we find out that if we design parsing and printing notations separately(see `only printing` code in `ch20.v`), we can pertain a good notation. 

However, there turns out to be more issues with class notation. Here we will list out the rest we have found:
- To make the symbols work with each other, we eventually developed a design principle called "monomorphic theorems, polymorphic symbols". See [tactics][4].
- Even with our notation definition, our notation doesn't prevent several *illegal* construction cases. See [style guide](./contribution_guide/style_guide.md).
- Class is generally missing a lot of things for dealing with the *scope*s. See [audit](./5_audit.md) for an analysis.
- Also, class is a good example that Russell doesn't make a clear distinction between language and its interpretation, so that we need to design a mechanic of *explicit interpretation*. See [tactics][4].

While not being stated explicitly, being mentioned in previous chapter(p.165), class, relations, etc. constitute to a "more convenient" new hierarchy. This is because theorems in this chapter has prepared a lot of aspects for class, including its equivalent for Axiom of Reducibility. It doesn't, though, provide insights such as "what is the equivalent of matrix to class?" and so on. That being said,

|           Property          |                Limitation             |
|-----------------------------|---------------------------------------|
| Highest proposition order   | Arbitrary + class?                    |
| Modus Ponens theorem        | Arbitrary                             |
| Generalization              | Predicative functions + class         |
| Functions                   | Arbitrary + class?                    |
| Introducing fresh variables | Arbitrary + class?                    |
| Theorem variants            | Arbitrary + class                     |
| Function type               | Can be untyped                        |
| Function parameters         | Individuals, matrices and classes     |

**Table 3.5: Proving context for chapter 20 - \***

[RTT]: https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT
[4]: ./4_tactics.md
