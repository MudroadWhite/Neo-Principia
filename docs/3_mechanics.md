# Mechanics of Principia Mathematica
## Basic setups
### How many types of propositions are there in Principia?
Principia has 3 types(not mathematical type) of propositions: `Pp`(primitive propositions), `Df`(definitions, usually definitions for new symbols) and `Thm`s(ordinary theorems). 

A hidden trait of proposition in Principia is those propositions written in natural language. With only some exceptions in chapter 1, most of them are about typing a specific symbol. Some of these typing rules are `Pp`; while some of them might be `Thm`, being derived from some previous typing rules.

### How to read the propositions in Principia?
Principia Mathematica uses Peano's *dot notation* just to eliminate the brackets. There are a lot of materials explaining how to understand the dot notation. In practice, Principia also sets up the indentation for propositions that have to be splitted into multiple lines, and their hints on priority, surprisingly, never go wrong. One can understand the priority, without knowing much on dot notations.

Each propositions in PM is supposed to come with a type, and the types form a hierarchy. Still,  PM doesn't express the hierarchy directly. PM's typing rules say "what different terms can be considered as the same type". Such "of the same type" style definitions have been scattered into all the chapters.

### How does Principia define symbols?
Different from most of the textbooks, Principia defines its symbols in a **compositional way**. In contrast to *`¬ a` should be defined as something*, chapter 9 demonstrates, immediately, things like *`¬` applied on an `∃` proposition should be defined as something*. It's a common practice to fix one symbol and assign a function for its interpretation, but Principia usually involves 2 operators at a time. 

Principia also defines symbols in an **inheriting way**. Propositions in a chapter "will be used in different ways" for later chapters. For example: 
1. In an early chapter, we define what is an *animal*, and write down theorems about it.
1. In a later chapter, we divide *animal*s into *dog*s and *cat*s.
2. To prove a theorem in later chapter, we directly reuse *animal* theorems instead of reinventing their analogues in *dog*s and *cat*s.

### How does Principia prove theorems?
Principia designs its theorems in a "**practical way**". Theorems in chapter 10 are being proposed, because they are needed in later chapters, not because they address important properties for first order logic, such as soundness and completeness. ~~We really don't need `1+1=2` in a lot of places.~~

Principia performs everything **one step at a time**. This automatically means functions in Principia are always "small-step". We don't need to concern things like free vs bounded variables to eliminate the ambiguity, because deduction takes one step at a time, and only when a guaranteed/hand-crafted candidate exist. Functions don't come with a scope, and an ad-hoc "scope" is defined for auxiliary purpose orthogonal to functions. See chapter 14 below.

During each steps of the proof, Principia **cites** the theorems and previous steps to perform the next deduction. They usually appeared in the form of `[*n1.m1 . *n2.m2]`. 

Context to prove theorems, like symbol definitions, have its **inheriting** nature. Theorems are proven in different context between different chapters. See [chapter 1](./3_mechanics.md/#chapter-1) for case in chapter 1 - 5, [chapter 9](./3_mechanics.md/#chapter-9) for case in chapter 9 - 11, [chapter 12](./3_mechanics.md/#chapter-12) for chapter 12 - 14, [chapter 20](./3_mechanics.md/#chapter-20) for beyond.

TODO: put the following in either `audit` or `suggestion`. Make a 1-sentence reference here
### What are the real problems to formalize Principia Mathematica?
With *reconstruct every theorems in PM as much as we can* as our assumption, our implementation is facing awareness to *how well does symbols of PM work with each other*. This means to the following:
1. Can we design the correct type system for PM, since PM doesn't explicitly type the propositions?
2. Can we distinguish different contexts for theorems in different chapters, since their validity is proven in different context?
3. Can we design a set of notations that can work well altogether?
4. For current implementation, can we give correct types to parameters? For example, is it really that function's type should be just `Prop -> Prop`, when the difference between untyped functions and predicative functions become more and more significant in later chapters?

Problems arisen from the assumption can be alleviated by some other reconstruction; see [Randall's](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT) suggestion on alternative symbols. These problems will not be discussed in this chapter, but can be inferred from analysis in [audit](./5_audit.md).

We now start exploring the main ideas for each chapters.

## Chapters
### Chapter 1
Chapter 1 presents some basic `Pp`s to set everything up, and practically speaking, we find it out that `Pp`s usually suggest something just as meta in the Rocq system: for PM's *modus ponens* to work, we will have to implement a *MP* tactic in Rocq. 

- Having something in our proof window means it has been asserted/implied true
- Asserting `H1 : P` means asserting `P` as an **elementary proposition**
- (\*1.1)If there is a rule saying that "if we can assert `H1` then we can assert `H2 : Q`", we are allowed to obtain `H2 : Q` in such a style. It could be happen if we are getting situations like `(|- P) -> (|- Q)`(p.92), which doesn't occur within formulae in PM.

There are no theorems depending on \*1.1 explicitly stated in PM.

In chapter 1 we also have a rough idea on how to denote a (elementary) *propositional function*. Such kind of simple denotation will be changed into something else in later chapters. In chapter 1-5, most propositional functions don't come barely themselves - their values for variables are somehow "fixed" already during all the inference, where `φ X` and `φ Y` does not mean the same thing(p.19).

```Rocq
(* This is an elementary proposition *)
Example example_ch1_proposition (X : Prop) := X.

(* This is an asserted elementary function value *)
Example example_ch1_prop_function_1 (φ : Prop) (X : Prop) := φ X.

(* This is the actual way to write the function, but we won't use it *)
Example example_ch1_prop_function_2 (φ : Prop) := fun (X : Prop) => φ X.
```
- Asserting an (elementary) **propositional function** means asserting `H1 : φ X`.
- (\*1.11)If `H2 : φ X → ψ X` can be implied, then we are allowed to imply `H3 : ψ X`.
- We use \*1.11 almost everywhere in PM, and \*1.1 is generally not used, see (p.93). Most judgments in PM are assertions on propositional functions.

\*1.11 will come to more significance after [chapter 9](./3_mechanics.md/#chapter-9).

`H1 : φ X` above should refer to something like `H1: (fun x => x ∧ x) X` in the proof window, but this doesn't appear in our implementation as we will mostly have simplified it away. By asserting a function, we don't assert `φ` solely(p.92) and we're still asserting a proposition. 

*What is a function in PM?* When it says something like "function X", it actually means "a function's *body* X, whose parameters are all symbols appeared within". If I say "function x ∧ y", it actually means `(fun x y => x ∧ y)` for Rocq's representation. The same applies to most theorems in PM. All PM function's variables are not bounded and occurring freely. Another way to see a function in PM is like it doesn't have the currying in typical FPs, but more like the function in C language where you have to pass in all parameters at once.

- (p.94)Definitional equality is undefined in PM
- **elementary propositions** are closed under `¬` and `∨`
- **elementary functions** are closed under `¬` and `∨`

By proving a theorem, we mean:
|           Property          |      Limitation        |
|-----------------------------|------------------------|
| Highest proposition order   | Elementary proposition |
| Modus Ponens theorem        | Only \*1.11            |
| Generalization              | Not allowed            |
| Functions                   | Not allowed            |
| Introducing fresh variables | Not allowed            |
| Theorem variants            | Not allowed            |
| Function type               | Elementary function    |
| Function parameters         | Only individuals       |

(p.92)Note: not to confuse "not-p" in the "(2) Elementary propositional functions" with `¬ p`, where `¬` is symbolic negation and "not" is a made-up predicate in natural language.

### Chapter 2
While everything in chapter 1 are primitive propositions, chapter 2 starts to use them to construct some basic results. 

- For general rules on citation, see related paragraphs in [How does Principia proof theorems?](./3_mechanics.md/#how-does-principia-proof-theorems).
- In particular, `[(x)]` is a *citation* to a definition/primitive proposition*. `[x]` is a *citation* to a *theorem*. We can also cite previous steps.
- Citations for modus ponens and syllogism will generally be omitted.

TODO: 
- distinguish between when to use MP and when to use Syll

### Chapter 3
Chapter 3 focuses on theorems about `∧`, which is constructed on `¬` and `∨`. In particular, \*3.03 allows us to immediately get `H3 : A ∧ B` if we have `H1 : A` and `H2 : B` in the proof window.

### Chapter 4
Chapter 4 focuses on theorems about `↔`, turning most theorems bidirectional. They are useful in our implementation in that we can `rewrite` on them; see [tactics](./4_tactics.md).

### Chapter 5
This chapter collects miscellaneous theorems of operators appeared in previous chapters, and is mostly proven because they are useful.

### Chapter 9
Propositions in this chapter starts to make a distinction between *elementary proposition*s and *1st order proposition*s, and the transition is being made through
- Generalization: the main technique to turn a *elementary proposition* into an *elementary function*
- *Individual*s: a placeholder, a very specific value, an unnamed constant, for a proposition to be generalized into a function or to assert a function during the proof. Sometimes individual seems to just mean something that we cannot further destructed in current denotation, whether it is a proposition, function or matrix(see [chapter 12](./3_mechanics.md/#chapter-12)). *These meanings are used mutually throughout the text.*

This chapter presents the only way for 1st order propositions to be constructed: generalizing from *elementary functions*. Combining with [chapter 1](./3_mechanics.md/#chapter-1) we are getting the following rules:

- **elementary propositions** are dependent on `¬` and `∨` (we cannot have `¬`s taking higher order propositions to break the type)
- **elementary functions** are dependent on **elementary propositions** (by generalizing individuals in them)
- **1st order propositions** are dependent on **elementary functions** (by quantifying all of the function variables)

There's a lot of things happening in the beginning of chapter 9.
- First of all \*1.1 and \*1.11 has assumed their version for **1st order propositions**(p.128)
- Then first few `Pp`s in chapter 9 are supposed to restricted to e-prop `¬` and `∨`(discussed in Chapter II, they are not 1-order `¬` and `∨`). 
- After we have demonstrated that they work just fine on `∃` as well, we can lift e-prop `¬` and `∨` to 1-order ones
- Then we have \*9.12 being the actual *modus ponens* synthesizing \*1.11.

Every `∀ x` is naturally taking just a `x`, not something like `∀ (x ∧ x)`. In this sense we are saying that `∀`, `∃` and more generally all *propositions*, *apparent variable*s only take *individual*s(the sole `x`) as their possible values(p.162), which is a useful and natural feature that is still considered in later chapters.

\*9.131, which I call it "of the same type algorithm", is a mixture of multiple aspects. It contains a [polymorphic typing algorithm](https://randall-holmes.github.io/Drafts/pm-no-compromise.pdf), plus it sets up a convention for individuals. Individuals are the propositional variables constituted to the expression of a proposition. They are not propositions nor functions(p.51, p.132). *All individuals will have the same (lowest possible)propositional order* within a theorem, and to be more exact, *have exactly the same proposition type*. 

The rest of the text is the typing algorithm for propositions and functions. Note that this typing algorithm can prevent constructions such as `P P`(p.40):


|        Element name      | Type name | Arguments                    | Identification rule                            |
|--------------------------|-----------|------------------------------|------------------------------------------------|
| Elementary proposition   | EProp     | None                         | All elementary propositions                    |
| Elementary function      | EFunc     | types of function parameters | Connectives on same functions                  |
| Proposition of nth order | Prop n    | type of the function \[\*\]  | `¬` on same type propositions; generalization on same type functions of 1 argument; generalization on 2nd argument of same type functions of 2 argument |
| Others                   | _         | _                            | Scattered through each chapters. e.g. \*11.311 |

**Table X: "of the same type" algorithm from chapter 9**

Within which several terms need some clarifications: 
- connectives : `¬` and `∨`
- same: same propositions/functions are same in number of argument, and each argument have the same type on that index; additionally, they are usually 1-order lower to the proposition/function being constructed
- other typing rules: usually consist of varied aspects to type on: how to type a new symbol; how to type a function with more arguments from function with less arguments, and so on

By proving a theorem in chapter 9 - 11, we mean:
|           Property          |          Limitation         |
|-----------------------------|-----------------------------|
| Highest proposition order   | 1st order proposition\[\*\] |
| Modus Ponens theorem        | Arbitrary                   |
| Generalization              | Allowed for E-props         |
| Functions                   | 1st order                   |
| Introducing fresh variables | Allowed for E-props         |
| Theorem variants            | Not allowed                 |
| Function type               | Untyped\[\*\*\]             |
| Function parameters         | <= 1 order                  |

**Table X: Proving context for chapter 9 - 11**

- **\[\*\]**: Several propositions in the beginning of chapter 9 is still limited to elementary propositions
- **\[\*\*\]**: Whether it is typed depends on how they are used in later chapter, and I'm still not sure about this

TODO: 
- All real variables in the theorems can be given arbitrary orders after chapter 11(p.127, p.128, discussion on typing `¬` and `∨`)
- can we generalize for functions?

Chapter 9's theorems are furthermore splitted into 2 parts for different purposes:
- Theorems written in natural language define the typing algorithm: what is a type, what parameters are functions allowed to take by the regulation of types. Eventually we prove that we can construct all possible functions for 1-higher order.
- Theorems written as formulae makes a *demonstration*: if our elementary propositional `¬` and `∨` is "enhanced" so that it can take one 1-order proposition as its operand, deduced theorems can extend all theorems in chapter 1 - 5 to their 1-higher order version. It could be done with mathematical induction, but we were out of the assumption for induction to work so we brute force everything.

### Chapter 10
In contrast to "what will be when `∨` is applied to different propositions", `∀` and `∃` are immediately allowed to be appeared in any positions of these two logic connectives(1-order only). The primitive proposition for `∀` and `∃` is therefore only one primitive proposition, stating how `∃` is defined(p.138), and the `∨` and `¬` in this chapter is e-prop version anymore, but the actual 1-order propositions. With different primitive propositions assumed, some of chapter 10 theorems are actually deriving the chapter 9 primitive propositions as theorems, for example, \*10.12. Similarly, the `of same type` statement in chapter 10 is being obtained by showing the strength of the new primitive proposition is just the same as the chapter 9 ones.(\*10.221)

### Chapter 11
Chapter 11's main purpose is extending functions with 1 variables to 2 variables, and by repeating such construction, we can get functions of arbitrary variables. This chapter also provides its own version of *modus ponens* for functions with 2 arguments.

### Chapter 12
Chapter 12 starts to bring awareness to the rigorous and complete hierarchy of *orders* and this is also the first chapter that we're going to think something like "so these theorems have more than one ways to use them"(p.163, "It *will* be seen that..."). 

The consideration for the hierarchy starts with *matrices* for generating *functions*, where the *function*'s definition has been changed(and both the old and new meaning of "function" is used mutually in the text!) - they are what expressions generated by a matrix. (p.164)1-order matrix retains the complete power as an elementary function under this hierarchy(Personal question: does this claim also hold for n-order matrices?).

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
1. (p.52)Matrix only takes matrices or individuals as variables. By "taking something as variable", we mean what symbols can be appeared in the `A` of the `∀ A` part, *before any instantiations*. Variables of the form `∀ (∃ a, φ a), (∃ a, φ a) x` seems to be out of consideration, which is some n-order function or proposition; also see (p.53). Note that we won't have this issue in previous chapters prior to the definition of matrix, and functions can take (elementary)propositions as parameters. Conversely, elementary propositions in this hierarchy is called elementary matrices. 
2. Order of functions are not dependent on order of arguments(p.164, also p.49 for difference between `fun x => φ x` and `fun x => ∀ φ, φ x`)
3. It appears that any `∀`s and any `∃`, under this hierarchy, cannot be produced by directly instantiating some functions; we have to start from completely constructing a matrix, then obtain all the quantifiers through generalizing individuals/other matrices with a controlled scope. The procedure here is clearly unnatural.

There is another way to understand the difference between a matrix and a proposition, by identifying their apparent and real variables(p.18). Is it really that *there are no propositions containing real variables*, as [Wittgenstein](https://wittgensteinproject.org/w/index.php/Notes_on_Logic) have said? We don't really know, but let's just vibe with the [examples](./3_mechanics.md/#chapter-12). One crucial difference between real and apparent variables, though, is that real variables are not given types(p.128, "in practical purpose") while apparent variables are given types.

Axiom of Reducibility is introduced in this chapter for 2 reasons:
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

**\[\*\]**: Untyped functions take a parameter and return a proposition of *unknown* order.
**\[\*\*\]**: See (p.52, 162, 163, 164).

In addition, not all symbols in an expression needs to be identified as variables. They can be **constants**(p.164). However we utilize the convenience of Rocq to ignore such requirement.

### Chapter 13
In Rocq, we have different types for `=`. We can have `=` on propositions, `=` on `=` between propositions, `=` on `=`... and so on. Russell realized that he should give the `=` a similar treatment, but the hierarchy is slightly different: `=` is itself treated as a propositional function, and `=` can be an identity on 1st order, second order, ... arbitrary order functions. The first citation of chapter 12's axiom of reducibility appears at \*13.101, and with which applied to \*13.101, the order of `=` has been generally collapsed off. 

The identity has to be defined at such a late chapter(p.22), because:
1. Identity is built on functions
2. Functions comes with different types within the hierarchy defined in chapter 12
3. Axiom of Reducibility has to be used in the proof, also because of the hierarchy. Also see (p.57) for a informal reasoning on why it needs to be used

Also see audit's [chapter 12 & 13](./5_audit.md/#chapter-12) for a deeper analysis.

### Chapter 14
This chapter begins with a significantly complicated symbol `(ιx)(φx)` to denote a *description*. Here are the reasons why this symbol is such complicated:
- `(ιx)` means the descriptions should be treated as the same type of a `x`. In chapter 20, `x` will be lifted to some random `α` denoting classes
- `(φx)` means the description should describe a thing just like `φx`

This special symbol comes with an explicit "scope" notion, also implicitly required for symbols later chapters. Typically speaking, only functions come with scopes, but PM is defining scopes for a ("incomplete")symbol(p.67). 

### Chapter 20
Definition of class in this chapter, at first glance, appears to be pretty obscure. It is not being stated clearly like a structure, and instead, how is it defined is written *in the middle of the text*. An extra difficulty at understanding its definition is its similarity to the definition of a function `Psi x^`. Both class and function(actually, its first appearance at \*20.59) have been presented in this chapter's theorems.

Another thing we can unfold into detail is the definition of \*20.02(p.188). 
1. `x∈(z^φz)` is a function of `φ`
2. If we pick this function as the `f` in \*20.01, we obtain `x∈(z^ψz) = ∃φ, φ z <[- z -]> ψ z /\ (x ∈ φ)`. The `x` at the rightmost cannot be renamed into anything else because it is the `x` defined in the "function" we are using.
3. In this form, we "patch" the expression with \*20.02, matching exactly the rightmost sub expression, and rewriting the whole expression into `x∈(z^ψz) = ∃φ, φ z <[- z -]> ψ z /\ φ x`, and then make a slight reordering.

(TODO: Use `n20_61` and its variants as a starting point to explain the missing of specifications)

Analyzing on how this proof applies also reveals more insights on how should we design PM symbols in Rocq. The depth of its influence result in our preference of "monomorphic theorems, polymorphic symbols" as a design guide. See [tactics](./4_tactics.md) for further explanation.

While not being stated explicitly, being hinted in previous chapters(TODO: source?), I suppose class has constituted to a hidden and "more practical" new hierarchy. This is because theorems in this chapter has prepared a lot of aspects for class, including its equivalent for Axiom of Reducibility. It doesn't, though, provide insights such as "what is the equivalent of matrix to class?" and so on. That being said,

|           Property          |                Limitation             |
|-----------------------------|---------------------------------------|
| Highest proposition order   | Arbitrary + class?                    |
| Modus Ponens theorem        | Arbitrary                             |
| Generalization              | Predicative functions(p.165) + class  |
| Functions                   | Arbitrary + class?                    |
| Introducing fresh variables | Arbitrary + class?                    |
| Theorem variants            | Arbitrary + class                     |
| Function type               | Can be untyped                        |
| Function parameters         | Individuals, matrices and classes     |

----------------

TODO:
- composition nature for types/defs, ref. *20.62
- ch9: rewrite parts about how operator works; plan to rewrite the whole chapter in the future, with custom "forall" highlighted and defined
  - the operators defined are directly obtaining 1-order props from e-props
  - 1-order props are just being assumed
- ch9: Explain when do we need `set X := Intro_x`
- ch9: type of props varies by funcs...  "practically ignored"(p.162); the definition can be fixed by change to "returning order of a function"
