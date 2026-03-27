# Mechanics of Principia Mathematica
## Basic setups
### What are the types pf propositions in Principia?
Principia has 3 types(not mathematical type) of theorems: `Pp`(primitive propositions), `Df`(definitions, usually definitions for new symbols) and `Thm`s(ordinary theorems). A hidden trait of proposition in Principia is those propositions written in natural language. 

With a few counter example in chapter 1, they are usually about typing a term with a specific symbol. A well formed term must be well typed. Some of these typing rules are `Pp`; while some of them might be `Thm`, being derived from some previous typing rules.

### How to read the propositions in Principia?
Principia Mathematica uses *dot notation* just to eliminate the brackets. There are a lot of materials explaining how to understand the dot notation. In practice, Principia also sets up the indentation for propositions that have to be splitted into multiple lines, and they surprisingly never go wrong. One can even understand the priority at ease with the indentations, without much on dot notations.

While types for propositions in PM constitutes to a hierarchy, PM doesn't express the hierarchy directly. Instead, typing rules say "what different terms can be considered as the same type". Such "of the same type" style definitions have been scattered into all the chapters.

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

### What are the real problems to formalize Principia Mathematica?
With *reconstruct every theorems in PM as much as we can* as our assumption, our implementation is facing awareness to *how well does symbols of PM work with each other*. This means to the following:
1. Can we design the correct type system for PM, since PM doesn't explicitly type the propositions?
2. Can we distinguish different contexts for theorems in different chapters, since their validity is proven in different context?
3. Can we design a set of notations that can work well altogether?
4. For current implementation, can we give correct types to parameters? For example, is it really that function's type should be just `Prop -> Prop`, when the difference between untyped functions and predicative functions become more and more significant in later chapters?

Problems arisen from the assumption can be alleviated by some other reconstruction; see [Randall's](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT) suggestion on alternative symbols. The problems listed above will not be discussed in this chapter, but can be inferred from analytics in [audit](./5_audit.md).

We now start exploring the main ideas for each chapters.

## Chapters
### Chapter 1
Chapter 1 presents some basic `Pp`s to set everything up, and practically speaking, we find it out that `Pp`s usually suggest something just as meta in the Rocq system: for PM's *modus ponens* to work, we will have to implement a *MP* tactic in Rocq - currently with their parameter types unchecked because we didn't implement it yet.

- Having something in our proof window means it has been asserted/implied true
- Asserting `H1 : P` means asserting `P` as an **elementary proposition**
- (\*1.1)If there is a rule saying that "if we can assert `H1` then we can assert `H2 : Q`", we are allowed to obtain `H2 : Q` in such a style. It could be happen if we are getting situations like `(|- P) -> (|- Q)`(p.92), which doesn't occur within formulae in PM.

There are no dependency explicitly stated in PM on \*1.1.

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

*What is a function in PM?* When it says something like "function X", it actually means "a function's *body* X, whose parameters are all symbols appeared within". If I say "function x ∧ y", it actually means `(fun x y => x ∧ y)` for Rocq's representation. The same applies to most theorems in PM.

- (p.94)Definitional equality is undefined in PM
- **elementary propositions** are closed under `¬` and `∨`
- **elementary functions** are closed under `¬` and `∨`

By proving a theorem, we mean:
- Everything is restricted to elementary propositions and elementary functions
- Deduction is performed through *modus ponens* designed in \*1.11. Currently we don't see dependencies for \*1.1

(p.92)Note: not to confuse "not-p" in the "(2) Elementary propositional functions" with `¬ p`, where `¬` is symbolic negation and "not" is a made-up predicate in natural language.

### Chapter 2
While everything in chapter 1 are primitive propositions, chapter 2 starts to use them to construct some basic results. 

- For general rules on citation, see related paragraphs in [How does Principia proof theorems?](./3_mechanics.md/#how-does-principia-proof-theorems).
- In particular, `[(x)]` is a *citation* to a definition/primitive proposition*. `[x]` is a *citation* to a *theorem*. We can also cite previous steps.
- Citations for modus ponens and syllogism will generally be omitted.

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

Later, a typing algorithm is given in this chapter, completely generating the hierarchy of proposition types for any order. In particular it gives special rules for individuals, as they are not propositions nor functions(p.51, p.132). Despite the explanation, why individual is not proposition is still unclear. My guess is that they are supposed to be only appeared as parameters, and cannot be asserted as a full proposition.

**TODO: REWRITE PARTS ABOUT TYPING ALGORITHM**

The typing algorithm is described both in name and in the style of "of the same type"(\*9.131). Basically the type information entails the order and the kind("is it a function or a proposition?") of the expression. This typing algorithm will prevent constructions such as `P P`(p.40).
1. **Individual.** All individuals have a `Individual` type. (p.162)Individuals are supposed to be some *specific fixed value*s
2. **EProp.** All elementary propositions have a `EProp` type
3. **EFunc.** Arguments: types of parameters. PM doesn't actually have the idea of `→` types, but it's quite obvious `→` types are the best abstraction. Elementary functions should have same type if 
    1. e-func A is obtained through `¬` on e-func B
    2. e-func A is obtained through `∨` on e-func B and C 
    3. They take same number of arguments, and each of argument is same in type
4. **Prop.** Argument: type of a single function. A higher order proposition type is obtained from a 1-order lower function. Two `Prop n` should have same type if
    1. Proposition A is obtained through `¬` on proposition B. `∨` can have different types for its arguments, so it doesn't preserve types
    2. Both proposition A and B are obtained by quantifying two propositional functions of the same 1-order lower type. Both of the functions either 
        1. Have exactly 1 parameter
        2. Have exactly 2 parameters and are quantified on the second parameter. This is the proposition-version rule to support typing for multiple-parameter functions
   Note that not all proposition of same order proposition have the same type, because of the types of functions.
5. **Untyped function.** Argument: unknown. Although it is completely not within the "of the same type" algorithm, it has been practically used throughout the text, and is implicitly allowed, getting even greater awareness(as well as confusion) in later chapters. If we want to build a type system however, it seems that we have to expose its nature from a modern view to go further on. For the same reason, there might be *untyped propositions* constructed on these function as well...
6. **Constants.** For something more specific, constants are some letters that shouldn't be treated as a variable, and is allowed to be appeared in functions. In our implementation such distinction is very hard to make a difference.

By proving a theorem in chapter 9 - 11, we mean:
- Proposition types are capped and proven at first order propositions, with extra e-prop type restrictions in case described above
- All real variables in the theorems can be given arbitrary orders after chapter 11(p.127, p.128, discussion on typing `¬` and `∨`)
- *Modus ponens* is already at its maximum strength
- *Generalization* can only be performed on *individual*s, being already atomic in the current expression. Note that currently we didn't implement generalization as a `Ltac`, and to fit better into the text, we should actually implement such tactic.
- Fresh *individual*s can be introduced in the middle of the proof on need

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

- **Predicative function** is synonym as **matrices**(p.164). Predicative function of `a` where `a`'s order is n, though, strictly refers to a matrix of order n+1.
- **Matrices** are built on **matrices** of a 1-level lower order.
- **Functions** are built on **matrices**, with *not all* of its variables generalized(p.14)
- **Propositions** are built on **matrices**, with *all* possible variables generalized

Several comments on matrices and functions:
1. (p.52)Matrix only takes matrices or individuals as variables. By "taking something as variable", we mean what symbols can be appeared in the `A` of the `∀ A` part, *before any instantiations*. Variables of the form `∀ (∃ a, φ a), (∃ a, φ a) x` seems to be out of consideration, which is some n-order function or proposition; also see (p.53). Note that we won't have this issue in previous chapters prior to the definition of matrix, and functions can take (elementary)propositions as parameters. Conversely, elementary propositions in this hierarchy is called elementary matrices. 
2. Order of functions are not dependent on order of arguments(p.164, also p.49 for difference between `fun x => φ x` and `fun x => ∀ φ, φ x`)
3. It appears that any `∀`s and any `∃`, under this hierarchy, cannot be produced by directly instantiating some functions; we have to start from completely constructing a matrix, then obtain all the quantifiers through generalizing individuals/other matrices with a controlled scope. The procedure here is clearly unnatural.

There is another way to understand the difference between a matrix and a proposition, by identifying their apparent and real variables(p.18). Is it really that *there are no propositions containing real variables*, as [Wittgenstein](https://wittgensteinproject.org/w/index.php/Notes_on_Logic) have said? We don't really know, but let's just vibe with the [examples](./3_mechanics.md/#chapter-12). One crucial difference between real and apparent variables, though, is that real variables are not given types(p.128, "in practical purpose") while apparent variables are given types.

Axiom of Reducibility is introduced in this chapter for 2 reasons:
1. (p.49)When we define `x = y` as `∀ φ, φ x → φ y`, assuming it is untyped, we might still have `φ := fun x => (∀ φ, φ x → φ y)` or `φ := fun y => ∀ φ, φ x → φ y`. In order words for `fun x => φ x`, `fun x => (∀ φ, φ x → φ a)` has been a value that needs to be avoided. 
2. On the other hand, sometimes we want to speak of as "many" functions as we can. It turns out that, while we cannot precisely say all functions of a parameter `a`, but we can say all `n`-order functions of a parameter `a` and set `n` to infinity.

For 2 above, axiom of reducibility says that: when we want to have a very large "all" function `fun a => φ a` with `φ` of order `n`, we can simulate with a predicate function `fun a => ψ a`. The predicativity of `ψ` here means it is just 1-order higher than `a`, and we are assuming *this `ψ` exists*. In the context of [chapter 13](./3_mechanics.md/#chapter-13), we can have a more intuitive understanding.

Chapter 12 also brings the symbol `!` to awareness, and will be frequently used in later chapters. `!` has several different meanings all within the same time:
1. Emphasize(p.163, the second "It will be seen that...") that we might consider both the function and its parameter as variables for an expression. The purpose is to make functions as variables easier for people to recognize.
2. Indicate that the function is a *predicative function*, not a random untyped one.

By proving a theorem,
- Theorems in all previous chapters are free to be **lift**ed to their higher order equivalents, which is independent of *Axiom of Reducibility*
- Not all symbols in an expression needs to be identified as variables. They can be **constants**(p.164)
- (p.52, 162, 163, 164)Only individuals and matrices are allowed as parameters for matrices. (n-order) functions and propositions are not allowed as parameters.
- (p.165)Only predicative functions are allowed to be generalized
- Functions are allowed to be *untyped*, taking a parameter and return a proposition of *unknown* order.

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
The first thing to mention about this chapter is the role of \*20.02(p.188). We unfold the proofs in PM in deeper expansion:
1. `x∈(z^φz)` is a function of `φ`
2. If we pick this function as the `f` in \*20.01, we obtain `x∈(z^ψz) = ∃φ, φ z <[- z -]> ψ z /\ (x ∈ φ)`. The `x` at the rightmost cannot be renamed into anything else because it is the `x` defined in the "function" we are using.
3. In this form, we "patch" the expression with \*20.02, matching exactly the rightmost sub expression, and rewriting the whole expression into `x∈(z^ψz) = ∃φ, φ z <[- z -]> ψ z /\ φ x`, and then make a slight reordering.

Analyzing on how this proof applies also reveals more insights on how should we design PM symbols in Rocq. (TODO: to be continued...in audit)

TODO: 
- A newer hierarchy to be "practical" to use
- ambiguity on the interpretation for `φ ! x` where we don't know if `!` stands for predicate or just the function as the focus
- Mixed symbol definitions making it hard to distinguish
- "ambiguity of function types for symbol definitions..."

## See Also
- https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html
- https://plato.stanford.edu/entries/pm-notation/
- https://en.wikipedia.org/wiki/Glossary_of_Principia_Mathematica
- https://randall-holmes.github.io/Drafts/notesonpm.pdf
- https://www.religion-online.org/article/the-axiomatic-matrix-of-whiteheads-process-and-reality/
- https://nap.nationalacademies.org/read/10866/chapter/66
- https://mathoverflow.net/questions/27793/russell-and-whiteheads-types-ramified-and-unramified

TODO:
- rewrite related parts about "of the same type" in chapter 9; examine chapter 10 & 11, maybe chapter 13 - 14 on typing rule
- composition nature for types/defs, ref. *20.62