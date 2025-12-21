# Neo Principia
Continuation of [Principia Mathematica's formalization](https://github.com/LogicalAtomist/principia) by Landon Elkind.

## Why working on it
- Principia Mathematica has a stable version
- Principia Mathematica is not textbook math
- Formalized PM is a good textbook for verifiers
- Formalizing PM feels like climbing a mountain
- Coq doesn't need a lot of version updates

## Features
Compatability.

- "Just `pose` and `rewrite`": No 3rd party library. Minimal, native and simple tactics. Forward style reasoning, as in original Principia's proof.
- Clear proof architecture and clean, maybe beautiful proof window.
- [Documented](./docs/README.md) and with [slides](./slides/).

## Can you make sure that the code/proof is 100% correct?
No. 

- This depends on how much and deep you interpret the terms. There exist concepts explained in natural language, not with formula. Some of these propositions will be written as comments in our code.
- The design of `Ltac` isn't good(to be more exact, `match` doesn't work as one might think), so that even successful `Qed`s are nevertheless false positives. Actually, I have caught several bugs in the repo from this issue.
- I didn't deeply examine the code in chapter 1 - 5.
- Under our interpretation, a few places out of the vast seem to be unprovable!

## Can Principia Mathematica can be completely formalized?
Yes. 

With [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/), there are already a lot of materials to help formalizing Principia Mathematica. Since our project covers the foundation of the rewriting system, and all advanced mathematical concepts are built on this system, formalizing PM is already theoretically complete, and remains to be a problem of engineering.

[This awesome blog](https://lawrencecpaulson.github.io/tag/Principia_Mathematica) has presented a series of critiques on PM. [Within which](https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html) the author states that 
1. PM has a notorious notation system. (For example, chapter 13 starts to go crazy for anyone reading it the first time)
2. Most theorems of PM are trivial, that is, chores that can directly derived from definitions
3. A lot of techniques has been developed since PM "released", including higher order logic, programming language analysis, etc.. and (my conclusion)these tools are supposed to be rich enough to revisit the history

We have gathered a lot of exceptional treatments than won't be seen in typical math textbooks during our formalization, for example, functions are not defined by lambda calculus, multiple definitions are being used for a single concept, etc.. This complicated situation is the main motivation for us to set our current goal: in contrast to immediately formally embed Principia into Rocq, we will just Rocq-validate everything **before chapter 14** to have a initial feeling about the situation.

## How deep can you formalize?
- This project is **not** going to give a formal model to Principia, as explained above.
- Distinguishing between `forall x y, P x y` and `forall x, forall y, P x y` is currently **on plan**.
- Limiting parameter's "type"(orders)s for a function is currently **partially supported**, by only writing them as a header in each of the chapters.
- Checking their types is currently **unavailable**.
- Designing functions that accepts arbitrary length is currently **unavailable**.
- Constructing "types" for every propositions in Principia is **on plan**.
- Expressing "types(orders) for a function's parameters" is **on plan**.
- Completely translate primitive propositions written in natural language, into formalized Rocq proof, is **on plan**.
- More to come...

## How much have you formalized?
**(172 - 94) = 78** pages.

- [x] Chapter 9 - A demonstration set of theorems to show chapter 1 - 5 can be extended to quantified propositions(with single "apparent variable"). Basic support for a predicate called "IsSameType". Support for instantiating individuals.
- [x] Chapter 10 - The real and practical alternative to chapter 9, being used in later chapters. Material implications converted to formal implications. Notation supports for `→` and `↔` with single apparent variable. One theorem seems to be unprovable.
- [x] Chapter 11 - Quantified propositions now extend to more than one variables. Notation supports for `→` and `↔` extended to multiple apparent variables as well.
- [x] Chapter 12 - Axiom of reducibility, and its conceptual support, the `Predicate` predicate.
- [x] Chapter 13 - A new set of theorems on Identity, which is different from definitional equality. Support for instantiating predicative functions. One theorem seems to be unprovable.
- [ ] (WIP)Chapter 14 - The `iota` operator for description, and its scope support.

## Running the code
Coq/Rocq version: 8.20.0, installed with the `opam` environment:

```bash
opam update
opam pin coq add 8.20.0
```
Running the project:

```bash
make
```

The `Makefile` for `make` is supposed to automatically detect all `.v` files under the `pm` folder, generate the `_CoqProject` file and compile the whole folder.

## Running the code, line by line
IDEs for Coq/Rocq varies, but here is my preference:

- WSL instance: Ubuntu 18.04 on WSL 2
- VS Code version: 1.80.0
- Extension installed locally: WSL. WSL's VSCode support can also be installed from extension at VSCode's side.
- Extension installed on WSL instance: VSCoq v0.3.7 from [OpenVSX](https://open-vsx.org/extension/maximedenes/vscoq).

## To contribute
Although I have tried to organize the issues well to indicate the current progress, I am not used to collaborate with others. It's suggested to raise an issue for inquiries, and I'll see what I can give.
