# Neo Principia
Continuation of [Principia Mathematica's formalization](https://github.com/LogicalAtomist/principia) by Landon Elkind.

## Why working on it
- Principia Mathematica has a stable version
- Coq doesn't need a lot of version updates
- Formalized PM is a good education material for verifiers
- Formalizing PM feels like climbing a mountain

## Features
This project aims towards demonstration and addresses compatability. Readers are supposed to be able to read the code line by line modulo technical hacks. Future contributers should find it easy to continue for better works while pertaining the style. 
- "Just `pose` and `rewrite`": Forward style reasoning, as in original Principia's proof. No 3rd party library. Minimal, native and simple tactics.
- Clear proof architecture and clean, maybe beautiful proof window.
- [Documented](./docs/README.md).

## Can you make sure that the code/proof is 100% correct?
No. Reasons:
- Rigor of proofs relies heavily on how much and how deep you interpret the terms. There are fundamental terms that either involve a brand new architecture, or I just cannot represent as code. This results in a portion of propositions written down as comments in natural language.
- The design of `Ltac` isn't good(to be more exact, `match` doesn't work as one might think), so that even successful `Qed`s are nevertheless false positives. Actually, I have caught several bugs in the repo from this issue.
- I didn't deeply examine the code in chapter 1 - 5.
- Under our interpretation, a few places out of the vast seem to be unprovable! If only I were filling an audit report.

## Can Principia Mathematica can be completely formalized?
With [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/), there are already a lot of materials to help understanding and formalizing Principia Mathematica. Practically speaking, I feel PM looks more like a rewriting system than a type system: initially, its propositions are supposed to be untyped and only concerns about inference. Typing rules are usually written in natural language, and types on terms are only strictly required as the chapter goes on and their rigor get refined. As our project covers the foundation of the rewriting system, and all advanced mathematical concepts are built on this system, formalizing PM is to just a problem of engineering.

To be more exact, [this awesome blog](https://lawrencecpaulson.github.io/tag/Principia_Mathematica)has presented a series of critiques on PM. [Within which](https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html) the author comments that 
1. PM has a notorious notation system. (For example, chapter 13 shocks me when I first read through it)
2. Most theorems of PM are trivial, that is, chores that can directly derived from definitions
3. A lot of techniques has been developed since PM "released", including higher order logic, programming language analysis, etc.. and (my conclusion)these tools are supposed to be rich enough to revisit the history

~~(Current plan
)Conclusion: despite the theoretical accessability, we're currently setting the end for the formalization at chapter 14, covering cover the full foundation of the rewriting system, plus several advanced mathematical concepts being formalized. This should make an demonstration that is rich enough for people to view at.~~

## How refined can you formalize?
Below are some technical aspects arisen from this project.
- Distinguish between `forall x y, P x y` and `forall x, forall y, P x y` is currently **on plan**.
- Limiting parameter's "type"(orders)s for a function is currently **partially supported**, by only writing them as a header in each of the chapters.
- Checking their types is currently **unavailable**.
- Designing functions that accepts arbitrary length is currently **unavailable**.
- Constructing "types" for every propositions in Principia is **on plan**.
- Expressing "types(orders) for a function's parameters" is **on plan**.
- Completely translate primitive propositions written in natural language, into formalized Rocq proof, is **on plan**.
- More to come...

## How much have you formalized?
This project is currently focused on the following parts:
- [x] Chapter 9 - A demonstration set of theorems to show chapter 1 - 5 can be extended to quantified propositions(with single "apparent variable"). Basic support for a predicate called "IsSameType". Support for instantiating individuals.
- [x] Chapter 10 - The real and practical alternative to chapter 9, being used in later chapters. Material implications converted to formal implications. Notation supports for `->` and `<->` with single apparent variable. One theorem seems to be unprovable.
- [x] Chapter 11 - Quantified propositions now extend to more than one variables. Notation supports for `->` and `<->` extended to multiple apparent variables as well.
- [x] Chapter 12 - Axiom of reducibility, and its conceptual support, the `Predicate` predicate.
- [ ] \[WIP\] Chapter 13 - A new set of theorems on Identity, which is different from definitional equality. Support for instantiating predicative functions. One theorem seems to be unprovable.

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
