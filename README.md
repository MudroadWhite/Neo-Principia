# Neo Principia
Continuation of [Principia Mathematica's formalization](https://github.com/LogicalAtomist/principia) by Landon Elkind.

## Why working on it
- Principia Mathematica has a stable version
- Principia Mathematica is not textbook math
- Formalized PM is a good textbook for verifiers
- Formalizing PM feels like climbing a mountain
- Rocq doesn't need a lot of version updates

## Features
Compatability.

- "Just `pose` and `rewrite`": No 3rd party library. Minimal, native and simple tactics. Forward style reasoning, as in original Principia's proof.
- Clear proof architecture and clean, maybe beautiful proof window.
- [Documented](./docs/README.md) and with [slides](./slides/).

## Can you make sure that the code/proof is 100% correct?
No. 

- This depends on how much and deep you interpret the terms. There exist ideas expressed in natural language, not with formulae. They will be written as comments in our code.
- The design of `Ltac` isn't good(to be more exact, `match` doesn't work as one might think), so that even successful `Qed`s are nevertheless false positives. Actually, I have caught several bugs in the repo from this issue.
- Our designs on notations still rely on manual checks.
- I didn't deeply examine the code in chapter 1 - 5.
- Under our interpretation, a few places out of the vast seem to be unprovable!

## Can Principia Mathematica can be completely formalized?
**Yes**: With [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/), there are already a lot of materials to help formalizing Principia Mathematica. Since our project covers the foundation of the rewriting system with which all advanced mathematical idea are built on, formalizing PM is already theoretically accessible.

**No**: Although math ideas in PM is supposed to be fixed and limited, how PM organizes these ideas - maybe the "meta" question of the whole book - is another story. Functions, types and other concepts such as descriptions in chapter 14 have their icebergs under the tips. They question the dependency relationships between themselves and the rewriting system, which should be even different from what people will acknowledge in modern type systems. We need to explore the odds before correctly define a deep embedding. From a software engineer's perspective, *early optimization is the root of all evil*. By doing this we will also gather non-trivial, easy problems for other people to collaborate with.

[This awesome blog](https://lawrencecpaulson.github.io/tag/Principia_Mathematica) has presented a series of critiques on PM. [Some of these critiques](https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html) pretty much summarize what we have seen so far:
1. PM has a notorious notation system.
2. Most theorems of PM are trivial, that is, chores that can directly derived from definitions
3. A lot of techniques has been developed since PM "released", including higher order logic, programming language analysis, etc..

Our current expectation is successfully express everything **before chapter 14** with a shallow embedding. 

## How deep can you formalize?
- This project is **not** going to give a formal model/deep embedding to Principia, as explained above.
- Distinguishing between `∀ x y, P x y` and `∀ x, ∀ y, P x y` is currently **on plan**.
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
- [x] Chapter 11 - Quantified propositions extended to more than one variables. Similarly, extended notation supports for `→` and `↔`.
- [x] Chapter 12 - Axiom of reducibility, and its conceptual support, the `Predicate` predicate.
- [x] Chapter 13 - Propositional equality(different from definitional equality). Support for instantiating predicative functions. One theorem seems to be unprovable.
- [ ] (WIP)Chapter 14 - The `iota` operator for descriptions, a predicate `iota_E` for its *existence* statement. Theorems on them.

## Running the code
Coq/Rocq version: 8.20.0, installed with the [opam](https://opam.ocaml.org/) environment:

```bash
opam update
opam pin coq add 8.20.0
```
Running the project:

```bash
make
```

The `Makefile` for `make` is supposed to automatically detect all `.v` files under the `pm` folder, generate the `_CoqProject` file and compile the whole folder.

### Running the code, line by line
IDEs for Coq/Rocq varies, but here is my preference:

- WSL instance: Ubuntu 18.04 on WSL 2
- VS Code version: 1.80.0
- Extension installed on VSCode locally: WSL. When running the extension, it will generate a notification to help you install VSCode support in the current WSL instance.
- Extension installed on VSCode, in its remote WSL environment: VSCoq v0.3.7 from [OpenVSX](https://open-vsx.org/extension/maximedenes/vscoq).

## To contribute
Although I have tried to organize the issues well to indicate the current progress, I am not used to collaborate with others. It's suggested to open an new issue for inquiries, and I'll see what I can give.
