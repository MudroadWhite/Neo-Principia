# Neo-Principia
Continuation of [Principia Mathematica's formalization](https://github.com/LogicalAtomist/principia) by Landon Elkind.

This project is currently focused on the following parts:
- [x] Chapter 9 - A demonstration set of theorems, extending from elementary propositions to quantified propositions(with single "apparent variable"). Basic support for a predicate called "IsSameType".
- [x] Chapter 10 - The real alternative to be used in the later chapters, converting material implications into formal implications. Notation supports for `->` and `<->` with single apparent variable. One theorem seems to be unprovable.
- [x] Chapter 11 - Notation supports for `->` and `<->`, extended to multiple apparent variables.
- [x] Chapter 12 - Axiom of reducibility, and its conceptual support, the `Predicate` predicate.
- [ ] \[WIP\] Chapter 13 - A new set of theorems on Identity, which is different from definitional equality.

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
No. Here are the reasons:
- Rigor of proofs relies heavily on how much and how deep you interpret the terms. There are fundamental terms that either involve a brand new architecture, or I just cannot represent as code. This results in a portion of propositions written down as comments in natural language.
- The design of `Ltac` isn't good(to be more exact, `match` doesn't work as one might think), so that even successful `Qed`s are nevertheless false positives. Actually, I have caught several bugs in the repo from this issue.
- I didn't examine the code in chapter 1 - 5.

## How much can you formalize?
Below are some technical aspects arisen from this project.
- Distinguish between `forall x y, P x y` and `forall x, forall y, P x y` is currently **on plan**.
- Limiting parameter's "type"(orders)s for a function is currently **partially supported**, by only writing them as a header in each of the chapters.
- Checking their types is currently **unavailable**.
- Designing functions that accepts arbitrary length is currently **unavailable**.
- Constructing "types" for every propositions in Principia is **on plan**.
- Expressing "types(orders) for a function's parameters" is **on plan**.
- Completely translate primitive propositions written in natural language, into formalized Rocq proof, is **on plan**.
- More to come...

## Running the code
Coq version: 8.20.0, installed with the `opam` environment:

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
- Extension installed locally: `WSL`. WSL's VSCode support can also be installed from extension at VSCode's side.
- Extension installed on WSL instance: VSCoq v0.3.7 from [OpenVSX](https://open-vsx.org/extension/maximedenes/vscoq).

## To contribute
Although I have tried to organize the issues well to indicate the current progress, I am not used to collaborate with others. It's suggested to raise an issue for inquiries, and I'll see what I can give.
