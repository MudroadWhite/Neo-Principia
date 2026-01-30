# Neo Principia
[![Screenshot](./header.png)](https://www.youtube.com/watch?v=MMD9n-YZ93o)

Continuation of [Principia Mathematica's formalization](https://github.com/LogicalAtomist/principia) by Landon Elkind.

## Why working on it
- Principia Mathematica has a stable version
- Principia Mathematica is not textbook math
- Formalized PM is a good textbook for verifiers
- Formalizing PM feels like building an obelisk
- Rocq doesn't need a lot of version updates

## Features
Compatability.

- [Documented](./docs/README.md) and with [slides](./slides/).
- "Just `pose` and `rewrite`": No 3rd party library. Minimal, native and simple tactics.
- "Just as it is": Clear proof structure, clean, maybe beautiful proof window. Forward style reasoning as Principia's direction.

## Can you make sure that the code/proof is 100% correct?
No. 

- This depends on how much and deep you interpret the terms. There exist ideas expressed in natural language, not with formulae. They will be written as comments in our code.
- Successful `Qed`s are still false positives, due to a lot of delicate details. For example, `Ltac` isn't well designed, important details are not expressed in propositions, etc.. I have caught several bugs in the repo because of them.
- Our designs on notations still rely on manual checks.
- I didn't deeply examine the code in chapter 1 - 5.
- In our code, a few of the theorems are still unprovable! They might either because it is really unprovable, or mostly just that we didn't figure out the correct way to prove it.

## Can Principia Mathematica can be completely formalized?
**Yes**: With [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/), there are already a lot of materials to help formalizing Principia Mathematica. Since our project covers the foundation of the rewriting system with which all advanced mathematical ideas are built on, formalizing PM is already theoretically accessible.

**No**: Although math ideas in PM are supposed to be fixed and limited, how PM organizes these ideas - maybe the "meta" question of the whole book - is another story. Functions, types and other concepts such as descriptions in chapter 14 have their icebergs under the tips. They question the dependency relationships between themselves and the rewriting system, which should be even different from what people will acknowledge in modern type systems. 

[This awesome blog](https://lawrencecpaulson.github.io/tag/Principia_Mathematica) has presented a series of critiques on PM. [Some of these critiques](https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html) pretty much summarize what we have seen so far: PM's notorious notation system, highly "trivial"(chores-like) theorems, and its historical background to guarantee a missing revisit.

[This awesome repo](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT) seems to arrive at similar observations. See paper in the repo on its in-depth discussions of PM's functions.

Our current expectation is successfully express everything **before chapter 14** with a shallow embedding. This allows us to retain tolerance to explore the odds, attune with the simplifications appeared in the text, and gather non-trivial, easy problems for other people to collaborate with. *Early optimization is the root of all evil*.

## How well have you formalized?
Which means 2 questions:

- **How much have you formalized?** 179 - 94 = 85 pages. See [mechanics](./docs/3_mechanics.md) for detailed discussions.
- **How deep can you formalize?** We won't construct the deep embedding, as explained above. See [audit](./docs/5_audit.md) for secondary limitations.

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
Although I have tried to organize the issues well to indicate the current progress, I don't have rich experience in collaborations. It's suggested to open a new issue for inquiries, and I'll see what I can give.

## Related works
- [Landon Elkind's formalization of Principia Mathematica](https://github.com/LogicalAtomist/principia)
- [ndrwnaguib's formalization in Lean](https://github.com/ndrwnaguib/principia)
- [Randall Holmes's formalization of ramified type theory](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT)