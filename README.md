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
- "Just `pose` and `rewrite`": No 3rd party library. Minimal, native and simple tactics. One theorem a line.
- "Just as it is": Principia flavor in maximum strength: Principia-style deduction; Principia-style symbols defined with `Notation`s. Clear proof structure, clean, maybe beautiful proof window. 

## Are you sure the code/proof is 100% correct?
No. Successful `Qed`s are still false positives, due to a lot of delicate details. For example: 
- `Ltac` isn't well designed
- We simplified some primitive propositions and merged them as a whole
- Some propositions are written in natural language
- I didn't deeply examine the code in chapter 1 - 5
- Our current implementation doesn't enforce the correct types on PM terms.

## Can Principia Mathematica be completely formalized?
Yes.

With [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/), there are already a lot of materials to help formalizing Principia Mathematica. Our project already covers the foundation of the rewriting system with which all advanced mathematical ideas are built on.

Beneath the code and down to the core, the difficulty in formalization is how PM organizes its ideas. This means:
- PM gets a mountain of notations and symbols
- PM doesn't explicitly type the propositions
- Some PM rules are written in natural language
- Theorems in different chapters are interpreted under different hierarchies, while the core idea for theorems are supposed to be shared among all chapters
- Terminologies also have different meanings in different chapters, and the range of the distinction is a manual work. For example, "functions" and "matrices"

[This awesome blog](https://lawrencecpaulson.github.io/tag/Principia_Mathematica) has presented a series of critiques on PM. [Some of these critiques](https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html) pretty much summarize what we have seen so far: PM's notorious notation system, highly "trivial"(chores-like) theorems, and its historical background to guarantee a missing revisit.

[This awesome repo](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT) seems to arrive at similar observations. See paper in the repo on its in-depth discussions of PM's functions.

Currently, we are using *shallow embedding* to express Principia Mathematica as much as we can. While this doesn't ensure 100% correctness, we are rewarded to retain tolerance to find the bugs, attune with the simplifications appeared in the text, and gather non-trivial, easy problems for other people to collaborate with. *Early optimization is the root of all evil*. See [project goal and milestones](./docs/1_overview.md/#project-goal-and-milestones) for further details.

As the most central idea, can we type every proposition in Principia? Within our reach, a plan to write the typing program in Rocq has started at slow speed, and *deep embedding for Principia Mathematica seems to be feasible*.

## How well have you formalized?
Which means 2 questions:

- **How much have you formalized?** 186 - 94 = 92 pages. See [mechanics](./docs/3_mechanics.md) for detailed discussions.
- **How deep can you formalize?** We won't construct the deep embedding for now, as explained above. See [audit](./docs/5_audit.md) for secondary limitations.

## Running the code
Coq/Rocq version: >= 8.20.0, installed with the [opam](https://opam.ocaml.org/) environment:

```bash
opam update
opam pin coq add 8.20.0
```
Running the project:

```bash
make
```

The awesome `Makefile` gathered from @clarus 's [awesome repo](https://github.com/formal-land/rocq-of-rust), is supposed to automatically detect all `.v` files under the `pm` folder, generate the `_CoqProject` file and compile the whole folder. This is done without deploying the project with `dune` environment.

(Minimum requirement for Coq is currently under investigation)

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