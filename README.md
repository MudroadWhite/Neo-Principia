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

## How well have you formalized?
Which means 3 questions:

- **How much can you formalize?** Theoretically, the whole book. See [overview](./docs/1_overview.md/#can-principia-mathematica-be-completely-formalized) for an analysis.
- **How much have you formalized?** 186 - 94 = 92 pages. See [mechanics](./docs/3_mechanics.md) for detailed discussions.
- **How deep can you formalize?** We're using shallow embedding, which is not rigorous deep embedding. See [audit](./docs/5_audit.md) for other secondary limitations.

## Are you sure the code/proof is 100% correct?
No. Successful `Qed`s are still false positives. We haven't typed the propositions and miss the insights from them.

## Running the code
Coq/Rocq version: >= 8.20.0, < 9.0, installed with the [opam](https://opam.ocaml.org/) environment:

```bash
opam update
opam install coq
opam pin add coq 8.20.0
```
Running the project:

```bash
make
```

The awesome `Makefile` gathered from [@clarus](https://github.com/clarus)'s [awesome repo](https://github.com/formal-land/rocq-of-rust), is supposed to automatically detect all `.v` files under the `pm` folder, generate the `_CoqProject` file and compile the whole folder. This is done without deploying the project with `dune` environment.

### Running the code, line by line
IDEs for Coq/Rocq varies, but here is my preference:

- WSL instance: Ubuntu 18.04 on WSL 2
- VS Code version: 1.80.0
- Extension installed on VSCode locally: WSL. When running the extension, it will generate a notification to help you install VSCode support in the current WSL instance.
- Extension installed on VSCode, in its remote WSL environment: VSCoq v0.3.7 from [OpenVSX](https://open-vsx.org/extension/maximedenes/vscoq).

## To contribute
Although I have tried to organize the issues well to indicate the current progress, I don't have rich experience in collaborations. A contribution guideline is currently working in progress. It's still suggested to open a new issue for inquiries, and I'll see what I can give.

## Related works
- [Landon Elkind's formalization of PM](https://github.com/LogicalAtomist/principia)
- [ndrwnaguib's formalization of PM in Lean](https://github.com/ndrwnaguib/principia)
- [Randall Holmes's RTT implementation](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT)
- [xamidi's propositional calculus theorems](https://github.com/xamidi/luk-pmproofs) from [Łukasiewicz's L1-system](https://www.jstage.jst.go.jp/article/pjab1945/41/6/41_6_436/_pdf)
- Also his [pmGenerator](https://github.com/xamidi/pmGenerator) for something I didn't know what is it yet
- [Metamath solitaire's implementation on propositional calculus theorems](https://us.metamath.org/mmsolitaire/pmproofs.txt)