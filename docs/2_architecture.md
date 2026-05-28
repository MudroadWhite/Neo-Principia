# Project architecture

## What's under this project?
- `./docs/` provides all necessary documentation for this project. 
- `./slides/` contains a pseudo-slide in markdown format for a presentation I held privately, written in Chinese.
- `./Makefile`, `meta.yml`, `.github/`, etc. for basic configurations on building this project.
- `./pm/` being the actual show of this project. 

## What's under `./pm`?
Each chapter in Principia has a corresponded `.v` file. In the future, we might further recluster the chapters into sections and parts.

`lib.v` mostly provides experimental/necessary features to be used globally.

Chapter 1 - 5, additionally with scattered proof pieces under `pm/misc`, are directly inherited from [Landon's formalization of Principia](https://github.com/LogicalAtomist/principia). We keep the code as original as possible as a reference, with only slight optimizations.

That being said, all conventions introduced below **applies after chapter 9**.

## What's under a single `.v` file?
1. `Require Import` that cites other chapters and `lib.v`, so that you can use theorems and tools from these imported files.
2. Occasional comments to explain what has been done here and there
3. *Variants* for existing theorems. This includes
   - `Admitted` propositions postfixed with `_alt`, `_pred` or `_class`
   - Locally introduced propositions postfixed with `a` within a `TOOLS` section, introduced below
4. Self-defined Rocq predicates, being necessary in later chapters. They should be put in the beginning of each chapters rather than being aggregated in `lib` to prevent large loading overhead and unnecessary warnings during compilation.
5. `Notations` defined corresponded to the symbols in Principia, and modeled with self-defined Rocq predicates. Each `Notation` comes with a `Scope`. To define a notation in a scope, we have to `Declare Scope`. To use the notation, we have to `Open Scope`. If we don't want the notation appear within proof, we command to `Close Scope`.
6. And eventually, everything left are the actual proofs, coming with `Definition`s and `Theorem`s.

- Every `Scope`s opened within a single file is **required** to be closed at the end of the file.

## What is `Definition` and `Theorem`?
As *vernacs* in the Rocq proof system, `Definition`s and `Theorem`s are being used, not because of their *literal meaning*, but because of their ability to correctly organize the data, just like a *class* or a *structure* in typical programming languages.

Rocq's `Definition`s are used to define *primitive propositions* and *definitions* in Principia. As the mechanic of `Definition` is interfering with the foundation of Principia, Principia's `Definition`s are immediately `Admitted` without providing any further proofs. Whether we should provide with proofs is a future question.

Similarly, `Theorem`s are used to define *theorems* in Principia, and are intended to be proven and `Qed`ed.

Every `Definition` or `Theorem` represents a proposition in Principia. They usually have both parameters on the left hand side of the `:`, plus a proposition that "has" parameters on the right hand side. But these parameters are different: *rhs* parameters are intended to be only filled through deductions, which will be mostly discussed in the [tactics](./4_tactics.md) chapter; and *lhs* parameters are the real ones to *set a proposition up*.

Additionally, for theorems in Principia, we are allowed to set up its *variants*. This will be also explained in [tactics](./4_tactics.md).

## What is `Notation`?
As chapters push on, PM will have higher requirements on symbol definitions to model the math ideas. `Notation`s in Rocq is the perfect tool for implementing more complicated symbols.

Each `Notation` comes with a `Scope` for us to freely switch between different notations. Each `Notation` will be additionally defined twice: one for easy writing, prefixed with `debug_`, and one for pretty printing.

## What's under a single proof?
For a theorem, if it has been splitted into several steps to prove in the text, rather than just citing related theorems for hints, we call this theorem comes with a "long proof". Otherwise it has a short proof.

- Our structure is **not required** to be enforced on short proofs.

Otherwise for a long proof, it usually has the following structure:
```Coq
Proof.
  (* TOOLS *)
  (* tools to set up... *)
  (* ******** *)
  assert (S1 : x + y = z).
  {
    (* subproof for S1, where "S" here stands for "step" *)
  }
  assert (S2 : x + y = z → x + y = z).
  {
    (* subproof for S2 *)
  }
  (* and so on... *)
  exact Sn.
Qed.

```

### `TOOLS` section
- A `TOOLS` header is **required** to be place at the beginning of a long proof, if any tool is being used.
- Other tools not being placed in the `TOOLS` section is **required** to be stated with an explicit comment.

Technical features, that can be be found under `lib.v`, usually require a "warmup" before being available, for example, introducing an extra individual with the proof(with `set (X := Intro_individual "x")`), or prepare a modified version of a theorem for more convenient use. `TOOLS` section is for performing such preparations.

### `assert` blocks
- All long proofs are **required** to adapt to the proof architecture picted above.

For long proofs, the first tactic we use always starts with an `assert`, for specifying intermediate steps corresponded to ones in the original text. 

There are several reasons for organizing proofs with `assert`. The most significant one is readability. Besides, we can have several equivalent forms for a proposition, i.e. `(fun x => x) x` is not very far from just `x` or `(fun y => y) x`. Switching between them requires delicate application with tactics for all different cases. If we set the desired form as a subgoal, we only need to use tactics to prove for a equivalent form to `x`, and skip the tedious transformations. One last thing for `assert` is that it limits the scope of theorems we use. When we leave the scope, these theorems are automatically cleared away, and only the intermediate steps as `S1` `S2` are being pertained. As a result, the proof window becomes extremely clean.

`assert`ed intermediate steps are introduced into the hypotheses.

## What are the tactics we use for a single proof?

As introduced above, `assert` and `set`, sets up the general architecture to write the proof.

Beneath the architecture comes the details of how we prove a theorem. By referring to [SEP](https://plato.stanford.edu/entries/principia-mathematica/), we can divide our tactics into 2 types. As the slogan says, "just `pose` and `rewrite`".

- `pose proof`, occasionally with `apply`, instantiates a existing theorem to use.
- `rewrite`, `setoid_rewrite`, custom defined Ltacs like `MP` `Syll`, or more generally, all tactics except `pose proof` are for rewriting to, and even a level down, deducing new propositions from existing propositions.

[tactics](./4_tactics.md) goes into the details of these tactics.
