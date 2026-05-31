# Overview

> Reading PM is maddening. ([Source](https://randall-holmes.github.io/Drafts/pmsemantics.pdf))

## What is Principia Mathematica?
Wiki's entry of [History of type theory](https://en.wikipedia.org/wiki/History_of_type_theory) says Principia is a *ramified theory of types*. This gives us the impression that Principia is a big type system, familiar to most of the functional programmers. At the moment, the only formalization of RTT I can find on GitHub is [written by Randall Holmes](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT).

We also have a type system, defaulted by most people, in [Lean](https://www.youtube.com/watch?v=d3K3ZfiyG3I)/[Rocq](https://www.youtube.com/watch?v=I42Qq7LCyO8). Propositions are elements of sets, functions are modeled with lambda calculus. The most significant one: by the noted CH correspondence, everything are either types or elements under types. These "common sense" fail in Principia. Propositions are not types. Sometimes for brevity propositions are untyped. The inference is performed by rewriting on propositions, not on types. Type plays a much more auxiliary role, and Principia which embodies ramified theory of types, is actually a rewriting system.

## What is the aesthetics for this project?
For formalizing Principia Mathematica, there can be many features that you want to address with. [pmGenerator](https://github.com/xamidi/pmGenerator) tries to produce the shortest proof as possible. [Randall's work](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT) attempts at reducing the complexity of PM with better mathematical notions. There might be ppl having other directions, such as providing maximum automation for Principia Mathematica's deduction.

Here is our take: pertain maximum PM flavor. Which means:
- We want to implement all symbols appeared in PM. In other fancier words, parse the syntax of PM at our best
- We want minimal setups to get the work done
- We want maximum PM theorems being proven
- We want each proof step be followed and presented
- In addition, we are allowed to simplify PM's proof when it goes tedious


TODO: 
- "Just `pose` and `rewrite`": No 3rd party library. Minimal, native and simple [tactics](./docs/4_tactics.md). One theorem a line.
- "Just as it is": Principia flavor in maximum strength: Following PM's symbol definitions, deductions faithfully. Clear proof structure, clean, maybe beautiful proof window. 
- [Documented](./docs/README.md)(WIP - will be rewritten for most of the parts) and with [slides](./slides/).

To be more exact, we have:
- Demonstrated a proof architecture to formalize most of the theorems in Principia Mathematica with remarkable strength
  - This architecture has maintained a balance between term-level clarity and proof simplicity
  - This architecture has broken the record of the formalization pass through chapter 5 to chapter 20, haven't yet unleashed its maximum potential
- Provided a clear document to help readers go through the apocalypse
- Identified several defects and ambiguity in PM from a modern theorem prover's perspective
- Proposed a specification for prospective participants for grinding down to perfection

## Can Principia Mathematica be completely formalized?
Yes. There are 3 arguments to support formalizing PM:
1. Modern provers have enough tools to design a language
   1. We can parse PM's complete syntax easily
   2. We can give fixed interpretation to the completed language. By *fixed* I mean it doesn't need to be extended and prepare for any other exceptions
2. We have considered everything in the *Introduction* chapter, which summarizes over the logical foundation setups in PM
3. PM is necessarily an old rewriting system

[This awesome blog](https://lawrencecpaulson.github.io/tag/Principia_Mathematica) has presented a series of critiques on PM. [Some of these critiques](https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html) have summarized over the situations we have seen: despite its historical background(see [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/)) to guarantee a missing revisit, PM still gets a notorious notation system, highly "trivial"(chores-like) theorems. Also see [this awesome repo](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT)'s paper on its in-depth discussions of PM's propositional functions.

When formalizing PM, we have occurred to the following difficulties:
- We have to manually record the theorems, since PM doesn't have a digital version
- We have to manually find the correct theorem to complete the proof
- We have to manually comprehend PM's mountain of notations, symbols, theorems, and different contexts to interpret them
- We have to manually [identify](https://x.com/prz_chojecki/status/2060662313464496342) different meanings for terminologies in different chapters. For example, "functions" and "matrices"
- Being the most difficult one, we have to manually type every propositions. This project doesn't type PM's propositions, rendering some completed proofs false positive.

All factors above resulted in our unique preference for the proof: a *shallow embedding* utilizing a mixture of 2 major mechanics, PM's original "bottom-up construction" method and our "`rewrite`/`setoid_rewrite`", being detailed in [tactics](./4_tactics). As our first time to formalize PM, there might be more details to be implemented in later chapters; hard-designed system can result in difficult reconstructions for any unpredictable changes. The shallow embedding, sacrificed the 100% accuracy, in return retains tolerance to find the bugs, [attunes](https://www.youtube.com/watch?v=Vrf2rYRQReA&t=559s) with the ambiguity appeared in the text, and gathers non-trivial, easy problems for other people to collaborate with. *Early optimization is the root of all evil*, and our major task is to collect necessary information to construct the deep embedding.

Eventually, can we type every proposition in Principia? Within our [vision](./6_suggestion.md), *deep embedding for Principia Mathematica seems to be feasible*.

## Can we port the proof to Lean?
No. This project is heavily relied on `setoid_rewrite`, and Lean doesn't support `setoid_rewrite`, see [reference](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Rewriting.20congruent.20relations.html). Porting the proof to Lean might involve reconstructing the proof with `Quotient`, which should be an interesting alternative to discover.

## What is the value of this project?
Proposing Principia Mathematica is a matter of theory, and verifying such a theory is a matter of application. This project aims to be a [scythe](https://www.youtube.com/watch?v=gRivMEEZZE8&t=1539s) to demystify a decaded myth. This project wraps up ideas in the book, writes down, organizes and iterates like a software product. This project is a small world to communicate, between math, philosophy and computer science people.

This project shows the [power](https://www.youtube.com/watch?v=c7X_-J8C9As) of type-theory-based modern formal verifiers, with only mediocre technology being used. This project uses Rocq like a bag of pitons to [sculpt a better checkpoint](https://x.com/jdlichtman/status/2015174938865655950) for participants to craft, and exhibits a structured PM with as minimal Rocq tactics as possible. It is to be detected bugs easily, modified easily, executed with controlled automation, and maybe built on with better abstractions. It saves you the time to buy a physical copy of the book, flip the pages with anxiety and boredom just to [grind](https://www.tiktok.com/@ryranthe1st/video/6960880389275585798) every line of proofs written in a [ruthless massive tomb](https://www.youtube.com/watch?v=aBUFiQV30eM) that appears in your dream and drags your hair into a mess every night. This project can inspire indie gamedevs whose core goal is making mediocre ideas into games; the flood of Principia Mathematica jokes therefore continues on X.

This is a project where you can read and write the code line by line.

## Who did what
All of chapter 1 - 5 are directly attributed to [Landon's formalization of Principia](https://github.com/LogicalAtomist/principia).

I started this project by
- [x] Making chapter 1 - 5 of Landon's original repository into a Rocq project
- [x] Simplifying `Nicod1_4.v`, `Yuelin.v`, `Jorgensen3_47.v`, `Lemma5_7.v`, cutting down 20% of their LoC and greatly enhance readability
- [x] Simplifying, bug-picking chapter 1 - 5, cutting down \~1k LoC in total
- [x] Redesigning custom `Ltac`s in chapter 1 - 5 to their perfection, eliminating all incorrect `Ltac` usages once and for all, plus cleanups like `clear`/`move` that were once necessary

Most code of chapter 1 - 5 are still pertained as a tribute to the previous work.

## Project status
We are building: 
- [x] Chapter 9 - A demonstration set of theorems to show chapter 1 - 5 can be extended to quantified propositions(with single "apparent variable"). Basic demonstration for a predicate called "IsSameType". Support for instantiating individuals.
- [x] Chapter 10 - The real and practical alternative to chapter 9, being used in later chapters. Material implications converted to formal implications. Notation supports for `→` and `↔` with single apparent variable.
- [x] Chapter 11 - Quantified propositions extended to more than one variables. Similarly, extended notation supports for `→` and `↔`.
- [x] Chapter 12 - Axiom of reducibility, and its conceptual support, the `Order` type.
- [x] Chapter 13 - Propositional equality(different from definitional equality). Support for instantiating predicative functions. 
- [x] Chapter 14 - `Notation` setups for `ι` the descriptions. Theorems on them.
- [x] Chapter 20 - Notation on class, and theorems of classes. Under the iceberg tip, making different notations working consistently with each others.

### Milestones
**Ongoing: Finish chapter 20**  Class is the last notion being introduced in the *Introduction* chapter. Implementing classes and relations symbolizes the availability to express everything in Principia, therefore this should be a very important feature, and maybe eliminate all technical difficulties for PM symbol definitions once and for all.

The 1st iteration to fill in the proof has finished, but filling in more missing proof definitely helps, so will be the current focus.

Even further plans: I could either
- Quit the project once chapter 20 has been completely translated
- Develop a new version of PM, with type system & AoR supported, and make a distinction from this project. I'm also planning to give version names like "staccato" "aria" or something

**2026.05:** Chapter 20, the last chapter we are translating, is mostly complete. We're heavily organizing the documentation, which seems to be more important. Also, welcome our [first PR](https://github.com/MudroadWhite/Neo-Principia/pull/133) from an external contributer.

**2026.02:** Chapter 14, the first chapter with an *incomplete/context based* symbol(the description), has been finished. Finishing these chapters involves both new context for theorems to be assumed, and more complicated symbols to be defined. Also, we have finished the complete documentation from chapter 1 to 14. This project has been mature enough to be examined by everyone, and viewers should find it way easier to comprehend and participate into criticisms towards Principia.

**2025.10:** Chapter 9, the first chapter after chapter 5, has been finished. Chapter 9's theorems has a whole new context to be interpreted, so designing a new way to prove the theorems, in contrast to chapter 1 - 5, is required. Completion of this chapter involves a lot of mind works and deprecated experiments. Also, "New Principia" has been renamed into "Neo Principia".

**2025.9:** New Principia, this project, has been started and established. We have set up a workable environment for Landon's project and successfully compiled everything in chapter 1 - 5.