# The Proof
This folder, `./pm/`, is the place where you see the proofs. The proof for chapter `n` will be put in the `.v` file named `ch*n*`.

## Who did what
[Landon's formalization of Principia](https://github.com/LogicalAtomist/principia) has been mostly pertained as a tribute.

[I(MDR)](https://github.com/MudroadWhite/) started this project by
- [x] Making chapter 1 - 5 of Landon's original repository into a Rocq project
- [x] Simplifying `Nicod1_4.v`, `Yuelin.v`, `Jorgensen3_47.v`, `Lemma5_7.v`, cutting down 20% of their LoC and greatly enhance readability
- [x] Simplifying, bug-picking chapter 1 - 5, cutting down \~1k LoC in total
- [x] Redesigning custom `Ltac`s in chapter 1 - 5 to their perfection, eliminating all incorrect `Ltac` usages once and for all, plus cleanups like `clear`/`move` that were once necessary

[Our first contributor, @tangyongsheng17-sudo](https://github.com/tangyongsheng17-sudo) is responsible for `./dagaz/` as our *purification* act on chapter 1 - 5, to provide a more refined, organized proof for them.

## Project status
We are building: 
- [ ] [Chapter 1](./ch1.v)
- [ ] [Chapter 2](./ch2.v)
- [ ] [Chapter 3](./ch3.v)
- [ ] [Chapter 4](./ch4.v)
- [ ] [Chapter 5](./ch5.v)
- [x] [Chapter 9](./ch9.v) - A demonstration set of theorems to show chapter 1 - 5 can be extended to quantified propositions(with single "apparent variable"). Basic demonstration for a predicate called "IsSameType". Support for instantiating individuals.
- [x] [Chapter 10](./ch10.v) - The real and practical alternative to chapter 9, being used in later chapters. Material implications converted to formal implications. Notation supports for `→` and `↔` with single apparent variable.
- [x] [Chapter 11](./ch11.v) - Quantified propositions extended to more than one variables. Similarly, extended notation supports for `→` and `↔`.
- [x] [Chapter 12](./ch12.v) - Axiom of reducibility, and its conceptual support, the `Order` type.
- [x] [Chapter 13](./ch13.v) - Propositional equality(different from definitional equality). Support for instantiating predicative functions. 
- [x] [Chapter 14](./ch14.v) - `Notation` setups for `ι` the descriptions. Theorems on them.
- [x] [Chapter 20](./ch20.v) - Notation on class, and theorems of classes. Under the iceberg tip, making different notations working consistently with each others.

### Milestones
**2026.06:** The documentation for this project is complete. There will be no more major updates for this project, unless something is happening. We have identified all technical difficulties, and they are enough to provide a solid foundation to formalize PM.

**2026.05:** Chapter 20, the last chapter we are translating, is mostly complete. We're heavily organizing the documentation, which seems to be more important. Also, welcome our [first PR](https://github.com/MudroadWhite/Neo-Principia/pull/133) from an external contributer.

**2026.02:** Chapter 14, the first chapter with an *incomplete/context based* symbol(the description), has been finished. Finishing these chapters involves both new context for theorems to be assumed, and more complicated symbols to be defined. Also, we have finished the complete documentation from chapter 1 to 14. This project has been mature enough to be examined by everyone, and viewers should find it way easier to comprehend and participate into criticisms towards Principia.

**2025.10:** Chapter 9, the first chapter after chapter 5, has been finished. Chapter 9's theorems has a whole new context to be interpreted, so designing a new way to prove the theorems, in contrast to chapter 1 - 5, is required. Completion of this chapter involves a lot of mind works and deprecated experiments. Also, "New Principia" has been renamed into "Neo Principia".

**2025.9:** New Principia, this project, has been started and established. We have set up a workable environment for Landon's project and successfully compiled everything in chapter 1 - 5.

--------
Happy proving!
