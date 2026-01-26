# Overview
## What is Principia Mathematica?
Wiki's entry of [History of type theory](https://en.wikipedia.org/wiki/History_of_type_theory) says Principia is a *ramified theory of types*. This gives us the impression that Principia is a big type system, familiar to most of the functional coders. At the moment, the only formalization of ramified theory of types I can find on GitHub is [written by Randall Holmes](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT).

We also have a type system, defaulted by most people, in Rocq. Propositions are elements of sets, functions are modeled with lambda calculus. The most significant one: by the noted CH correspondence, everything are either types or elements under types. These "common sense" fail in Principia. Propositions are not types. Sometimes for brevity propositions are untyped. The inference is performed by rewriting on propositions, not on types. Type plays a much more auxiliary role, and Principia which embodies ramified theory of types, is actually a rewriting system.

## What is the value of this project?
Proposing Principia Mathematica is a matter of theory, and verifying such a theory is a matter of application. This project aims to be a scythe to demystify a myth. This project wraps up math and philosophy ideas, writes down, organizes and iterates like a software. This project is a small world to communicate, between math, philosophy and computer science people.

This project shows the power of type-theory-based modern formal verifiers, with only mediocre technology being used. This project [sculpts a better base](https://x.com/jdlichtman/status/2015174938865655950) for others to craft, and exposes how much of PM cannot be automated. It is to be detected bugs easily, modified easily, executed with controlled automation, and maybe built on with better abstractions. It saves you the time to buy a physical copy of the book, flip the pages with anxiety and boredom just to grind every line of proofs written in a ruthless massive tomb that appears in your dream and drags your hair into a mess every night. This project can inspire indie gamedevs whose core goal is making mediocre ideas into games; the flood of Principia Mathematica jokes therefore continues on X.

## Who did what
All of chapter 1 - 5 are directly attributed to [Landon's formalization of Principia](https://github.com/LogicalAtomist/principia).

I started this project by
- [x] Making chapter 1 - 5 into a Rocq project
- [x] Simplifying `Nicod1_4.v`, `Yuelin.v`, `Jorgensen3_47.v`, `Lemma5_7.v` in Landon's original repository, cutting down 20% of their LoC and greatly enhance readability
- [x] Simplifying, bug-picking chapter 1 - 5, cutting down \~1k LoC in total
- [x] Rest of the works can be found at the beginning of [mechanics](./3_mechanics.md).