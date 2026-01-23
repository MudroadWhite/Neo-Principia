# Overview
## What is Principia Mathematica?
Wiki's entry of [History of type theory](https://en.wikipedia.org/wiki/History_of_type_theory) says Principia is a *ramified theory of types*. This gives us the impression that Principia is a big type system. The only formalization of ramified theory of types I can find on GitHub so far is [written by Randall Holmes](https://github.com/Randall-Holmes/Randall-Holmes.github.io/tree/master/RTT).

We also have a type system, the default for most people, for Rocq. Propositions are elements of sets, functions are modeled with lambda calculus. The most significant one: by the noted CH correspondence, everything are either types or elements under types. These "common sense" fail in Principia. Propositions are not types. Sometimes for brevity propositions are untyped. The inference is performed by rewriting on propositions, not on types. Type plays a much more auxiliary role, and Principia which embodies ramified theory of types, is actually a rewriting system.

## What is the value of this project?
This project aims to be a scythe to demystify a myth. This project is a small world to communicate, between theory and application, and between math, philosophy and computer science people. This project wraps up math and philosophical ideas, written down, organized and iterates like a software. This project shows the power of type-theory-based modern formal verifiers, with only mediocre technology being used. This project can inspire indie gamedevs whose core job is making mediocre ideas into games; the jokes flood of Principia Mathematica on X therefore continues.

With shallow embedding, this project aims at providing a better base for others. It is to be detected bugs easily, modified easily, evaluated everything with a controlled automation, and maybe built on with better abstractions.

## Who did what
All of chapter 1 - 5 are directly attributed to [Landon's formalization of Principia](https://github.com/LogicalAtomist/principia).

I started this project by
- [x] Making chapter 1 - 5 into a Rocq project
- [x] Simplifying `Nicod1_4.v`, `Yuelin.v`, `Jorgensen3_47.v`, `Lemma5_7.v` in Landon's original repository, cutting down 20% of their LoC and greatly enhance readability
- [x] Simplifying, bug-picking chapter 1 - 5, cutting down \~1k LoC in total
- [x] Rest of the works can be found at the beginning of the project [README](../README.md).