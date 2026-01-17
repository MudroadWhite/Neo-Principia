# Audit Report
We're aware that: 
- Distinguishing between `∀ x y, P x y` and `∀ x, ∀ y, P x y` is currently **on plan**.
- Limiting parameter's "type"(orders)s for a function is currently **partially supported**, by only writing them as a header in each of the chapters.
- Checking their types is currently **unavailable**.
- Designing functions that accepts arbitrary length is currently **unavailable**.
- Constructing "types" for every propositions in Principia is **on plan**.
- Expressing "types(orders) for a function's parameters" is **on plan**.
- Completely translate primitive propositions written in natural language, into formalized Rocq proof, is **on plan**.
- More to come...

It has been a convention for formal verification people to attach an audit report for their projects, and we should have our own analogue.

## What is the value of this project?
This project aims to be a scythe to demystify a myth. This project is a small world to communicate, between theory and application, and between math, philosophy and computer science people. This project wraps up math and philosophical ideas, written down, organized and iterates like a software. This project shows the power of type-theory-based modern formal verifiers, with only mediocre technology being used. This project can potentially be an inspiration for Steam indie videogames, because making mediocre ideas into games is what these developers do.

## Evaluation
Evaluation for Principia is based on the following questions:
1. For each chapter, what are the new ideas being brought up?
2. Are these ideas easy to be expressed in Rocq?
3. Are proofs in each chapter complete? How much have it missed?

Within which, anatomy on ideas(1) is performed in [mechanics](./3_mechanics.md). We start straight into the commentaries without reviewing them.

**Definitions.** We didn't express the *compositional* and *inheriting* nature of Principia. "Registering" new meanings to already defined theorems seems to suggest practical utilization of concepts in programming languages: typeclasses, interfaces, perhaps even monads.

**Chapter 9.**
- formalized most of the theorems... 
- but useless anyways

TODO:
- chapter 9, ... chapter 11: nice
- chapter 13 14: can be verified with larger tweaks; notation is annoying
