# 5. Audit Report

It has been a convention for formal verification people to attach an audit report for every project they work on, and we should have our own analogue.

## What is the value of this project?
This project aims to be a scythe to demystify a myth. This project revisits the history and tries to draw a period to the past. This project is a small world to communicate, between theory and application, and between math, philosophy and computer science people. This project wraps up math and philosophical ideas, written down, organized and iterates like a software. This project shows the power of type-theory-based modern formal verifiers, with only mediocre technology being used. This project can potentially be an inspiration for Steam indie videogames, because making mediocre ideas into games is what these developers do.

## Overview: what is Principia Mathematica?
From wiki's entry of [History of type theory](https://en.wikipedia.org/wiki/History_of_type_theory), the "type system" we are formalizing is called "ramified theory of types". 

Commonly used type systems(or just the default of Rocq) will give us some "common sense": propositions are elements of sets, functions are modeled with lambda calculus, etc.. Perhaps the most significant one: everything are either types or elements under types. These "common sense" fail in ramified theory of types: the inference is performed by rewriting on propositions. These propositions are not modeled with types themselves(actually what CH correspondence does), and sometimes for brevity they are "untyped". Types in this system play on a much more auxiliary role.

We shall also note that the definitions in Principia is different from most textbook math and programming practices: we usually fix an operator and assign a function for its interpretation, but definitions in Principia usually involves 2 operators at a time. In contrast to *`~ a` should be defined as something*, we can immediately see in chapter 9 that they start with *`~` applied on an `∃` proposition should be defined as something*. At this moment, our formalization doesn't express such detail, but it seems to suggest something like typeclasses or interfaces, maybe even monads to interpret these definitions correctly, for its strong implication on *compositions*.

## Evaluation
The evaluation for this project is based on the following questions:
1. For each chapter, what are the new ideas being brought up?
2. Are these ideas easy to be expressed in Rocq?
3. Are proofs in each chapter complete? How much have it missed?

We will start straightly into the commentaries, without reviewing the definitions of ideas in each chapter. Anatomy on ideas are performed in [mechanics](./3_mechanics.md).

**Chapter 9**.
- formalized most of the theorems... 
- but useless anyways

TODO:
- chapter 9, ... chapter 11: nice
- chapter 13 14: can be verified with larger tweaks; notation is annoying
