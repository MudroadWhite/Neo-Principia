# Suggestion for future works
As everyone should [expect](https://www.youtube.com/watch?v=qhF2Dxrt9i4), this chapter intends to draw a full period to the project. It has been 100 yrs ago that Russell and Whitehead published such a book that only receive a couple of readers; history flows fast, and 2008 comes with first complete proof for 4-color theorem, later been [discussed](https://proofassistants.stackexchange.com/questions/1105/how-does-the-formal-proof-of-the-four-color-theorem-work) on the internet. It should have been a regret that I haven't finished this project earlier; we have implemented a formalization project with extremely simple setups, even easier than the 4-color theorem; the difficulty for reading Principia Mathematica, after 100 years, should be easier than an open source project. 

Before getting further, several ppl should be given credits and thanks: Guillaume Clauret, my first boss, who initiated, ignited my ability to motor the Rocq prover; Landon Elkind the predecessor of this project; Randall Holmes, another precious source of information, many thanks for your warm and welcoming discussions that helps the completion of this project. We're having a collaborator, [tangyongsheng17-sudo](https://github.com/tangyongsheng17-sudo) who will make this project even better looking; without any of above, this project will not be complete.

We have a lot of things done, and still a lot of things undone and unplanned. Below is a collection of suggestions that prospective investigators might be interested in. To make the project better, one might want to:
- Figure out the precise meaning of elementary proposition and elementary propositional functions
  - which enables us to implement propositions as propositions, and functions as functions
  - which enables us to design `∨`, `¬`, and `∀` precisely, no longer as Rocq's defaults
  - which might enables us to construct meaningful proof objects
  - and which enables the availability to design a typing algorithm, that patches the most crucial insight missed in this project
- Design a full hierarchy system mechanic, which might
  - include a polymorphic `Hierarchy` type to abstract over necessary ingredients
  - include a `Base` type to settle down an order for all individuals to share with, and for functions' types built on them
  - include a `shift` tactic/predicate where `shift x thm` produces a x-order lifted version of the theorem
  - include another `shift` where `Base` can be changed from `Prop` into `Class` or other symbol types
- Record and implement all `!`s appeared in the text, to make a strict difference for predicative and impredicative functions
  - which enables us to implement Axiom of Reducibility
- Implement the scoping mechanic proposed in `experiment.v`
- Design tactics for generalization and instantiation such that they are as convenient as `MP`
- Investigate deep into `setoid_rewrite` so that it supports rewriting on custom-defined notations like descriptions and classes
- Classify theorems in chapter 1 - 10, to see if they have a conventional name like "absorption rule" more than just a number
  - which enables us to see the conceptual relations between the theorems explicitly

And at the very end, it is recommended for any investigators to independently formalize one whole chapter at a time, to enjoy the joy and the pain that I have felt; as something I have learnt during writing this project, designing the framework, rather than presenting the complete proof, is the most enjoyable part for the development. It is recommended for any investigators to soon leave it to the next successor, to allocate the rest of your life on even more meaningful events; as a project of historical perspective, we always have the freedom to pace casually and walk with a light mood. Should there be ppl taking over the continuation, there shall be one day when the most compact and detailed crystallization of `1+1=2` can be witnessed, no more cloaked up as a century myth.

\- 2026.06.12, hastily finished by 

MDR/MudroadWhite. Onward, to my next project!
