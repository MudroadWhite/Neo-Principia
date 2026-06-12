# Suggestion for future works
As everyone should expect, this chapter intends to draw a full period to the project. It has been 100 yrs ago that Russell and Whitehead published such a book that only receive a couple of readers; history flows fast, and in 2008, first complete proof for 4-color theorem has been published and be [discussed](https://proofassistants.stackexchange.com/questions/1105/how-does-the-formal-proof-of-the-four-color-theorem-work) on the internet. It should have been a regret that I haven't finished this project earlier; we have implemented a formalization project with extremely simple setups, and the difficulty for reading Principia Mathematica, after 100 years, should be supposed to be even easier than a open source project. 

Before getting further, several ppl should be given credits and thanks: Landon Elkind as the predecessor of this project; Randall Holmes, as another precious source of information, and many thanks for your warm and welcoming discussions that helps the completion of this project. We're having a collaborator, [tangyongsheng17-sudo](https://github.com/tangyongsheng17-sudo) who will make this project even better looking; Without any of above, this project will not be complete.

We have a lot of things done, and still a lot of things undone and unplanned. Below is a collection of suggestions that prospective investigators might be interested in. To make the project better, one might want to:
- Figure out the precise meaning of elementary proposition and elementary propositional functions
  - Which enables us to implement propositions as propositions, and functions as functions
  - Which enables us to use custom `\/`, `~`, and `forall` precisely
  - Which might enables us to construct meaningful proof objects
  - And which enables the availability to design a typing algorithm
  - Furthermore enables the availability to design correct hierarchies
- Design a full hierarchy system mechanic, which might
  - include a polymorphic `Hierarchy` type to abstract over necessary ingredients
  - include a `Base` order for all individuals to share with, and for functions' types built on them
  - include a `shift` tactic where `shift x thm` produces a x-order lifted version of the theorem
  - include another `shift` where `Base` can be changed from `Prop` into `Class` or other symbol types
- Record and implement all `!`s appeared in the text, to make a strict difference for predicative and impredicative functions
  - Which enables us to implement Axiom of Reducibility
- Implement the scoping mechanic proposed in `experiment.v`
- Design tactics for generalization and instantiation such that they are as convenient as `MP`
- Investigate deep into `setoid_rewrite` so that it supports rewriting on custom-defined notations like descriptions and classes
- Classify theorems in chapter 1 - 10, to see if they have a conventional name like "absorption rule" more than just a number

And at the very last, it is recommended for any investigators to independently formalize one whole chapter at a time, to enjoy the joy and the pain that I have felt. As something I have learnt during writing this project, designing the framework, rather than presenting the complete proof, is the most enjoyable part for the development. Should there be anyone accepting the challenge, hopefully one day everyone will witness the most compact and detailed crystalization of `1+1=2`, no more cloaked up as a century myth.

\- 2026.06.12, hastily finished by 

MDR/MudroadWhite. Onward, to my next project!