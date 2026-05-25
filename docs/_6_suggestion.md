# Suggestion for future architecture

TODO: 100 yrs ago, Russell and Whitehead published the book that only few customers dare to read. TODO: x yrs ago, several ppl attemped to write this book into a program. now this is an open source project...

From the analysis in [tactics](./4_tactics.md), we are witnessing how nontrivial it can be to implement a *proof architecture*, by which I mean something similar to the design patterns in software design, could emerge just because this is how someone wants to simplify the proof and organize the content. This is something that AI currently doesn't aim at, see [example](https://www.youtube.com/watch?v=lcgPj7hge-E). While we didn't reveal the whole proof structure, we have gathered enough information for the next step. This chapter is a suggestion for a specification of PM's complete type system, based on the details we have gathered in [Audit Report](./5_audit.md).

TODO:
1. Randall's conversation influenced our insight; suggestion on MP and individuals
2. "Base order" and "shift" operator
3. impredicativity vs predivativity, the design of `!`
4. Extra scoping rules
5. MP and other tactics
6. polymorphic notations and monomorphic theorems(?)
7. Utilization of `setoid_rewrite` (for schemes? investigate deeper into its automatic power?)
8. Philosophy of "internalization" (relate to the inheritance nature)
9. For future successors and participants: independently design a chapter, or design your own typing system for Principia
10. What have I learned: designing the framework is the most enjoyable part; difference between AI and hand written FV: u can design the architecture on your own and shrink the proof - produce organized things could be a challenge

## Future directions
- classify theorems
- schemes for theorems/variants
- add type, add predicativity, add AoR
- tactic automation?
- construct meaningful proof objects
