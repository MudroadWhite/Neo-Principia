# Suggestion

This chapter is a proposal for a specification of PM's type system, based on the details we have gathered in [Audit Report](./5_audit.md).

Ideas:
- Randall's work mostly mathematically analyze the symbols in PM
- We analyze PM symbols by checking how well can they implemented in Rocq

TODO:
1. "Base order" and "shift" operator
2. impredicativity vs predivativity, the design of `!`
3. Extra scoping rules
4. MP and other tactics
5. polymorphic notations and monomorphic theorems(?)
6. Utilization of `setoid_rewrite`