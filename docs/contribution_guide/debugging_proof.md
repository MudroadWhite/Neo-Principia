# Debugging proofs for Neo Principia
While most of the chapters are filled with pretty greek letters, they are the results of complete artifact being prettified. Developing the code involves debugging. Debugging could mean, for example:
- `simpl` to simplify a hypothesis or goal
- `Close Scope`/`Open Scope` somewhere to enable/disable specific notations.
- `pose proof` / `Print` a theorem to see how it looks like or for reference
- `move` to rearrange the order of hypotheses
- `clear` to remove some hypothesis that will never be used

In particular, for every `Notation` we have designed, in addition to their prettified version, we also come with an extra set of `debug` scope for actual development. Notations for `debug` scope is not intended to print beautifully, but to write easily. 

- The duality mentioned above is **required** to be enforced on all `Notation`s we have designed.
