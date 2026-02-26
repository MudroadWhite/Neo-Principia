(* PM.pm.lib - tools, libraries, notations(temporarily?), and others to be used through the project *)

Require Import Unicode.Utf8.
Require Import ClassicalFacts.
Require Import Classical_Prop.
Require Import PropExtensionality.
Require Import String.

Export Unicode.Utf8.
Export Classical_Prop.
Export ClassicalFacts.
Export PropExtensionality.
Export String.

(* p.23: `=` propositions are allowed to be turned into `↔` propositions. An 
alternative tactic to this is `apply propositional_extensionality`. *)
Theorem eq_to_equiv : ∀ (P Q : Prop),
  (P = Q) → (P ↔ Q).
Proof.
  intros P Q H.
  split; try rewrite -> H; trivial.
Qed.

(* Chapter 12 & 13: a proposition, typed, of order `n`.
NOTE: 
- Unless necessary, we should never use ANYTHING beyond `Order 1`. It is for convenience 
  when we really need this we can search all occurences of Orders to be adapted
- For chapter 12, we might want to define an extra `Order2`. This should be implemented when
  necessary
TODO: 
- maybe in the future, checkout the definition for matrix and try to see if we can also integrate
in a definition for matrix
- add an extra implicit argument {shift : nat} where shift = 0 by default
*)
Fixpoint Order (n : nat) : Type :=
  match n with
  | 0 => Prop
  | (S m) => let A := Order m in (A -> Prop)
  end.

(* p.51: To instantiate variables appeared in a propositional function, we use the concept 
of "individual", designed as as wrapper just to tag an real variable. This allows easy identification 
on them and they are free to be created everywhere.
Individual cannot appear solely so they are neither propositions nor functions. But they can be passed 
into functions at will as parameters. Therefore, (p.133) there is a special rule to identify that they 
always have the same type
As parameters, however, rules in (p.133) is flawed: if I have one individual for 0-order parameters and
another for 1-order parameter, altogether for a 2-order function, will they still have the same type?
Currently we only set Individual to order 0, but it is supposed to be of any order 
*)

(* EXPERIMENTAL: the predicate below serves merely just for "how an untyped function of PM should be
defined in Rocq". Currently it is never used anywhere and only demonstrates an experimental idea *)
defined in Rocq". Currently it is never used anywhere and only demonstrates an experimental idea *)
Definition Intro_untyped {A : Type} (s : string) : A -> Prop. Admitted.

(* `Intro` Rocq predicates are used for introducing a term in the middle of the proof, which 
is something specific for PM's proofs. Here we provide the version for individuals and predicates *)
Definition Intro_individual (s : string) : Order 0. Admitted.

(* For the same reason above, I believe that predicative functions coming fresh(after chapter 13) should 
also be considered as individuals. TODO: This should be merged with `Intro_individual` *)
Definition Intro_pred (s : string) (n : nat) : Order n. Admitted.
